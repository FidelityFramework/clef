namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.Syntax
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.Infrastructure
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module LazyIdentityTypes = Clef.Compiler.NativeTypedTree.Expressions.Types
module LazyIdentityCollections = Clef.Compiler.NativeTypedTree.Expressions.Collections
module LazyIdentityApplications = Clef.Compiler.NativeTypedTree.Expressions.Applications
module LazyIdentityLiterals = Clef.Compiler.NativeTypedTree.Expressions.Literals
module LazyIdentityMono = Clef.Compiler.Nanopass.Monomorphization
module LazyIdentityValues = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues

module private LazyThunkIdentities =
    let same expected actual = Assert.Equal(formatType (applySubst expected), formatType (applySubst actual))

    let expression source =
        match parseStringWithDefaults ("module LazyIdentity\nlet observed = " + source) "lazy-identity.clef" with
        | ParseSuccess (ParsedInput.ImplFile implementation) ->
            let (SynModuleOrNamespace(decls = declarations)) = Assert.Single implementation.Contents
            let binding = declarations |> List.pick (function SynModuleDecl.Let(bindings = [binding]) -> Some binding | _ -> None)
            let (SynBinding(expr = expression)) = binding
            expression
        | parsed -> failwithf "Expected one parsed lazy expression: %A" parsed

    // Exercise the owning checker before Baker replaces logical thunk formals
    // with the physical environment formal. Body cases deliberately use the
    // real source binding lookup and capture analysis.
    let rec rawExpr (env: LazyIdentityTypes.TypeEnv) (builder: NodeBuilder) = function
        | SynExpr.Const(constant, range) ->
            match LazyIdentityLiterals.checkConst env constant with
            | Ok(ty, value) -> builder.Create(SemanticKind.Literal value, ty, LazyIdentityTypes.rangeToSourceRange range)
            | Error error -> failwithf "Literal failed: %A" error
        | SynExpr.Ident identifier ->
            let binding = LazyIdentityTypes.tryLookupBinding identifier.idText env |> Option.get
            builder.Create(SemanticKind.VarRef(identifier.idText, binding.NodeId), binding.Type,
                           LazyIdentityTypes.rangeToSourceRange identifier.idRange)
        | SynExpr.Paren(inner, _, _, _) -> rawExpr env builder inner
        | SynExpr.Lazy(inner, range) ->
            LazyIdentityCollections.checkLazy rawExpr LazyIdentityApplications.computeCaptures
                env builder inner (LazyIdentityTypes.rangeToSourceRange range)
        | other -> failwithf "Unsupported raw fixture expression: %A" other

    let raw source env builder = rawExpr env builder (expression source)

    let assertFormal (nodes: Map<NodeId, SemanticNode>) expectedArena (owner: SemanticNode) =
        match owner.Kind with
        | SemanticKind.LazyExpr(thunkId, ownerCaptures) ->
            let thunk = nodes[thunkId]
            match thunk.Kind with
            | SemanticKind.Lambda([(name, formalType, formalId)], bodyId, captures, _, LambdaContext.LazyThunk) ->
                Assert.True(nodes.ContainsKey formalId, sprintf "Lazy thunk formal %A must be resident" formalId)
                let formal = nodes[formalId]
                match formal.Kind with
                | SemanticKind.PatternBinding actual -> Assert.Equal(name, actual)
                | kind -> failwithf "Logical unit formal is not a parameter: %A" kind
                same Types.unitType formalType
                same Types.unitType formal.Type
                match applySubst thunk.Type with
                | NativeType.TFun(domain, result) -> same formalType domain; same nodes[bodyId].Type result
                | ty -> failwithf "Thunk lost its unit callable boundary: %A" ty
                same (Types.mkLazyType nodes[bodyId].Type) owner.Type
                Assert.Equal<NodeId list>([formalId; bodyId], thunk.Children)
                Assert.Equal<NodeId list>([thunkId], owner.Children)
                Assert.Equal(Some thunkId, formal.Parent)
                Assert.Equal(Some thunkId, nodes[bodyId].Parent)
                Assert.Equal(Some owner.Id, thunk.Parent)
                Assert.Equal<SourceRange>({ owner.Range with End = owner.Range.Start }, formal.Range)
                Assert.Equal(expectedArena, formal.ArenaAffinity)
                for role, participant in [EdgeRole.Parameter, formalId; EdgeRole.Body, bodyId] do
                    Assert.Contains(kindEdges thunkId thunk.Kind, fun edge ->
                        edge.Class = EdgeClass.Structural && edge.Role = role && edge.Ordinal = 0 &&
                        edge.Target = thunkId && edge.Sources = [participant])
                Assert.Equal<CaptureInfo list>(ownerCaptures, captures)
                formal, nodes[bodyId], captures
            | kind -> failwithf "Expected exactly one logical lazy formal: %A" kind
        | kind -> failwithf "Expected a source lazy owner: %A" kind

    let env () = { LazyIdentityTypes.createTypeEnv () with CurrentArena = ArenaAffinity.Explicit "source-lazy-arena" }
    let range = { File = "lazy-identity.clef"; Start = { Line = 1; Column = 0 }; End = { Line = 1; Column = 15 } }

    let checkSource source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node -> match node.Kind with SemanticKind.Error _ -> true | _ -> false)
        result.Graph

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LazyThunkIdentity")>]
type LazyThunkIdentityCases() =
    [<Fact>]
    member _.``Parsed lazy unit has a resident formal with source ownership before saturation``() =
        let builder = NodeBuilder()
        let env = LazyThunkIdentities.env ()
        let owner = LazyThunkIdentities.raw "lazy ()" env builder
        let _, body, captures = LazyThunkIdentities.assertFormal builder.Nodes env.CurrentArena owner
        Assert.Empty captures
        match body.Kind with
        | SemanticKind.Literal NativeLiteral.Unit -> ()
        | kind -> failwithf "Original lazy unit body was replaced: %A" kind

    [<Theory>]
    [<InlineData(false, false)>]
    [<InlineData(false, true)>]
    [<InlineData(true, false)>]
    member _.``Synthetic unit formal never shadows a lexical source named _unit``(parameter: bool, isMutable: bool) =
        let builder = NodeBuilder()
        let kind = if parameter then SemanticKind.PatternBinding "_unit" else SemanticKind.Binding("_unit", isMutable, false, None)
        let sourceType = DimensionalCases.measuredInt DimensionalCases.metre
        let source = builder.Create(kind, sourceType, LazyThunkIdentities.range)
        let env = LazyThunkIdentities.env () |> LazyIdentityTypes.addBinding "_unit" sourceType isMutable (Some source.Id) false
        let owner = LazyThunkIdentities.raw "lazy _unit" env builder
        let formal, body, captures = LazyThunkIdentities.assertFormal builder.Nodes env.CurrentArena owner
        let capture = Assert.Single captures
        Assert.Equal("_unit", capture.Name)
        Assert.Equal(isMutable, capture.IsMutable)
        Assert.Equal(Some source.Id, capture.SourceNodeId)
        Assert.NotEqual(source.Id, formal.Id)
        LazyThunkIdentities.same sourceType capture.Type
        match body.Kind with
        | SemanticKind.VarRef("_unit", Some definition) -> Assert.Equal(source.Id, definition)
        | kind -> failwithf "Synthetic formal replaced the source read: %A" kind

    [<Fact>]
    member _.``Nested lazy boundaries own distinct unit formals and retain the nested body``() =
        let builder = NodeBuilder()
        let env = LazyThunkIdentities.env ()
        let outer = LazyThunkIdentities.raw "lazy (lazy ())" env builder
        let first, inner, _ = LazyThunkIdentities.assertFormal builder.Nodes env.CurrentArena outer
        let second, body, _ = LazyThunkIdentities.assertFormal builder.Nodes env.CurrentArena inner
        Assert.NotEqual(first.Id, second.Id)
        match body.Kind with SemanticKind.Literal NativeLiteral.Unit -> () | kind -> failwithf "Lost nested unit body: %A" kind

    [<Fact>]
    member _.``Mixed outer and nested same-name reads retain exactly one outer capture``() =
        let builder = NodeBuilder()
        let range = LazyThunkIdentities.range
        let sourceType = DimensionalCases.measuredInt DimensionalCases.metre
        let outer = builder.Create(SemanticKind.PatternBinding "_unit", sourceType, range)
        let env = LazyThunkIdentities.env () |> LazyIdentityTypes.addBinding "_unit" sourceType false (Some outer.Id) false
        let first = builder.Create(SemanticKind.VarRef("_unit", Some outer.Id), sourceType, range)
        let inner = builder.Create(SemanticKind.PatternBinding "_unit", Types.boolType, range)
        let innerRead = builder.Create(SemanticKind.VarRef("_unit", Some inner.Id), Types.boolType, range)
        let nested = builder.Create(
            SemanticKind.Lambda(["_unit", Types.boolType, inner.Id], innerRead.Id, [], None, LambdaContext.RegularClosure),
            NativeType.TFun(Types.boolType, Types.boolType), range, children = [inner.Id; innerRead.Id])
        builder.SetParent(inner.Id, nested.Id)
        builder.SetParent(innerRead.Id, nested.Id)
        let repeated = builder.Create(SemanticKind.VarRef("_unit", Some outer.Id), sourceType, range)
        let children = [first.Id; nested.Id; repeated.Id]
        let body = builder.Create(SemanticKind.Sequential children, sourceType, range, children = children)
        for child in children do builder.SetParent(child, body.Id)
        let captures = LazyIdentityApplications.computeCaptures builder env body.Id Set.empty
        let capture = Assert.Single captures
        Assert.Equal("_unit", capture.Name)
        Assert.Equal(Some outer.Id, capture.SourceNodeId)
        Assert.NotEqual(Some inner.Id, capture.SourceNodeId)
        Assert.False capture.IsMutable
        LazyThunkIdentities.same sourceType capture.Type
        Assert.Equal<Set<string>>(Set.singleton "_unit", LazyIdentityApplications.collectVarRefs builder body.Id)

    [<Theory>]
    [<InlineData("let _unit: int<m> = 17<m>\n    let observed = lazy _unit\n    ignore observed")>]
    [<InlineData("let mutable _unit: int<m> = 17<m>\n    let observed = lazy _unit\n    ignore observed")>]
    member _.``Source local _unit retains its exact capture slot through lazy elaboration``(body: string) =
        let graph = LazyThunkIdentities.checkSource ("[<EntryPoint>]\nlet main _ =\n    " + body + "\n    0")
        let source, mutableValue = graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with SemanticKind.Binding("_unit", mutableValue, _, _) -> Some(node, mutableValue) | _ -> None) |> Assert.Single
        let contract = LazyIdentityValues.instances graph |> Map.values |> Assert.Single
        Assert.Equal((source.Id, source.Id, mutableValue), Assert.Single contract.Captured)

    [<Fact>]
    member _.``A source binding inside the lazy body does not capture a shadowed outer _unit``() =
        let graph = LazyThunkIdentities.checkSource """
[<EntryPoint>]
let main _ =
    let _unit: int<m> = 17<m>
    let observed = lazy (let _unit: int<m> = 23<m> in _unit)
    ignore observed
    0
"""
        let sources = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding("_unit", _, _, _) -> true | _ -> false) |> Seq.toList
        Assert.Equal(2, sources.Length)
        let contract = LazyIdentityValues.instances graph |> Map.values |> Assert.Single
        Assert.Empty contract.Captured
        let inner = sources |> List.maxBy (fun node -> node.Range.Start.Line, node.Range.Start.Column)
        let outer = sources |> List.find (fun node -> node.Id <> inner.Id)
        Assert.Contains(graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.VarRef("_unit", Some definition) -> definition = inner.Id | _ -> false)
        Assert.DoesNotContain(graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.VarRef("_unit", Some definition) -> definition = outer.Id | _ -> false)

    [<Fact>]
    member _.``Generic lazy specialization preserves source formal and capture correspondence``() =
        let builder = NodeBuilder()
        let range = LazyThunkIdentities.range
        let parameter = freshTypeParam "'value" TypeParamKind.Type range
        let valueType = NativeType.TVar parameter
        let source = builder.Create(SemanticKind.PatternBinding "_unit", valueType, range)
        let env = LazyThunkIdentities.env () |> LazyIdentityTypes.addBinding "_unit" valueType false (Some source.Id) false
        let owner = LazyThunkIdentities.raw "lazy _unit" env builder
        let originalFormal, _, _ = LazyThunkIdentities.assertFormal builder.Nodes env.CurrentArena owner
        let signature ty = NativeType.TFun(ty, Types.mkLazyType ty)
        let code = builder.Create(SemanticKind.Lambda(["_unit", valueType, source.Id], owner.Id, [], Some "make", LambdaContext.RegularClosure),
                                  signature valueType, range, children = [source.Id; owner.Id])
        builder.SetParent(source.Id, code.Id)
        builder.SetParent(owner.Id, code.Id)
        let declaration = builder.Create(SemanticKind.Binding("make", false, false, None), NativeType.TForall([parameter], signature valueType),
                                         range, children = [code.Id])
        builder.SetParent(code.Id, declaration.Id)
        let requests = [Types.boolType; Types.intType] |> List.map (fun ty ->
            builder.Create(SemanticKind.VarRef("make", Some declaration.Id), signature ty, range))
        builder.Create(SemanticKind.ModuleDef("LazyIdentity", declaration.Id :: List.map _.Id requests), Types.unitType, range) |> ignore
        let original = builder.Nodes
        let specialized = LazyIdentityMono.runWithEvidence original
        let clones = specialized.Nodes.Values |> Seq.choose (fun node ->
            PhaseEmitter.specializationSnapshot node |> Option.filter (fun trace -> trace.SourceNode = owner.Id)
            |> Option.map (fun trace -> node, trace)) |> Seq.toList
        Assert.Equal(2, clones.Length)
        for clone, trace in clones do
            let formal, body, captures = LazyThunkIdentities.assertFormal specialized.Nodes env.CurrentArena clone
            let capture = Assert.Single captures
            let captured = capture.SourceNodeId |> Option.get
            Assert.NotEqual(source.Id, captured)
            Assert.NotEqual(formal.Id, captured)
            Assert.Empty(freeTypeVars capture.Type)
            let formalTrace = PhaseEmitter.specializationSnapshot specialized.Nodes[formal.Id] |> Option.get
            Assert.Equal(originalFormal.Id, formalTrace.SourceNode)
            let captureTrace = PhaseEmitter.specializationSnapshot specialized.Nodes[captured] |> Option.get
            Assert.Equal(source.Id, captureTrace.SourceNode)
            match body.Kind with
            | SemanticKind.VarRef("_unit", Some definition) -> Assert.Equal(captured, definition)
            | kind -> failwithf "Specialization lost captured read identity: %A" kind
            Assert.Equal<NodeId list>(original[owner.Id].Children, trace.Input.Children)
            Assert.Equal<NodeId list>(clone.Children, trace.Output.Children)
            Assert.True(specialized.Nodes.ContainsKey originalFormal.Id)
            Assert.Contains(specialized.Derivations, fun edge ->
                edge.Role = EdgeRole.SchemeSpecialization && edge.Target = formal.Id && List.contains originalFormal.Id edge.Sources)

namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.Nanopass.Recipe
module SeqRecipes = Clef.Compiler.Baker.Recipes.SeqRecipes
module Decomposition = Clef.Compiler.Baker.Recipes.Decomposition
module FanOut = Clef.Compiler.Nanopass.FanOut
module FoldIn = Clef.Compiler.Nanopass.FoldIn
module Obligations = Clef.Compiler.Nanopass.ObligationElaboration

// Exercise the actual producer recipe and normal fan-out/fold-in boundary.
// These open, typed input graphs are not executable sequence/frame fixtures.
module private SeqProducerRecipes =
    let range: SourceRange =
        { File = "seq-producer-recipe.clef"; Start = { Line = 8; Column = 4 }; End = { Line = 8; Column = 46 } }
    type Fixture = {
        Graph: SemanticGraph; Site: SemanticNode; Operands: SemanticNode list
        Operation: string; Element: NativeType; Output: NativeType
        Callback: SemanticNode; Cell: SemanticNode; Observer: SemanticNode
    }

    let fixture operation =
        let builder = NodeBuilder()
        let create kind ty children = builder.Create(kind, ty, range, children = children)
        let input = DimensionalCases.measuredInt DimensionalCases.metre
        let output = if operation = "filter" || operation = "append" then input else DimensionalCases.measuredInt DimensionalCases.second
        let seqInput, seqOutput = Types.mkSeqType input, Types.mkSeqType output
        let cellValue = create (SemanticKind.PatternBinding "initialCell") output []
        let cell = create (SemanticKind.Binding ("cell", true, false, None)) output [cellValue.Id]
        let cellRead = create (SemanticKind.VarRef ("cell", Some cell.Id)) output []
        let capture = { Name = "cell"; Type = output; IsMutable = true; SourceNodeId = Some cell.Id }
        let parameter = create (SemanticKind.PatternBinding "value") input []
        let callbackResult, callbackBody =
            if operation = "filter" then
                let yes = create (SemanticKind.Literal (NativeLiteral.Bool true)) Types.boolType []
                Types.boolType, create (SemanticKind.Sequential [cellRead.Id; yes.Id]) Types.boolType [cellRead.Id; yes.Id]
            elif operation = "collect" then
                let construct = create (SemanticKind.PatternBinding "innerSequence") (NativeType.TFun(output, seqOutput)) []
                seqOutput, create (SemanticKind.Application (construct.Id, [cellRead.Id])) seqOutput [construct.Id; cellRead.Id]
            else output, cellRead
        let callbackType = NativeType.TFun(input, callbackResult)
        let callback = create (SemanticKind.Lambda (["value", input, parameter.Id], callbackBody.Id, [capture], Some "source", LambdaContext.RegularClosure)) callbackType [parameter.Id; callbackBody.Id]
        let factory name ty supplied =
            let unitParameter = create (SemanticKind.PatternBinding "_") Types.unitType []
            let body, captures =
                match supplied with
                | Some (value: SemanticNode) -> value, [capture]
                | None ->
                    let externalValue = create (SemanticKind.PatternBinding (name + "Value")) ty []
                    create (SemanticKind.VarRef (name + "Value", Some externalValue.Id)) ty [],
                    [{ Name = name + "Value"; Type = ty; IsMutable = false; SourceNodeId = Some externalValue.Id }]
            let functionType = NativeType.TFun(Types.unitType, ty)
            let lambda = create (SemanticKind.Lambda (["_", Types.unitType, unitParameter.Id], body.Id, captures, Some "source", LambdaContext.RegularClosure)) functionType [unitParameter.Id; body.Id]
            let binding = create (SemanticKind.Binding (name, false, false, None)) functionType [lambda.Id]
            let reference = create (SemanticKind.VarRef (name, Some binding.Id)) functionType []
            let unitValue = create (SemanticKind.Literal NativeLiteral.Unit) Types.unitType []
            create (SemanticKind.Application (reference.Id, [unitValue.Id])) ty [reference.Id; unitValue.Id]
        let first = if operation = "append" then factory "left" seqInput None else factory "callbackFactory" callbackType (Some callback)
        let second = factory "right" seqInput None
        let info = { Module = IntrinsicModule.Seq; Operation = operation; Category = IntrinsicCategory.Pure; FullName = "Seq." + operation }
        let intrinsic = create (SemanticKind.Intrinsic info) (NativeType.TFun(first.Type, NativeType.TFun(second.Type, seqOutput))) []
        let site = create (SemanticKind.Application (intrinsic.Id, [first.Id; second.Id])) seqOutput [intrinsic.Id; first.Id; second.Id]
        let observer = create (SemanticKind.PatternBinding "observe") (NativeType.TFun(seqOutput, Types.boolType)) []
        let observed = create (SemanticKind.Application (observer.Id, [site.Id])) Types.boolType [observer.Id; site.Id]
        let graph = builder.Build []
        let graph = Obligations.foldIn (Obligations.elaborate graph) graph
        { Graph = graph; Site = site; Operands = [first; second]; Operation = operation
          Element = input; Output = output; Callback = callback; Cell = cell; Observer = observed }

    let decompose fixture =
        let context = Decomposition.mkContext range fixture.Output None ("Seq." + fixture.Operation) fixture.Site.Id
        let result = SeqRecipes.tryDecompose context fixture.Operation (fixture.Operands |> List.map _.Id) fixture.Element (Some fixture.Output) None None |> Option.get
        let creator _ _ = RecipeCreated {
            OriginalNodeId = fixture.Site.Id; NewNodes = result.NewNodes @ result.AuxFunctions
            ReplacementRootId = result.ResultNodeId; ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Seq." + fixture.Operation }
        let recipes = FanOut.fanOut "Baker" (fun node -> node.Id = fixture.Site.Id) creator fixture.Graph
        result, FoldIn.foldIn recipes fixture.Graph

    let owner (graph: SemanticGraph) newNodes =
        newNodes |> List.choose (fun (node: SemanticNode) ->
            match node.Kind with SemanticKind.SeqExpr _ -> Some graph.Nodes[node.Id] | _ -> None) |> Assert.Single

    let generator (graph: SemanticGraph) (owner: SemanticNode) =
        match owner.Kind with
        | SemanticKind.SeqExpr (id, ownerCaptures) ->
            let generator = graph.Nodes[id]
            match generator.Kind with
            | SemanticKind.Lambda ([(name, parameterType, parameter)], body, captures, _, LambdaContext.SeqGenerator) ->
                let formal = graph.Nodes[parameter]
                Assert.Equal(SemanticKind.PatternBinding name, formal.Kind)
                DimensionalCases.same (NativeType.TNativePtr owner.Type) formal.Type
                DimensionalCases.same formal.Type parameterType
                DimensionalCases.same (NativeType.TFun(parameterType, Types.boolType)) generator.Type
                Assert.Equal<NodeId list>([parameter; body], generator.Children)
                Assert.Equal(Some generator.Id, formal.Parent)
                Assert.Equal(Some generator.Id, graph.Nodes[body].Parent)
                Assert.Equal(Some owner.Id, generator.Parent)
                Assert.Equal<CaptureInfo list>(ownerCaptures, captures)
                let relations = kindEdges generator.Id generator.Kind
                for role, id in [EdgeRole.Parameter, parameter; EdgeRole.Body, body] do
                    Assert.Contains(relations, fun edge -> edge.Role = role && edge.Target = generator.Id && edge.Sources = [id])
                generator, body, captures
            | kind -> failwithf "Producer SeqExpr contains a raw body instead of its generator: %A" kind
        | kind -> failwithf "Expected producer owner: %A" kind

    let descendants (graph: SemanticGraph) root =
        let rec walk seen id =
            if Set.contains id seen then seen
            else graph.Nodes[id].Children |> List.fold walk (Set.add id seen)
        walk Set.empty root

    let snapshots fixture (result: Decomposition.Result) (graph: SemanticGraph) =
        match graph.Nodes[result.ResultNodeId].Kind with
        | SemanticKind.Sequential [first; second; ownerId] ->
            let bindings = [first; second]
            for operand, snapshot in List.zip fixture.Operands bindings do
                match graph.Nodes[snapshot].Kind with
                | SemanticKind.Binding (_, false, false, _) ->
                    Assert.Equal<NodeId list>([operand.Id], graph.Nodes[snapshot].Children)
                    DimensionalCases.same operand.Type graph.Nodes[snapshot].Type
                | kind -> failwithf "Formation did not snapshot its supplied operand: %A" kind
            graph.Nodes[ownerId], bindings
        | kind -> failwithf "Producer formation lost ordered eager operand snapshots: %A" kind

    let intrinsicApplication moduleName operation (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Application (callee, arguments) ->
            match graph.Nodes[callee].Kind with
            | SemanticKind.Intrinsic info when info.Module = moduleName && info.Operation = operation -> Some arguments
            | _ -> None
        | _ -> None

    let enumeration (graph: SemanticGraph) body =
        match graph.Nodes[body].Kind with
        | SemanticKind.Sequential [binding; loop] ->
            let initialization = Assert.Single graph.Nodes[binding].Children
            match graph.Nodes[binding].Kind with
            | SemanticKind.Binding (_, false, false, _) -> ()
            | kind -> failwithf "Enumerator lacks a local initialization binding: %A" kind
            Assert.True((intrinsicApplication IntrinsicModule.Seq "getEnumerator" graph initialization).IsSome)
            match graph.Nodes[loop].Kind with
            | SemanticKind.WhileLoop (condition, loopBody) ->
                let uses = descendants graph loop |> Set.toList |> List.choose (fun id ->
                    ["moveNext"; "current"] |> List.tryPick (fun operation -> intrinsicApplication IntrinsicModule.SeqEnumerator operation graph id))
                Assert.Equal(2, uses.Length)
                for arguments in uses do
                    match graph.Nodes[Assert.Single arguments].Kind with
                    | SemanticKind.VarRef (_, Some definition) -> Assert.Equal(binding, definition)
                    | kind -> failwithf "Enumeration did not reuse its initialized local value: %A" kind
                Assert.DoesNotContain(initialization, descendants graph loop)
                binding, condition, loopBody
            | kind -> failwithf "Expected deferred enumeration loop: %A" kind
        | kind -> failwithf "Enumerator initialization does not precede iteration inside generator: %A" kind

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SeqProducerRecipes")>]
type SeqProducerRecipeCases() =
    [<Theory>]
    [<InlineData("map")>]
    [<InlineData("filter")>]
    [<InlineData("collect")>]
    [<InlineData("append")>]
    member _.``Producer recipes share the typed sequence owner and unit yield contract``(operation: string) =
        let fixture = SeqProducerRecipes.fixture operation
        let result, graph = SeqProducerRecipes.decompose fixture
        let owner = SeqProducerRecipes.owner graph result.NewNodes
        DimensionalCases.same (Types.mkSeqType fixture.Output) owner.Type
        let _, body, _ = SeqProducerRecipes.generator graph owner
        let yields = SeqProducerRecipes.descendants graph body |> Set.toList |> List.choose (fun id ->
            let node = graph.Nodes[id]
            match node.Kind with
            | SemanticKind.Yield payload -> Some (node, payload, fixture.Output)
            | SemanticKind.YieldBang sequence -> Some (node, sequence, owner.Type)
            | _ -> None)
        Assert.NotEmpty yields
        for node, value, expected in yields do
            DimensionalCases.same Types.unitType node.Type
            DimensionalCases.same expected graph.Nodes[value].Type
        if operation <> "append" then SeqProducerRecipes.enumeration graph body |> ignore

    [<Fact>]
    member _.``Map formation snapshots eager factories while enumeration and callback stay deferred``() =
        let fixture = SeqProducerRecipes.fixture "map"
        let result, graph = SeqProducerRecipes.decompose fixture
        let owner, snapshots = SeqProducerRecipes.snapshots fixture result graph
        let _, body, captures = SeqProducerRecipes.generator graph owner
        Assert.Equal<Set<NodeId>>(Set.ofList snapshots, captures |> List.choose _.SourceNodeId |> Set.ofList)
        Assert.All(captures, fun capture -> Assert.False capture.IsMutable)
        let bodyNodes = SeqProducerRecipes.descendants graph body
        for operand in fixture.Operands do Assert.DoesNotContain(operand.Id, bodyNodes)
        let localReferences = bodyNodes |> Set.toList |> List.choose (fun id ->
            match graph.Nodes[id].Kind with SemanticKind.VarRef (_, Some definition) -> Some definition | _ -> None) |> Set.ofList
        for snapshot in snapshots do Assert.Contains(snapshot, localReferences)
        SeqProducerRecipes.enumeration graph body |> ignore
        match graph.Nodes[fixture.Callback.Id].Kind with
        | SemanticKind.Lambda (_, _, [capture], _, _) ->
            Assert.True capture.IsMutable
            Assert.Equal(Some fixture.Cell.Id, capture.SourceNodeId)
        | kind -> failwithf "Snapshot changed callback's retained cell: %A" kind

    [<Fact>]
    member _.``Append snapshots both sources before deferring ordered delegation``() =
        let fixture = SeqProducerRecipes.fixture "append"
        let result, graph = SeqProducerRecipes.decompose fixture
        let owner, snapshots = SeqProducerRecipes.snapshots fixture result graph
        let _, body, captures = SeqProducerRecipes.generator graph owner
        Assert.Equal<Set<NodeId>>(Set.ofList snapshots, captures |> List.choose _.SourceNodeId |> Set.ofList)
        match graph.Nodes[body].Kind with
        | SemanticKind.Sequential [left; right] ->
            for delegation, snapshot in List.zip [left; right] snapshots do
                match graph.Nodes[delegation].Kind with
                | SemanticKind.YieldBang value ->
                    match graph.Nodes[value].Kind with
                    | SemanticKind.VarRef (_, Some definition) -> Assert.Equal(snapshot, definition)
                    | kind -> failwithf "Delegation re-evaluates a forming operand: %A" kind
                | kind -> failwithf "Expected ordered delegation: %A" kind
        | kind -> failwithf "Append lost its delegation sequence: %A" kind

    [<Fact>]
    member _.``Filter reads current once before predicate and reuses it only in the yielding branch``() =
        let fixture = SeqProducerRecipes.fixture "filter"
        let result, graph = SeqProducerRecipes.decompose fixture
        let owner, _ = SeqProducerRecipes.snapshots fixture result graph
        let _, body, _ = SeqProducerRecipes.generator graph owner
        let _, _, loopBody = SeqProducerRecipes.enumeration graph body
        match graph.Nodes[loopBody].Kind with
        | SemanticKind.Sequential [currentBinding; current; conditional] ->
            let initialization = Assert.Single graph.Nodes[currentBinding].Children
            Assert.True((SeqProducerRecipes.intrinsicApplication IntrinsicModule.SeqEnumerator "current" graph initialization).IsSome)
            match graph.Nodes[currentBinding].Kind, graph.Nodes[current].Kind with
            | SemanticKind.Binding (_, false, false, _), SemanticKind.VarRef (_, Some definition) -> Assert.Equal(currentBinding, definition)
            | kinds -> failwithf "Filter did not retain its one observed current value: %A" kinds
            match graph.Nodes[conditional].Kind with
            | SemanticKind.IfThenElse (predicate, yes, Some no) ->
                match graph.Nodes[predicate].Kind, graph.Nodes[yes].Kind with
                | SemanticKind.Application (_, [argument]), SemanticKind.Yield payload ->
                    Assert.Equal(current, argument)
                    Assert.Equal(current, payload)
                | kinds -> failwithf "Filter changed the current value between predicate and yield: %A" kinds
                Assert.Equal(SemanticKind.Literal NativeLiteral.Unit, graph.Nodes[no].Kind)
            | kind -> failwithf "Filter lost guarded yielding: %A" kind
        | kind -> failwithf "Current is not evaluated before predicate and branch selection: %A" kind

    [<Fact>]
    member _.``Fold-in preserves existing proof incidence and source provenance across producer formation``() =
        let fixture = SeqProducerRecipes.fixture "map"
        let originalNodes, originalEdges = fixture.Graph.Nodes, fixture.Graph.Edges
        let affected = originalEdges |> List.filter (fun edge -> List.contains fixture.Site.Id edge.Sources) |> Assert.Single
        let unrelated = originalEdges |> List.filter (fun edge -> not (List.contains fixture.Site.Id edge.Sources))
        Assert.NotEmpty unrelated
        let result, graph = SeqProducerRecipes.decompose fixture
        let _, _ = SeqProducerRecipes.snapshots fixture result graph
        let retained = graph.Edges |> List.filter (fun edge -> edge.Target = affected.Target) |> Assert.Single
        Assert.Equal<NodeId list>(affected.Sources |> List.map (fun id -> if id = fixture.Site.Id then result.ResultNodeId else id), retained.Sources)
        Assert.Equal(affected.Class, retained.Class)
        Assert.Equal(affected.Role, retained.Role)
        Assert.Equal(affected.Ordinal, retained.Ordinal)
        Assert.Equal(originalNodes[affected.Target].Kind, graph.Nodes[affected.Target].Kind)
        for edge in unrelated do
            Assert.Contains(graph.Edges, fun candidate ->
                candidate.Sources = edge.Sources && candidate.Target = edge.Target &&
                candidate.Class = edge.Class && candidate.Role = edge.Role && candidate.Ordinal = edge.Ordinal)
        Assert.Same(originalNodes, fixture.Graph.Nodes)
        Assert.Same(originalEdges, fixture.Graph.Edges)
        Assert.Equal(SeqProducerRecipes.range, graph.Nodes[result.ResultNodeId].Range)
        let anchor = { SeqProducerRecipes.range with End = SeqProducerRecipes.range.Start }
        for node in result.NewNodes do
            if node.Id <> result.ResultNodeId then Assert.Equal<SourceRange>(anchor, node.Range)
            Assert.Equal(Some (MetadataValue.String "Baker"), node.Metadata.TryFind ElaborationMetadata.Kind)
            Assert.Equal(Some (MetadataValue.String "Seq.map"), node.Metadata.TryFind ElaborationMetadata.For)
        for operand in fixture.Operands do Assert.Equal(operand.Range, graph.Nodes[operand.Id].Range)

namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module DelegationPass = Clef.Compiler.Nanopass.SequenceDelegation
module DelegationOwners = Clef.Compiler.Nanopass.SequenceOwnership
module DelegationObligations = Clef.Compiler.Nanopass.ObligationElaboration

// Delegation exposes ordinary iteration to later suspension work. These cases
// establish graph evaluation placement, not a resumable frame or native runner.
module private Delegation =
    let check source =
        let source = "module Delegation\n[<Measure>] type m\n" + source + "\n[<EntryPoint>]\nlet main _ = ignore outer; 0\n"
        match parseAndCheck source "sequence-delegation.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result.Graph
        | CheckFailure result -> failwithf "Expected admitted delegation: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed delegation: %A" errors

    let children (node: SemanticNode) =
        let derived = kindEdges node.Id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
        match node.Kind with SemanticKind.Binding _ | SemanticKind.Intrinsic _ -> derived @ node.Children | _ -> derived

    let scope (graph: SemanticGraph) root =
        let rec walk seen id =
            if Set.contains id seen then seen
            else
                let seen = Set.add id seen
                let node = graph.Nodes[id]
                match node.Kind with
                | SemanticKind.SeqExpr _ | SemanticKind.Lambda _ | SemanticKind.LazyExpr _ -> seen
                | _ -> children node |> List.fold walk seen
        walk Set.empty root

    let body (graph: SemanticGraph) (owner: SemanticNode) =
        match owner.Kind with
        | SemanticKind.SeqExpr (generator, _) ->
            match graph.Nodes[generator].Kind with
            | SemanticKind.Lambda (_, body, _, _, LambdaContext.SeqGenerator) -> body
            | kind -> failwithf "Missing sequence generator: %A" kind
        | kind -> failwithf "Expected owner: %A" kind

    let owner (graph: SemanticGraph) =
        let binding = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding ("outer", _, _, _) -> true | _ -> false)
        let rec value id =
            let node = graph.Nodes[id]
            match node.Kind with
            | SemanticKind.TypeAnnotation (inner, _) -> value inner
            | SemanticKind.Sequential values -> value (List.last values)
            | SemanticKind.SeqExpr _ -> node
            | kind -> failwithf "Expected sequence value: %A" kind
        value (Assert.Single binding.Children)

    let rec ordered (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Sequential values -> values |> List.collect (ordered graph)
        | _ -> [id]

    let application moduleName operation (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Application (callee, arguments) ->
            match graph.Nodes[callee].Kind with
            | SemanticKind.Intrinsic info when info.Module = moduleName && info.Operation = operation -> Some arguments
            | _ -> None
        | _ -> None

    type Iteration = { Root: NodeId; Binding: NodeId; Input: NodeId; Loop: NodeId; Condition: NodeId; Body: NodeId }

    let tryIteration (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Sequential [binding; loop] ->
            match graph.Nodes[binding].Kind, graph.Nodes[binding].Children, graph.Nodes[loop].Kind with
            | SemanticKind.Binding (_, false, false, _), [initialization], SemanticKind.WhileLoop (condition, body) ->
                application IntrinsicModule.Seq "getEnumerator" graph initialization
                |> Option.map (fun arguments ->
                    { Root = id; Binding = binding; Input = Assert.Single arguments; Loop = loop; Condition = condition; Body = body })
            | _ -> None
        | _ -> None

    let iterations graph root = scope graph root |> Set.toList |> List.choose (tryIteration graph)

    let referenceTo (graph: SemanticGraph) definition id =
        match graph.Nodes[id].Kind with
        | SemanticKind.VarRef (_, Some actual) -> Assert.Equal(definition, actual)
        | kind -> failwithf "Expected a reference to retained local %A: %A" definition kind

    let assertPull (graph: SemanticGraph) iteration =
        let moveNext = application IntrinsicModule.SeqEnumerator "moveNext" graph iteration.Condition |> Option.get
        referenceTo graph iteration.Binding (Assert.Single moveNext)
        match graph.Nodes[iteration.Body].Kind with
        | SemanticKind.Sequential [currentBinding; currentRef; action] ->
            let initializer = Assert.Single graph.Nodes[currentBinding].Children
            let current = application IntrinsicModule.SeqEnumerator "current" graph initializer |> Option.get
            referenceTo graph iteration.Binding (Assert.Single current)
            referenceTo graph currentBinding currentRef
            let currentCalls = scope graph iteration.Loop |> Set.toList |> List.filter (fun id ->
                match application IntrinsicModule.SeqEnumerator "current" graph id with
                | Some [argument] ->
                    match graph.Nodes[argument].Kind with
                    | SemanticKind.VarRef (_, Some definition) -> definition = iteration.Binding
                    | _ -> false
                | _ -> false)
            Assert.Equal<NodeId list>([initializer], currentCalls)
            currentRef, action
        | kind -> failwithf "Current must be read once before the iteration action: %A" kind

    let noDelegation (graph: SemanticGraph) =
        Assert.DoesNotContain(graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.YieldBang _ -> true | _ -> false)

    let range: SourceRange =
        { File = "delegation-recipe.clef"; Start = { Line = 7; Column = 4 }; End = { Line = 7; Column = 29 } }

    type Fixture = { Graph: SemanticGraph; Site: NodeId; Operand: NodeId; Effect: NodeId; Owner: NodeId; Generator: NodeId; Formal: NodeId }

    let fixture scalar =
        let builder = NodeBuilder()
        let create kind ty children = builder.Create(kind, ty, range, children = children)
        let no = create (SemanticKind.Literal (NativeLiteral.Bool false)) Types.boolType []
        let cell = create (SemanticKind.Binding ("cell", true, false, None)) Types.boolType [no.Id]
        let target = create (SemanticKind.VarRef ("cell", Some cell.Id)) Types.boolType []
        let yes = create (SemanticKind.Literal (NativeLiteral.Bool true)) Types.boolType []
        let effect = create (SemanticKind.Set(target.Id, yes.Id)) Types.unitType [target.Id; yes.Id]
        let sequenceType = Types.mkSeqType Types.boolType
        let inputType = if scalar then Types.boolType else sequenceType
        let input = create (SemanticKind.PatternBinding "input") inputType []
        let inputRef = create (SemanticKind.VarRef ("input", Some input.Id)) inputType []
        let operand = create (SemanticKind.Sequential [effect.Id; inputRef.Id]) inputType [effect.Id; inputRef.Id]
        let site = create (SemanticKind.YieldBang operand.Id) Types.unitType [operand.Id]
        let after = create (SemanticKind.Set(target.Id, no.Id)) Types.unitType [target.Id; no.Id]
        let body = create (SemanticKind.Sequential [site.Id; after.Id]) Types.unitType [site.Id; after.Id]
        let pointerType = NativeType.TNativePtr sequenceType
        let formal = create (SemanticKind.PatternBinding "_seq_ptr") pointerType []
        let capture = { Name = "cell"; Type = Types.boolType; IsMutable = true; SourceNodeId = Some cell.Id }
        let generator = create (SemanticKind.Lambda (["_seq_ptr", pointerType, formal.Id], body.Id, [capture], None, LambdaContext.SeqGenerator)) (NativeType.TFun(pointerType, Types.boolType)) [formal.Id; body.Id]
        let owner = create (SemanticKind.SeqExpr(generator.Id, [capture])) sequenceType [generator.Id]
        builder.SetParent(site.Id, body.Id)
        builder.SetParent(formal.Id, generator.Id)
        builder.SetParent(body.Id, generator.Id)
        builder.SetParent(generator.Id, owner.Id)
        builder.SetEmissionStrategy(site.Id, EmissionStrategy.SeparateFunction 1)
        // An independent, resident ordinary application obligation must survive.
        let measured = DimensionalCases.measuredInt DimensionalCases.metre
        let observed = create (SemanticKind.PatternBinding "distance") measured []
        let observer = create (SemanticKind.PatternBinding "observe") (NativeType.TFun(measured, Types.boolType)) []
        create (SemanticKind.Application(observer.Id, [observed.Id])) Types.boolType [observer.Id; observed.Id] |> ignore
        let graph = builder.Build []
        let graph = DelegationObligations.foldIn (DelegationObligations.elaborate graph) graph
        let graph, diagnostics = DelegationOwners.normalize graph
        Assert.Empty diagnostics
        { Graph = graph; Site = site.Id; Operand = operand.Id; Effect = effect.Id; Owner = owner.Id; Generator = generator.Id; Formal = formal.Id }

    let edgeFields (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceDelegation")>]
type SequenceDelegationCases() =
    [<Fact>]
    member _.``Elaboration preserves the source site and unrelated participants and proof relations``() =
        let fixture = Delegation.fixture false
        let graph = DelegationPass.normalize fixture.Graph
        let original, site = fixture.Graph.Nodes[fixture.Site], graph.Nodes[fixture.Site]
        DimensionalCases.same Types.unitType site.Type
        Assert.Equal(original.Range, site.Range)
        Assert.Equal(original.Parent, site.Parent)
        Assert.Equal(original.EmissionStrategy, site.EmissionStrategy)
        Assert.Equal(fixture.Graph.Nodes[fixture.Operand].Range, graph.Nodes[fixture.Operand].Range)
        match site.Kind with
        | SemanticKind.Sequential [expanded] -> Assert.True((Delegation.tryIteration graph expanded).IsSome)
        | kind -> failwithf "Delegation did not retain its source boundary: %A" kind
        for KeyValue(id, node) in fixture.Graph.Nodes do
            if id <> fixture.Site then
                // Ordinary fold-in refreshes containment parents, including
                // the original operand now consumed by getEnumerator.
                let retained = graph.Nodes[id]
                Assert.Equal(node.Kind, retained.Kind)
                DimensionalCases.same node.Type retained.Type
                Assert.Equal(node.Range, retained.Range)
                Assert.Equal<NodeId list>(node.Children, retained.Children)
                Assert.Equal(node.EmissionStrategy, retained.EmissionStrategy)
                Assert.Equal<Map<string, MetadataValue>>(node.Metadata, retained.Metadata)
        let added = graph.Nodes.Values |> Seq.filter (fun node -> not (fixture.Graph.Nodes.ContainsKey node.Id)) |> Seq.toList
        Assert.NotEmpty added
        for node in added do
            Assert.Equal<SourceRange>({ original.Range with End = original.Range.Start }, node.Range)
            match node.Kind with
            | SemanticKind.SeqExpr _ | SemanticKind.Lambda _ -> failwith "Delegation invented another deferred owner"
            | _ -> ()
        let independent = fixture.Graph.Edges |> List.filter (fun edge -> edge.Class <> EdgeClass.Suspension)
        Assert.Contains(independent, fun edge -> edge.Class = EdgeClass.Obligation)
        for edge in independent do
            Assert.Contains(graph.Edges, fun retained -> Delegation.edgeFields retained = Delegation.edgeFields edge)
        let origin = graph.Edges |> List.filter (fun edge ->
            edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.DelegationOrigin) |> Assert.Single
        Assert.Equal<NodeId list>([fixture.Site; fixture.Operand], origin.Sources)
        match graph.Nodes[origin.Target].Kind with
        | SemanticKind.Yield _ -> ()
        | kind -> failwithf "Delegation provenance did not retain its generated cut: %A" kind
        Assert.Equal(SemanticKind.YieldBang fixture.Operand, fixture.Graph.Nodes[fixture.Site].Kind)

    [<Fact>]
    member _.``Delegation initializes its effectful operand once before repeated pulls and current reads``() =
        let fixture = Delegation.fixture false
        let graph = DelegationPass.normalize fixture.Graph
        let iteration = Delegation.iterations graph fixture.Site |> Assert.Single
        Assert.Equal(fixture.Operand, iteration.Input)
        Assert.Contains(fixture.Effect, Delegation.scope graph iteration.Binding)
        Assert.DoesNotContain(fixture.Effect, Delegation.scope graph iteration.Loop)
        let currentRef, action = Delegation.assertPull graph iteration
        Assert.Equal(SemanticKind.Yield currentRef, graph.Nodes[action].Kind)
        DimensionalCases.same Types.unitType graph.Nodes[action].Type
        let owned, diagnostics = DelegationOwners.normalize graph
        Assert.Empty diagnostics
        let relation = owned.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Suspension && edge.Target = action) |> Assert.Single
        Assert.Equal<NodeId list>([fixture.Owner; fixture.Generator], relation.Sources)
        Assert.DoesNotContain(owned.Edges, fun edge -> edge.Class = EdgeClass.Suspension && edge.Target = fixture.Site)

    [<Theory>]
    [<InlineData("seq { yield 4 }")>]
    [<InlineData("(seq { () }: seq<int>)")>]
    member _.``Effects after delegation remain after the pull loop including an empty input``(input: string) =
        let graph = Delegation.check ("let mutable trace = 0\nlet outer = seq {\n    trace <- 1\n    yield! (trace <- 2; " + input + ")\n    trace <- 3\n}")
        Delegation.noDelegation graph
        let body = Delegation.body graph (Delegation.owner graph)
        let iteration = Delegation.iterations graph body |> Assert.Single
        let actions = Delegation.ordered graph body
        Assert.Equal(4, actions.Length)
        Assert.Equal(iteration.Binding, actions[1])
        Assert.Equal(iteration.Loop, actions[2])
        for id in [actions[0]; actions[3]] do
            match graph.Nodes[id].Kind with SemanticKind.Set _ -> () | kind -> failwithf "Surrounding effect moved: %A" kind
        match graph.Nodes[iteration.Input].Kind with
        | SemanticKind.Sequential [effect; inner] ->
            let rec value id =
                match graph.Nodes[id].Kind with
                | SemanticKind.TypeAnnotation (inner, _) -> value inner
                | kind -> kind
            match graph.Nodes[effect].Kind, value inner with
            | SemanticKind.Set _, SemanticKind.SeqExpr _ -> ()
            | kinds -> failwithf "Operand effects or delayed input moved: %A" kinds
        | kind -> failwithf "Delegation operand was not retained: %A" kind

    [<Fact>]
    member _.``A delegation inside a source loop initializes within each visit to that body``() =
        let graph = Delegation.check """
let mutable running = true
let outer = seq {
    while running do
        yield! seq { yield 1 }
        running <- false
}
"""
        let body = Delegation.body graph (Delegation.owner graph)
        match graph.Nodes[body].Kind with
        | SemanticKind.WhileLoop (_, loopBody) ->
            let iteration = Delegation.iterations graph loopBody |> Assert.Single
            let actions = Delegation.ordered graph loopBody
            Assert.Equal<NodeId list>([iteration.Binding; iteration.Loop], actions |> List.take 2)
            match graph.Nodes[List.last actions].Kind with SemanticKind.Set _ -> () | kind -> failwithf "Lost post-delegation update: %A" kind
        | kind -> failwithf "Delegation changed the containing loop: %A" kind

    [<Fact>]
    member _.``Collect obtains one callback sequence per source current before draining it``() =
        let graph = Delegation.check "let outer = Seq.collect (fun (value: int<m>) -> seq { yield value }) (seq { yield 1<m> })"
        Delegation.noDelegation graph
        let body = Delegation.body graph (Delegation.owner graph)
        let outer = Delegation.tryIteration graph body |> Option.get
        let current, action = Delegation.assertPull graph outer
        let inner = Delegation.iterations graph action |> Assert.Single
        Assert.DoesNotContain(inner.Binding, Delegation.scope graph outer.Binding)
        match graph.Nodes[inner.Input].Kind with
        | SemanticKind.Application (callee, [environment; argument]) ->
            Assert.Equal(current, argument)
            // The callback's source operand is still current. Its additional
            // implementation formal receives this occurrence's environment.
            let callback =
                match graph.Nodes[environment].Kind with
                | SemanticKind.EnvironmentReference callback -> callback
                | kind -> failwithf "Collect lost the callback environment occurrence: %A" kind
            let owner = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.tryEnvironmentOwner graph callback |> Option.get
            match graph.Nodes[owner].Kind, graph.Nodes[callee].Kind with
            | SemanticKind.ClosureValue(implementation, _), SemanticKind.VarRef(_, Some binding) ->
                Assert.Equal<NodeId list>([implementation], graph.Nodes[binding].Children)
            | kinds -> failwithf "Collect lost the callback implementation identity: %A" kinds
        | kind -> failwithf "Collect lost its per-current callback: %A" kind
        Assert.DoesNotContain(inner.Input, Delegation.scope graph inner.Loop)
        let current, action = Delegation.assertPull graph inner
        Assert.Equal(SemanticKind.Yield current, graph.Nodes[action].Kind)

    [<Fact>]
    member _.``Append retains ordered source snapshots and exhausts the first loop before the second``() =
        let graph = Delegation.check "let outer = Seq.append (seq { yield 1<m> }) (seq { yield 2<m> })"
        let owner = Delegation.owner graph
        let body = Delegation.body graph owner
        let actions = Delegation.ordered graph body
        let iterations = Delegation.iterations graph body |> List.sortBy (fun iteration -> List.findIndex ((=) iteration.Binding) actions)
        Assert.Equal(2, iterations.Length)
        Assert.Equal<NodeId list>(iterations |> List.collect (fun iteration -> [iteration.Binding; iteration.Loop]), actions)
        let captures = match owner.Kind with SemanticKind.SeqExpr (_, captures) -> captures | _ -> failwith "owner"
        Assert.Equal(2, captures.Length)
        for iteration, capture in List.zip iterations captures do
            Delegation.referenceTo graph (Option.get capture.SourceNodeId) iteration.Input
            Delegation.assertPull graph iteration |> ignore
        Delegation.noDelegation graph

    [<Fact>]
    member _.``Nested owners keep distinct formals and shared source cell capture identity``() =
        let graph = Delegation.check "let produce () =\n    let mutable trace = 1<m>\n    seq { yield! (seq { yield trace }); yield trace }\nlet outer = produce ()"
        let cell = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding ("trace", true, _, _) -> true | _ -> false)
        let owners = graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList
        Assert.Equal(2, owners.Length)
        let formals = owners |> List.map (fun owner ->
            match owner.Kind with
            | SemanticKind.SeqExpr (generator, captures) ->
                Assert.Contains(captures, fun capture -> capture.IsMutable && capture.SourceNodeId = Some cell.Id)
                match graph.Nodes[generator].Kind with
                | SemanticKind.Lambda ([_, _, formal], _, generatorCaptures, _, LambdaContext.SeqGenerator) ->
                    Assert.Equal<CaptureInfo list>(captures, generatorCaptures)
                    Assert.Equal(Some generator, graph.Nodes[formal].Parent)
                    formal
                | kind -> failwithf "Generator/formal changed: %A" kind
            | _ -> failwith "owner")
        Assert.Equal(2, formals |> Set.ofList |> Set.count)
        let relations = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Suspension && edge.Role = EdgeRole.Delimiter)
        Assert.Equal(3, relations.Length)
        for relation in relations do
            let owner = graph.Nodes[relation.Sources.Head]
            Assert.Contains(relation.Target, Delegation.scope graph (Delegation.body graph owner))
            match graph.Nodes[relation.Target].Kind with SemanticKind.Yield _ -> () | kind -> failwithf "Stale delegation ownership: %A" kind

    [<Fact>]
    member _.``A second normalization does not allocate another iteration or alter resident relations``() =
        let first = DelegationPass.normalize (Delegation.fixture false).Graph
        let second = DelegationPass.normalize first
        Delegation.noDelegation second
        Assert.Same(first.Nodes, second.Nodes)
        Assert.Equal<(EdgeClass * EdgeRole * int * NodeId list * NodeId) list>(first.Edges |> List.map Delegation.edgeFields, second.Edges |> List.map Delegation.edgeFields)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Missing ownership and invalid scalar operands are not destructively elaborated``(scalar: bool) =
        let fixture = Delegation.fixture scalar
        let graph = if scalar then fixture.Graph else { fixture.Graph with Edges = fixture.Graph.Edges |> List.filter (fun edge -> edge.Class <> EdgeClass.Suspension) }
        let result = DelegationPass.normalize graph
        Assert.Same(graph.Nodes, result.Nodes)
        Assert.Equal(SemanticKind.YieldBang fixture.Operand, result.Nodes[fixture.Site].Kind)
        Assert.Equal<(EdgeClass * EdgeRole * int * NodeId list * NodeId) list>(graph.Edges |> List.map Delegation.edgeFields, result.Edges |> List.map Delegation.edgeFields)

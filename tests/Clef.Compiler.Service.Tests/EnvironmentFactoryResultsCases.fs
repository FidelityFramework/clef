namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module EnvironmentResults = Clef.Compiler.Nanopass.EnvironmentFactoryResults
module EnvironmentValues = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module EnvironmentIncidence = Clef.Compiler.Baker.Ingredients.Closures

module private EnvironmentFactories =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        Assert.True result.Graph.Platform.IsNone
        result.Graph

    let bareSource = """
[<EntryPoint>]
let main _ =
    let offset = 10
    let mutable formations = 0
    let callback = fun (value: int) -> value + offset
    let bareMap: (int -> int) -> seq<int> -> seq<int> = Seq.map
    let first = bareMap (formations <- formations + 1; callback)
    let second = bareMap (formations <- formations + 2; callback)
    let firstValues = first (seq { yield 3 })
    let secondValues = second (seq { yield 4 })
    for value in firstValues do ignore value
    for value in secondValues do ignore value
    formations
"""

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false))
        |> Assert.Single

    let implementation name graph =
        EnvironmentValues.tryImplementation graph (binding name graph).Id
        |> Option.defaultWith (fun () -> failwith "Factory lost its actual implementation")

    let prepare (graph: SemanticGraph) = EnvironmentResults.prepare graph graph.Codata.Value.Curry

    let relations role (graph: SemanticGraph) = graph.Edges |> List.filter (fun edge -> edge.Role = role)

    let sourceSignature (node: SemanticNode) =
        match node.Metadata.TryFind ClosureMetadata.SourceSignature with
        | Some (MetadataValue.Type ty) -> ty
        | _ -> node.Type

    let calls implementation (graph: SemanticGraph) =
        let resolved = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        resolved.Calls |> Map.toList |> List.choose (fun (id, call) ->
            match call.Targets, graph.Nodes[id].Kind with
            | [target], SemanticKind.Application(callee, arguments) when call.Complete && not call.Unknown && target.Lambda = implementation ->
                Some(graph.Nodes[id], callee, arguments)
            | _ -> None)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "EnvironmentFactoryResults")>]
type EnvironmentFactoryResultsCases() =
    [<Theory>]
    [<InlineData(true, false)>]
    [<InlineData(false, true)>]
    [<InlineData(true, true)>]
    member _.``Explicit eager factory boundaries retain their marker identity and caller residence`` (eagerResult: bool, eagerCallee: bool) =
        let result = if eagerResult then "eager (fun value -> value + seed)" else "fun value -> value + seed"
        let callee = if eagerCallee then "(eager make)" else "make"
        let template = """
let make (seed: int) = __RESULT__
[<EntryPoint>]
let main _ =
    let first = __CALLEE__ (eager 7)
    let second = __CALLEE__ 8
    ignore (first 1)
    ignore (second 2)
    0
"""
        let source = template.Replace("__RESULT__", result).Replace("__CALLEE__", callee)
        let original = EnvironmentFactories.check source
        let implementation = EnvironmentFactories.implementation "make" original
        let originalCalls = EnvironmentFactories.calls implementation original
        Assert.Equal(2, originalCalls.Length)
        let markers = original.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.EagerExpr _ -> true | _ -> false) |> Seq.toList
        Assert.NotEmpty markers
        let prepared, _ = EnvironmentFactories.prepare original
        let calls = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall prepared
        Assert.Equal(2, calls.Length)
        Assert.Equal(2, calls |> List.map (fun row -> row.Sources[3]) |> List.distinct |> List.length)
        for marker in markers do
            Assert.Equal(marker.Kind, prepared.Nodes[marker.Id].Kind)
            Assert.Equal<NodeId list>(marker.Children, prepared.Nodes[marker.Id].Children)
        for call, callee, arguments in originalCalls do
            let invocation =
                match prepared.Nodes[call.Id].Kind with
                | SemanticKind.Sequential [_; actual] -> prepared.Nodes[actual]
                | kind -> failwithf "Expected destination-only factory prefix, got %A" kind
            match invocation.Kind with
            | SemanticKind.Application(actualCallee, _ :: actuals) ->
                Assert.Equal(callee, actualCallee)
                Assert.Equal<NodeId list>(arguments, actuals)
            | kind -> failwithf "Expected preserved factory invocation, got %A" kind
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments prepared
        Assert.Empty reading.Unresolved
        for row in calls do Assert.True(reading.Sites.ContainsKey row.Sources[3])
        if eagerResult then
            let marker = markers |> List.find (fun marker ->
                match marker.Kind with
                | SemanticKind.EagerExpr value -> match original.Nodes[value].Kind with SemanticKind.ClosureValue _ -> true | _ -> false
                | _ -> false)
            for row in calls do
                Assert.Contains(reading.Evidence, fun proof ->
                    proof.Role = EdgeRole.EnvironmentResidence && List.contains row.Sources[3] proof.Sources && List.contains marker.Id proof.Sources)
            let malformed = { prepared with Nodes = prepared.Nodes.Add(marker.Id, { prepared.Nodes[marker.Id] with Children = [] }) }
            let retracted = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments malformed
            for row in calls do Assert.False(retracted.Sites.ContainsKey row.Sources[3])
            Assert.NotEmpty retracted.Unresolved
        if eagerCallee then
            let marker = markers |> List.find (fun marker ->
                originalCalls |> List.exists (fun (_, callee, _) -> callee = marker.Id))
            let malformed = { original with Nodes = original.Nodes.Add(marker.Id, { marker with Children = [] }) }
            let retracted, _ = EnvironmentFactories.prepare malformed
            Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination retracted)

    [<Fact>]
    member _.``Bare map front gives each captured callback result distinct caller storage and exact formation incidence`` () =
        let original = EnvironmentFactories.check EnvironmentFactories.bareSource
        let implementation = EnvironmentFactories.implementation "bareMap" original
        let graph, curry = EnvironmentFactories.prepare original
        let destination = EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination graph |> Assert.Single
        Assert.Equal(EdgeClass.Provenance, destination.Class)
        let owner, formal =
            match destination.Sources with
            | [actual; owner; formal] -> Assert.Equal(implementation, actual); owner, formal
            | participants -> failwithf "Incomplete result destination: %A" participants
        match graph.Nodes[owner].Kind, graph.Nodes[destination.Target].Kind with
        | SemanticKind.ClosureValue(_, environment), SemanticKind.EnvironmentCreate(actual, _) ->
            Assert.Equal(destination.Target, environment)
            Assert.Equal(owner, actual)
        | kinds -> failwithf "Destination lost the exact returned closure constructor: %A" kinds
        let calls = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph
        Assert.Equal(2, calls.Length)
        let allocations = calls |> List.map (fun edge ->
            Assert.Equal(EdgeClass.Provenance, edge.Class)
            match edge.Sources, graph.Nodes[edge.Target].Kind with
            | [actual; constructor; resultFormal; allocation; supplied], SemanticKind.Application(_, arguments) ->
                Assert.Equal(implementation, actual)
                Assert.Equal(destination.Target, constructor)
                Assert.Equal(formal, resultFormal)
                Assert.Equal(supplied, arguments.Head)
                Assert.Equal<NodeId list>(arguments, curry.SaturatedCalls[edge.Target].AllArgNodes)
                match graph.Nodes[allocation].Kind, graph.Nodes[supplied].Kind with
                | SemanticKind.EnvironmentAllocate actualOwner, SemanticKind.VarRef(_, Some held) ->
                    Assert.Equal(owner, actualOwner)
                    Assert.Equal(allocation, Assert.Single graph.Nodes[held].Children)
                | kinds -> failwithf "Result storage lacks its actual allocation and value: %A" kinds
                allocation
            | evidence -> failwithf "Incomplete exact result call: %A" evidence)
        Assert.Equal(2, allocations |> Set.ofList |> Set.count)
        // Representation preparation does not assert a storage lifetime.
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Role = EdgeRole.EnvironmentResidence)

    [<Fact>]
    member _.``Environment factory preparation inserts only result storage and retains ordinary argument demand frontiers`` () =
        let original = EnvironmentFactories.check EnvironmentFactories.bareSource
        let implementation = EnvironmentFactories.implementation "bareMap" original
        let calls = EnvironmentFactories.calls implementation original
        Assert.Equal(2, calls.Length)
        let graph, _ = EnvironmentFactories.prepare original
        for call, callee, arguments in calls do
            let ordered =
                match graph.Nodes[call.Id].Kind with SemanticKind.Sequential values -> values | kind -> failwithf "Missing destination preparation: %A" kind
            Assert.Equal(2, ordered.Length)
            match graph.Nodes[ordered.Head].Kind, graph.Nodes[Assert.Single graph.Nodes[ordered.Head].Children].Kind with
            | SemanticKind.Binding(_, false, false, None), SemanticKind.EnvironmentAllocate _ -> ()
            | kinds -> failwithf "Preparation added something other than caller result storage: %A" kinds
            let actuals =
                match graph.Nodes[List.last ordered].Kind with SemanticKind.Application(_, supplied) -> supplied.Tail | kind -> failwithf "Missing invocation: %A" kind
            Assert.Equal<NodeId list>(arguments, actuals)
            for argument in arguments do
                let evaluations = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && List.contains argument node.Children)
                Assert.Single evaluations |> ignore
            for id in [implementation; callee] do
                Assert.Equal(formatType (EnvironmentFactories.sourceSignature original.Nodes[id]),
                             formatType (EnvironmentFactories.sourceSignature graph.Nodes[id]))
                Assert.True(graph.Nodes[id].Metadata.ContainsKey ClosureMetadata.SourceSignature)
            Assert.Equal(call.Range, graph.Nodes[call.Id].Range)
        let writes graph = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && (match node.Kind with SemanticKind.Set _ -> true | _ -> false)) |> Seq.map _.Id |> Set.ofSeq
        Assert.Equal<Set<NodeId>>(writes original, writes graph)

    [<Fact>]
    member _.``A stored factory alias preserves its formation and original callee while receiving distinct result storage`` () =
        let original = EnvironmentFactories.check """
let mutable formations = 0
[<EntryPoint>]
let main _ =
    let stored = (formations <- formations + 1; fun (offset: int) -> fun value -> value + offset)
    let first = stored 3
    let second = stored 4
    if first 5 = second 4 then formations else 1
"""
        let stored = EnvironmentFactories.binding "stored" original
        let formation = original.Nodes[Assert.Single stored.Children]
        match formation.Kind with
        | SemanticKind.Sequential values -> Assert.Equal(2, values.Length)
        | kind -> failwithf "Expected the original deferred formation: %A" kind
        let implementation = EnvironmentFactories.implementation "stored" original
        let calls = EnvironmentFactories.calls implementation original
        Assert.Equal(2, calls.Length)
        let graph, _ = EnvironmentFactories.prepare original
        let destinations = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph
        Assert.Equal(2, destinations.Length)
        Assert.Equal(2, destinations |> List.map (fun row -> row.Sources[3]) |> Set.ofList |> Set.count)
        Assert.Equal<NodeId list>(stored.Children, graph.Nodes[stored.Id].Children)
        Assert.Equal<NodeId list>(formation.Children, graph.Nodes[formation.Id].Children)
        for call, callee, arguments in calls do
            let invocation =
                match graph.Nodes[call.Id].Kind with
                | SemanticKind.Sequential [storage; invocation] ->
                    match graph.Nodes[Assert.Single graph.Nodes[storage].Children].Kind with
                    | SemanticKind.EnvironmentAllocate _ -> ()
                    | kind -> failwithf "Unexpected preparation operand: %A" kind
                    graph.Nodes[invocation]
                | kind -> failwithf "Factory alias lost destination-only preparation: %A" kind
            match invocation.Kind with
            | SemanticKind.Application(actualCallee, actualArguments) ->
                Assert.Equal(callee, actualCallee)
                Assert.Equal<NodeId list>(arguments, actualArguments.Tail)
                match graph.Nodes[callee].Kind with
                | SemanticKind.VarRef(_, Some declaration) -> Assert.Equal(stored.Id, declaration)
                | kind -> failwithf "Alias demand identity changed: %A" kind
            | kind -> failwithf "Missing original invocation: %A" kind

    [<Fact>]
    member _.``A capturing factory keeps its own environment first and inserts result storage before source arguments`` () =
        let original = EnvironmentFactories.check """
[<EntryPoint>]
let main _ =
    let mutable effects = 0
    let mutable formations = 0
    let make = fun (offset: int) -> fun value -> effects <- value; value + offset
    let callback = make (formations <- 1; 7)
    let mapped = Seq.map callback (seq { yield 2 })
    for value in mapped do ignore value
    formations
"""
        let implementation = EnvironmentFactories.implementation "make" original
        let environment = EnvironmentFactories.relations EdgeRole.EnvironmentFormal original |> List.filter (fun edge -> List.tryLast edge.Sources = Some implementation) |> Assert.Single
        let call, _, originalArguments = EnvironmentFactories.calls implementation original |> Assert.Single
        let graph, _ = EnvironmentFactories.prepare original
        let destination = EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination graph |> Assert.Single
        let resultFormal = List.last destination.Sources
        match graph.Nodes[implementation].Kind with
        | SemanticKind.Lambda((_, _, first) :: (_, _, second) :: _, _, [], _, _) ->
            Assert.Equal(environment.Target, first)
            Assert.Equal(resultFormal, second)
        | kind -> failwithf "Factory lost environment-first order: %A" kind
        let invocation = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph |> Assert.Single
        let supplied =
            match graph.Nodes[invocation.Target].Kind with SemanticKind.Application(_, arguments) -> arguments | _ -> failwith "Missing prepared call"
        Assert.Equal(List.last invocation.Sources, supplied[1])
        let ordered = match graph.Nodes[call.Id].Kind with SemanticKind.Sequential values -> values | _ -> failwith "Missing frontier"
        Assert.Equal(2, ordered.Length)
        Assert.Equal<NodeId list>(originalArguments, supplied.Head :: List.skip 2 supplied)
        Assert.Equal(Some(0, supplied[0]), (EnvironmentValues.callEnvironments graph).TryFind invocation.Target)
        Assert.Equal(formatType (EnvironmentFactories.sourceSignature original.Nodes[implementation]),
                     formatType (EnvironmentFactories.sourceSignature graph.Nodes[implementation]))

    [<Fact>]
    member _.``An opaque extra use retracts all destination preparation for the otherwise closed factory`` () =
        let original = EnvironmentFactories.check EnvironmentFactories.bareSource
        let implementation = EnvironmentFactories.implementation "bareMap" original
        let _, callee, _ = EnvironmentFactories.calls implementation original |> List.head
        let consumer = original.Nodes.Values |> Seq.find (fun node -> node.IsReachable && (match node.Kind with SemanticKind.Literal _ -> true | _ -> false))
        let opaque = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Symbol 0 callee consumer.Id
        let changed = { original with Edges = opaque :: original.Edges }
        let prepared, _ = EnvironmentFactories.prepare changed
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination prepared)
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultCall prepared)
        let control, _ = EnvironmentFactories.prepare original
        Assert.Single(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination control) |> ignore

    [<Fact>]
    member _.``A mixed known and opaque callable alternative cannot acquire one factory destination`` () =
        let original = EnvironmentFactories.check EnvironmentFactories.bareSource
        let implementation = EnvironmentFactories.implementation "bareMap" original
        let _, callee, _ = EnvironmentFactories.calls implementation original |> List.head
        let source = original.Nodes[callee]
        let known = { source with Id = NodeId.fresh(); Parent = Some callee }
        let opaque = { source with Id = NodeId.fresh(); Kind = SemanticKind.PatternBinding "opaque"; Children = []; Parent = Some callee }
        let condition = { source with Id = NodeId.fresh(); Kind = SemanticKind.Literal(NativeLiteral.Bool true); Type = Types.boolType; Children = []; Parent = Some callee }
        let chosen = { source with Kind = SemanticKind.IfThenElse(condition.Id, known.Id, Some opaque.Id); Children = [condition.Id; known.Id; opaque.Id] }
        let added = [known; opaque; condition; chosen]
        let graph =
            { original with Nodes = added |> List.fold (fun nodes node -> Map.add node.Id node nodes) original.Nodes
                            Edges = (original.Edges |> List.filter (fun edge -> edge.Target <> callee)) @ (added |> List.collect EnvironmentIncidence.structuralIncidence) }
        let prepared, _ = EnvironmentFactories.prepare graph
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination prepared)
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultCall prepared)

    [<Fact>]
    member _.``Stored partial factory application retains its earlier supplied effect without destination preparation`` () =
        let original = EnvironmentFactories.check """
let make (left: int) (right: int) = fun value -> left + right + value
[<EntryPoint>]
let main _ =
    let mutable formations = 0
    let partial = make (formations <- 1; 3)
    let callback = partial 4
    let values = Seq.map callback (seq { yield 2 })
    for value in values do ignore value
    formations
"""
        Assert.NotEmpty original.Codata.Value.Curry.PartialApplications
        let prepared, _ = EnvironmentFactories.prepare original
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination prepared)
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultCall prepared)
        let partial = EnvironmentFactories.binding "partial" original
        Assert.Equal<NodeId list>(partial.Children, prepared.Nodes[partial.Id].Children)

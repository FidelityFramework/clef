namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module FactoryResults = Clef.Compiler.Nanopass.SequenceFactoryResults
module FactoryResidence = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence

module private Factories =
    let check body =
        let result = DimensionalCases.check body
        DimensionalCases.noErrors result
        Assert.True result.Graph.Platform.IsNone
        result.Graph

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

    let lambda (graph: SemanticGraph) name =
        graph.Nodes[Assert.Single (binding name graph).Children]

    let owner (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false)
        |> Assert.Single

    let calls (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind, applySubst node.Type with SemanticKind.Application _, NativeType.TSeq _ -> true | _ -> false)
        |> Seq.toList

    let signature (node: SemanticNode) =
        match node.Metadata.TryFind ClosureMetadata.SourceSignature with
        | Some (MetadataValue.Type ty) -> ty
        | _ -> node.Type

    let rec arguments (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Application(callee, supplied) -> arguments graph callee @ supplied
        | SemanticKind.TypeAnnotation(inner, _) -> arguments graph inner
        | _ -> []

    let prepare graph = FactoryResults.prepare graph graph.Codata.Value.Curry

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceFactoryResults")>]
type SequenceFactoryResultsCases() =
    [<Fact>]
    member _.``Direct captured scalar factory receives a caller-owned destination without changing its capture identity``() =
        let graph = Factories.check """
let make (seed: int<m>) = seq { yield seed }
[<EntryPoint>]
let main _ =
    let values = make 7<m>
    for value in values do ignore value
    0
"""
        let owner, lambda = Factories.owner graph, Factories.lambda graph "make"
        // Select by the direct callee, rather than source-line offsets in the
        // shared dimensional prelude or the generated enumeration operation.
        let factory = Factories.binding "make" graph
        let call = Factories.calls graph |> List.find (fun node ->
            match node.Kind with
            | SemanticKind.Application(callee, _) -> match graph.Nodes[callee].Kind with SemanticKind.VarRef(_, Some target) -> target = factory.Id | _ -> false
            | _ -> false)
        let prepared = Factories.prepare graph
        Assert.Empty prepared.Unresolved
        let destination = prepared.Graph.Nodes[prepared.Destinations[owner.Id]]
        Assert.Equal(owner.Type, destination.Type)
        match prepared.Graph.Nodes[lambda.Id].Kind with
        | SemanticKind.Lambda((_, ty, formal) :: _, _, _, _, _) -> Assert.Equal(destination.Id, formal); Assert.Equal(owner.Type, ty)
        | kind -> failwithf "Factory has no hidden typed formal: %A" kind
        let originalCaptures = match owner.Kind with SemanticKind.SeqExpr(_, captures) -> captures |> List.choose _.SourceNodeId | _ -> []
        let captures = match prepared.Graph.Nodes[owner.Id].Kind with SemanticKind.SeqExpr(_, captures) -> captures |> List.choose _.SourceNodeId | _ -> []
        Assert.NotEmpty captures
        Assert.Equal<NodeId list>(originalCaptures, captures)
        Assert.Equal(call.Range, prepared.Graph.Nodes[call.Id].Range)
        Assert.Same(graph.FieldRanges, prepared.Graph.FieldRanges)
        Assert.Same(graph.ElementRanges, prepared.Graph.ElementRanges)
        Assert.Same(graph.Layouts, prepared.Graph.Layouts)
        Assert.False(destination.Metadata.ContainsKey ClosureMetadata.SourceSignature)

    [<Fact>]
    member _.``Unstored curried operands are snapshotted once in source order before allocating the destination``() =
        let graph = Factories.check """
let mutable trace = 0
let first () = trace <- trace * 10 + 1; 7
let second () = trace <- trace * 10 + 2; 8
let make left right = seq { yield left + right }
[<EntryPoint>]
let main _ =
    let values = make (first ()) (second ())
    for value in values do ignore value
    trace
"""
        let call = Factories.calls graph |> List.filter (fun node -> (Factories.arguments graph node.Id).Length = 2) |> Assert.Single
        let arguments = Factories.arguments graph call.Id
        let prepared = Factories.prepare graph
        Assert.Empty prepared.Unresolved
        let ordered = match prepared.Graph.Nodes[call.Id].Kind with SemanticKind.Sequential ordered -> ordered | kind -> failwithf "No eager frontier: %A" kind
        Assert.Equal(4, ordered.Length)
        let snapshots = ordered |> List.take 2 |> List.map (fun id -> prepared.Graph.Nodes[id])
        Assert.Equal<NodeId list>(arguments, snapshots |> List.map (fun node -> Assert.Single node.Children))
        let allocationBinding = prepared.Graph.Nodes[ordered[2]]
        let allocation = prepared.Graph.Nodes[Assert.Single allocationBinding.Children]
        Assert.True(prepared.AllocationOrigins.ContainsKey allocation.Id)
        let actualCall = ordered[3]
        Assert.Equal(allocation.Id, prepared.FactoryCalls[actualCall])
        let actualArguments = prepared.Curry.SaturatedCalls[actualCall].AllArgNodes
        Assert.Equal(3, actualArguments.Length)
        for snapshot, argument in List.zip snapshots actualArguments.Tail do
            match prepared.Graph.Nodes[argument].Kind with
            | SemanticKind.VarRef(_, Some source) -> Assert.Equal(snapshot.Id, source)
            | kind -> failwithf "An operand would be evaluated again: %A" kind
        for argument in arguments do
            let uses = prepared.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && List.contains argument node.Children) |> Seq.toList
            Assert.Single uses |> ignore
            Assert.Equal(graph.Nodes[argument].Range, prepared.Graph.Nodes[argument].Range)

    [<Fact>]
    member _.``Public callable signatures stay source-level while semantic signatures include destination storage``() =
        let graph = Factories.check "let make (seed: int<m>) = seq { yield seed }\n[<EntryPoint>]\nlet main _ = ignore (make 3<m>); 0\n"
        let factory, lambda = Factories.binding "make" graph, Factories.lambda graph "make"
        let callee = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.VarRef(_, Some source) -> source = factory.Id | _ -> false) |> Assert.Single
        let prepared = Factories.prepare graph
        Assert.Empty prepared.Unresolved
        for original in [factory; lambda; callee] do
            let changed = prepared.Graph.Nodes[original.Id]
            Assert.Equal(formatType (Factories.signature original), formatType (Factories.signature changed))
            Assert.True(changed.Metadata.ContainsKey ClosureMetadata.SourceSignature)
            match applySubst changed.Type with
            | NativeType.TFun(NativeType.TSeq _, remainder) -> Assert.Equal(formatType original.Type, formatType remainder)
            | ty -> failwithf "Missing semantic destination type: %s" (formatType ty)

    [<Fact>]
    member _.``Two calls receive distinct storage and exact call-to-allocation and allocation-to-owner maps``() =
        let graph = Factories.check "let make seed = seq { yield seed }\n[<EntryPoint>]\nlet main _ =\n    let first = make 3\n    let second = make 4\n    ignore first\n    ignore second\n    0\n"
        let prepared = Factories.prepare graph
        Assert.Empty prepared.Unresolved
        Assert.Single prepared.Destinations |> ignore
        Assert.Equal(2, prepared.FactoryCalls.Count)
        Assert.Equal(2, prepared.AllocationOrigins.Count)
        Assert.Equal(2, prepared.FactoryCalls.Values |> Set.ofSeq |> Set.count)
        let owner = Factories.owner graph
        for pair in prepared.FactoryCalls do
            Assert.Equal(owner.Id, prepared.AllocationOrigins[pair.Value])
            match prepared.Graph.Nodes[pair.Value].Kind with
            | SemanticKind.ContinuationAllocate actual -> Assert.Equal(owner.Id, actual)
            | kind -> failwithf "Call has no explicit destination allocation: %A" kind
            let supplied = prepared.Curry.SaturatedCalls[pair.Key].AllArgNodes.Head
            let binding = match prepared.Graph.Nodes[supplied].Kind with SemanticKind.VarRef(_, Some source) -> source | _ -> failwith "No destination reference"
            Assert.Equal(pair.Value, Assert.Single prepared.Graph.Nodes[binding].Children)

    [<Fact>]
    member _.``Stored partial remains residual instead of moving an earlier eager snapshot into each call``() =
        let graph = Factories.check "let make (left: int) (right: int) = seq { yield left + right }\n[<EntryPoint>]\nlet main _ =\n    let partial = make 3\n    let values = partial 4\n    ignore values\n    0\n"
        let factory = Factories.binding "make" graph
        let prepared = Factories.prepare graph
        Assert.Empty prepared.Destinations
        Assert.Empty prepared.AllocationOrigins
        Assert.Empty prepared.FactoryCalls
        Assert.Contains(prepared.Unresolved, fun residual -> residual.Factory = factory.Id && residual.Reason.Contains "partial")
        Assert.Equal(formatType factory.Type, formatType prepared.Graph.Nodes[factory.Id].Type)

    [<Fact>]
    member _.``Factory-local mutable capture cannot outlive its cell merely by moving the result frame``() =
        let graph = Factories.check """
let make (seed: int) =
    let mutable local = seed
    seq { yield local }
[<EntryPoint>]
let main _ =
    let values = make 7
    for value in values do ignore value
    0
"""
        let owner, factory = Factories.owner graph, Factories.binding "make" graph
        match owner.Kind with
        | SemanticKind.SeqExpr(_, captures) -> Assert.Contains(captures, fun capture -> capture.IsMutable && capture.Name = "local")
        | _ -> failwith "Expected sequence owner"
        // Clearing the convenience parent field must not hide the cell's
        // allocation in the factory activation from the lifetime check.
        let graph = { graph with Nodes = graph.Nodes |> Map.map (fun _ node -> { node with Parent = None }) }
        let prepared = Factories.prepare graph
        Assert.Empty prepared.Destinations
        Assert.Contains(prepared.Unresolved, fun residual ->
            residual.Factory = factory.Id && residual.Reason.Contains "Factory-local capture 'local'" && residual.Reason.Contains "region")
        let reading = FactoryResidence.analyzePrepared prepared.Graph prepared.Destinations prepared.FactoryCalls
        Assert.False(reading.Sites.ContainsKey owner.Id)

    [<Fact>]
    member _.``Mutable state declared inside the sequence remains internal while caller allocation gets a bounded residence``() =
        let graph = Factories.check """
let make (seed: int) = seq {
    let mutable current = seed
    yield current
    current <- current + 1
    yield current
}
[<EntryPoint>]
let main _ =
    let values = make 7
    for value in values do ignore value
    0
"""
        let prepared = Factories.prepare graph
        Assert.Empty prepared.Unresolved
        Assert.Single prepared.Destinations |> ignore
        let reading = FactoryResidence.analyzePrepared prepared.Graph prepared.Destinations prepared.FactoryCalls
        Assert.Empty reading.Unresolved
        Assert.Equal(2, reading.Sites.Count) // Caller result storage + fresh iterator.
        for pair in prepared.AllocationOrigins do Assert.Equal(EscapeKind.StackScoped, reading.Sites[pair.Key])
        // A plain call argument is insufficient proof: the exact admitted
        // initialization relation is necessary at the hidden first operand.
        let withoutCallProof = FactoryResidence.analyzePrepared prepared.Graph prepared.Destinations Map.empty
        for allocation in prepared.AllocationOrigins.Keys do Assert.False(withoutCallProof.Sites.ContainsKey allocation)
        Assert.NotEmpty withoutCallProof.Unresolved

    [<Fact>]
    member _.``Nested sequential factory prefixes retain their eager statements before the single result constructor``() =
        let graph = Factories.check """
let mutable trace = 0
let make () =
    if trace <> 0 then trace <- 8
    trace <- 2
    seq { yield 7<m> }
[<EntryPoint>]
let main _ =
    let values = make ()
    for value in values do ignore value
    trace
"""
        let owner, implementation = Factories.owner graph, Factories.lambda graph "make"
        let body = match implementation.Kind with SemanticKind.Lambda(_, body, _, _, _) -> body | _ -> failwith "Expected factory Lambda"
        let rec terminalPath id =
            id :: (match graph.Nodes[id].Kind with
                   | SemanticKind.Sequential values -> terminalPath (List.last values)
                   | SemanticKind.TypeAnnotation(value, _) -> terminalPath value
                   | _ -> [])
        let path = terminalPath body
        Assert.True(path.Length >= 3, "Fixture must exercise nested Sequential result positions")
        Assert.Equal(owner.Id, List.last path)
        let prepared = Factories.prepare graph
        Assert.Empty prepared.Unresolved
        Assert.True(prepared.Destinations.ContainsKey owner.Id)
        for id in path |> List.filter ((<>) owner.Id) do
            Assert.Equal(graph.Nodes[id].Kind, prepared.Graph.Nodes[id].Kind)
            Assert.Equal<NodeId list>(graph.Nodes[id].Children, prepared.Graph.Nodes[id].Children)
        let destination = prepared.Destinations[owner.Id]
        Assert.Contains(prepared.Graph.Edges, fun edge ->
            edge.Target = destination && edge.Class = EdgeClass.Provenance
            && List.contains owner.Id edge.Sources)

    [<Fact>]
    member _.``A result constructor also used in an eager prefix cannot share its caller destination``() =
        let graph = Factories.check """
let make () =
    ignore 1
    seq { yield 7<m> }
[<EntryPoint>]
let main _ =
    let values = make ()
    for value in values do ignore value
    0
"""
        let owner, implementation = Factories.owner graph, Factories.lambda graph "make"
        let shared = { graph with Nodes = graph.Nodes.Add(implementation.Id, { implementation with Children = implementation.Children @ [owner.Id] }) }
        // The added structural use is in a separate position of the same
        // activation; lexical scope alone must not authorize one destination.
        let prepared = Factories.prepare shared
        Assert.False(prepared.Destinations.ContainsKey owner.Id)
        Assert.Contains(prepared.Unresolved, fun failure -> failure.Reason.Contains("shared or repeated"))

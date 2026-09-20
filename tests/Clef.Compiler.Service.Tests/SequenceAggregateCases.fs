namespace Clef.Compiler.Service.Tests

open Xunit
open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
module AggregateAdmission = Clef.Compiler.PSGSaturation.SemanticGraph.AggregateValues
module AggregatePlacement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module AggregateRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module AggregateRuntime = Clef.Compiler.Nanopass.SequenceRuntime
module AggregateSnapshots = Clef.Compiler.Nanopass.SequenceAggregateValues
module AggregateCopies = Clef.Compiler.Baker.Ingredients.AggregateCopies

module private AggregateFixture =
    let platform: PlatformContext =
        let rep name family bits low high: NumericRepresentation =
            { Name = name; Capability = "native"; Family = family; Bits = bits
              MinMagnitude = low; MaxMagnitude = high; Boundary = "wrap" }
        let reps = [rep "signed8" "int" 8 "-128" "127"; rep "unsigned8" "uint" 8 "0" "255"
                    rep "signed64" "int" 64 "-9223372036854775808" "9223372036854775807"
                    rep "unsigned64" "uint" 64 "0" "18446744073709551615"]
        { PlatformId = "aggregate-transport-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
          Representations = reps |> List.map (fun rep -> rep.Name, rep) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = None
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.empty
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let source = """
[<EntryPoint>]
let main _ =
    let selected = Seq.tryHead (seq { yield (None: int<m> option); yield Some 9<m> })
    let accepted = match selected with Some None -> true | _ -> false
    ignore accepted
    0
"""
    let graph source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        let graph, diagnostics = AggregateRanges.run (Some platform) { result.Graph with Platform = Some platform }
        Assert.Empty diagnostics
        AggregatePlacement.settle (Some platform) graph, result.Graph.Codata.Value.Curry

    let current graph =
        let reads, certificates = Clef.Compiler.Nanopass.SequenceCurrentAdmission.certify graph
        Assert.Single reads |> ignore
        Set.minElement reads, reads, certificates

    type Value = Number of int64 | Flag of bool | Storage of NodeId | Unit
    // An evaluator of the emitted selected-case copy only. An inactive payload
    // read fails immediately, independently of the pattern implementation.
    let execute (nodes: Map<NodeId, SemanticNode>) (cells: System.Collections.Generic.Dictionary<NodeId, int * int64 option>) root =
        let rec evaluate id =
            match nodes[id].Kind with
            | SemanticKind.PatternBinding _ -> Storage id
            | SemanticKind.Sequential values -> values |> List.fold (fun _ value -> evaluate value) Unit
            | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> Number value
            | SemanticKind.DUGetTag(source, _) -> Number(int64 (fst cells[source]))
            | SemanticKind.DUEliminate(source, 1, "Some", _) ->
                match cells[source] with 1, Some value -> Number value | _ -> failwith "Read an inactive Option payload"
            | SemanticKind.Application(callee, [left; right]) ->
                match nodes[callee].Kind with
                | SemanticKind.Intrinsic { Operation = "op_Equality" } -> Flag(evaluate left = evaluate right)
                | kind -> failwithf "Unexpected copy operation: %A" kind
            | SemanticKind.IfThenElse(guard, yes, Some no) ->
                match evaluate guard with Flag true -> evaluate yes | Flag false -> evaluate no | _ -> failwith "Nonboolean copy guard"
            | SemanticKind.DUInitialize(destination, _, tag, payload) ->
                let value = payload |> Option.map (fun id -> match evaluate id with Number value -> value | _ -> failwith "Nonscalar payload")
                cells[destination] <- tag, value
                Unit
            | kind -> failwithf "Unexpected copy node: %A" kind
        evaluate root |> ignore

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceAggregate")>]
type SequenceAggregateCases() =
    [<Fact>]
    member _.``Current owns exact settled Option bytes rather than a descriptor to temporary storage``() =
        let graph, curry = AggregateFixture.graph AggregateFixture.source
        let originalNodes, originalEdges = graph.Nodes, graph.Edges
        let settled, runtime = AggregateRuntime.normalize graph curry
        Assert.Empty runtime.Diagnostics
        let frame = runtime.Frames.Values |> Assert.Single
        let slot = frame.Slots |> List.find (fun slot -> slot.Source = frame.Current)
        let _, bytes, alignment = AggregateAdmission.scalarOption graph slot.ValueType |> Option.get
        Assert.Equal(CaptureSlotKind.InlineValue slot.ValueType, slot.Holds)
        Assert.Equal(SettledSlot.InlineBytes(bytes, alignment), slot.Field.Slot)
        Assert.Equal(Some bytes, slot.Field.Size)
        Assert.Contains(settled.Nodes.Values, fun node -> node.IsReachable && match node.Kind with SemanticKind.DUInitialize _ -> true | _ -> false)
        Assert.DoesNotContain(settled.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.FrameWrite(_, slot, _) -> slot = frame.Current | _ -> false)
        Assert.Contains(settled.Edges, fun edge -> edge.Role = EdgeRole.AggregateCopy)
        Assert.Same(originalNodes, graph.Nodes)
        Assert.Same(originalEdges, graph.Edges)

    [<Fact>]
    member _.``External snapshot retains successful pull activation layout and source identity``() =
        let graph, _ = AggregateFixture.graph AggregateFixture.source
        let current, reads, certificates = AggregateFixture.current graph
        let prepared = AggregateSnapshots.prepare graph reads certificates
        Assert.Empty prepared.Unresolved
        let allocation = prepared.Graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.AggregateStorage _ -> true | _ -> false) |> Assert.Single
        Assert.Equal(Some EscapeKind.StackScoped, prepared.Residences.TryFind allocation.Id)
        Assert.Equal(graph.Nodes[current].Range, prepared.Graph.Nodes[current].Range)
        DimensionalCases.same graph.Nodes[current].Type prepared.Graph.Nodes[current].Type
        let raw = Assert.Single prepared.Reads
        Assert.NotEqual(current, raw)
        let certificate = Assert.Single prepared.Certificates
        Assert.Equal(raw, certificate.Target)
        Assert.Contains(current, certificate.Sources)
        let snapshot = prepared.Graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.AggregateSnapshot) |> Assert.Single
        Assert.Contains(allocation.Id, snapshot.Sources)
        Assert.Contains(raw, snapshot.Sources)
        for edge in prepared.Graph.Edges do
            for participant in edge.Target :: edge.Sources do Assert.True(prepared.Graph.Nodes.ContainsKey participant)

    [<Fact>]
    member _.``Opaque use retracts current snapshot residence at the exact consumer``() =
        let graph, _ = AggregateFixture.graph AggregateFixture.source
        let current, reads, certificates = AggregateFixture.current graph
        let consumer = graph.Nodes.Values |> Seq.find (fun node -> node.IsReachable && match node.Kind with SemanticKind.Literal _ -> true | _ -> false)
        let changed = { graph with Edges = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Symbol 0 current consumer.Id :: graph.Edges }
        let prepared = AggregateSnapshots.prepare changed reads certificates
        Assert.Contains((current, consumer.Id), prepared.Unresolved)
        Assert.Empty prepared.Residences
        Assert.DoesNotContain(prepared.Graph.Nodes.Values, fun node -> match node.Kind with SemanticKind.AggregateStorage _ -> true | _ -> false)
        Assert.Empty (AggregateSnapshots.prepare graph reads certificates).Unresolved

    [<Fact>]
    member _.``Missing successful pull relation cannot allocate a current snapshot``() =
        let graph, _ = AggregateFixture.graph AggregateFixture.source
        let current, reads, _ = AggregateFixture.current graph
        let prepared = AggregateSnapshots.prepare graph reads []
        Assert.Contains((current, current), prepared.Unresolved)
        Assert.Empty prepared.Residences
        Assert.DoesNotContain(prepared.Graph.Nodes.Values, fun node -> match node.Kind with SemanticKind.AggregateStorage _ -> true | _ -> false)

    [<Fact>]
    member _.``Returned snapshot needs a caller destination and is not granted local residence``() =
        let graph, _ = AggregateFixture.graph """
let selected () = Seq.tryHead (seq { yield Some 1<m> })
[<EntryPoint>]
let main _ = ignore (selected ()); 0
"""
        let current, reads, certificates = AggregateFixture.current graph
        let prepared = AggregateSnapshots.prepare graph reads certificates
        Assert.Contains(prepared.Unresolved, fun (site, _) -> site = current)
        Assert.Empty prepared.Residences

    [<Fact>]
    member _.``Nested reference payload and captured Option are not admitted by scalar transport``() =
        let graph, _ = AggregateFixture.graph AggregateFixture.source
        let current, _, _ = AggregateFixture.current graph
        let original = graph.Nodes[current]
        let nestedType = NativeType.TApp(Types.optionTyCon, [original.Type])
        Assert.True(AggregateAdmission.scalarOption graph nestedType |> Option.isNone)
        let capture: CaptureInfo = { Name = "captured"; Type = original.Type; IsMutable = false; SourceNodeId = Some current }
        match AggregatePlacement.placeEnvironment graph [capture] with
        | Error (AggregatePlacement.ContinuationPlacementError.UnsupportedField(actual, _)) -> Assert.Equal(current, actual)
        | result -> failwithf "Captured aggregate acquired unproved storage: %A" result

    [<Fact>]
    member _.``Selected-case copies preserve earlier snapshots and never read None payload``() =
        let builder = NodeBuilder()
        let ty = NativeType.TApp(Types.optionTyCon, [Types.intType])
        let source = builder.Create(SemanticKind.PatternBinding "source", ty, dummyRange)
        let first = builder.Create(SemanticKind.PatternBinding "first", ty, dummyRange)
        let second = builder.Create(SemanticKind.PatternBinding "second", ty, dummyRange)
        let copy destination =
            let state = SaturationState.create dummyRange "copy-test" 0 source.Id None
            match run state (AggregateCopies.option source.Id destination Types.intType) with
            | Matched(root, evidence), nodes -> root, evidence, nodes
            | other -> failwithf "Copy recipe failed: %A" other
        let firstRoot, firstEdge, firstNodes = copy first.Id
        let root = firstNodes |> List.find (fun node -> node.Id = firstRoot)
        Assert.Equal(SemanticKind.Sequential [source.Id; first.Id; firstEdge.Target], root.Kind)
        let decision = firstNodes |> List.find (fun node -> node.Id = firstEdge.Target)
        match decision.Kind with
        | SemanticKind.IfThenElse(_, _, Some none) ->
            let noPayload = firstNodes |> List.find (fun node -> node.Id = none)
            Assert.Equal(SemanticKind.DUInitialize(first.Id, "None", 0, None), noPayload.Kind)
        | kind -> failwithf "Missing selected-case copy: %A" kind
        // This recipe also runs after RangeAnalysis. Its closed tag/literal
        // facts must be complete when emitted; Alex cannot infer them later.
        for node in firstNodes do
            match node.Kind with
            | SemanticKind.DUGetTag _ -> Assert.Equal(Some(ValueRange.bounded 0I 1I), node.ValueRange)
            | SemanticKind.DUEliminate _ -> Assert.Equal(Some ValueRange.Unbounded, node.ValueRange)
            | SemanticKind.Application _ when Types.tryGetNTUKind node.Type = Some NTUKind.NTUbool ->
                Assert.Equal(Some ValueRange.boolean, node.ValueRange)
            | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> Assert.Equal(Some(ValueRange.bounded (bigint value) (bigint value)), node.ValueRange)
            | _ -> ()
        let secondRoot, _, secondNodes = copy second.Id
        let nodes = (builder.Build []).Nodes |> fun initial -> (firstNodes @ secondNodes) |> List.fold (fun nodes node -> Map.add node.Id node nodes) initial
        let cells = System.Collections.Generic.Dictionary<NodeId, int * int64 option>()
        cells[source.Id] <- 1, Some 11L
        AggregateFixture.execute nodes cells firstRoot
        cells[source.Id] <- 1, Some 22L
        AggregateFixture.execute nodes cells secondRoot
        Assert.Equal((1, Some 11L), cells[first.Id])
        Assert.Equal((1, Some 22L), cells[second.Id])
        cells[source.Id] <- 0, None
        AggregateFixture.execute nodes cells secondRoot
        Assert.Equal((0, None), cells[second.Id])
        Assert.Equal((1, Some 11L), cells[first.Id])
        Assert.Contains(source.Id, firstEdge.Sources)
        Assert.Contains(first.Id, firstEdge.Sources)

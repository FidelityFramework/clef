namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe

module Instances = Clef.Compiler.PSGSaturation.SemanticGraph.CallableInstantiations
module InstanceEnvironments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module ContinuationIngress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress

module private InstanceContinuationFixture =
    let graph () =
        let source = """module MeasuredContinuation
[<Measure>] type m
[<EntryPoint>]
let main _ =
    let scale = 2
    let mutable calls = 0
    let mapper = fun value -> calls <- (calls + 1) % 100; value * scale
    let alias = mapper
    let mapped = Seq.map alias (seq { yield 3<m>; yield 4<m> })
    for value in mapped do ignore value
    calls
"""
        LazyResidenceFixture.programWith (Some source)

    let implementation (graph: SemanticGraph) =
        let declaration =
            graph.Nodes.Values |> Seq.find (fun node ->
                match node.Kind with SemanticKind.Binding("mapper", false, _, _) -> true | _ -> false)
        InstanceEnvironments.tryImplementation graph declaration.Id |> Option.get

    let invocations (graph: SemanticGraph) implementation =
        let read = Instances.callReader graph
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable)
        |> Seq.choose (fun node -> read node.Id implementation) |> Seq.toList

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableInstantiations")>]
type CallableInstanceContinuationCases() =
    [<Fact>]
    member _.``Fold-in preserves the complete original invocation behind a continuation call``() =
        let graph = InstanceContinuationFixture.graph ()
        let implementation = InstanceContinuationFixture.implementation graph
        let call = InstanceContinuationFixture.invocations graph implementation |> List.head
        let row = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.EnvironmentInvocation && edge.Sources[1] = implementation && call.Participants.Contains edge.Target) |> Assert.Single
        let ids = row.Target :: row.Sources |> List.distinct
        let replacements = ids |> List.map (fun id -> id, { graph.Nodes[id] with Id = NodeId.fresh() }) |> Map.ofList
        let replace id = replacements.TryFind id |> Option.map _.Id |> Option.defaultValue id
        let recipes = ids |> List.map (fun id ->
            let node = replacements[id]
            { OriginalNodeId = id; ReplacementRootId = node.Id; NewNodes = [node]
              ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Measured invocation replacement" })
        let folded = Clef.Compiler.Nanopass.FoldIn.foldIn (RecipeSet.fromList "Baker" recipes) graph
        let proof = Instances.callReader folded (replace call.Site) (replace implementation) |> Option.get
        let actual = folded.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EnvironmentInvocation && edge.Target = replace row.Target) |> Assert.Single
        Assert.Equal<NodeId list>(List.map replace row.Sources, actual.Sources)
        Assert.Equal(call.Callable.InstanceType, proof.Callable.InstanceType)
        for old in ids do
            Assert.False(folded.Nodes.ContainsKey old)
            Assert.DoesNotContain(old, proof.Participants)
            Assert.Contains(replace old, proof.Participants)

    [<Fact>]
    member _.``Measured continuation invokes the same checked instance through its actual frame environment``() =
        let graph = InstanceContinuationFixture.graph ()
        let implementation = InstanceContinuationFixture.implementation graph
        let calls = InstanceContinuationFixture.invocations graph implementation
        Assert.NotEmpty calls
        let ingress = ContinuationIngress.analyze graph
        let frames = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind, applySubst node.Type with
            | SemanticKind.FrameRead _, NativeType.TFun _ -> InstanceEnvironments.tryImplementation graph node.Id = Some implementation
            | _ -> false) |> Seq.toList
        Assert.NotEmpty frames
        for frame in frames do
            Assert.True(graph.Codata.Value.CallableCarriers.ContainsKey frame.Id)
            Assert.True(ContinuationIngress.allowsOccurrence ingress frame.Id)
            match frame.Kind with
            | SemanticKind.FrameRead(_, original) when not graph.Nodes[original].IsReachable ->
                Assert.False(ContinuationIngress.allowsOccurrence ingress original)
                Assert.True((ContinuationIngress.tryRetainedEvidence ingress original).IsSome)
            | _ -> ()
        for call in calls do
            Assert.Equal(implementation, call.Implementation)
            Assert.Equal("int<m> -> int<m>", formatType call.Callable.InstanceType)
            Assert.Contains(call.Site, call.Participants)
            Assert.Contains(call.Callable.Occurrence, call.Participants)
            Assert.Equal(call.Parameters.Length, call.Arguments.Length)

    [<Theory>]
    [<InlineData("missing invocation")>]
    [<InlineData("duplicate invocation")>]
    [<InlineData("wrong callable")>]
    [<InlineData("wrong code")>]
    [<InlineData("different environment")>]
    [<InlineData("wrong ordered arguments")>]
    [<InlineData("changed instantiation")>]
    [<InlineData("extra writer")>]
    member _.``Changed source invocation or frame writer retracts the instantiated physical call``(change: string) =
        let graph = InstanceContinuationFixture.graph ()
        let implementation = InstanceContinuationFixture.implementation graph
        let call = InstanceContinuationFixture.invocations graph implementation |> List.head
        let row = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.EnvironmentInvocation && edge.Sources[1] = implementation && call.Participants.Contains edge.Target) |> Assert.Single
        let replaceRow f = { graph with Edges = graph.Edges |> List.map (fun edge -> if obj.ReferenceEquals(edge, row) then f edge else edge) }
        let changed =
            match change with
            | "missing invocation" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> not (obj.ReferenceEquals(edge, row))) }
            | "duplicate invocation" -> { graph with Edges = row :: graph.Edges }
            | "wrong callable" -> replaceRow (fun edge -> { edge with Sources = implementation :: List.tail edge.Sources })
            | "wrong code" -> replaceRow (fun edge -> { edge with Sources = edge.Sources[0] :: edge.Sources[0] :: List.skip 2 edge.Sources })
            | "different environment" ->
                let original = graph.Nodes[row.Sources[2]]
                let owner = graph.Codata.Value.KnownCallables[call.Callable.Occurrence].EnvironmentOwner
                let allocation = { original with Id = NodeId.fresh(); Kind = SemanticKind.EnvironmentAllocate owner; Children = [] }
                let originalCall = graph.Nodes[row.Target]
                let callee, arguments = match originalCall.Kind with SemanticKind.Application(callee, arguments) -> callee, arguments | _ -> failwith "Expected physical call"
                let arguments = allocation.Id :: List.tail arguments
                { graph with Nodes = graph.Nodes.Add(allocation.Id, allocation).Add(originalCall.Id,
                                             { originalCall with Kind = SemanticKind.Application(callee, arguments); Children = callee :: arguments }) }
            | "wrong ordered arguments" -> replaceRow (fun edge -> { edge with Sources = List.take 2 edge.Sources @ (List.skip 2 edge.Sources |> List.rev) })
            | "changed instantiation" ->
                let actual = call.Callable.ValuePath |> Seq.map (fun id -> graph.Nodes[id]) |> Seq.find (fun node -> node.Metadata.ContainsKey(SchemeMetadata.argument 0))
                let changed = { actual with Metadata = actual.Metadata.Remove(SchemeMetadata.argument 0) }
                { graph with Nodes = graph.Nodes.Add(actual.Id, changed) }
            | "extra writer" ->
                let access = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.ContinuationSlotAccess && call.Participants.Contains edge.Target && edge.Sources.Length > 4)
                let existing = graph.Nodes[access.Sources[4]]
                let writer = { existing with Id = NodeId.fresh() }
                { graph with Nodes = graph.Nodes.Add(writer.Id, writer) }
            | _ -> failwith "Unknown mutation"
        Assert.True((Instances.callReader changed call.Site implementation).IsNone, change)
        Assert.True((Instances.callReader graph call.Site implementation).IsSome)

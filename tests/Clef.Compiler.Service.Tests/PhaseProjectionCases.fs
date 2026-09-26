namespace Clef.Compiler.Service.Tests

open System.Text.Json
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Infrastructure
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private PhaseProjectionFixture =
    let graph () =
        let original = (DimensionalCases.check "[<EntryPoint>]\nlet main _ = 0").Graph
        let template = original.Nodes.Values |> Seq.head
        let nodes = [1 .. 8] |> List.map (fun id ->
            let id = NodeId id
            id, { template with Id = id; Kind = SemanticKind.Literal NativeLiteral.Unit
                                Type = Types.unitType; IsReachable = id = NodeId 1
                                Children = if id = NodeId 1 then [NodeId 6] else []
                                Parent = if id = NodeId 1 then Some(NodeId 8) else None }) |> Map.ofList
        let edge cls role sources target =
            { Class = cls; Role = role; Sources = List.map NodeId sources; Target = NodeId target; Ordinal = 0 }
        { original with Nodes = nodes; DeclarationRoots = [NodeId 1, DeclRoot.EntryPoint]
                        Edges = [edge EdgeClass.Provenance EdgeRole.EnrichedWith [2] 1
                                 edge EdgeClass.Range EdgeRole.EnrichedWith [3] 2
                                 edge EdgeClass.Obligation EdgeRole.EnrichedWith [3; 99] 7
                                 edge EdgeClass.Provenance EdgeRole.EnrichedWith [5] 4
                                 edge EdgeClass.Reference EdgeRole.Definition [6] 1] }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "PhaseProjection")>]
type PhaseProjectionCases() =
    [<Fact>]
    member _.``Pruned artifacts retain transitive joint evidence without changing reachability`` () =
        let graph = PhaseProjectionFixture.graph ()
        let view = PhaseEmitter.selectGraphView PhaseConfig.GraphArtifactMode.Pruned graph
        Assert.Equal<NodeId list>([1; 2; 3; 7] |> List.map NodeId, view.Nodes.Keys |> Seq.toList)
        Assert.Equal(3, view.Metadata.RetainedUnreachableNodeCount)
        Assert.Equal(4, view.Edges.Length)
        Assert.Equal<int list>([99], view.Metadata.MissingNodeIds)
        for id in [2; 3; 7] do Assert.False(view.Nodes[NodeId id].IsReachable)
        Assert.Equal(8, graph.Nodes.Count)
        Assert.Equal(5, graph.Edges.Length)
        for node in view.Nodes.Values do Assert.Same(graph.Nodes[node.Id], node)
        let full = PhaseEmitter.selectGraphView PhaseConfig.GraphArtifactMode.Full graph
        Assert.Same(graph.Nodes, full.Nodes)
        Assert.Same(graph.Edges, full.Edges)
        Assert.Equal("full", full.Metadata.Mode)

    [<Fact>]
    member _.``Diagnostic boundary references retain original incidence and are listed explicitly`` () =
        let graph = PhaseProjectionFixture.graph ()
        let view = PhaseEmitter.selectGraphView PhaseConfig.GraphArtifactMode.Pruned graph
        Assert.Equal<int list>([6; 8], view.Metadata.ExternalNodeIds)
        Assert.Equal<NodeId list>([NodeId 6], view.Nodes[NodeId 1].Children)
        Assert.Equal(Some(NodeId 8), view.Nodes[NodeId 1].Parent)
        Assert.Contains(view.Edges, fun edge -> edge.Class = EdgeClass.Reference && edge.Sources = [NodeId 6])
        Assert.Equal(8, view.Metadata.SourceNodeCount)
        Assert.Equal(4, view.Metadata.EmittedNodeCount)

    [<Fact>]
    member _.``References carried by a semantic kind remain visible at the diagnostic boundary`` () =
        let graph = PhaseProjectionFixture.graph ()
        let referenced = { graph.Nodes[NodeId 1] with Kind = SemanticKind.VarRef("external", Some(NodeId 5)) }
        let graph = { graph with Nodes = graph.Nodes.Add(referenced.Id, referenced) }
        let view = PhaseEmitter.selectGraphView PhaseConfig.GraphArtifactMode.Pruned graph
        Assert.Equal<int list>([5; 6; 8], view.Metadata.ExternalNodeIds)
        Assert.Equal(SemanticKind.VarRef("external", Some(NodeId 5)), view.Nodes[referenced.Id].Kind)
        Assert.False(view.Nodes.ContainsKey(NodeId 5))

    [<Fact>]
    member _.``Changing a joint relation retracts its diagnostic participant closure`` () =
        let graph = PhaseProjectionFixture.graph ()
        let changed = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Class <> EdgeClass.Range) }
        let view = PhaseEmitter.selectGraphView PhaseConfig.GraphArtifactMode.Pruned changed
        Assert.Equal<NodeId list>([NodeId 1; NodeId 2], view.Nodes.Keys |> Seq.toList)
        Assert.Empty view.Metadata.MissingNodeIds
        let empty = { graph with DeclarationRoots = []; Nodes = graph.Nodes |> Map.map (fun _ node -> { node with IsReachable = false }) }
        let view = PhaseEmitter.selectGraphView PhaseConfig.GraphArtifactMode.Pruned empty
        Assert.Empty view.Nodes
        Assert.Empty view.Edges

    [<Fact>]
    member _.``Serialized projection distinguishes full graph counts from emitted view and resets to full`` () =
        let previous = PhaseConfig.getConfig ()
        try
            PhaseConfig.enablePrunedGraphArtifacts ()
            PhaseConfig.enableArtifacts "unused" [5]
            Assert.Equal(PhaseConfig.GraphArtifactMode.Pruned, (PhaseConfig.getConfig()).GraphMode)
            let graph = PhaseProjectionFixture.graph ()
            let view = PhaseEmitter.selectGraphView (PhaseConfig.getConfig()).GraphMode graph
            let output : PhaseTypes.PhaseOutput = {
                Summary = PhaseTypes.createSummaryWithReachability PhaseTypes.PhaseId.Final 8 1 1 0L
                View = view.Metadata
                Nodes = view.Nodes.Values |> Seq.map (fun node ->
                    PhaseEmitter.createNodeOutput (NodeId.value node.Id) "Literal" "unit" node.IsReachable
                        (List.map NodeId.value node.Children) (Option.map NodeId.value node.Parent)) |> Seq.toList
                Edges = view.Edges |> List.map (fun edge ->
                    { PhaseTypes.PhaseEdgeOutput.Sources = edge.Sources |> List.map NodeId.value
                      Target = NodeId.value edge.Target; Class = string edge.Class
                      Role = string edge.Role; Ordinal = edge.Ordinal })
                EntryPoints = [1]; Diagnostics = [] }
            use json = JsonDocument.Parse(PhaseEmitter.serializePhaseOutput output)
            Assert.Equal(8, json.RootElement.GetProperty("summary").GetProperty("nodeCount").GetInt32())
            Assert.Equal(4, json.RootElement.GetProperty("nodes").GetArrayLength())
            let metadata = json.RootElement.GetProperty("view")
            Assert.Equal("pruned-with-evidence", metadata.GetProperty("mode").GetString())
            Assert.Equal(2, metadata.GetProperty("externalNodeIds").GetArrayLength())
            let missing = metadata.GetProperty("missingNodeIds")
            Assert.Equal(99, missing[0].GetInt32())
            PhaseConfig.disableEmission ()
            PhaseConfig.enableArtifacts "unused" [5]
            Assert.Equal(PhaseConfig.GraphArtifactMode.Full, (PhaseConfig.getConfig()).GraphMode)
        finally PhaseConfig.setConfig previous

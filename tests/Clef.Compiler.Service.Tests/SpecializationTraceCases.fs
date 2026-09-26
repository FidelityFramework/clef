namespace Clef.Compiler.Service.Tests

open System.Text.Json
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.Infrastructure
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.Nanopass.Recipe
module TraceMono = Clef.Compiler.Nanopass.Monomorphization
module TraceFold = Clef.Compiler.Nanopass.FoldIn

module private SpecializationTraceFixture =
    let create () =
        let builder = NodeBuilder()
        let range = { File = "specialization-trace.clef"; Start = { Line = 1; Column = 0 }; End = { Line = 1; Column = 25 } }
        let valueParameter = freshTypeParam "'value" TypeParamKind.Type range
        let measureParameter = freshMeasureVar None |> measureCellOf
        let valueType = NativeType.TVar valueParameter
        let measured dimension = NativeType.TNum(CarrierRef.Carrier Types.intTyCon, dimension)
        let measureType = measured (Dimension.ofVar (measureVarOf measureParameter))
        let signature value measure = NativeType.TFun(value, NativeType.TFun(measure, value))
        let formal = builder.Create(SemanticKind.PatternBinding "value", valueType, range)
        let scale = builder.Create(SemanticKind.PatternBinding "scale", measureType, range)
        let read = builder.Create(SemanticKind.VarRef("value", Some formal.Id), valueType, range)
        let code = builder.Create(SemanticKind.Lambda(["value", valueType, formal.Id; "scale", measureType, scale.Id], read.Id, [], Some "keep", LambdaContext.RegularClosure), signature valueType measureType, range, children = [formal.Id; scale.Id; read.Id])
        let declaration = builder.Create(SemanticKind.Binding("keep", false, false, None), NativeType.TForall([valueParameter; measureParameter], signature valueType measureType), range, children = [code.Id])
        let requests = [Types.boolType, DimensionalCases.metre; Types.boolType, DimensionalCases.second; Types.intType, DimensionalCases.metre]
                       |> List.map (fun (value, dimension) -> builder.Create(SemanticKind.VarRef("keep", Some declaration.Id), signature value (measured dimension), range))
        let root = builder.Create(SemanticKind.ModuleDef("Trace", [declaration.Id] @ List.map _.Id requests), Types.unitType, range)
        let original = builder.Build []
        let result = TraceMono.runWithEvidence original.Nodes
        let graph = { original with Nodes = result.Nodes; Edges = result.Derivations; DeclarationRoots = [root.Id, DeclRoot.EntryPoint] }
        original, graph, declaration.Id, code.Id, requests

    let traces (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose PhaseEmitter.specializationSnapshot |> Seq.toList

    let replace (graph: SemanticGraph) original =
        let before = graph.Nodes[original]
        let replacement = { before with Id = NodeId.fresh(); Kind = SemanticKind.Literal NativeLiteral.Unit
                                        Type = Types.unitType; Children = []; Parent = None; Metadata = Map.empty }
        let recipe = { OriginalNodeId = original; NewNodes = [replacement]; NewEdges = []
                       ReplacementRootId = replacement.Id; ElaborationKind = "Baker"; ElaborationSource = "trace-followup" }
        TraceFold.foldIn (RecipeSet.fromList "Saturation" [recipe]) graph, replacement.Id

    let serialize mode (graph: SemanticGraph) =
        let view = PhaseEmitter.selectGraphView mode graph
        let output : PhaseTypes.PhaseOutput = {
            Summary = PhaseTypes.createSummaryWithReachability PhaseTypes.PhaseId.Final graph.Nodes.Count (graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.length) graph.DeclarationRoots.Length 0L
            View = view.Metadata
            Nodes = view.Nodes.Values |> Seq.map (fun node ->
                { PhaseEmitter.createNodeOutput (NodeId.value node.Id) (sprintf "%A" node.Kind) (formatType node.Type) node.IsReachable (node.Children |> List.map NodeId.value) (node.Parent |> Option.map NodeId.value) with
                    Specialization = PhaseEmitter.specializationSnapshot node }) |> Seq.toList
            Edges = view.Edges |> List.map (fun edge ->
                { PhaseTypes.PhaseEdgeOutput.Sources = List.map NodeId.value edge.Sources
                  Target = NodeId.value edge.Target; Class = string edge.Class; Role = string edge.Role; Ordinal = edge.Ordinal })
            EntryPoints = graph.DeclarationRoots |> List.map (fst >> NodeId.value); Diagnostics = [] }
        PhaseEmitter.serializePhaseOutput output

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SpecializationTrace")>]
type SpecializationTraceCases() =
    [<Fact>]
    member _.``Applied specialization records exact source clone and actual requests without pretending shared measures are concrete``() =
        let original, graph, declaration, _, requests = SpecializationTraceFixture.create ()
        Assert.True(original.Nodes[declaration].IsReachable)
        Assert.False(graph.Nodes[declaration].IsReachable)
        let traces = SpecializationTraceFixture.traces graph
        let declarations = traces |> List.filter (fun trace -> trace.SourceNode = declaration)
        Assert.Equal(2, declarations.Length)
        let shared = declarations |> List.find (fun trace -> trace.Requests.Length = 2)
        Assert.Equal<string list>(["Type"; "Measure"], shared.Parameters |> List.map snd)
        Assert.Equal(2, shared.CodeArguments.Length)
        Assert.Equal<NodeId list>(requests |> List.take 2 |> List.map _.Id, shared.Requests |> List.map fst)
        Assert.NotEqual(snd shared.Requests[0], snd shared.Requests[1])
        Assert.Equal(shared.Input.Type, formatType original.Nodes[declaration].Type)
        for trace in traces do
            Assert.Equal(formatType graph.Nodes[trace.CloneNode].Type, trace.Output.Type)
            Assert.Contains(graph.Edges, fun edge ->
                edge.Role = EdgeRole.SchemeSpecialization && edge.Target = trace.CloneNode &&
                edge.Sources = [trace.SourceDeclaration; trace.SourceNode; trace.CloneDeclaration; trace.CloneNode] @ List.map fst trace.Requests)

    [<Fact>]
    member _.``Later fold-in keeps frozen origins and remaps only current derivation targets``() =
        let _, graph, declaration, code, requests = SpecializationTraceFixture.create ()
        let trace = SpecializationTraceFixture.traces graph |> List.find (fun trace -> trace.SourceNode = code)
        let before = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.SchemeSpecialization && edge.Target = trace.CloneNode)
        let afterClone, replacement = SpecializationTraceFixture.replace graph trace.CloneNode
        let afterSource, sourceReplacement = SpecializationTraceFixture.replace afterClone declaration
        let after, requestReplacement = SpecializationTraceFixture.replace afterSource requests.Head.Id
        let row = after.Edges |> List.find (fun edge -> edge.Role = EdgeRole.SchemeSpecialization && edge.Target = replacement)
        Assert.Equal<NodeId list>(before.Sources, row.Sources)
        Assert.DoesNotContain(sourceReplacement, row.Sources)
        Assert.DoesNotContain(requestReplacement, row.Sources)
        Assert.False(after.Nodes[requests.Head.Id].IsReachable)
        Assert.False(after.Nodes[trace.CloneNode].IsReachable)
        Assert.False(after.Nodes[declaration].IsReachable)
        Assert.Equal(Some trace, PhaseEmitter.specializationSnapshot after.Nodes[trace.CloneNode])
        Assert.Equal(graph.DeclarationRoots, after.DeclarationRoots)
        Assert.DoesNotContain(after.DeclarationRoots, fun (id, _) -> id = declaration || id = trace.CloneNode)

    [<Fact>]
    member _.``In-place fold-in preserves snapshot while current type and structure change``() =
        let _, graph, _, code, _ = SpecializationTraceFixture.create ()
        let trace = SpecializationTraceFixture.traces graph |> List.find (fun trace -> trace.SourceNode = code)
        let changed = { graph.Nodes[trace.CloneNode] with Kind = SemanticKind.Literal NativeLiteral.Unit; Type = Types.unitType; Children = []; Metadata = Map.empty }
        let recipe = { OriginalNodeId = changed.Id; NewNodes = [changed]; NewEdges = []; ReplacementRootId = changed.Id
                       ElaborationKind = "Baker"; ElaborationSource = "in-place-trace-control" }
        let after = TraceFold.foldIn (RecipeSet.fromList "Saturation" [recipe]) graph
        Assert.Equal(Types.unitType, after.Nodes[changed.Id].Type)
        Assert.Equal(Some trace, PhaseEmitter.specializationSnapshot after.Nodes[changed.Id])
        Assert.NotEqual(formatType after.Nodes[changed.Id].Type, trace.Output.Type)

    [<Fact>]
    member _.``Retired historical parents cannot overwrite a current reused child's occurrence parent``() =
        // A different fan-out branch can reserve its replacement first. Map
        // order must not let the later-numbered historical parent win.
        let replacementId = NodeId.fresh()
        let _, graph, _, code, _ = SpecializationTraceFixture.create ()
        let trace = SpecializationTraceFixture.traces graph |> List.find (fun trace -> trace.SourceNode = code)
        let original = graph.Nodes[trace.CloneNode]
        let child = original.Children |> List.last
        let replacement = { original with Id = replacementId; Kind = SemanticKind.Sequential [child]; Children = [child]
                                          Metadata = Map.empty; IsReachable = false }
        let recipe = { OriginalNodeId = original.Id; NewNodes = [replacement]; NewEdges = []; ReplacementRootId = replacementId
                       ElaborationKind = "Baker"; ElaborationSource = "reused-current-child" }
        let after = TraceFold.foldIn (RecipeSet.fromList "Saturation" [recipe]) graph
        Assert.Equal(Some replacementId, after.Nodes[child].Parent)
        Assert.Equal(Some trace, PhaseEmitter.specializationSnapshot after.Nodes[original.Id])
        // The same remains true at the next fold-in; a library declaration's
        // false reachability did not remove its current structural authority.
        let again = TraceFold.foldIn (RecipeSet.empty "Saturation") after
        Assert.Equal(Some replacementId, again.Nodes[child].Parent)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Full and pruned artifacts serialize original snapshots after an actual fold-in``(pruned: bool) =
        let _, graph, declaration, code, _ = SpecializationTraceFixture.create ()
        let trace = SpecializationTraceFixture.traces graph |> List.find (fun trace -> trace.SourceNode = code)
        let after, replacement = SpecializationTraceFixture.replace graph trace.CloneNode
        let mode = if pruned then PhaseConfig.GraphArtifactMode.Pruned else PhaseConfig.GraphArtifactMode.Full
        use json = JsonDocument.Parse(SpecializationTraceFixture.serialize mode after)
        let nodes = json.RootElement.GetProperty("nodes").EnumerateArray() |> Seq.toList
        let retired = nodes |> List.find (fun node -> node.GetProperty("id").GetInt32() = NodeId.value trace.CloneNode)
        Assert.False(retired.GetProperty("isReachable").GetBoolean())
        let tape = retired.GetProperty("specialization")
        Assert.Equal(NodeId.value declaration, tape.GetProperty("sourceDeclaration").GetInt32())
        Assert.Equal(trace.Input.Type, tape.GetProperty("input").GetProperty("type").GetString())
        Assert.True(tape.GetProperty("retiresSource").GetBoolean())
        Assert.Equal(trace.Output.Type, tape.GetProperty("output").GetProperty("type").GetString())
        Assert.Equal(trace.Requests.Length, tape.GetProperty("requests").GetArrayLength())
        Assert.Equal(2, tape.GetProperty("codeArguments").GetArrayLength())
        Assert.Contains(json.RootElement.GetProperty("edges").EnumerateArray(), fun row ->
            row.GetProperty("role").GetString() = "SchemeSpecialization" && row.GetProperty("target").GetInt32() = NodeId.value replacement)
        Assert.Equal(0, json.RootElement.GetProperty("view").GetProperty("missingNodeIds").GetArrayLength())

    [<Fact>]
    member _.``Copied metadata does not manufacture another specialization event``() =
        let _, graph, _, _, _ = SpecializationTraceFixture.create ()
        let trace = SpecializationTraceFixture.traces graph |> List.head
        let copy = { graph.Nodes[trace.CloneNode] with Id = NodeId.fresh() }
        Assert.True(PhaseEmitter.specializationSnapshot copy |> Option.isNone)

    [<Fact>]
    member _.``Historical evidence cannot activate a graph with no executable roots``() =
        let _, graph, _, _, _ = SpecializationTraceFixture.create ()
        let retired = { graph with DeclarationRoots = []; Nodes = graph.Nodes |> Map.map (fun _ node -> { node with IsReachable = false }) }
        let view = PhaseEmitter.selectGraphView PhaseConfig.GraphArtifactMode.Pruned retired
        Assert.Empty view.Nodes
        Assert.Empty view.Edges
        Assert.NotEmpty retired.Edges
        Assert.True(graph.Nodes.Values |> Seq.exists _.IsReachable)

    [<Fact>]
    member _.``Real recursive source seeds specialization correspondence in initial graph and preserves it through Baker``() =
        let result = DimensionalCases.check "let rec keep n value = if n = 0 then value else keep (n - 1) value\n[<EntryPoint>]\nlet main _ = if keep 2 true then keep 1 7 else 0"
        DimensionalCases.noErrors result
        let graph = result.Graph
        let traces = SpecializationTraceFixture.traces graph
        Assert.NotEmpty traces
        for trace in traces do
            Assert.True(graph.Nodes.ContainsKey trace.SourceNode)
            Assert.True(graph.Nodes.ContainsKey trace.SourceDeclaration)
            Assert.Contains(graph.Edges, fun edge ->
                edge.Role = EdgeRole.SchemeSpecialization && List.contains trace.CloneNode edge.Sources && graph.Nodes.ContainsKey edge.Target)
        Assert.DoesNotContain(graph.DeclarationRoots, fun (id, _) -> traces |> List.exists (fun trace -> trace.SourceDeclaration = id))

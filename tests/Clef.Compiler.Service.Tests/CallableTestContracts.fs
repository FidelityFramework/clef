namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module TestEnvironments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

/// Shared semantic assertions for source callables before and after canonical
/// code/environment materialization. No generated symbol is identity evidence.
module CallableTestContracts =
    let implementation graph = TestEnvironments.tryImplementation graph
    let known graph = TestEnvironments.tryKnown graph
    let sourceDeclaration graph = TestEnvironments.trySourceDeclaration graph

    let shape (graph: SemanticGraph) occurrence =
        let implementation = TestEnvironments.tryImplementation graph occurrence |> Option.get
        let code = graph.Nodes[implementation]
        match code.Kind with
        | SemanticKind.Lambda (parameters, body, captures, _, _) ->
            match TestEnvironments.tryKnown graph occurrence with
            | Some carrier ->
                Assert.Equal(code.Id, carrier.Implementation)
                Assert.Empty captures
                let owner = graph.Nodes[carrier.EnvironmentOwner]
                Assert.Equal(Some (MetadataValue.Type owner.Type), code.Metadata.TryFind ClosureMetadata.SourceSignature)
                let relation = graph.Edges |> List.filter (fun edge ->
                    edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.EnvironmentFormal &&
                    edge.Sources = [owner.Id; implementation]) |> Assert.Single
                let _, ty, formal = List.head parameters
                Assert.Equal(relation.Target, formal)
                DimensionalCases.same TestEnvironments.environmentType ty
                Assert.Equal(Some owner.Id, TestEnvironments.tryEnvironmentOwner graph formal)
                TestEnvironments.capturedInitializers graph owner.Id |> Option.get |> ignore
                code, List.tail parameters, body, TestEnvironments.captures graph owner.Id
            | None -> code, parameters, body, captures
        | kind -> failwithf "Callable lost its actual implementation: %A" kind

    let sourceDefinition (graph: SemanticGraph) occurrence =
        match TestEnvironments.trySourceDeclaration graph occurrence with
        | Some declaration -> declaration
        | None ->
            match graph.Nodes[occurrence].Kind with
            | SemanticKind.VarRef (_, Some declaration) -> declaration
            | kind -> failwithf "Expected an exact source reference: %A" kind

    let referenceTo (graph: SemanticGraph) expected occurrence =
        match graph.Nodes[occurrence].Kind with
        | SemanticKind.VarRef _ -> Assert.Equal(expected, sourceDefinition graph occurrence)
        | SemanticKind.EnvironmentRead (environment, slot) ->
            Assert.Equal(expected, slot)
            Assert.Equal(Some expected, TestEnvironments.tryCapturedValue graph environment slot)
        | kind -> failwithf "Expected a read of source declaration %A: %A" expected kind

    let captures (graph: SemanticGraph) (node: SemanticNode) =
        match node.Kind with
        | SemanticKind.Lambda (_, _, captures, _, _) -> captures
        | SemanticKind.ClosureValue _ ->
            TestEnvironments.capturedInitializers graph node.Id |> Option.get |> ignore
            TestEnvironments.captures graph node.Id
        | _ -> []

    let assertMutableCapture (graph: SemanticGraph) source =
        Assert.Contains(graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Lambda (_, _, captures, _, _) ->
                captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some source)
            | SemanticKind.ClosureValue _ ->
                TestEnvironments.capturedInitializers graph node.Id
                |> Option.exists (List.contains (source, source, true))
            | _ -> false)

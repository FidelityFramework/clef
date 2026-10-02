namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Infrastructure
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module LazyCallablePublication = Clef.Compiler.PSGSaturation.Publication.RevisionPublication
module LazyCallableEmission = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission
module LazyCallableStorage = Clef.Compiler.PSGSaturation.SemanticGraph.StorageWitness
module LazyCallableDeclarations = Clef.Compiler.PSGSaturation.SemanticGraph.CallableEmission

module private LazyCallableFixture =
    let check () =
        let source =
            [ "module GenericLazyPublication"
              "let make value = lazy value"
              "[<EntryPoint>]"
              "let main _ ="
              "    let first = make true"
              "    let second = make false"
              "    if Lazy.force first && not (Lazy.force second) then 0 else 1" ]
            |> String.concat "\n"
        LazyResidenceFixture.programWith (Some source)

    let publish (graph: SemanticGraph) =
        match LazyCallablePublication.publish graph with
        | Ok revision -> revision
        | Error failures -> failwithf "Expected source publication: %A" failures

    let publicId id = Fidelity.PSG.NodeId (NodeId.value id)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LazyCallablePublication")>]
type LazyCallablePublicationCases() =
    [<Fact>]
    member _.``Generic lazy history remains source resident without entering the live revision`` () =
        let graph = LazyCallableFixture.check ()
        let original =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.LazyExpr _ -> true | _ -> false)
            |> Assert.Single
        let thunkId =
            match original.Kind with
            | SemanticKind.LazyExpr(thunk, _) -> thunk
            | _ -> failwith "Expected the retained generic source formation."
        let thunk = graph.Nodes[thunkId]
        let formalId, bodyId =
            match thunk.Kind with
            | SemanticKind.Lambda([_, _, formal], body, _, _, LambdaContext.LazyThunk) -> formal, body
            | other -> failwithf "Expected the retained logical lazy thunk: %A" other
        for id in [original.Id; thunkId; formalId; bodyId] do
            Assert.True(graph.Nodes.ContainsKey id)
            Assert.False(graph.Nodes[id].IsReachable)
        Assert.Equal(Some original.Id, thunk.Parent)
        Assert.Equal(Some thunkId, graph.Nodes[formalId].Parent)
        Assert.Equal<NodeId list>([formalId; bodyId], thunk.Children)
        Assert.False(graph.Codata.Value.LazyLayouts.ContainsKey original.Id)

        let clone, trace =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                PhaseEmitter.specializationSnapshot node
                |> Option.filter (fun trace -> trace.SourceNode = thunkId)
                |> Option.map (fun trace -> node, trace))
            |> Assert.Single
        Assert.True(clone.IsReachable)
        Assert.Equal(thunkId, trace.SourceNode)
        Assert.Equal(clone.Id, trace.CloneNode)
        Assert.Equal<NodeId list>(thunk.Children, trace.Input.Children)
        Assert.Equal(thunk.Parent, trace.Input.Parent)
        Assert.True(graph.Nodes.ContainsKey trace.SourceDeclaration)
        Assert.False(graph.Nodes[trace.SourceDeclaration].IsReachable)
        match graph.Nodes[trace.SourceDeclaration].Type with
        | NativeType.TForall(parameters, _) -> Assert.NotEmpty parameters
        | other -> failwithf "Expected the retained generic source declaration: %A" other
        Assert.Contains(graph.Edges, fun edge ->
            edge.Role = EdgeRole.SchemeSpecialization && edge.Target = clone.Id &&
            List.contains thunkId edge.Sources)

        let revision = LazyCallableFixture.publish graph
        for id in [original.Id; thunkId; formalId; bodyId; trace.SourceDeclaration] do
            Assert.False(revision.Nodes.ContainsKey (LazyCallableFixture.publicId id))
        Assert.Empty revision.Edges
        Assert.True(revision.Nodes[LazyCallableFixture.publicId clone.Id].IsReachable)

        let declarations =
            revision.Emission.Callable.Declarations.Values
            |> Seq.filter (fun declaration -> declaration.Context = Fidelity.PSG.LambdaContext.LazyThunk)
            |> Seq.map _.Implementation |> Set.ofSeq
        let laidOut =
            revision.Emission.Storage.Lazies.Values |> Seq.map (fun contract -> contract.Layout.Thunk) |> Set.ofSeq
        Assert.NotEmpty declarations
        Assert.DoesNotContain(LazyCallableFixture.publicId thunkId, declarations)
        Assert.Contains(LazyCallableFixture.publicId clone.Id, declarations)
        Assert.Equal<Set<Fidelity.PSG.NodeId>>(laidOut, declarations)
        for id in declarations do Assert.True(revision.Nodes[id].IsReachable)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Fact>]
    member _.``A live lazy with missing layout is refused by its source storage owner`` () =
        let graph = LazyCallableFixture.check ()
        let layout = graph.Codata.Value.LazyLayouts.Values |> Assert.Single
        Assert.True(graph.Nodes[layout.Owner].IsReachable)
        Assert.True(graph.Nodes[layout.Thunk].IsReachable)
        let changed =
            { graph with
                Codata = lazy { graph.Codata.Value with LazyLayouts = graph.Codata.Value.LazyLayouts.Remove layout.Owner } }
        match LazyCallableDeclarations.project changed with
        | Ok _ -> failwith "A live lazy thunk declaration was admitted without its storage layout."
        | Error failures ->
            Assert.Contains(failures, fun failure ->
                failure.Occurrence = Some layout.Thunk &&
                failure.Reason = "Live lazy thunk declaration has no current validated storage layout.")
        match LazyCallableStorage.project changed with
        | Ok _ -> failwith "A current live lazy was admitted without its storage layout."
        | Error failures ->
            Assert.Contains(failures, fun failure ->
                failure.Occurrence = Some layout.Owner &&
                failure.Reason = "Lazy source instance has no published storage layout.")
        match LazyCallableEmission.prepare changed with
        | Ok _ -> failwith "Source witness preparation accepted the missing live lazy layout."
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Occurrence = Some layout.Owner)

    [<Fact>]
    member _.``Live ordinary closure implementations keep their callable declarations`` () =
        let graph = CallableEmissionFixture.checkedProgram ()
        let projection = CallableEmissionFixture.project graph
        let implementations =
            projection.Carriers.Values |> Seq.map _.Implementation |> Set.ofSeq
            |> Set.filter (fun id -> graph.Nodes[id].IsReachable)
        Assert.NotEmpty implementations
        for implementation in implementations do
            let declaration = projection.Declarations[implementation]
            Assert.Equal(implementation, declaration.Implementation)
            match graph.Nodes[implementation].Kind with
            | SemanticKind.Lambda(parameters, body, captures, _, context) ->
                Assert.NotEqual(LambdaContext.LazyThunk, context)
                Assert.Equal<NodeId list>(parameters |> List.map (fun (_, _, id) -> id), declaration.Parameters |> List.map (fun (_, _, id) -> id))
                Assert.Equal(body, declaration.Result)
                Assert.Equal<CaptureInfo list>(captures, declaration.Captures)
            | other -> failwithf "Expected settled closure implementation: %A" other

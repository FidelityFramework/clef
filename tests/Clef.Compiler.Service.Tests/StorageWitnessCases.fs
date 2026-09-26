namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module StorageProjection = Clef.Compiler.PSGSaturation.SemanticGraph.StorageWitness
module PublishedWitness = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "StorageWitness")>]
type StorageWitnessCases() =
    [<Fact>]
    member _.``Publication retains actual lazy program instances startup and writable inventory``() =
        let graph = LazyResidenceFixture.programWith None
        let projection =
            match PublishedWitness.tryStorage graph with
            | Result.Ok projection -> projection
            | Result.Error reason -> failwith reason
        Assert.NotEmpty projection.Lazies
        Assert.NotEmpty projection.LazyPrograms
        Assert.True projection.Startup.IsSome
        Assert.NotEmpty projection.SlotAuthorities
        Assert.Equal<ProgramStorageInventory>(graph.Codata.Value.ProgramStorage, projection.ProgramStorage)
        for KeyValue(binding, actual) in projection.LazyPrograms do
            Assert.Equal(Some(actual.Owner, actual.Allocation), Clef.Compiler.Nanopass.LazyRuntime.programInstance graph binding)
            Assert.Equal(Some EscapeKind.StaticLifetime, graph.Codata.Value.Escapes.TryFind actual.Allocation)

    [<Fact>]
    member _.``Copied storage projection supplies no publication authority``() =
        let graph = LazyResidenceFixture.programWith None
        let copied = { graph with Codata = lazy graph.Codata.Value }
        Assert.True(PublishedWitness.tryStorage graph |> Result.isOk)
        Assert.True(PublishedWitness.tryStorage copied |> Result.isError)
        // Source re-publication may validate the copy; the passive getter
        // cannot perform that work or repair authority as a side effect.
        Assert.True(StorageProjection.project copied |> Result.isOk)
        Assert.True(PublishedWitness.tryStorage copied |> Result.isError)

    [<Theory>]
    [<InlineData("layout")>]
    [<InlineData("duplicate-layout")>]
    [<InlineData("origin")>]
    [<InlineData("startup")>]
    member _.``Stale lazy and startup authority is a located source publication error`` defect =
        let graph = LazyResidenceFixture.programWith None
        let owner, layout = graph.Codata.Value.LazyLayouts |> Map.toList |> List.head
        let revised =
            match defect with
            | "layout" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.LazyLayout || edge.Target <> owner) }
            | "duplicate-layout" ->
                let row = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.LazyLayout && edge.Target = owner)
                { graph with Edges = row :: graph.Edges }
            | "origin" ->
                let origins = graph.Codata.Value.LazyOrigins.Add(layout.Formal, NodeId.fresh())
                { graph with Codata = lazy { graph.Codata.Value with LazyOrigins = origins } }
            | _ -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramEntryCall) }
        match StorageProjection.project revised with
        | Result.Ok _ -> failwith "Stale source storage was admitted"
        | Result.Error failures ->
            Assert.NotEmpty failures
            Assert.Contains(failures, fun failure -> failure.Occurrence.IsSome && not failure.Participants.IsEmpty)
        Assert.True(PublishedWitness.tryStorage revised |> Result.isError)

    [<Fact>]
    member _.``Sequence projection preserves exact family copies and program template identities``() =
        let graph = SequenceProgramFixture.direct ()
        let projection =
            match PublishedWitness.tryStorage graph with
            | Result.Ok projection -> projection
            | Result.Error reason -> failwith reason
        Assert.NotEmpty projection.Sequences
        Assert.Equal<Map<NodeId, SequenceTemplateCopy>>(graph.Codata.Value.SequenceTemplateCopies, projection.SequenceCopies)
        let first = SequenceProgramFixture.binding "first" graph
        let alias = SequenceProgramFixture.binding "alias" graph
        let second = SequenceProgramFixture.binding "second" graph
        Assert.Equal(projection.SequencePrograms[first.Id].Allocation, projection.SequencePrograms[alias.Id].Allocation)
        Assert.NotEqual(projection.SequencePrograms[first.Id].Allocation, projection.SequencePrograms[second.Id].Allocation)

    [<Fact>]
    member _.``Changed sequence family proof fails source publication with its occurrence``() =
        let graph = SequenceProgramFixture.direct ()
        let row = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.SequenceFamilyLayout)
        let revised = { graph with Edges = row :: graph.Edges }
        match StorageProjection.project revised with
        | Result.Ok _ -> failwith "Duplicate sequence family proof was admitted"
        | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Occurrence.IsSome)

    [<Fact>]
    member _.``Requirement projection retains its exact ordered continuation and refuses changed premise``() =
        let source = """module RequirementPublication
let check (value: bool) =
    match value with
    | true -> 1
[<EntryPoint>]
let main _ = check true
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let projection =
            match PublishedWitness.tryStorage graph with
            | Result.Ok projection -> projection
            | Result.Error reason -> failwith reason
        let site, requirement = Assert.Single(projection.Requirements |> Map.toList)
        let sourceContract =
            Clef.Compiler.PSGSaturation.SemanticGraph.Requirements.tryRequirement graph site
            |> Option.defaultWith (fun () -> failwith "The source requirement is absent")
        Assert.Equal<NodeId list>(
            [sourceContract.Site; sourceContract.Condition; sourceContract.Frontier; sourceContract.Continuation],
            [requirement.Site; requirement.Condition; requirement.Frontier; requirement.Continuation])
        Assert.Equal(sourceContract.Diagnostic, requirement.Diagnostic)
        Assert.Equal<NodeId list>(sourceContract.Participants, requirement.Participants)
        Assert.Equal(sourceContract.PatternTest, requirement.PatternTest)
        // Baker's general ordered requirement has no specialized terminal
        // pattern row. Publication must preserve that distinction exactly.
        Assert.True requirement.PatternTest.IsNone
        Assert.False(projection.PatternRequirements.ContainsKey requirement.Continuation)
        match graph.Nodes[requirement.Frontier].Kind with
        | SemanticKind.Sequential nodes -> Assert.Equal<NodeId list>([site; requirement.Continuation], nodes)
        | _ -> failwith "The source requirement lost its ordered frontier"
        let node = graph.Nodes[requirement.Condition]
        let revised = { graph with Nodes = graph.Nodes.Add(node.Id, { node with Type = Types.unitType }) }
        match StorageProjection.project revised with
        | Result.Ok _ -> failwith "Changed requirement premise was admitted"
        | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Occurrence = Some site)

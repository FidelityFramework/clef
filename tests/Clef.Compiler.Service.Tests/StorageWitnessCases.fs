namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module StorageProjection = Clef.Compiler.PSGSaturation.SemanticGraph.StorageWitness
module PublishedWitness = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission
module NumericProjection = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication

module private PoolInventoryFixture =
    let source = """module PoolInventory
let consume (left: string) (right: string) = if left = right then 1 else 0
[<EntryPoint>]
let main _ = consume "first" "second" + consume "first" "first"
"""
    let graph () = LazyResidenceFixture.programWith (Some source)

    let literal (graph: SemanticGraph) =
        graph.StaticStringPool.Value.Entries
        |> List.find (fun entry -> entry.Content = "first")
        |> _.NodeIds |> List.head

    let anchorNames (node: SemanticNode) =
        match node.Metadata.TryFind ObligationMetadata.Anchors with
        | Some(MetadataValue.StringList names) -> names
        | other -> failwithf "Source participant has no anchor inventory: %A" other

    let currentAnchors (graph: SemanticGraph) id =
        graph.Edges |> List.choose (fun edge ->
            if edge.Class <> EdgeClass.Obligation || not (List.contains id edge.Sources) then None
            else
                match graph.Nodes.TryFind edge.Target with
                | Some { Kind = SemanticKind.Obligation info } -> Some info.Id
                | _ -> failwith "Current source incidence targets an absent claim") |> Set.ofList

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "StorageWitness")>]
type StorageWitnessCases() =
    [<Theory>]
    [<InlineData("source")>]
    [<InlineData("target")>]
    member _.``An owning obligation recipe refuses an absent source or target rather than dropping its consequence`` missing =
        let graph = PoolInventoryFixture.graph ()
        let id = PoolInventoryFixture.literal graph
        let edge = graph.Edges |> List.find (fun edge -> edge.Class = EdgeClass.Obligation && List.contains id edge.Sources)
        let next = graph.Nodes.Keys |> Seq.map NodeId.value |> Seq.max |> (+) 1
        let claim = { graph.Nodes[edge.Target] with Id = NodeId next }
        let absent = NodeId(next + 1)
        let enrichment : Clef.Compiler.Baker.Ingredients.Obligations.Enrichment =
            if missing = "source" then
                { NewNodes = [claim]; Annotated = []; NewEdges = [{ edge with Target = claim.Id; Sources = [absent] }] }
            else
                { NewNodes = []; Annotated = []; NewEdges = [{ edge with Target = absent; Sources = [id] }] }
        let error = Assert.Throws<System.InvalidOperationException>(fun () ->
            Clef.Compiler.Nanopass.ObligationElaboration.foldIn enrichment graph |> ignore)
        Assert.Contains(string (NodeId.value absent), error.Message)
        Assert.Contains((if missing = "source" then "current source participant" else "target"), error.Message)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Owner retirement preserves a coincident display anchor only at another current claim participant`` retainsHere =
        let graph = PoolInventoryFixture.graph ()
        let id = PoolInventoryFixture.literal graph
        let edge = graph.Edges |> List.find (fun edge ->
            if edge.Class <> EdgeClass.Obligation || not (List.contains id edge.Sources) then false
            else match graph.Nodes[edge.Target].Kind with SemanticKind.Obligation info -> info.Kind = "terminator-sentinel" | _ -> false)
        let original = graph.Nodes[edge.Target]
        let name = match original.Kind with SemanticKind.Obligation info -> info.Id | _ -> failwith "Expected sentinel claim"
        let second = graph.StaticStringPool.Value.Entries |> List.find (fun entry -> entry.Content = "second") |> _.NodeIds |> List.head
        let participant = if retainsHere then id else second
        // Both literal storages have their settled NUL sentinel. A distinct
        // current claim may intentionally carry the same display anchor name.
        let nextId = graph.Nodes.Keys |> Seq.map NodeId.value |> Seq.max |> fun value -> NodeId(value + 1)
        let other = { original with Id = nextId }
        let enrichment : Clef.Compiler.Baker.Ingredients.Obligations.Enrichment =
            { NewNodes = [other]; Annotated = []
              NewEdges = [{ edge with Target = other.Id; Sources = [participant] }] }
        let graph = Clef.Compiler.Nanopass.ObligationElaboration.foldIn enrichment graph
        let retired = Clef.Compiler.Baker.Recipes.ObligationRecipes.retireAnchors (Set.singleton original.Id) graph
        let revised =
            { retired with Nodes = retired.Nodes.Remove original.Id
                           Edges = retired.Edges |> List.filter (fun current -> current.Target <> original.Id) }
        let held = PoolInventoryFixture.anchorNames revised.Nodes[id]
        Assert.Equal(retainsHere, List.contains name held)
        Assert.Equal<Set<string>>(PoolInventoryFixture.currentAnchors revised id, Set.ofList held)
        Assert.Contains(name, PoolInventoryFixture.anchorNames revised.Nodes[participant])

    [<Fact>]
    member _.``Numeric owner replacement retires old proof identities and writes exact current literal consequences``() =
        let graph = PoolInventoryFixture.graph ()
        let id = PoolInventoryFixture.literal graph
        let retired = graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
            if node.Metadata.ContainsKey "Baker.NumericOwned" then Some id else None) |> Set.ofList
        Assert.NotEmpty retired
        let revised = Clef.Compiler.Nanopass.NumericSettlement.normalize graph
        Assert.All(retired, fun id ->
            Assert.False(revised.Nodes.ContainsKey id)
            Assert.DoesNotContain(revised.Edges, fun edge -> edge.Target = id))
        let names = PoolInventoryFixture.anchorNames revised.Nodes[id]
        Assert.Equal<Set<string>>(PoolInventoryFixture.currentAnchors revised id, Set.ofList names)
        Assert.Equal(names.Length, (Set.ofList names).Count)
        Assert.Contains("storage_first", names)
        Assert.Contains("view_first", names)
        Assert.Contains("sentinel_first", names)
        Assert.Contains("layout_user_strings", names)
        Assert.Contains(names, fun name -> name.StartsWith "numeric_")
        match NumericProjection.project revised with
        | Ok _ -> ()
        | Error failures -> failwithf "A claim's consequence invalidated its own source premises: %A" failures

    [<Fact>]
    member _.``Consequence annotations do not become numeric premises while pool authoring still requires their truth``() =
        let graph = PoolInventoryFixture.graph ()
        let id = PoolInventoryFixture.literal graph
        let literal = graph.Nodes[id]
        let changed =
            { literal with Metadata = literal.Metadata.Add(ObligationMetadata.Anchors, MetadataValue.StringList ["unwritten-claim"]) }
        let revised = { graph with Nodes = graph.Nodes.Add(id, changed) }
        match NumericProjection.project revised with
        | Ok _ -> ()
        | Error failures -> failwithf "Derived annotations were treated as numeric semantic premises: %A" failures
        Assert.True(StorageProjection.project revised |> Result.isError)

    [<Theory>]
    [<InlineData("semantic-metadata")>]
    [<InlineData("range")>]
    [<InlineData("source-shape")>]
    member _.``Anchor consequence exclusion preserves semantic metadata range and source shape invalidation`` defect =
        let graph = PoolInventoryFixture.graph ()
        let id = PoolInventoryFixture.literal graph
        let literal = graph.Nodes[id]
        let changed =
            match defect with
            | "semantic-metadata" -> { literal with Metadata = literal.Metadata.Add("Source.SemanticIntent", MetadataValue.String "changed") }
            | "range" -> { literal with ValueRange = Some(ValueRange.point 99I) }
            | _ -> { literal with Kind = SemanticKind.Literal(NativeLiteral.String "changed") }
        let revised = { graph with Nodes = graph.Nodes.Add(id, changed) }
        match NumericProjection.project revised with
        | Error _ -> ()
        | Ok _ -> failwith "Source semantic premises were weakened together with consequence annotation exclusion"

    [<Fact>]
    member _.``Pool inventory contains every source literal obligation including duplicate occurrences``() =
        let graph = PoolInventoryFixture.graph ()
        let pool = graph.StaticStringPool |> Option.defaultWith (fun () -> failwith "Source pool is missing")
        let projection =
            StorageProjection.project graph
            |> Result.defaultWith (fun failures -> failwithf "Source pool inventory failed: %A" failures)
        let literalIds = pool.Entries |> List.collect _.NodeIds |> Set.ofList
        let obligations =
            graph.Edges |> List.choose (fun edge ->
                match graph.Nodes.TryFind edge.Target with
                | Some { Kind = SemanticKind.Obligation info }
                    when edge.Class = EdgeClass.Obligation && List.exists literalIds.Contains edge.Sources -> Some info
                | _ -> None)
        Assert.Contains(obligations, fun info -> info.Kind = "storage-reservation")
        Assert.Contains(obligations, fun info -> info.Kind = "view-containment")
        Assert.Contains(obligations, fun info -> info.Kind = "terminator-sentinel")
        Assert.Contains("layout_user_strings", projection.LiteralPoolAnchors)
        Assert.All(obligations, fun info -> Assert.Contains(info.Id, projection.LiteralPoolAnchors))
        Assert.Equal<Set<string>>(Set.ofList ("layout_user_strings" :: List.map (fun (info: ObligationInfo) -> info.Id) obligations), Set.ofList projection.LiteralPoolAnchors)
        let duplicate = pool.Entries |> List.find (fun entry -> entry.Content = "first")
        Assert.True(duplicate.NodeIds.Length > 1)
        Assert.Equal(projection.LiteralPoolAnchors.Length, (Set.ofList projection.LiteralPoolAnchors).Count)

    [<Fact>]
    member _.``Detached layout proof body cannot authorize the pool after its current incidence and annotations withdraw``() =
        let graph = PoolInventoryFixture.graph ()
        let pool = graph.StaticStringPool.Value
        let layout = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Obligation info -> info.Id = "layout_user_strings" | _ -> false)
        let nodes = graph.Nodes |> Map.map (fun _ node ->
            match node.Metadata.TryFind ObligationMetadata.Anchors with
            | Some(MetadataValue.StringList anchors) ->
                let retained = MetadataValue.StringList(anchors |> List.filter ((<>) "layout_user_strings"))
                { node with Metadata = node.Metadata.Add(ObligationMetadata.Anchors, retained) }
            | _ -> node)
        let revised = { graph with Nodes = nodes; Edges = graph.Edges |> List.filter (fun edge -> edge.Target <> layout.Id) }
        Assert.True(revised.Nodes.ContainsKey layout.Id)
        match StorageProjection.project revised with
        | Ok _ -> failwith "A detached historical layout proof body authorized current allocation"
        | Error failures -> Assert.Contains(failures, fun failure ->
            failure.Occurrence = Some pool.DeclarationNode && failure.Reason.Contains("matching current source layout obligation"))

    [<Theory>]
    [<InlineData("missing-anchor")>]
    [<InlineData("duplicate-anchor")>]
    [<InlineData("withdrawn-obligation")>]
    [<InlineData("missing-obligation-body")>]
    member _.``Pool inventory rejects changed current literal obligation authority at its source`` defect =
        let graph = PoolInventoryFixture.graph ()
        let id = PoolInventoryFixture.literal graph
        let literal = graph.Nodes[id]
        let names =
            match literal.Metadata.TryFind ObligationMetadata.Anchors with
            | Some(MetadataValue.StringList names) when not names.IsEmpty -> names
            | other -> failwithf "Source literal has no obligation inventory: %A" other
        let edge = graph.Edges |> List.find (fun edge -> edge.Class = EdgeClass.Obligation && List.contains id edge.Sources)
        let revised =
            match defect with
            | "missing-anchor" ->
                let changed = { literal with Metadata = literal.Metadata.Add(ObligationMetadata.Anchors, MetadataValue.StringList(List.tail names)) }
                { graph with Nodes = graph.Nodes.Add(id, changed) }
            | "duplicate-anchor" ->
                let changed = { literal with Metadata = literal.Metadata.Add(ObligationMetadata.Anchors, MetadataValue.StringList(names.Head :: names)) }
                { graph with Nodes = graph.Nodes.Add(id, changed) }
            | "withdrawn-obligation" ->
                let retained = graph.Edges |> List.filter (fun current -> current.Class <> EdgeClass.Obligation || current.Target <> edge.Target)
                { graph with Edges = retained }
            | _ -> { graph with Nodes = graph.Nodes.Remove edge.Target }
        match StorageProjection.project revised with
        | Ok _ -> failwith "A changed literal proof inventory was admitted"
        | Error failures ->
            Assert.Contains(failures, fun failure ->
                failure.Occurrence = Some id &&
                    (failure.Reason.Contains("obligation anchor inventory") || failure.Reason.Contains("malformed current obligation")))

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

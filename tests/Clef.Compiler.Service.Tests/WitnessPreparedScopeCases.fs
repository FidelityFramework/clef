namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module PreparedEmission = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission
module PreparedScopes = Clef.Compiler.Baker.Recipes.WitnessScopeRecipes
module PreparedRows = Clef.Compiler.Baker.Recipes.WitnessForeignDemandRecipes
module Publication = Clef.Compiler.PSGSaturation.Publication.RevisionPublication
module SourceGraph = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph

module private PreparedScopeFixture =
    let dormantLibraryGraph count opened =
        let parse path text =
            match parseStringWithDefaults text path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Prepared scope fixture did not parse: %A" errors
        let dependency =
            "module DormantLibrary\n" +
            ([1..count] |> List.map (fun index -> $"let unused{index} (value: int) = value + {index}\n") |> String.concat "")
        let client = "module PreparedScope\n" + (if opened then "open DormantLibrary\n" else "// open DormantLibrary\n") + "[<EntryPoint>]\nlet main _ = 0\n"
        let clientPath = System.IO.Path.GetFullPath "prepared-scope.clef"
        let result = checkParsedInputsWithPlatformAndSources [
            parse "write-authority.clef" IntrinsicWriteFixture.authority
            parse "dormant-library.clef" dependency
            parse clientPath client ] (Some IntrinsicWriteFixture.platform) (Set.singleton clientPath)
        DimensionalCases.noErrors result
        PreparedEmission.tryRead result.Graph |> Result.defaultWith failwith |> ignore
        result.Graph

    let graph () =
        let parse path text =
            match parseStringWithDefaults text path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Prepared scope fixture did not parse: %A" errors
        let result = checkParsedInputsWithPlatform [
            parse "write-authority.clef" IntrinsicWriteFixture.authority
            parse "prepared-scope.clef" "module PreparedScope\nlet unused (x: int) = x + 1\n[<EntryPoint>]\nlet main _ = 0\n" ] (Some IntrinsicWriteFixture.platform)
        DimensionalCases.noErrors result
        PreparedEmission.tryRead result.Graph |> Result.defaultWith failwith |> ignore
        result.Graph

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "WitnessPreparedScope")>]
type WitnessPreparedScopeTests() =
    [<Fact>]
    member _.``Demanded occurrence diagnostics retain source scope without dormant graph inventory``() =
        let graph = PreparedScopeFixture.dormantLibraryGraph 64 true
        let frozen = graph.Codata.Value.WitnessPublishedRows.Value
        let reading = Publication.prepareOccurrences graph |> Result.defaultWith failwith
        let revision: Fidelity.PSG.CheckedRevisionId = { Session = "source-workspace"; Ordinal = 37UL }
        let delivery, headers, roots = Publication.publishOccurrences revision "source-workspace:9" reading |> Result.defaultWith failwith
        Assert.Equal(revision, delivery.Transaction.TargetRevision)
        Assert.Equal("source-workspace:9", delivery.Transaction.TargetCursor.Subscription)
        Assert.Equal(37UL, delivery.Sections.Head.Descriptor.Content.Version)
        Assert.Empty(Fidelity.PSG.OccurrenceDelivery.check delivery)
        Assert.Single(delivery.Sections) |> ignore
        let section = delivery.Sections.Head
        Assert.Equal<Set<_>>(frozen.Nodes.Keys |> Set.ofSeq, section.Descriptor.LiveOccurrences)
        Assert.True(section.Occurrences.Count < graph.Nodes.Count)
        for pair in section.Occurrences do
            Assert.Same(frozen.Nodes[pair.Key], pair.Value.Body)
            Assert.Equal<Fidelity.PSG.ChildDisposition list>(frozen.SourceReadings.Children[pair.Key], pair.Value.Children)
            Assert.True(pair.Value.Body.IsReachable)
            Assert.False(pair.Value.Body.Range.File.EndsWith "dormant-library.clef")
        Assert.Equal<Fidelity.PSG.SourceContextHeader list>(frozen.SourceReadings.ContextHeaders.Values |> Seq.toList, headers)
        Assert.Equal<Fidelity.PSG.NodeId list>(frozen.SourceReadings.Contexts |> Map.toList |> List.choose (fun (id, paths) ->
            if List.contains [] paths then Some id else None), roots)
        Assert.Empty section.Descriptor.RequiredBoundaries
        Assert.Empty section.Descriptor.OwnedArtifacts

    [<Fact>]
    member _.``Occurrence diagnostic refuses unknown references without enlarging source scope``() =
        let graph = PreparedScopeFixture.graph ()
        let held = graph.Codata.Value.WitnessPublishedRows.Value
        let key, body = held.Nodes |> Map.toSeq |> Seq.head
        let missing = Fidelity.PSG.NodeId System.Int32.MaxValue
        let changed = { held with Nodes = held.Nodes.Add(key, { body with Kind = Fidelity.PSG.SemanticKind.VarRef("missing", Some missing) }) }
        let result = Clef.Compiler.Baker.Recipes.WitnessPublishedRowsRecipes.occurrenceRows changed
        match result with
        | Error reason -> Assert.Contains("unavailable identity", reason)
        | Ok _ -> failwith "Unknown boundary reference acquired an occurrence diagnostic body."
        Assert.False(held.Nodes.ContainsKey missing)
        Assert.True(Publication.prepareOccurrences graph |> Result.isOk)

    [<Fact>]
    member _.``Prepared roots carry Baker live scope without inactive source bodies``() =
        let graph = PreparedScopeFixture.graph ()
        let held = graph.Codata.Value.WitnessLiveScope |> Option.defaultWith (fun () -> failwith "Prepared source scope was absent")
        let current = PreparedScopes.project graph |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.True(PreparedScopes.matches held current)
        Assert.Equal<Set<_>>(graph.Nodes |> Map.toSeq |> Seq.choose (fun (id, node) ->
                                match node.Kind with SemanticKind.Obligation _ | SemanticKind.TypeDef _ -> None | _ when node.IsReachable -> Some id | _ -> None) |> Set.ofSeq,
                             held.Occurrences.Keys |> Set.ofSeq)
        Assert.DoesNotContain(held.Occurrences.Values, fun row -> not row.Body.IsReachable)
        Assert.Contains(graph.Nodes.Values, fun node -> not node.IsReachable)
        PreparedEmission.admit graph |> Result.defaultWith (sprintf "%A" >> failwith)

    [<Fact>]
    member _.``Removing live scope admission requires source republication``() =
        let graph = PreparedScopeFixture.graph ()
        let changed = { graph with Codata = lazy { graph.Codata.Value with WitnessLiveScope = None } }
        match PreparedEmission.admit changed with
        | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains "Live occurrence scope")
        | Result.Ok _ -> failwith "Source admission survived withdrawal of its live scope"
        Assert.True((PreparedEmission.tryRead changed |> Result.isError))
        let invalidated = SourceGraph.invalidateWitness graph
        Assert.True(invalidated.Codata.Value.WitnessLiveScope.IsNone)
        Assert.True((PreparedEmission.tryRead invalidated |> Result.isError))

    [<Fact>]
    member _.``Prepared foreign demand and incidence rows are required before publication``() =
        let graph = PreparedScopeFixture.graph ()
        let held = graph.Codata.Value.WitnessPreparedRows |> Option.defaultWith (fun () -> failwith "Prepared source rows were absent")
        Assert.True(PreparedRows.matches held (PreparedRows.project graph))
        Assert.NotEmpty held.Edges
        Assert.True(Publication.publish graph |> Result.isOk)
        let withdrawn = { graph with Codata = lazy { graph.Codata.Value with WitnessPreparedRows = None } }
        match PreparedEmission.admit withdrawn with
        | Result.Error failures ->
            Assert.Contains(failures, fun failure -> failure.Reason.Contains "Baker-prepared foreign, demand and incidence rows")
        | Result.Ok _ -> failwith "Source admission survived withdrawal of its prepared rows"
        Assert.True(Publication.publish withdrawn |> Result.isError)
        let invalidated = SourceGraph.invalidateWitness graph
        Assert.True(invalidated.Codata.Value.WitnessPreparedRows.IsNone)
        Assert.True(Publication.publish invalidated |> Result.isError)

    [<Fact>]
    member _.``Unused open and dormant library growth do not enlarge published body or fact inventories``() =
        let cases = [PreparedScopeFixture.dormantLibraryGraph 1 false
                     PreparedScopeFixture.dormantLibraryGraph 1 true
                     PreparedScopeFixture.dormantLibraryGraph 64 true]
        let original = List.head cases
        Assert.True((List.last cases).Nodes.Count > original.Nodes.Count)
        let expected = original.Codata.Value.WitnessLiveRows |> Option.defaultWith (fun () -> failwith "Selected source rows absent")
        let publish graph = Publication.publish graph |> Result.defaultWith (sprintf "%A" >> failwith)
        let first = publish original
        let limits : Fidelity.PSG.BinaryLimits =
            { MaxBytes = 4 * 1024 * 1024; MaxCollectionLength = 10000; MaxDepth = 128
              MaxStringBytes = 1024 * 1024; MaxBigIntegerBytes = 1024; MaxValues = 1000000 }
        let encodedSize revision =
            Fidelity.PSG.Binary.encode limits revision
            |> Result.map Array.length
            |> Result.defaultWith (sprintf "Selected source payload failed binary integrity: %A" >> failwith)
        let expectedBytes = encodedSize first
        for graph in cases do
            let selected = graph.Codata.Value.WitnessLiveRows |> Option.defaultWith (fun () -> failwith "Selected source rows absent")
            let revision = publish graph
            Assert.Equal(expected.FactIdentities.Count, selected.FactIdentities.Count)
            Assert.Equal(first.Nodes.Count, revision.Nodes.Count)
            Assert.Equal(first.Emission.Callable.ValueShapes.Count, revision.Emission.Callable.ValueShapes.Count)
            Assert.Equal(first.Emission.Callable.AliasTargets.Count, revision.Emission.Callable.AliasTargets.Count)
            Assert.Equal(first.Emission.Numeric.OccurrenceRepresentations.Count, revision.Emission.Numeric.OccurrenceRepresentations.Count)
            Assert.Equal(first.ModuleClassifications.Count, revision.ModuleClassifications.Count)
            Assert.Equal(expectedBytes, encodedSize revision)
            Assert.Empty revision.Edges
            Assert.DoesNotContain(revision.Nodes.Values, fun body ->
                match body.Kind with Fidelity.PSG.SemanticKind.ModuleDef _ -> true | _ -> false)
            Assert.DoesNotContain(revision.Nodes.Values, fun body -> body.Range.File.EndsWith "dormant-library.clef")
            Assert.True(selected.Emission.Callable.ValueShapes.Keys |> Seq.forall selected.FactIdentities.Contains)
            Assert.True(selected.Emission.Numeric.TypeRepresentations.Keys |> Seq.forall selected.TypeIdentities.Contains)
            Assert.True(selected.FactIdentities.Count < graph.Nodes.Count)
            Assert.NotEmpty(graph.Codata.Value.WitnessPreparedRows.Value.Edges)

    [<Fact>]
    member _.``Withdrawing selected live fact rows requires source republication``() =
        let graph = PreparedScopeFixture.graph ()
        let changed = { graph with Codata = lazy { graph.Codata.Value with WitnessLiveRows = None } }
        match PreparedEmission.admit changed with
        | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason = "Baker-selected live fact rows differ from the current source snapshot.")
        | Result.Ok _ -> failwith "Source admission survived withdrawal of selected rows"
        Assert.True(PreparedEmission.tryRead changed |> Result.isError)
        Assert.True(Publication.publish changed |> Result.isError)
        Assert.True((SourceGraph.invalidateWitness graph).Codata.Value.WitnessLiveRows.IsNone)

    [<Theory>]
    [<InlineData("foreign")>]
    [<InlineData("demand")>]
    [<InlineData("incidence")>]
    member _.``Source reobservation refuses corrupted prepared rows without repairing them`` domain =
        let graph = PreparedScopeFixture.graph ()
        let held = graph.Codata.Value.WitnessPreparedRows |> Option.defaultWith (fun () -> failwith "Prepared source rows were absent")
        let occurrence = graph.Nodes |> Map.toSeq |> Seq.find (fun (_, node) -> node.IsReachable) |> fst
        let changedRows =
            match domain with
            | "foreign" -> { held with Foreign = { held.Foreign with MappedCalls = held.Foreign.MappedCalls.Add occurrence } }
            | "demand" -> { held with Demand = { held.Demand with Operands = held.Demand.Operands.Add(occurrence, occurrence) } }
            | "incidence" -> { held with Edges = List.tail held.Edges }
            | unknown -> failwithf "Unknown prepared-row domain: %s" unknown
        Assert.NotEqual<WitnessPreparedRows>(held, changedRows)
        let changed = { graph with Codata = lazy { graph.Codata.Value with WitnessPreparedRows = Some changedRows } }
        match PreparedEmission.admit changed with
        | Result.Error failures ->
            Assert.Contains(failures, fun failure -> failure.Reason = "Baker-prepared foreign, demand and incidence rows differ from the current source snapshot.")
        | Result.Ok _ -> failwithf "Source admission accepted corrupt %s rows" domain
        Assert.Equal<WitnessPreparedRows option>(Some changedRows, changed.Codata.Value.WitnessPreparedRows)
        Assert.True(Publication.publish changed |> Result.isError)
        Assert.True(Publication.publish graph |> Result.isOk)

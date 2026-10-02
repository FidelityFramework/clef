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
    member _.``Prepared roots carry Baker live scope without inactive source bodies``() =
        let graph = PreparedScopeFixture.graph ()
        let held = graph.Codata.Value.WitnessLiveScope |> Option.defaultWith (fun () -> failwith "Prepared source scope was absent")
        let current = PreparedScopes.project graph |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.True(PreparedScopes.matches held current)
        Assert.Equal<Set<_>>(graph.Nodes |> Map.toSeq |> Seq.choose (fun (id, node) ->
                                match node.Kind with SemanticKind.Obligation _ -> None | _ when node.IsReachable -> Some id | _ -> None) |> Set.ofSeq,
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
        Assert.True(Publication.publish IntrinsicWriteFixture.platform graph |> Result.isOk)
        let withdrawn = { graph with Codata = lazy { graph.Codata.Value with WitnessPreparedRows = None } }
        match PreparedEmission.admit withdrawn with
        | Result.Error failures ->
            Assert.Contains(failures, fun failure -> failure.Reason.Contains "Baker-prepared foreign, demand and incidence rows")
        | Result.Ok _ -> failwith "Source admission survived withdrawal of its prepared rows"
        Assert.True(Publication.publish IntrinsicWriteFixture.platform withdrawn |> Result.isError)
        let invalidated = SourceGraph.invalidateWitness graph
        Assert.True(invalidated.Codata.Value.WitnessPreparedRows.IsNone)
        Assert.True(Publication.publish IntrinsicWriteFixture.platform invalidated |> Result.isError)

    [<Fact>]
    member _.``Unused open and dormant library growth do not enlarge published body or fact inventories``() =
        let cases = [PreparedScopeFixture.dormantLibraryGraph 1 false
                     PreparedScopeFixture.dormantLibraryGraph 1 true
                     PreparedScopeFixture.dormantLibraryGraph 64 true]
        let original = List.head cases
        Assert.True((List.last cases).Nodes.Count > original.Nodes.Count)
        let expected = original.Codata.Value.WitnessLiveRows |> Option.defaultWith (fun () -> failwith "Selected source rows absent")
        let publish graph = Publication.publish IntrinsicWriteFixture.platform graph |> Result.defaultWith (sprintf "%A" >> failwith)
        let first = publish original
        for graph in cases do
            let selected = graph.Codata.Value.WitnessLiveRows |> Option.defaultWith (fun () -> failwith "Selected source rows absent")
            let revision = publish graph
            Assert.Equal(expected.FactIdentities.Count, selected.FactIdentities.Count)
            Assert.Equal(first.Nodes.Count, revision.Nodes.Count)
            Assert.Equal(first.Emission.Callable.ValueShapes.Count, revision.Emission.Callable.ValueShapes.Count)
            Assert.Equal(first.Emission.Callable.AliasTargets.Count, revision.Emission.Callable.AliasTargets.Count)
            Assert.Equal(first.Emission.Numeric.OccurrenceRepresentations.Count, revision.Emission.Numeric.OccurrenceRepresentations.Count)
            Assert.Equal(first.ModuleClassifications.Count, revision.ModuleClassifications.Count)
            Assert.Empty revision.Edges
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
        Assert.True(Publication.publish IntrinsicWriteFixture.platform changed |> Result.isError)
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
        Assert.True(Publication.publish IntrinsicWriteFixture.platform changed |> Result.isError)
        Assert.True(Publication.publish IntrinsicWriteFixture.platform graph |> Result.isOk)

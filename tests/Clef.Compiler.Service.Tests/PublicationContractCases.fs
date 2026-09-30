namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Publication = Clef.Compiler.PSGSaturation.Publication.RevisionPublication
module Emission = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

/// The revision a compilation publishes, examined against the structural rules of
/// the contract it conforms to. The producer holds the same rules as its readers.
module private PublicationFixture =
    // A lazy value holds a state of the representation named uint8, so the platform offers it.
    let private byteState : Clef.Compiler.NativeTypedTree.NativeTypes.NumericRepresentation =
        { Name = "uint8"; Capability = "native"; Family = "uint"; Bits = 8
          MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap" }

    let platform =
        { IntrinsicWriteFixture.platform with
            Representations = IntrinsicWriteFixture.platform.Representations.Add(byteState.Name, byteState) }

    let authority =
        IntrinsicWriteFixture.authority.Replace(
            "Representations = [| ",
            "Representations = [| { Name = \"uint8\"; Capability = \"native\"; Family = \"uint\"; Bits = 8; MinMagnitude = \"0\"; MaxMagnitude = \"255\"; Boundary = \"wrap\" }; ")

    let check (name: string) (body: string) =
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "%A" errors
        let result =
            Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                [ parse authority "write-authority.clef"; parse body (name + ".clef") ]
                (Some platform)
        DimensionalCases.noErrors result
        result.Graph

    let publish (graph: SemanticGraph) =
        match Publication.publish platform graph with
        | Ok revision -> revision
        | Error failures -> failwithf "Publication refused: %A" failures

    let programs =
        [ "scalar", "module Scalar\nlet calculate first second = first + second\n[<EntryPoint>]\nlet main _ = calculate (-7) 700\n"
          "record", "module Pair\ntype Pair = { Value: int; Ready: bool }\n[<EntryPoint>]\nlet main _ =\n    let pair = { Value = -7; Ready = true }\n    if pair.Ready then pair.Value else 0\n"
          "lazy", "module Deferred\nlet make (value: bool) = lazy value\n[<EntryPoint>]\nlet main _ =\n    let first = make false\n    let second = make true\n    let alias = first\n    ignore (Lazy.force alias)\n    ignore (Lazy.force second)\n    0\n"
          "functions", "module Three\nlet double (value: int) = value + value\nlet negate (value: int) = 0 - value\nlet both (value: int) = double (negate value)\n[<EntryPoint>]\nlet main _ = both 3 + double 4\n" ]
        |> Map.ofList

type PublicationContractCases() =
    [<Theory>]
    [<InlineData("scalar")>]
    [<InlineData("record")>]
    [<InlineData("lazy")>]
    [<InlineData("functions")>]
    member _.``A published revision satisfies every structural rule of the contract`` name =
        let revision = PublicationFixture.check name PublicationFixture.programs[name] |> PublicationFixture.publish
        Assert.Equal(Fidelity.PSG.Revision.Schema, revision.Header.Schema)
        Assert.Equal(Publication.Producer, revision.Header.Producer)
        Assert.NotEmpty revision.Nodes
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Theory>]
    [<InlineData("scalar")>]
    [<InlineData("lazy")>]
    member _.``A published revision carries the entire edge set`` name =
        let graph = PublicationFixture.check name PublicationFixture.programs[name]
        let revision = PublicationFixture.publish graph
        let implied =
            graph.Nodes |> Map.toList
            |> List.sumBy (fun (_, node) -> (Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node).Length)
        Assert.Equal(implied + graph.Edges.Length, revision.Edges.Length)
        // Every relation Baker recorded is published with its role.
        let recorded = graph.Edges |> List.countBy (fun edge -> sprintf "%A" edge.Class) |> Map.ofList
        let published = revision.Edges |> List.countBy (fun edge -> sprintf "%A" edge.Class) |> Map.ofList
        for KeyValue(edgeClass, count) in recorded do
            Assert.True(published.TryFind edgeClass |> Option.exists (fun held -> held >= count),
                        sprintf "The revision holds fewer %s edges than the graph" edgeClass)

    [<Fact>]
    member _.``A graph whose projection was withdrawn is not published`` () =
        let graph = PublicationFixture.check "scalar" PublicationFixture.programs["scalar"]
        match Publication.publish PublicationFixture.platform (Emission.invalidate graph) with
        | Error failures ->
            Assert.Contains(failures, fun failure ->
                failure.Reason = "Source emission admission: The current graph has no complete source witness projection.")
        | Ok _ -> failwith "A graph with no source witness projection was published."

    [<Fact>]
    member _.``A graph changed after its projection is not published`` () =
        let graph = PublicationFixture.check "scalar" PublicationFixture.programs["scalar"]
        let changed = { graph with DeclarationRoots = [] }
        match Publication.publish PublicationFixture.platform changed with
        | Error failures ->
            Assert.Contains(failures, fun failure ->
                failure.Reason.StartsWith "Source emission admission: The current graph differs from its source witness projection input")
        | Ok _ -> failwith "A graph that differs from its projection input was published."

    [<Theory>]
    [<InlineData("row")>]
    [<InlineData("premise")>]
    member _.``A graph whose literal storage changed after its projection is not published`` change =
        let graph = IntrinsicWriteFixture.pooledGraph (IntrinsicWriteFixture.demandBody "0")
        let kept = IntrinsicWriteFixture.literal graph "kept"
        let never = IntrinsicWriteFixture.literal graph "never demanded"
        Assert.NotEqual(graph.LiteralStorage[kept], graph.LiteralStorage[never])
        let changed =
            match change, graph.LiteralStorage[never] with
            | "row", row -> { graph with LiteralStorage = graph.LiteralStorage.Add(kept, row) }
            | _, LiteralStorage.NotMaterialized (StoragePremise.Established omissions) ->
                { graph with LiteralStorage = graph.LiteralStorage.Add(never, LiteralStorage.NotMaterialized (StoragePremise.Pending omissions)) }
            | _, row -> failwithf "The literal that no demanded position reads has the storage row %A" row
        match Publication.publish IntrinsicWriteFixture.platform changed with
        | Error failures ->
            Assert.Contains(failures, fun failure ->
                failure.Reason.StartsWith "Source emission admission: The current graph differs from its source witness projection input")
        | Ok _ -> failwith "A graph whose literal storage differs from its projection input was published."

    [<Fact>]
    member _.``Independent scalar function regions survive renumbering and isolate an edited body`` () =
        let source prefix second =
            "module RegionReuse\n" + prefix + "let first () = true\nlet second () = " + second +
            "\n[<EntryPoint>]\nlet main _ = if first () && second () then 0 else 1\n"
        let regions text =
            let graph = PublicationFixture.check "region-reuse" text
            let prepared = match Emission.prepare graph with Ok graph -> graph | Error failures -> failwithf "%A" failures
            let revision = PublicationFixture.publish prepared
            let segmentation = revision.Codata.WitnessSegmentation |> Option.get
            let names = segmentation.Regions |> List.map (fun region -> region.Identity, region) |> Map.ofList
            let covered = segmentation.Regions |> List.collect (fun region -> Set.toList region.Members)
            Assert.Equal(revision.Nodes.Count, covered.Length)
            Assert.Equal(revision.Nodes.Count, Set.ofList covered |> Set.count)
            names
        let before = regions (source "" "false")
        let after = regions (source "let extra () = false\n" "true")
        let first = "callable:RegionReuse:first"
        let second = "callable:RegionReuse:second"
        Assert.True(before.ContainsKey first, sprintf "Missing independent first region: %A" before.Keys)
        Assert.True(before.ContainsKey second, sprintf "Missing independent second region: %A" before.Keys)
        Assert.NotEqual(before[first].Root, after[first].Root)
        Assert.Equal(before[first].Fingerprint, after[first].Fingerprint)
        Assert.NotEqual(before[second].Fingerprint, after[second].Fingerprint)
        Assert.NotEmpty after[first].Supports
        Assert.Equal(Fidelity.PSG.WitnessRegionKind.Common, after["common"].Flavor)

    [<Fact>]
    member _.``Source admission retracts a changed region fingerprint and publication rejects its stale roots`` () =
        let graph = PublicationFixture.check "region-retraction" "module RegionRetraction\nlet flag () = true\n[<EntryPoint>]\nlet main _ = if flag () then 0 else 1\n"
        let prepared = match Emission.prepare graph with Ok graph -> graph | Error failures -> failwithf "%A" failures
        let segmentation = prepared.Codata.Value.WitnessSegmentation |> Option.get
        let changedSegmentation =
            { segmentation with
                Regions = segmentation.Regions |> List.map (fun region -> { region with Fingerprint = "stale" }) }
        let changed =
            { prepared with
                Codata = lazy { prepared.Codata.Value with WitnessSegmentation = Some changedSegmentation } }
        match Emission.admit changed with
        | Ok () -> failwith "Source admitted a stale region contract"
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason = "Witness segmentation differs from the current source snapshot.")
        match Publication.publish PublicationFixture.platform changed with
        | Ok _ -> failwith "Publication copied stale region roots"
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains "current graph differs")

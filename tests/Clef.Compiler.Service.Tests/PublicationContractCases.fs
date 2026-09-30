namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Publication = Clef.Compiler.PSGSaturation.Publication.RevisionPublication
module Emission = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission
module Dispatch = Clef.Compiler.Baker.Recipes.ProofDispatchRecipes
module Discharge = Clef.Compiler.Nanopass.ObligationDischarge
module NativeGraph = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph

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

    let prepare graph =
        match Emission.prepare graph with Ok prepared -> prepared | Error failures -> failwithf "%A" failures

    // An independent obligation lets dispatch freshness be tested without a
    // domain-specific reader rejecting the mutation before this source seam.
    let dispatchGraph body =
        let graph = check "dispatch" programs["scalar"]
        let subjects = graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.truncate 2 |> Seq.toList
        Assert.Equal(2, subjects.Length)
        let info : ObligationInfo =
            { Id = "dispatch_contract_control"; Kind = "dispatch-control"; Logic = "QF_LIA"
              Statement = "Dispatch inventory fixture"; Source = "dispatch.clef:1:1"; Refs = []
              Body = body }
        let node = Clef.Compiler.Baker.Ingredients.Obligations.obligationNode subjects.Head 0 info
        let row ordinal sources : Hyperedge =
            { Sources = sources; Target = node.Id; Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = ordinal }
        let changed =
            { graph with Nodes = graph.Nodes.Add(node.Id, node)
                         Edges = graph.Edges @ [row 2 (List.map _.Id subjects); row 7 [subjects.Head.Id]] }
        // Adding the fixture node changes the complete source census. Renew
        // its owning domains before testing the separate dispatch contract.
        let settled =
            changed
            |> Clef.Compiler.Nanopass.NumericSettlement.normalize
            |> Clef.Compiler.Nanopass.MemorySettlement.normalize
            |> Clef.Compiler.Nanopass.SpatialSettlement.normalize
            |> Clef.Compiler.Nanopass.BoundarySettlement.normalize
        settled, node.Id

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

    [<Theory>]
    [<InlineData("scalar")>]
    [<InlineData("record")>]
    [<InlineData("lazy")>]
    [<InlineData("functions")>]
    member _.``Baker dispatch preserves the complete legacy inventory source grouping and query bytes`` name =
        let graph = PublicationFixture.check name PublicationFixture.programs[name]
        let dispatch = graph.Codata.Value.ProofDispatch |> Option.get
        let required = NativeGraph.obligations graph |> List.map (fun (node, info) -> node.Id, info)
        Assert.True(dispatch.Required = required)
        let sources =
            graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains)
            |> List.groupBy _.Target
            |> List.map (fun (target, rows) -> target, List.map _.Sources rows) |> Map.ofList
        Assert.True(dispatch.SourceGroups = sources)
        let query = Discharge.smtLib (List.map snd required)
        Assert.Equal<Result<string, (NodeId * string list) list>>(Ok query, dispatch.Query)
        let revision = PublicationFixture.publish graph
        Assert.Equal(query, revision.ObligationQuery)
        Assert.Equal<string list>(required |> List.map (snd >> _.Id), revision.Obligations |> List.map _.Id)
        let publicId id = Fidelity.PSG.NodeId (NodeId.value id)
        let publicSources = sources |> Map.toList |> List.map (fun (id, rows) -> publicId id, rows |> List.map (List.map publicId)) |> Map.ofList
        Assert.True((publicSources = revision.ObligationSources))
        Assert.True(Result.isOk (Emission.admit graph))

    [<Theory>]
    [<InlineData("absent")>]
    [<InlineData("query")>]
    [<InlineData("inventory")>]
    member _.``Missing or altered stored dispatch is refused by source admission and publication`` change =
        let graph = PublicationFixture.check "scalar" PublicationFixture.programs["scalar"]
        let dispatch = graph.Codata.Value.ProofDispatch |> Option.get
        let changedPlan =
            match change with
            | "absent" -> None
            | "query" -> Some { dispatch with Query = Ok "(check-sat)" }
            | _ -> Some { dispatch with Required = List.tail dispatch.Required }
        let changed = { graph with Codata = lazy { graph.Codata.Value with ProofDispatch = changedPlan } }
        match Emission.admit changed with
        | Ok () -> failwith "Source admitted missing or stale dispatch"
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason = "Proof dispatch differs from the current source snapshot.")
        Assert.True(Result.isError (Publication.publish PublicationFixture.platform changed))
        let renewed = PublicationFixture.prepare changed
        Assert.True(Result.isOk (Emission.admit renewed))
        Assert.True(Result.isOk (Publication.publish PublicationFixture.platform renewed))

    [<Theory>]
    [<InlineData("class")>]
    [<InlineData("ordinal")>]
    [<InlineData("role")>]
    [<InlineData("source-order")>]
    [<InlineData("group-order")>]
    member _.``Equal queries and unchanged nodes cannot preserve changed Constrains incidence`` change =
        let raw, target = PublicationFixture.dispatchGraph (ObligationBody.StorageReservation(3, 4))
        let graph = PublicationFixture.prepare raw
        let mutate (edge: Hyperedge) =
            if edge.Target <> target then edge else
            match change with
            | "class" -> { edge with Class = EdgeClass.Reference }
            | "ordinal" -> { edge with Ordinal = edge.Ordinal + 1 }
            | "role" -> { edge with Role = EdgeRole.Body }
            | "source-order" -> { edge with Sources = List.rev edge.Sources }
            | _ -> edge
        let edges =
            if change = "group-order" then
                let unrelated, related = graph.Edges |> List.partition (fun edge -> edge.Target <> target)
                unrelated @ List.rev related
            else List.map mutate graph.Edges
        let changed = { graph with Edges = edges }
        Assert.Same(graph.Nodes, changed.Nodes)
        let current = match Dispatch.materialize changed with Ok plan -> plan | Error failures -> failwithf "%A" failures
        let held = graph.Codata.Value.ProofDispatch |> Option.get
        Assert.Equal<Result<string, (NodeId * string list) list>>(held.Query, current.Query)
        Assert.False(Dispatch.matches held current)
        match Emission.admit changed with
        | Ok () -> failwith "Source admitted changed dispatch incidence"
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason = "Proof dispatch differs from the current source snapshot.")
        Assert.True(Result.isError (Publication.publish PublicationFixture.platform changed))

    [<Fact>]
    member _.``Changing an obligation body retracts its retained query`` () =
        let raw, target = PublicationFixture.dispatchGraph (ObligationBody.StorageReservation(3, 4))
        let graph = PublicationFixture.prepare raw
        let node = graph.Nodes[target]
        let info = match node.Kind with SemanticKind.Obligation info -> info | _ -> failwith "Expected obligation"
        let changedNode = { node with Kind = SemanticKind.Obligation { info with Body = ObligationBody.StorageReservation(3, 3) } }
        let changed = { graph with Nodes = graph.Nodes.Add(target, changedNode) }
        match Emission.admit changed with
        | Ok () -> failwith "Source admitted a query rendered for an older body"
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason = "Proof dispatch differs from the current source snapshot.")
        let renewed = PublicationFixture.prepare changed
        Assert.NotEqual<Result<string, (NodeId * string list) list>>(graph.Codata.Value.ProofDispatch.Value.Query, renewed.Codata.Value.ProofDispatch.Value.Query)
        Assert.True(Result.isError (Publication.publish PublicationFixture.platform changed))

    [<Fact>]
    member _.``Pending dispatch retains exact missing reasons without a query or new preparation failure`` () =
        let reasons = ["The complete initialization census is missing."; "The source role is unavailable."]
        let raw, target = PublicationFixture.dispatchGraph (ObligationBody.Pending reasons)
        let graph = PublicationFixture.prepare raw
        let dispatch = graph.Codata.Value.ProofDispatch |> Option.get
        Assert.Equal<Result<string, (NodeId * string list) list>>(Error [target, reasons], dispatch.Query)
        Assert.Contains(dispatch.Required, fun (id, info) -> id = target && info.Body = ObligationBody.Pending reasons)
        Assert.True(Result.isOk (Emission.admit graph))
        match Publication.publish PublicationFixture.platform graph with
        | Ok _ -> failwith "Publication accepted unavailable dispatch"
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Occurrence = Some target && failure.Reason.Contains "premises are unavailable")

    [<Fact>]
    member _.``Malformed rendering fails at the source obligation before publication`` () =
        let raw, target = PublicationFixture.dispatchGraph (ObligationBody.ConsecutiveLayout([], 0, None))
        match Emission.prepare raw with
        | Ok _ -> failwith "Malformed layout produced a dispatch plan"
        | Error failures ->
            Assert.Contains(failures, fun failure -> failure.Occurrence = Some target && failure.Reason.StartsWith "Proof dispatch rendering failed:")
            let diagnostics = Emission.diagnostics raw failures
            Assert.Contains(diagnostics, fun diagnostic -> diagnostic.Code = "CCS8403" && diagnostic.Range = raw.Nodes[target].Range)

    [<Fact>]
    member _.``Source invalidation withdraws dispatch without changing the prior graph`` () =
        let graph = PublicationFixture.check "scalar" PublicationFixture.programs["scalar"]
        let invalidated = Emission.invalidate graph
        Assert.True(graph.Codata.Value.ProofDispatch.IsSome)
        Assert.True(invalidated.Codata.Value.ProofDispatch.IsNone)

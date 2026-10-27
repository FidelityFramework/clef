namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module PreparedEmission = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission
module PreparedScopes = Clef.Compiler.Baker.Recipes.WitnessScopeRecipes
module PreparedRows = Clef.Compiler.Baker.Recipes.WitnessForeignDemandRecipes
module SelectedRows = Clef.Compiler.Baker.Recipes.WitnessLiveRowsRecipes
module DeviceAccess = Clef.Compiler.PSGSaturation.SemanticGraph.DeviceAccess
module Mmio = Clef.Compiler.PSGSaturation.SemanticGraph.Mmio
module Predicates = Clef.Compiler.PSGSaturation.SemanticGraph.Predicates
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

    let private checkMmioGraph body =
        let directory = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/ffi-reconcile-20261013/mmio-source-agreement", System.Guid.NewGuid().ToString("N")))
        System.IO.Directory.CreateDirectory directory |> ignore
        let platform = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../../Fidelity.Platform/Profiles/EK_RA6M5_HelloBlinky/Fidelity.Platform.fidproj"))
        System.IO.File.WriteAllText(System.IO.Path.Combine(directory, "Main.clef"), "module MmioCheck\n[<EntryPoint>]\nlet main _ =\n    " + body + "\n    0\n")
        let project = System.IO.Path.Combine(directory, "Test.fidproj")
        System.IO.File.WriteAllText(project, String.concat "\n" [
            "[package]"; "name=\"MmioCheck\""; "version=\"0.1.0\""
            "[compilation]"; "target=\"mcu\""
            "[platform]"; "runtime_model=\"bare\""; "os=\"none\""; "arch=\"arm_cortex_m33\""
            "[dependencies]"; sprintf "platform={path=%A}" platform
            "[build]"; "sources=[\"Main.clef\"]"; "output=\"test.elf\""; "output_kind=\"embedded\"" ])
        let result = Clef.Compiler.Project.ProjectChecker.checkProject project
                     |> Result.defaultWith (fun failures -> failwithf "Real MMIO project failed before returning its final graph: %A" failures)
        result.CheckResult.Graph

    // Composer/tests/Mmio/Program.fs positive source, checked through the real
    // project owner. Publication diagnostics must not hide the final source facts.
    let mmioGraph = lazy (
        String.concat "\n    " [
            "let r8 = Mmio.reg8 0x40080D03"
            "let r16 = Mmio.reg16 0x4008081A"
            "let r32 = Mmio.reg32 0x40080818"
            "Mmio.write8 r8 255"
            "Mmio.write16 r16 65535"
            "Mmio.write32 r32 4294967295"
            "let _ = Mmio.read8 r8"
            "let _ = Mmio.read16 r16"
            "let _ = Mmio.read32 r32"
            "let mutable attempts = 0"
            "while attempts < 4 && Mmio.read8 r8 = 0 do"
            "    attempts <- attempts + 1" ]
        |> checkMmioGraph)

    // The representation prerequisite excludes the unrelated polling loop.
    // Immutable source aliases need no new address or language admission rule.
    let mmioPointerGraph = lazy (
        String.concat "\n    " [
            "let r8 = Mmio.reg8 0x40080D03"
            "let r16 = Mmio.reg16 0x4008081A"
            "let r32 = Mmio.reg32 0x40080818"
            "let a8 = r8"
            "let a16 = r16"
            "let a32 = r32"
            "Mmio.write8 a8 1"
            "Mmio.write16 a16 1"
            "Mmio.write32 a32 1"
            "let _ = Mmio.read8 a8"
            "let _ = Mmio.read16 a16"
            "let _ = Mmio.read32 a32" ]
        |> checkMmioGraph)

    let selectedRows (graph: SemanticGraph) =
        let facts = graph.Codata.Value
        SelectedRows.project graph facts.WitnessEmission.Value facts.WitnessLiveScope.Value
            facts.WitnessPreparedRows.Value facts.WitnessSegmentation.Value

    let withMmio id row (graph: SemanticGraph) =
        { graph with Codata = lazy { graph.Codata.Value with Mmio = graph.Codata.Value.Mmio.Add(id, row) } }

    let unresolvedRow : MmioAccessEvidence =
        { Operation = "read8"; Address = bigint 0x40080D03; Bits = 8; Binding = None }

    let assertFailure id reason (failures: WitnessProjectionFailure list) =
        let failure = Assert.Single failures
        Assert.Equal(reason, failure.Reason)
        Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
        Assert.Equal(Some id, failure.Occurrence)
        Assert.Equal<Set<_>>(Set.singleton id, failure.Participants)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "WitnessPreparedScope")>]
type WitnessPreparedScopeTests() =
    [<Fact>]
    member _.``Real MMIO constructors and handle arguments have source pointer representations``() =
        let graph = PreparedScopeFixture.mmioPointerGraph.Value
        let rows = graph.Codata.Value.Mmio
        let constructors = rows |> Map.filter (fun _ row -> row.Operation.StartsWith "reg")
        let accessors = rows |> Map.filter (fun _ row -> row.Operation.StartsWith "read" || row.Operation.StartsWith "write")
        Assert.Equal(3, constructors.Count)
        Assert.Equal(6, accessors.Count)
        Assert.Equal<Set<int>>(Set.ofList [8; 16; 32], constructors.Values |> Seq.map _.Bits |> Set.ofSeq)
        let domain = graph.Edges |> List.choose (fun edge ->
            match edge.Role with EdgeRole.NumericDomain domain -> Some domain | _ -> None) |> Assert.Single
        let pointerAt id =
            Assert.True(domain.Premises.ContainsKey id, sprintf "MMIO occurrence %A has no numeric-domain premise" id)
            match domain.OccurrenceRepresentations.TryFind id with
            | Some(Ok(ValueRepresentation.Scalar(SettledSlot.Pointer 1))) -> ()
            | other -> failwithf "MMIO occurrence %A lacks its source Pointer 1 representation: %A" id other
        for KeyValue(site, _) in constructors do pointerAt site
        for KeyValue(site, row) in accessors do
            match Mmio.operation graph site with
            | Some(operation, handle :: _) when operation = row.Operation ->
                pointerAt handle
                match Predicates.valueOf graph handle with
                | Some origin -> Assert.True(constructors.ContainsKey origin.Id, "Immutable handle no longer resolves to its real MMIO constructor")
                | None -> failwithf "MMIO handle occurrence %A has no source value" handle
            | other -> failwithf "MMIO accessor %A lost its source operation and handle argument: %A" site other

    [<Fact>]
    member _.``Real MMIO source retains nonempty settled operation agreement on its final graph``() =
        let graph = PreparedScopeFixture.mmioGraph.Value
        let rows = graph.Codata.Value.Mmio
        Assert.NotEmpty rows
        Assert.Empty(DeviceAccess.checkSelected graph rows)

    [<Fact>]
    member _.``Real MMIO source refuses a different retained operation at the same occurrence``() =
        let graph = PreparedScopeFixture.mmioGraph.Value
        let rows = graph.Codata.Value.Mmio
        Assert.NotEmpty rows
        let id, row = rows |> Map.toSeq |> Seq.head
        let replacement = if row.Operation = "read8" then "write8" else "read8"
        let changed = rows.Add(id, { row with Operation = replacement })
        DeviceAccess.checkSelected graph changed
        |> PreparedScopeFixture.assertFailure id (sprintf "Selected MMIO operation '%s' differs from source operation '%s'." replacement row.Operation)

    [<Fact>]
    member _.``Preparation refuses a selected MMIO row without a source operation``() =
        let graph = PreparedScopeFixture.graph ()
        let id = graph.Codata.Value.WitnessLiveRows.Value.FactIdentities
                 |> Seq.find (fun id -> graph.Nodes.ContainsKey id && (Mmio.operation graph id |> Option.isNone))
        let changed = PreparedScopeFixture.withMmio id PreparedScopeFixture.unresolvedRow graph
        Assert.True((PreparedScopeFixture.selectedRows changed).Codata.Mmio.ContainsKey id)
        match PreparedEmission.prepare changed with
        | Error failures -> PreparedScopeFixture.assertFailure id "Selected MMIO evidence has no source MMIO operation." failures
        | Ok _ -> failwith "Preparation admitted a selected non-MMIO source occurrence."

    [<Fact>]
    member _.``Admission reobserves MMIO operations even when retained and current selected rows agree``() =
        let graph = PreparedScopeFixture.graph ()
        let id = graph.Codata.Value.WitnessLiveRows.Value.FactIdentities
                 |> Seq.find (fun id -> graph.Nodes.ContainsKey id && (Mmio.operation graph id |> Option.isNone))
        let changed = PreparedScopeFixture.withMmio id PreparedScopeFixture.unresolvedRow graph
        let projection = changed.Codata.Value.WitnessEmission.Value
        let scope = PreparedScopes.projectWithEmission projection changed |> Result.defaultWith (sprintf "%A" >> failwith)
        let segmentation = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessSegmentation.project changed projection scope
        let changed = { changed with Codata = lazy { changed.Codata.Value with WitnessLiveScope = Some scope; WitnessSegmentation = Some segmentation } }
        let selected = PreparedScopeFixture.selectedRows changed
        Assert.True(selected.Codata.Mmio.ContainsKey id)
        let held = { changed with Codata = lazy { changed.Codata.Value with WitnessLiveRows = Some selected } }
        Assert.True(SelectedRows.matches selected (PreparedScopeFixture.selectedRows held))
        match PreparedEmission.admit held with
        | Error failures -> PreparedScopeFixture.assertFailure id "Selected MMIO evidence has no source MMIO operation." failures
        | Ok () -> failwith "Admission trusted mutually consistent stale MMIO rows."

    [<Fact>]
    member _.``Unselected MMIO evidence does not enlarge source publication obligations``() =
        let graph = PreparedScopeFixture.dormantLibraryGraph 1 false
        let selected = PreparedScopeFixture.selectedRows graph
        let id = graph.Nodes.Keys |> Seq.find (fun id -> not (selected.FactIdentities.Contains id))
        let changed = PreparedScopeFixture.withMmio id PreparedScopeFixture.unresolvedRow graph
        let current = PreparedScopeFixture.selectedRows changed
        // FactIdentities is the actual closeFacts union valueFacts selection.
        Assert.False(current.FactIdentities.Contains id)
        Assert.False(current.Codata.Mmio.ContainsKey id)
        PreparedEmission.prepare changed |> Result.defaultWith (sprintf "%A" >> failwith) |> ignore

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

open Clef.Compiler.NativeTypedTree.NativeTypes

module private MmioMeetFixture =
    module Native = Clef.Compiler.NativeTypedTree.NativeTypes
    module Meets = Clef.Compiler.PSGSaturation.SemanticGraph.Meets
    module Ranges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
    module Numeric = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication

    let check (guest: bool) (declarations: string) (main: string) =
        let directory = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/ffi-reconcile-20261013/mmio-meets", System.Guid.NewGuid().ToString("N")))
        System.IO.Directory.CreateDirectory directory |> ignore
        let profile = if guest then "RestrictedGuest64" else "EK_RA6M5_HelloBlinky"
        let platform = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../../Fidelity.Platform/Profiles", profile, "Fidelity.Platform.fidproj"))
        System.IO.File.WriteAllText(System.IO.Path.Combine(directory, "Declarations.clef"), declarations)
        System.IO.File.WriteAllText(System.IO.Path.Combine(directory, "Main.clef"), main)
        let project = System.IO.Path.Combine(directory, "Test.fidproj")
        System.IO.File.WriteAllText(project, String.concat "\n" [
            "[package]"; "name=\"DeviceAccessCheck\""; "version=\"0.1.0\""
            "[compilation]"; "target=\"" + (if guest then "cpu" else "mcu") + "\""
            "[platform]"; "runtime_model=\"bare\""; "os=\"none\""; "arch=\"" + (if guest then "x86_64" else "arm_cortex_m33") + "\""
            "[dependencies]"; sprintf "platform={path=%A}" platform
            "[build]"; "sources=[\"Declarations.clef\",\"Main.clef\"]"; "output=\"test.elf\""; "output_kind=\"embedded\"" ])
        Clef.Compiler.CheckExecution.synchronized (fun () -> Clef.Compiler.Project.ProjectChecker.checkProject project)
        |> Result.defaultWith (fun errors -> failwithf "MMIO meet source setup failed: %A" errors)

    let guest =
        lazy (
            check true
                """module DeviceAccessCheck.Declarations
open Fidelity.Platform.Contracts
open Fidelity.Platform.Profiles.RestrictedGuest64
let mapping: DeviceMapping = { Name = "transport-map"; Region = Description.transportRegion; AddressSpace = "cpu-virtual"; Base = Some 8589934592; Lifetime = "image"; Establishment = "boot-contract"; Source = "synthetic boot mapping premise" }
let grant: DeviceGrant = { Name = "transport"; Mapping = mapping; Registers = [| Description.status; Description.control |]; Access = "rw"; Predicates = [||] }
let plan: Expr<DeviceAccessPlan> = <@ { Name = "restricted-guest"; Grants = [| grant |] } @>
"""
                """module DeviceAccessCheck
open DeviceAccessCheck.Declarations
[<EntryPoint>]
let main _ =
    let status = Mmio.bind32 "transport" "status"
    let control = Mmio.bind32 "transport" "control"
    let _ = Mmio.read32 status
    Mmio.write32 control 1
    0
"""
        )

    let raw bits shape value =
        let preparation, argument =
            match shape with
            | "direct" -> "", value
            | "alias" -> "    let value = " + value + "\n", "value"
            | "annotation" -> "", "(" + value + ": int)"
            | _ -> failwith "Unknown MMIO source shape"
        let main =
            String.concat "" [
                "module DeviceAccessCheck\n[<EntryPoint>]\nlet main _ =\n"
                (sprintf "    let handle = Mmio.reg%d 0x40080818\n" bits)
                preparation
                (sprintf "    Mmio.write%d handle %s\n    let _ = Mmio.read%d handle\n    0\n" bits argument bits)
            ]
        check false "module DeviceAccessCheck.Declarations\n" main

    let write (graph: SemanticGraph) =
        let site, access = graph.Codata.Value.Mmio |> Map.toSeq |> Seq.filter (fun (_, row) -> row.Operation.StartsWith "write") |> Assert.Single
        let operand =
            match Mmio.operation graph site with
            | Some(operation, [_; value]) when operation = access.Operation -> value
            | other -> failwithf "MMIO meet fixture lost its exact write arguments: %A" other
        site, operand, access

    let publishedId (Native.NodeId value) = Fidelity.PSG.NodeId value

    let assertMeet site operand bits (rows: Meet list) =
        Assert.True(rows.Length = 1, sprintf "MMIO exact-one meet: %A" rows)
        let row = List.head rows
        Assert.Equal(site, row.Consumer)
        Assert.Equal(operand, row.Operand)
        Assert.Equal(8, row.From)
        Assert.Equal(bits, row.To)
        Assert.Equal(MeetKind.ExtendUnsigned, row.Adapt)

    let healthy graph =
        Numeric.project graph |> Result.defaultWith (sprintf "%A" >> failwith) |> ignore
        Assert.Empty(Numeric.completeness graph)
        PreparedEmission.tryRead graph |> Result.defaultWith failwith |> ignore

    let direct (graph: SemanticGraph) accesses = Meets.deviceAccess graph.Platform graph accesses

    let assertNoMeet label (rows: Map<Native.NodeId, Meet list>) =
        Assert.True(rows.IsEmpty, sprintf "%s unexpectedly emitted Adapt/From/To: %A" label (rows |> Map.toList |> List.collect (snd >> List.map (fun row -> row.Adapt, row.From, row.To))))

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "MmioMeets")>]
type MmioMeetTests() =
    [<Fact>]
    member _.``MMIO guest write preserves exact widening through source selection and publication``() =
        let result = MmioMeetFixture.guest.Value
        let graph = result.CheckResult.Graph
        let site, operand, access = MmioMeetFixture.write graph
        Assert.Equal("write32", access.Operation)
        Assert.Equal(32, access.Bits)
        let beforeRange = graph.Nodes[operand].ValueRange
        Assert.Equal(Some(ValueRange.point 1I), beforeRange)
        MmioMeetFixture.assertMeet site operand 32 (graph.Codata.Value.Meets.TryFind site |> Option.defaultValue [])
        let selected = graph.Codata.Value.WitnessLiveRows.Value
        MmioMeetFixture.assertMeet site operand 32 (selected.Codata.Meets.TryFind site |> Option.defaultValue [])
        Assert.False(hasErrors result.CheckResult, result |> Clef.Compiler.Project.ProjectChecker.getErrorMessages |> String.concat "\n")
        MmioMeetFixture.healthy graph
        let revision = Clef.Compiler.Project.ProjectChecker.publish result |> Result.defaultWith (sprintf "%A" >> failwith)
        let key, value = MmioMeetFixture.publishedId site, MmioMeetFixture.publishedId operand
        let foreign = revision.Foreign.Mmio[key]
        Assert.Equal(key, foreign.Site)
        Assert.Equal(value, foreign.Arguments[1])
        let row = revision.Codata.Meets.TryFind key |> Option.defaultValue [] |> Assert.Single
        Assert.Equal(key, row.Consumer)
        Assert.Equal(value, row.Operand)
        Assert.Equal(8, row.From)
        Assert.Equal(32, row.To)
        Assert.Equal(Fidelity.PSG.MeetKind.ExtendUnsigned, row.Adapt)
        Assert.Equal("write32", revision.Codata.Mmio[key].Operation)
        Assert.Equal(32, revision.Codata.Mmio[key].Bits)
        Assert.Equal(beforeRange, graph.Nodes[operand].ValueRange)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Theory>]
    [<InlineData(8, "direct")>]
    [<InlineData(16, "direct")>]
    [<InlineData(16, "alias")>]
    [<InlineData(16, "annotation")>]
    member _.``MMIO raw source shapes preserve exact transaction operand identity``(bits: int, shape: string) =
        let result = MmioMeetFixture.raw bits shape "1"
        Assert.False(hasErrors result.CheckResult, result |> Clef.Compiler.Project.ProjectChecker.getErrorMessages |> String.concat "\n")
        let graph = result.CheckResult.Graph
        let site, operand, access = MmioMeetFixture.write graph
        Assert.Equal(bits, access.Bits)
        Assert.True(access.Binding.IsNone, "Raw fixture unexpectedly acquired a declaration plan")
        let annotationInner =
            if shape = "annotation" then
                match graph.Nodes[operand].Kind with
                | SemanticKind.TypeAnnotation(inner, _) ->
                    Assert.NotEqual(operand, inner)
                    Assert.True(graph.Nodes[operand].Children = [inner], "Annotation must retain its exact held child")
                    let numeric = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph |> Result.defaultWith (sprintf "%A" >> failwith)
                    let wrapperCarrier = numeric.Values[operand]
                    let innerCarrier = numeric.Values[inner]
                    Assert.True(wrapperCarrier.Slot = innerCarrier.Slot,
                                sprintf "Annotation carrier differs from its held child: %A / %A" wrapperCarrier.Slot innerCarrier.Slot)
                    Some inner
                | other -> failwithf "Annotation fixture lost its held TypeAnnotation occurrence: %A" other
            else None
        let rows = graph.Codata.Value.Meets.TryFind site |> Option.defaultValue []
        if bits = 8 then Assert.Empty rows else MmioMeetFixture.assertMeet site operand bits rows
        MmioMeetFixture.healthy graph
        let revision = Clef.Compiler.Project.ProjectChecker.publish result |> Result.defaultWith (sprintf "%A" >> failwith)
        let key, value = MmioMeetFixture.publishedId site, MmioMeetFixture.publishedId operand
        Assert.Equal(value, revision.Foreign.Mmio[key].Arguments[1])
        let published = revision.Codata.Meets.TryFind key |> Option.defaultValue []
        if bits = 8 then Assert.Empty published
        else
            let row = Assert.Single published
            Assert.Equal(value, row.Operand)
            Assert.Equal(key, row.Consumer)
            Assert.Equal(8, row.From)
            Assert.Equal(bits, row.To)
            Assert.Equal(Fidelity.PSG.MeetKind.ExtendUnsigned, row.Adapt)
            match annotationInner with
            | Some inner ->
                let publishedInner = MmioMeetFixture.publishedId inner
                match revision.Nodes[value].Kind with
                | Fidelity.PSG.SemanticKind.TypeAnnotation(actualInner, _) -> Assert.Equal(publishedInner, actualInner)
                | other -> failwithf "Publication lost the annotation occurrence: %A" other
                Assert.True(revision.Nodes[value].Children = [publishedInner], "Publication changed the held annotation child")
                for occurrence in [value; publishedInner] do
                    match revision.Emission.Callable.ValueShapes.TryFind occurrence with
                    | Some(Fidelity.PSG.CallableValueShape.Data owner) -> Assert.Equal(occurrence, owner)
                    | other -> failwithf "Annotation scalar input lacks its exact published Data shape: %A" other
                let representations = revision.Emission.Numeric.OccurrenceRepresentations
                Assert.True(representations.TryFind value = representations.TryFind publishedInner,
                            "Published annotation representation differs from its held child")
                for occurrence in [value; publishedInner] do
                    match representations.TryFind occurrence with
                    | Some(Ok(Fidelity.PSG.ValueRepresentation.Scalar(Fidelity.PSG.SettledSlot.Integer(width, _)))) ->
                        Assert.Equal(row.From, width)
                    | other -> failwithf "Annotation consumer input is not an exact published integer carrier: %A" other
            | None -> ()
        let nonwrites = graph.Codata.Value.Mmio |> Map.toList |> List.filter (fun (_, row) -> not(row.Operation.StartsWith "write"))
        Assert.Equal(2, nonwrites.Length)
        for id, _ in nonwrites do Assert.Empty(graph.Codata.Value.Meets.TryFind id |> Option.defaultValue [])
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Fact>]
    member _.``MMIO out of range source remains CCS8210 without an adaptation``() =
        let result = MmioMeetFixture.raw 8 "direct" "256"
        Assert.True(hasErrors result.CheckResult)
        let refusal =
            result.CheckResult.Diagnostics
            |> List.exists (fun diagnostic ->
                let effective = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.Diagnostic.effectiveSeverity diagnostic
                diagnostic.Code = "CCS8210"
                && diagnostic.Message = "MMIO write value is not proven within the unsigned register width"
                && effective = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error)
        Assert.True(refusal, result |> Clef.Compiler.Project.ProjectChecker.getErrorMessages |> String.concat "\n")
        let graph = result.CheckResult.Graph
        let site = graph.Nodes.Keys |> Seq.filter (fun id ->
            match Mmio.operation graph id with Some("write8", _) -> graph.Nodes[id].IsReachable | _ -> false) |> Assert.Single
        Assert.False(graph.Codata.Value.Mmio.ContainsKey site)
        Assert.Empty(graph.Codata.Value.Meets.TryFind site |> Option.defaultValue [])

    [<Fact>]
    member _.``MMIO forged wider carrier cannot publish a narrowing meet``() =
        let graph = MmioMeetFixture.guest.Value.CheckResult.Graph
        let site, operand, access = MmioMeetFixture.write graph
        let node = graph.Nodes[operand]
        let kind = NTUKind.NTUuint(NTUWidth.Fixed 64)
        let carrier = mkNTUTypeConRef "uint64" kind (TypeLayout.Inline(8, 8))
        let changed = { graph with Nodes = graph.Nodes.Add(operand, { node with Type = NativeType.TApp(carrier, []) }) }
        Assert.Equal(node.ValueRange, changed.Nodes[operand].ValueRange)
        Assert.Equal(Some 64, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth changed operand)
        Assert.Equal(Mmio.operation graph site, Mmio.operation changed site)
        MmioMeetFixture.direct changed (Map.ofList [site, access]) |> MmioMeetFixture.assertNoMeet "F1 forged wider carrier"

    [<Fact>]
    member _.``MMIO forged negative range cannot publish a signed extension``() =
        let graph = MmioMeetFixture.guest.Value.CheckResult.Graph
        let site, operand, access = MmioMeetFixture.write graph
        let node = graph.Nodes[operand]
        let changed = { graph with Nodes = graph.Nodes.Add(operand, { node with ValueRange = Some(ValueRange.point -1I) }) }
        Assert.Equal(Some 8, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth changed operand)
        Assert.Equal(Some(ValueRange.point -1I), changed.Nodes[operand].ValueRange)
        Assert.Equal(Mmio.operation graph site, Mmio.operation changed site)
        MmioMeetFixture.direct changed (Map.ofList [site, access]) |> MmioMeetFixture.assertNoMeet "F2 forged negative range"

    [<Fact>]
    member _.``MMIO forged nonwrite account cannot authorize source write adaptation``() =
        let graph = MmioMeetFixture.guest.Value.CheckResult.Graph
        let site, operand, access = MmioMeetFixture.write graph
        Assert.Equal(Some 8, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph operand)
        Assert.Equal("write32", access.Operation)
        Assert.Equal(32, access.Bits)
        MmioMeetFixture.direct graph (Map.ofList [site, { access with Operation = "read32" }])
        |> MmioMeetFixture.assertNoMeet "F3 forged nonwrite account"

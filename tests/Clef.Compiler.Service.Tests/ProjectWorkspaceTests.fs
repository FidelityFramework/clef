namespace Clef.Compiler.Service.Tests

open System
open System.IO
open System.Threading
open Xunit
open Clef.Compiler
open Clef.Compiler.Project
open Clef.Compiler.NativeTypedTree.Infrastructure
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.NativeTypedTree.NativeTypes
open Fidelity.FSharp.Incremental.Hosting

type private WorkspaceFiles(?scratchRoot: string) =
    let directory = Path.Combine(defaultArg scratchRoot (Path.GetTempPath()), "clef-workspace-tests-" + Guid.NewGuid().ToString("N"))
    let project = Path.Combine(directory, "App.fidproj")
    let source = Path.Combine(directory, "App.clef")
    do
        Directory.CreateDirectory directory |> ignore
        File.WriteAllText(source, "module App\nlet value = 1\n")
        File.WriteAllText(project, "[package]\nname = \"App\"\n[compilation]\ntarget = \"library\"\n[build]\noutput_kind = \"library\"\nsources = [\"App.clef\"]\n")
    member _.Project = project
    member _.Source = source
    member _.Directory = directory
    interface IDisposable with member _.Dispose() = Directory.Delete(directory, true)

module private WorkspaceCases =
    let need = function Ok value -> value | Error error -> failwithf "%A" error
    let run workflow = Async.RunSynchronously(workflow, timeout = 15000)
    let reserve (workspace: ProjectWorkspace<'T>) = workspace.BeginReserve() |> need |> fun value -> run (value.ObserveAsync()) |> need
    let demand revision inputs (workspace: ProjectWorkspace<'T>) = workspace.BeginDemand(revision, inputs) |> need
    let close (workspace: ProjectWorkspace<'T>) = run (workspace.CloseAsync()) |> need
    let entered (signal: ManualResetEventSlim) = Assert.True(signal.Wait(10000), "The owned checker did not reach its deterministic barrier.")

module private ProjectPolicyCases =
    let files () =
        new WorkspaceFiles(scratchRoot = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/ffi-reconcile-20261013/optional-entry-retirement-20261016/project-policy-tests")))

    let configure (files: WorkspaceFiles) model =
        let policy = if model = "" then "" else "memory_model = \"" + model + "\"\n"
        let text =
            "[package]\nname = \"App\"\n[compilation]\ntarget = \"cpu\"\n" + policy
            + "[build]\noutput_kind = \"library\"\nsources = [\"App.clef\"]\n[platform]\nruntime_model = \"libc\"\n"
        File.WriteAllText(files.Source, "module App\nlet value () = ()\n")
        File.WriteAllText(files.Project, text)
        text

    let digest (text: string) =
        System.Text.Encoding.UTF8.GetBytes text
        |> System.Security.Cryptography.SHA256.HashData
        |> Convert.ToHexString

    let policy (result: ProjectCheckResult) =
        Assert.False(ProjectChecker.hasErrors result, String.concat "\n" (ProjectChecker.getErrorMessages result))
        result.CheckResult.PlatformContext
        |> Option.bind _.ProjectMemoryPolicy
        |> Option.defaultWith (fun () -> failwith "The checked project lost its captured memory policy.")

module private LineageCases =
    let capture (files: WorkspaceFiles) text (workspace: ProjectWorkspace<'T>) =
        let revision = WorkspaceCases.reserve workspace
        let demand = WorkspaceCases.demand revision (Map.ofList [files.Source, text]) workspace
        let result = WorkspaceCases.run (demand.ObserveAsync())
        WorkspaceCases.run (demand.ReleaseAsync()) |> WorkspaceCases.need
        revision, result

    let named name (state: DeclarationLineage) =
        state.Active |> Map.toList |> List.filter (fun (address, _) -> address.Name = name) |> List.exactlyOne

    let key (state: DeclarationLineage) (address, lifetime: DeclarationLifetime) =
        Clef.Compiler.Baker.Ingredients.Obligations.declarationIdentity
            (Guid.Parse state.Epoch) lifetime.BirthRevision address.SourceUnit (address.Owner @ [address.Name])

/// Project-level proof controls reuse the source platform authority and existing
/// workspace capture; they inspect source claims, never manufacture a discharge.
module private LibraryClaimCases =
    let configurePlatform (files: WorkspaceFiles) =
        File.WriteAllText(Path.Combine(files.Directory, "Platform.clef"), SourcePlatformFixture.authority)
        File.WriteAllText(Path.Combine(files.Directory, "Platform.fidproj"),
            "[package]\nname = \"Platform\"\n[compilation]\ntarget = \"cpu\"\n[build]\noutput_kind = \"library\"\nsources = [\"Platform.clef\"]\n[platform]\nruntime_model = \"freestanding\"\ndescription = \"WriteAuthority.description\"\n")
        File.ReadAllText files.Project

    let selectPlatform (files: WorkspaceFiles) projectText supplied =
        File.WriteAllText(files.Project,
            projectText + (if supplied then "[dependencies]\nplatform = { path = \"Platform.fidproj\" }\n" else ""))

    let check (files: WorkspaceFiles) source (workspace: ProjectWorkspace<ProjectCheckResult>) =
        let _, observed = LineageCases.capture files source workspace
        let result = observed |> WorkspaceCases.need
        Assert.False(ProjectChecker.hasErrors result, String.concat "\n" (ProjectChecker.getErrorMessages result))
        Assert.DoesNotContain(result.CheckResult.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8011")
        result.CheckResult.Graph

    let exported name (graph: SemanticGraph) =
        graph.DeclarationRoots |> List.choose (fun (id, purpose) ->
            match purpose, graph.Nodes[id].Kind with
            | DeclRoot.LibraryExport, SemanticKind.Binding(name = actual) when actual = name -> Some graph.Nodes[id]
            | _ -> None) |> Assert.Single

    let carrierClaim (graph: SemanticGraph) (site: SemanticNode) =
        let identity =
            Clef.Compiler.Baker.Ingredients.Obligations.sourceClaimId "numeric-carrier-coverage" site
            |> Option.defaultWith (fun () -> failwith "The checked source site has no canonical carrier claim identity.")
        let claims = graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind = "numeric-carrier-coverage" && info.Id = identity ->
                let incidence = graph.Edges |> List.filter (fun edge ->
                    edge.Target = node.Id && edge.Role = EdgeRole.Constrains && List.contains site.Id edge.Sources)
                let edge = Assert.Single incidence
                Assert.Equal(EdgeClass.Obligation, edge.Class)
                Some info
            | _ -> None) |> Seq.toList
        Assert.Single claims

    let pending (claim: ObligationInfo) =
        match claim.Body with
        | ObligationBody.Pending reasons ->
            Assert.NotEmpty reasons
            match Clef.Compiler.Nanopass.ObligationDischarge.trySmtLib [claim] with
            | Error unavailable -> Assert.Equal<string list>(reasons, (Assert.Single unavailable).MissingPremises)
            | Ok text -> failwithf "Pending source claim produced a solver query: %s" text
        | other -> failwithf "Expected Pending source claim, got %A" other

    let sharedInput graph =
        let declaration = exported "publicApi" graph
        let prefix =
            match declaration.Metadata.TryFind "Source.DeclarationIncarnation" with
            | Some(MetadataValue.String identity) -> identity + "/"
            | _ -> failwith "Exported API lost declaration identity"
        let formal = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind, node.Metadata.TryFind "Source.ObligationSite" with
            | SemanticKind.PatternBinding _, Some(MetadataValue.String site) -> node.IsReachable && site.StartsWith(prefix, StringComparison.Ordinal)
            | _ -> false) |> Assert.Single
        let claim = carrierClaim graph formal
        pending claim
        claim

    let incidence (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target

    let receivingEdit () =
        use files = new WorkspaceFiles(scratchRoot = Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/scratch/issue148-selective-source"))
        let app = "[package]\nname = \"App\"\n[compilation]\ntarget = \"cpu\"\n[build]\noutput_kind = \"console\"\nsources = [\"App.clef\"]\n"
        configurePlatform files |> ignore
        selectPlatform files app true
        let platform = Path.Combine(files.Directory, "Platform.clef")
        File.WriteAllText(platform,
            SourcePlatformFixture.authority.Replace("Representations = [| ",
                "Representations = [| { Name = \"int8\"; Capability = \"native\"; Family = \"int\"; Bits = 8; MinMagnitude = \"-128\"; MaxMagnitude = \"127\"; Boundary = \"wrap\" }; "))
        let source = """
module ReceivingAggregate
type Holder = { Apply: bool -> bool }
type Outer = { Run: Holder -> bool }
let first (value: bool) = value
let run (holder: Holder) = holder.Apply true

[<EntryPoint>]
let main _ =
    let outer = { Run = run }
    if outer.Run { Apply = first } then 12 / 3 else 1
"""
        let comment = source + "// Stable trailing source comment.\n"
        let workspace = ProjectWorkspace<ProjectCheckResult>(files.Project, id)
        let capture (text: string) =
            File.WriteAllText(files.Source, text)
            check files text workspace
        let advance baseline candidate =
            let graph, schedule, recipes =
                Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild.rebuildSelective baseline candidate |> WorkspaceCases.need
            Assert.Empty recipes.Recipes
            graph, schedule
        try
            let initial = capture source
            let unchanged, _ = advance initial (capture comment)
            let previous = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare unchanged |> WorkspaceCases.need
            let candidate = capture (comment.Replace("12 / 3", "12 / 4"))
            let reconciled, schedule = advance previous candidate
            previous, candidate, reconciled, schedule
        finally WorkspaceCases.close workspace

[<CollectionDefinition("ProjectWorkspace", DisableParallelization = true)>]
type ProjectWorkspaceCollection() = class end

[<Collection("ProjectWorkspace"); Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProjectWorkspace")>]
type ProjectWorkspaceTests() =
    [<Fact>]
    member _.``A revised divisor publishes all ordered domain companions and keeps the two startup claim roles``() =
        let _, candidate, graph, _ = LibraryClaimCases.receivingEdit ()
        let ready = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare graph |> WorkspaceCases.need
        Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish ready |> WorkspaceCases.need |> ignore
        let remap id = graph.Codata.Value.SSAAssignment.Value.NodeRemap[id]
        let domainKeys (edge: Hyperedge) =
            match edge.Role with
            | EdgeRole.BoundaryDomain d -> Some (Map.keys d.Premises |> Seq.toList)
            | EdgeRole.MemoryDomain d -> Some (Map.keys d.Premises |> Seq.toList)
            | EdgeRole.NumericDomain d -> Some (Map.keys d.Premises |> Seq.toList)
            | EdgeRole.SpatialModuleDomain d -> Some (Map.keys d.Premises |> Seq.toList)
            | _ -> None
        let domains = candidate.Edges |> List.filter (domainKeys >> Option.isSome)
        Assert.Equal(4, domains.Length)
        for original in domains do
            let target = remap original.Target
            let domain = graph.Edges |> List.filter (fun edge -> edge.Target = target && (domainKeys edge).IsSome) |> Assert.Single
            let expected = (domainKeys domain).Value
            Assert.False(List.map remap original.Sources = expected, "This edit must exercise an actual order change.")
            Assert.Equal<NodeId list>(expected, domain.Sources)
            let companion = graph.Edges |> List.filter (fun edge -> edge.Target = target && edge.Role = EdgeRole.EnrichedWith) |> Assert.Single
            Assert.Equal<NodeId list>(expected, companion.Sources)
            let fault = { graph with Edges = graph.Edges |> List.map (fun edge ->
                                        if LibraryClaimCases.incidence edge = LibraryClaimCases.incidence companion then { edge with Sources = List.head expected :: expected } else edge) }
            match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare fault with
            | Ok _ -> failwithf "Admitted a duplicate in %A's rewrite relation." domain.Class
            | Error failures ->
                let reason =
                    match domain.Role with
                    | EdgeRole.BoundaryDomain _ -> "BoundaryEmission: The ordered boundary relation, adaptation, rewrite record or proof outcome is missing, duplicated or inconsistent."
                    | EdgeRole.NumericDomain _ -> "NumericPublication: The numeric carrier, joint premises, rewrite record or checked coverage obligation is inconsistent."
                    | EdgeRole.MemoryDomain _ -> "MemoryPublication: The memory operation, complete participants or source rewrite record is inconsistent."
                    | EdgeRole.SpatialModuleDomain _ -> "SpatialPublication: The complete spatial plan, participants, proof census or source rewrite record is inconsistent."
                    | _ -> failwith "Expected a source domain."
                Assert.Contains(failures, fun (failure: WitnessProjectionFailure) ->
                    failure.Occurrence = Some target && failure.Reason = reason)
        let plan = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read ready |> Option.get
        let claims = [ for kind, site in ["ProgramEntryCall", plan.EntryCall; "ProgramInitialization", plan.Spine] do
                          let role = "numeric-carrier-coverage/" + kind
                          let carrier = ready.Codata.Value.WitnessEmission.Value.Numeric.Values[site]
                          let target = Assert.Single carrier.Obligations
                          let info = match ready.Nodes[target].Kind with SemanticKind.Obligation ob -> ob | _ -> failwith "Expected a source claim."
                          let issue = Clef.Compiler.Baker.Ingredients.Obligations.sourceClaimId
                          let common = Clef.Compiler.Baker.Ingredients.Obligations.commonSourceClaimId
                          let source = ready.Nodes[plan.SourceBinding]
                          Assert.Equal(Some info.Id, issue role source)
                          let edge = ready.Edges |> List.filter (fun row -> row.Target = target && row.Role = EdgeRole.Constrains) |> Assert.Single
                          Assert.Equal<NodeId list>(Set.toList carrier.Participants, edge.Sources)
                          Assert.True((common role info.Id source).IsSome)
                          Assert.True((common role info.Id ready.Nodes[plan.SourceLambda]).IsNone)
                          Assert.True((common "numeric-carrier-coverage" info.Id source).IsNone)
                          Assert.True((common role (info.Id + "0") source).IsNone)
                          yield info.Id ]
        Assert.Equal(2, (List.distinct claims).Length)

    [<Fact>]
    member _.``A numeric premise remapping onto an unmapped key keeps its duplicate incidence and is refused``() =
        let previous, candidate, current, schedule = LibraryClaimCases.receivingEdit ()
        let plan = current.Codata.Value.SSAAssignment.Value
        let row, domain = candidate.Edges |> List.choose (fun row ->
            match row.Role with EdgeRole.NumericDomain domain -> Some(row, domain) | _ -> None) |> Assert.Single
        let retained =
            schedule.Receipt.Alignment
            |> Map.toSeq
            |> Seq.choose (fun (oldId, candidateId) ->
                if plan.NodeRemap.TryFind candidateId = Some oldId then Some candidateId else None)
            |> Set.ofSeq
        // The fault runs through physical reconciliation, so use that exact
        // allocation plan to choose its unmapped collision coordinate.
        let _, physicalPlan =
            Clef.Compiler.Nanopass.SSAAssignment.reconcileAndAssign previous schedule.Receipt.Alignment retained candidate
            |> WorkspaceCases.need
        let id = domain.Premises.Keys |> Seq.find (fun id -> not (candidate.Nodes.ContainsKey physicalPlan.NodeRemap[id]))
        let collision = physicalPlan.NodeRemap[id]
        let changed = { domain with Premises = domain.Premises.Add(collision, domain.Premises[id]) }
        let domainRow = Clef.Compiler.Baker.Ingredients.NumericValues.domainRow
        let rewrite = Clef.Compiler.Baker.Ingredients.NumericValues.domainRewrite
        let corrupt edge =
            if LibraryClaimCases.incidence edge = LibraryClaimCases.incidence row then domainRow row.Target changed
            elif LibraryClaimCases.incidence edge = LibraryClaimCases.incidence (rewrite row.Target domain) then rewrite row.Target changed
            else edge
        let fault = { candidate with Edges = candidate.Edges |> List.map corrupt }
        let rebuilt, actualPlan =
            match Clef.Compiler.Nanopass.SSAAssignment.reconcileAndAssign previous schedule.Receipt.Alignment retained fault with
            | Result.Ok result -> result
            | Result.Error failure -> failwithf "Expected checked SSA reconciliation: %A" failure
        let actualRemap = actualPlan.NodeRemap
        Assert.Equal(collision, actualRemap[id])
        let actual = rebuilt.Edges |> List.filter (fun edge -> edge.Target = actualRemap[row.Target] &&
                                                               match edge.Role with EdgeRole.NumericDomain _ -> true | _ -> false) |> Assert.Single
        Assert.Equal(2, actual.Sources |> List.filter ((=) collision) |> List.length)
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project rebuilt with
        | Ok _ -> failwith "Admitted the collapsed numeric premise."
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Occurrence = Some actual.Target &&
                                                                     failure.Reason = "NumericPublication: The numeric carrier, joint premises, rewrite record or checked coverage obligation is inconsistent.")

    [<Theory>]
    [<InlineData("windows", "win32", "x86_64-pc-windows-msvc", true)>]
    [<InlineData("windows", "win32", "x86_64-unknown-linux-gnu", false)>]
    [<InlineData("windows", "win32", "x86_64-w64-windows-gnu", false)>]
    [<InlineData("linux", "win32", "x86_64-unknown-linux-gnu", false)>]
    [<InlineData("windows", "libc", "x86_64-pc-windows-msvc", false)>]
    member _.``Windows source core requires the declared Win32 AMD64 ABI``(os: string, runtime: string, triple: string, admitted: bool) =
        use files = new WorkspaceFiles()
        let authority =
            SourcePlatformFixture.authority
                .Replace("Os = \"linux\"", "Os = \"" + os + "\"")
                .Replace("Runtime = \"freestanding\"", "Runtime = \"" + runtime + "\"")
                .Replace("x86_64-unknown-linux-gnu", triple)
                .Replace("Surfaces = [| { Endpoints = [| write |] } |]", "Surfaces = [||]")
        let parse source path =
            match Clef.Compiler.NativeService.parseStringWithDefaults source path with
            | Clef.Compiler.NativeService.ParseSuccess value -> value
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "%A" errors
        let result = Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                        [parse authority "write-authority.clef"; parse "module App\n[<EntryPoint>]\nlet main _ = 37\n" files.Source]
                        (Some SourcePlatformFixture.platform)
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.read result.Graph
        if admitted then
            Assert.Empty reading.Findings
            Assert.Equal(Some RuntimeModel.Win32, reading.Platform |> Option.bind _.Core |> Option.bind Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.runtimeModel)
        else
            Assert.Contains(reading.Findings, fun finding -> finding.Message.Contains("Windows") || finding.Message.Contains("triple"))

    [<Fact>]
    member _.``Win32 runtime is an explicit platform capability distinct from libc``() =
        use files = new WorkspaceFiles()
        File.WriteAllText(files.Project, "[package]\nname=\"WindowsPlatform\"\n[compilation]\ntarget=\"cpu\"\n[build]\noutput_kind=\"library\"\nsources=[\"App.clef\"]\n[platform]\nruntime_model=\"win32\"\nos=\"windows\"\narch=\"x86_64\"\n")
        let platform = FidprojLoader.loadBindingPlatformSection files.Project |> WorkspaceCases.need
        Assert.Equal(RuntimeModel.Win32, platform.RuntimeModel)

    [<Theory>]
    [<InlineData("EK_RA6M5_HelloBlinky", "arm_cortex_m33", "mcu-renesas-ra6m5-ek-ra6m5", "CortexM33")>]
    [<InlineData("STM32H747I_DISCO_HelloDISCO", "arm_cortex_m7", "stm32h747i-disco-hellodisco-internal", "CortexM7")>]
    member _.``Tracked profile aliases retain readable source WordSize declarations``(profile: string, architecture: string, identity: string, cpu: string) =
        let platform = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "../../../Fidelity.Platform/Profiles", profile, "Fidelity.Platform.fidproj"))
        let description = Path.Combine(Path.GetDirectoryName platform, "Description.clef")
        let selected = "Fidelity.Platform.Profiles." + profile + ".Description.descriptor"
        Assert.True(File.Exists platform, "The tracked profile project must exist at its primary-checkout path.")
        use files = new WorkspaceFiles(scratchRoot = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/ffi-reconcile-20261013/consti-profile-wordsize")))
        File.WriteAllText(files.Source, "module App\n[<EntryPoint>]\nlet main _ = 0\n")
        File.WriteAllText(files.Project, String.concat "\n" [
            "[package]"; "name=\"ProfileWordSize\""; "version=\"0.1.0\""
            "[compilation]"; "target=\"mcu\""
            "[platform]"; "runtime_model=\"bare\""; "os=\"none\""; sprintf "arch=%A" architecture
            "[dependencies]"; sprintf "platform={path=%s}" (Fidelity.Data.JSON.Json.serialize (Fidelity.Data.JSON.JsonValue.String platform))
            "[build]"; "sources=[\"App.clef\"]"; "output=\"profile.elf\""; "output_kind=\"embedded\"" ])
        let result = ProjectChecker.checkProject files.Project |> WorkspaceCases.need
        for diagnostic in result.CheckResult.Diagnostics do
            printfn "BP1 profile=%s diagnostic=%A" profile diagnostic
        let graph = result.CheckResult.Graph
        let context = graph.Platform |> Option.defaultWith (fun () -> failwith "The checked profile lost its platform context.")
        Assert.Equal(Some selected, context.PlatformDescription)
        Assert.Contains((Path.GetFullPath description).Replace('\\', '/'), context.PlatformSourcePaths)
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.read graph
        let declared = reading.Platform |> Option.defaultWith (fun () -> failwithf "Selected profile was not read: %A" reading.Findings)
        Assert.Equal(identity, declared.Id)
        let core = declared.Core |> Option.defaultWith (fun () -> failwith "Selected profile has no declared core.")
        let record, fields = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.recordOf graph core.Node |> Option.defaultWith (fun () -> failwith "Selected core is not a record.")
        Assert.Equal(Some "TargetCore", Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.typeName record)
        let _, fieldId = fields |> List.filter (fst >> (=) "WordSizeBits") |> Assert.Single
        let value, path = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.valuePath graph fieldId |> Option.defaultWith (fun () -> failwith "WordSizeBits alias has no source value path.")
        let actual = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.int64Of graph fieldId
        let register = core.Widths |> List.filter (fun width -> width.Name = "Register") |> Assert.Single
        printfn "BP1 profile=%s project=%s selected=%s identity=%s core=%A field=%A path=%A source=%s value=%A kind=%A register=%d findings=%A" profile platform selected declared.Id core.Node fieldId path value.Range.File actual value.Kind register.Bits reading.Findings
        Assert.Equal(Some (int64 register.Bits), actual)
        let suffix = "Hardware/Silicon/CPU/Arm/" + cpu + "/Description.clef"
        Assert.True(value.Range.File.Replace('\\', '/').EndsWith(suffix, StringComparison.Ordinal), sprintf "The effective WordSizeBits value must originate in %s, got %s" suffix value.Range.File)
        Assert.DoesNotContain(reading.Findings, fun finding -> finding.Message.Contains("WordSizeBits", StringComparison.Ordinal) || finding.Message.Contains("CAbi", StringComparison.Ordinal))
        let abiRecords =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.RecordExpr _ -> Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.typeName node = Some "CAbiDescriptor" && context.PlatformSourcePaths.Contains(Path.GetFullPath node.Range.File)
                | _ -> false)
            |> Seq.toList
        printfn "BP1 profile=%s selectedCAbiCount=%d" profile abiRecords.Length
        if abiRecords.IsEmpty then
            Assert.Empty abiRecords
            printfn "BP1 profile=%s no selected CAbi declaration" profile
        for abi in abiRecords do
            let _, abiFields = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.recordOf graph abi.Id |> Option.get
            let field name = abiFields |> List.filter (fst >> (=) name) |> Assert.Single |> snd
            let name = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.stringOf graph (field "Name")
            let pointer = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.int64Of graph (field "PointerBits")
            let registers = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.int64Of graph (field "ScalarAggregateRegisterBytes")
            printfn "BP1 profile=%s CAbi=%A source=%s Name=%A PointerBits=%A ScalarAggregateRegisterBytes=%A" profile abi.Id abi.Range.File name pointer registers
            Assert.True(name.IsSome, sprintf "Selected CAbi %A Name is unreadable." abi.Id)
            for fieldName, value in ["PointerBits", pointer; "ScalarAggregateRegisterBytes", registers] do
                Assert.True(value |> Option.exists (fun value -> value >= int64 Int32.MinValue && value <= int64 Int32.MaxValue), sprintf "Selected CAbi %A %s must be an exact signed32 value, got %A." abi.Id fieldName value)

    [<Fact>]
    member _.``Creation reservation and close perform no project capture or checking``() =
        let missing = Path.Combine(Path.GetTempPath(), Guid.NewGuid().ToString("N"), "Missing.fidproj")
        let workspace = ProjectWorkspace<int>(missing, fun _ -> failwith "Unexpected checking")
        Assert.Equal(0L, workspace.Revision)
        Assert.Equal(1L, WorkspaceCases.reserve workspace)
        Assert.True(workspace.Current.IsNone)
        WorkspaceCases.close workspace

    [<Fact>]
    member _.``Malformed volatile path is typed refusal and leaves the reservation usable``() =
        use files = new WorkspaceFiles()
        let workspace = ProjectWorkspace<_>(files.Project, fun result -> result.SourceFiles)
        try
            let revision = WorkspaceCases.reserve workspace
            match workspace.BeginDemand(revision, Map.ofList ["\u0000", "invalid"]) with
            | Error(ProjectWorkspaceError.CheckFailed _) -> ()
            | other -> failwithf "Malformed input path did not fail closed: %A" other
            Assert.True(workspace.Current.IsNone)
            let valid = WorkspaceCases.demand revision Map.empty workspace
            WorkspaceCases.run (valid.ObserveAsync()) |> WorkspaceCases.need |> Assert.Single |> ignore
            WorkspaceCases.run (valid.ReleaseAsync()) |> WorkspaceCases.need
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Two real workspaces share process ownership through complete projection``() =
        use firstFiles = new WorkspaceFiles()
        use secondFiles = new WorkspaceFiles()
        File.WriteAllText(secondFiles.Source, "module App\nlet value = 2\n")
        use entered = new ManualResetEventSlim()
        use proceed = new ManualResetEventSlim()
        use secondEntered = new ManualResetEventSlim()
        let first = ProjectWorkspace<_>(firstFiles.Project, fun result ->
            entered.Set()
            if not (proceed.Wait(10000)) then failwith "Test barrier was not released."
            result.SourceFiles)
        let second = ProjectWorkspace<_>(secondFiles.Project, fun result ->
            secondEntered.Set()
            result.SourceFiles)
        try
            let firstDemand = WorkspaceCases.demand (WorkspaceCases.reserve first) Map.empty first
            WorkspaceCases.entered entered
            let secondDemand = WorkspaceCases.demand (WorkspaceCases.reserve second) Map.empty second
            // No elapsed delay establishes ordering: the diagnostic proves the
            // second evaluator is requesting the gate already held by the first.
            Assert.True(SpinWait.SpinUntil((fun () -> CheckExecution.waitingCount() > 0), 10000))
            Assert.False(secondEntered.IsSet)
            proceed.Set()
            let firstResult = WorkspaceCases.run (firstDemand.ObserveAsync()) |> WorkspaceCases.need
            let secondResult = WorkspaceCases.run (secondDemand.ObserveAsync()) |> WorkspaceCases.need
            Assert.True(secondEntered.IsSet)
            Assert.Contains("value = 1", firstResult |> List.exactlyOne |> snd)
            Assert.Contains("value = 2", secondResult |> List.exactlyOne |> snd)
            WorkspaceCases.run (firstDemand.ReleaseAsync()) |> WorkspaceCases.need
            WorkspaceCases.run (secondDemand.ReleaseAsync()) |> WorkspaceCases.need
        finally
            proceed.Set()
            WorkspaceCases.close first
            WorkspaceCases.close second

    [<Fact>]
    member _.``Owned capture shares demand permits reservation and remains joined by close``() =
        use files = new WorkspaceFiles()
        use entered = new ManualResetEventSlim()
        use proceed = new ManualResetEventSlim()
        let mutable captures = 0
        let mutable checks = 0
        let prepare path inputs =
            Interlocked.Increment(&captures) |> ignore
            let result = ProjectChecker.prepare path inputs
            entered.Set()
            if not (proceed.Wait(10000)) then failwith "Capture barrier was not released."
            result
        let workspace = ProjectWorkspace<int>(files.Project,
            (fun _ -> Interlocked.Increment(&checks)), PhaseConfig.defaultConfig, prepare)
        try
            let revision = WorkspaceCases.reserve workspace
            let first = WorkspaceCases.demand revision Map.empty workspace
            WorkspaceCases.entered entered
            let second = WorkspaceCases.demand revision Map.empty workspace
            let replacement = workspace.BeginReserve() |> WorkspaceCases.need
            Assert.Equal(revision + 1L, WorkspaceCases.run (replacement.ObserveAsync()) |> WorkspaceCases.need)
            Assert.Equal(1, captures)
            Assert.False(proceed.IsSet)
            Assert.True(workspace.Current.IsNone)
            let closing = workspace.BeginClose()
            Assert.True((AsyncMailbox.tryClose closing).IsNone)
            proceed.Set()
            WorkspaceCases.run (AsyncMailbox.awaitClose closing) |> WorkspaceCases.need
            Assert.Equal(0, checks)
            Assert.Equal<Result<int, _>>(Error ProjectWorkspaceError.Superseded, WorkspaceCases.run (first.ObserveAsync()))
            Assert.Equal<Result<int, _>>(Error ProjectWorkspaceError.Superseded, WorkspaceCases.run (second.ObserveAsync()))
        finally
            proceed.Set()
            WorkspaceCases.close workspace

    [<Fact>]
    member _.``Demand after withdrawal reuses the same generation capture without rereading disk``() =
        use files = new WorkspaceFiles()
        use entered = new ManualResetEventSlim()
        use proceed = new ManualResetEventSlim()
        let mutable captures = 0
        let mutable checks = 0
        let prepare path inputs =
            Interlocked.Increment(&captures) |> ignore
            let result = ProjectChecker.prepare path inputs
            entered.Set()
            if not (proceed.Wait(10000)) then failwith "Capture barrier was not released."
            result
        let workspace = ProjectWorkspace<_>(files.Project,
            (fun result -> Interlocked.Increment(&checks) |> ignore; result.SourceFiles), PhaseConfig.defaultConfig, prepare)
        try
            let revision = WorkspaceCases.reserve workspace
            let first = WorkspaceCases.demand revision Map.empty workspace
            WorkspaceCases.entered entered
            WorkspaceCases.run (first.ReleaseAsync()) |> WorkspaceCases.need
            // An unreserved external edit cannot mutate this generation's
            // already captured semantic inputs. A new generation is required.
            File.WriteAllText(files.Source, "module App\nlet value = 2\n")
            let second = WorkspaceCases.demand revision Map.empty workspace
            proceed.Set()
            let result = WorkspaceCases.run (second.ObserveAsync()) |> WorkspaceCases.need
            Assert.Equal(1, captures)
            Assert.Equal(1, checks)
            Assert.Contains("value = 1", result |> List.exactlyOne |> snd)
            WorkspaceCases.run (second.ReleaseAsync()) |> WorkspaceCases.need
        finally
            proceed.Set()
            WorkspaceCases.close workspace

    [<Fact>]
    member _.``Different texts for normalized source aliases are refused before admission``() =
        use files = new WorkspaceFiles()
        let workspace = ProjectWorkspace<_>(files.Project, fun result -> result.SourceFiles)
        try
            let revision = WorkspaceCases.reserve workspace
            let alias = Path.Combine(files.Directory, ".", "App.clef")
            match workspace.BeginDemand(revision, Map.ofList [files.Source, "first"; alias, "second"]) with
            | Error(ProjectWorkspaceError.CheckFailed message) -> Assert.Contains("Conflicting volatile input aliases", message)
            | other -> failwithf "Ambiguous normalized input was admitted: %A" other
            let demand = WorkspaceCases.demand revision Map.empty workspace
            WorkspaceCases.run (demand.ObserveAsync()) |> WorkspaceCases.need |> Assert.Single |> ignore
            WorkspaceCases.run (demand.ReleaseAsync()) |> WorkspaceCases.need
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Volatile source cannot replace a distinct consumed metadata view``() =
        use files = new WorkspaceFiles()
        File.WriteAllText(files.Project, File.ReadAllText(files.Project).Replace("App.clef", "App.fidproj"))
        let workspace = ProjectWorkspace<int>(files.Project, fun _ -> failwith "Ambiguous capture reached checking")
        try
            let revision = WorkspaceCases.reserve workspace
            let demand = WorkspaceCases.demand revision (Map.ofList [files.Project, "module App\nlet value = 1\n"]) workspace
            match WorkspaceCases.run (demand.ObserveAsync()) with
            | Error(ProjectWorkspaceError.CheckFailed message) -> Assert.Contains("conflicts with captured project metadata", message)
            | other -> failwithf "Ambiguous metadata/source view was accepted: %A" other
            let diagnostics = workspace.DrainDiagnostics()
            Assert.Single(diagnostics) |> ignore
            Assert.Contains("conflicts with captured project metadata", diagnostics.Head.Failure.Message)
            WorkspaceCases.run (demand.ReleaseAsync()) |> WorkspaceCases.need
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Same generation shares a complete check and one withdrawn consumer preserves another``() =
        use files = new WorkspaceFiles()
        use entered = new ManualResetEventSlim()
        use proceed = new ManualResetEventSlim()
        let mutable checks = 0
        let workspace = ProjectWorkspace<_>(files.Project, fun result ->
            Interlocked.Increment(&checks) |> ignore
            entered.Set()
            if not (proceed.Wait(10000)) then failwith "Test barrier was not released."
            result.SourceFiles)
        try
            let revision = WorkspaceCases.reserve workspace
            let first = WorkspaceCases.demand revision Map.empty workspace
            let second = WorkspaceCases.demand revision Map.empty workspace
            WorkspaceCases.entered entered
            WorkspaceCases.run (first.ReleaseAsync()) |> WorkspaceCases.need
            proceed.Set()
            let result = WorkspaceCases.run (second.ObserveAsync()) |> WorkspaceCases.need
            Assert.Equal(1, checks)
            Assert.Equal<string>(File.ReadAllText files.Source, result |> List.exactlyOne |> snd)
            Assert.Equal<Result<_, _>>(Error ProjectWorkspaceError.Released, WorkspaceCases.run (first.ObserveAsync()))
            WorkspaceCases.run (second.ReleaseAsync()) |> WorkspaceCases.need
        finally
            proceed.Set()
            WorkspaceCases.close workspace

    [<Fact>]
    member _.``Cancelling an observer does not withdraw its retained consumer``() =
        use files = new WorkspaceFiles()
        use entered = new ManualResetEventSlim()
        use proceed = new ManualResetEventSlim()
        use cancelled = new CancellationTokenSource()
        let workspace = ProjectWorkspace<_>(files.Project, fun result ->
            entered.Set()
            if not (proceed.Wait(10000)) then failwith "Test barrier was not released."
            result.SourceFiles)
        try
            let revision = WorkspaceCases.reserve workspace
            let demand = WorkspaceCases.demand revision Map.empty workspace
            let observer = Async.StartAsTask(demand.ObserveAsync(), cancellationToken = cancelled.Token)
            WorkspaceCases.entered entered
            cancelled.Cancel()
            Assert.ThrowsAny<OperationCanceledException>(fun () -> observer.WaitAsync(TimeSpan.FromSeconds 10.).GetAwaiter().GetResult() |> ignore) |> ignore
            proceed.Set()
            let result = WorkspaceCases.run (demand.ObserveAsync()) |> WorkspaceCases.need
            Assert.Single(result) |> ignore
            WorkspaceCases.run (demand.ReleaseAsync()) |> WorkspaceCases.need
        finally
            proceed.Set()
            WorkspaceCases.close workspace

    [<Fact>]
    member _.``Backpressure preserves withdrawal slots after observation cancellation and close drains``() =
        use files = new WorkspaceFiles()
        use entered = new ManualResetEventSlim()
        use proceed = new ManualResetEventSlim()
        use cancelled = new CancellationTokenSource()
        let workspace = ProjectWorkspace<int>(files.Project, fun _ ->
            entered.Set()
            if not (proceed.Wait(10000)) then failwith "Test barrier was not released."
            1)
        try
            let revision = WorkspaceCases.reserve workspace
            let first = WorkspaceCases.demand revision Map.empty workspace
            let observer = Async.StartAsTask(first.ObserveAsync(), cancellationToken = cancelled.Token)
            WorkspaceCases.entered entered
            let demands = ResizeArray<ProjectDemand<int>>()
            demands.Add first
            let mutable backpressure = false
            while not backpressure && demands.Count < 256 do
                match workspace.BeginDemand(revision, Map.empty) with
                | Ok demand -> demands.Add demand
                | Error ProjectWorkspaceError.Busy -> backpressure <- true
                | Error error -> failwithf "Unexpected admission error: %A" error
            Assert.True(backpressure)
            cancelled.Cancel()
            Assert.ThrowsAny<OperationCanceledException>(fun () -> observer.WaitAsync(TimeSpan.FromSeconds 10.).GetAwaiter().GetResult() |> ignore) |> ignore
            for demand in demands do WorkspaceCases.run (demand.ReleaseAsync()) |> WorkspaceCases.need
            let closing = workspace.BeginClose()
            Assert.True((AsyncMailbox.tryClose closing).IsNone)
            proceed.Set()
            WorkspaceCases.run (AsyncMailbox.awaitClose closing) |> WorkspaceCases.need
        finally
            proceed.Set()
            WorkspaceCases.close workspace

    [<Fact>]
    member _.``Reservation acknowledges while old checker runs and suppresses its late result``() =
        use files = new WorkspaceFiles()
        use entered = new ManualResetEventSlim()
        use proceed = new ManualResetEventSlim()
        let mutable checks = 0
        let workspace = ProjectWorkspace<_>(files.Project, fun result ->
            if Interlocked.Increment(&checks) = 1 then
                entered.Set()
                if not (proceed.Wait(10000)) then failwith "Test barrier was not released."
            result.SourceFiles)
        try
            let firstRevision = WorkspaceCases.reserve workspace
            let first = WorkspaceCases.demand firstRevision Map.empty workspace
            WorkspaceCases.entered entered
            let reservation = workspace.BeginReserve() |> WorkspaceCases.need
            let currentRevision = WorkspaceCases.run (reservation.ObserveAsync()) |> WorkspaceCases.need
            Assert.Equal(currentRevision, WorkspaceCases.run (reservation.ObserveAsync()) |> WorkspaceCases.need)
            Assert.True(workspace.Current.IsNone)
            File.WriteAllText(files.Source, "module App\nlet value = 2\n")
            let second = WorkspaceCases.demand currentRevision Map.empty workspace
            Assert.Equal<Result<_, _>>(Error ProjectWorkspaceError.Superseded, WorkspaceCases.run (first.ObserveAsync()))
            proceed.Set()
            let result = WorkspaceCases.run (second.ObserveAsync()) |> WorkspaceCases.need
            Assert.Contains("value = 2", result |> List.exactlyOne |> snd)
            Assert.Equal(2, checks)
            WorkspaceCases.run (first.ReleaseAsync()) |> WorkspaceCases.need
            WorkspaceCases.run (second.ReleaseAsync()) |> WorkspaceCases.need
        finally
            proceed.Set()
            WorkspaceCases.close workspace

    [<Fact>]
    member _.``Close joins noninterruptible checking and restores process configuration``() =
        use files = new WorkspaceFiles()
        use entered = new ManualResetEventSlim()
        use proceed = new ManualResetEventSlim()
        let previous = CheckExecution.synchronized PhaseConfig.getConfig
        let workspace = ProjectWorkspace<int>(files.Project, fun _ ->
            entered.Set()
            if not (proceed.Wait(10000)) then failwith "Test barrier was not released."
            failwith "Deliberate projector failure")
        try
            let revision = WorkspaceCases.reserve workspace
            WorkspaceCases.demand revision Map.empty workspace |> ignore
            WorkspaceCases.entered entered
            let closing = workspace.BeginClose()
            Assert.True((AsyncMailbox.tryClose closing).IsNone)
            proceed.Set()
            WorkspaceCases.run (AsyncMailbox.awaitClose closing) |> WorkspaceCases.need
            CheckExecution.synchronized (fun () -> Assert.Equal(previous, PhaseConfig.getConfig()))
            let diagnostics = workspace.DrainDiagnostics()
            Assert.Single(diagnostics) |> ignore
            Assert.Equal("ccs-check", diagnostics.Head.Failure.Code)
            Assert.Equal("Deliberate projector failure", diagnostics.Head.Failure.Message)
            Assert.Empty(workspace.DrainDiagnostics())
        finally
            proceed.Set()
            WorkspaceCases.close workspace

    [<Fact>]
    member _.``Captured metadata and source are the actual checked bytes and conflicting overrides fail``() =
        use files = new WorkspaceFiles()
        let dependency = Path.Combine(files.Directory, "Library.fidproj")
        let dependencySource = Path.Combine(files.Directory, "Library.clef")
        File.WriteAllText(dependencySource, "module Library\nlet value = 3\n")
        File.WriteAllText(dependency, "[package]\nname = \"Library\"\n[compilation]\ntarget = \"library\"\n[build]\noutput_kind = \"library\"\nsources = [\"Library.clef\"]\n[link]\nlibraries = [\"first\"]\n")
        File.AppendAllText(files.Project, "[dependencies]\nlibrary = { path = \"Library.fidproj\" }\n")
        let workspace = ProjectWorkspace<_>(files.Project, fun result -> result.InputFiles, result.SourceFiles, result.Options.LinkedLibraries)
        try
            let revision = WorkspaceCases.reserve workspace
            let source = "module App\nlet value = 4\n"
            let overrides = Map.ofList [files.Source, source]
            let demand = WorkspaceCases.demand revision overrides workspace
            match workspace.BeginDemand(revision, Map.empty) with
            | Error ProjectWorkspaceError.ConflictingInputs -> ()
            | other -> failwithf "Conflicting capture was admitted: %A" other
            let inputs, sources, libraries = WorkspaceCases.run (demand.ObserveAsync()) |> WorkspaceCases.need
            Assert.Equal<string>(source, Map.ofList inputs |> Map.find (files.Source.Replace('\\', '/')))
            Assert.Equal<string>(File.ReadAllText dependency, Map.ofList inputs |> Map.find (dependency.Replace('\\', '/')))
            Assert.Equal<string list>([dependencySource; files.Source] |> List.map (fun path -> path.Replace('\\', '/')), List.map fst sources)
            Assert.Equal<string list>(["first"], libraries)
            WorkspaceCases.run (demand.ReleaseAsync()) |> WorkspaceCases.need
            let next = WorkspaceCases.reserve workspace
            File.WriteAllText(dependency, File.ReadAllText(dependency).Replace("first", "second"))
            let updated = WorkspaceCases.demand next Map.empty workspace
            let _, _, updatedLibraries = WorkspaceCases.run (updated.ObserveAsync()) |> WorkspaceCases.need
            Assert.Equal<string list>(["second"], updatedLibraries)
            WorkspaceCases.run (updated.ReleaseAsync()) |> WorkspaceCases.need
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Malformed project source cannot publish a shortened project or recover old success``() =
        use files = new WorkspaceFiles()
        let workspace = ProjectWorkspace<_>(files.Project, fun result -> ProjectChecker.hasErrors result, result.CheckResult.Graph.Nodes.Count, ProjectChecker.publish result)
        try
            let revision = WorkspaceCases.reserve workspace
            File.WriteAllText(files.Source, "module App\nlet value = (\n")
            let demand = WorkspaceCases.demand revision Map.empty workspace
            let errors, nodes, publication = WorkspaceCases.run (demand.ObserveAsync()) |> WorkspaceCases.need
            Assert.True(errors)
            Assert.Equal(0, nodes)
            Assert.True(Result.isError publication)
            WorkspaceCases.run (demand.ReleaseAsync()) |> WorkspaceCases.need
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Selected platform target comes from the metadata capture used by checking``() =
        use files = new WorkspaceFiles()
        let binding = Path.Combine(files.Directory, "Platform.fidproj")
        File.WriteAllText(Path.Combine(files.Directory, "Platform.clef"), "module Platform\nlet marker = 1\n")
        let metadata = "[package]\nname = \"Platform\"\n[compilation]\ntarget = \"cpu\"\n[build]\noutput_kind = \"library\"\nsources = [\"Platform.clef\"]\n[platform]\nruntime_model = \"libc\"\n"
        File.WriteAllText(binding, metadata)
        File.AppendAllText(files.Project, "[dependencies]\nplatform = { path = \"Platform.fidproj\" }\n")
        let prepared = ProjectChecker.prepare files.Project Map.empty |> WorkspaceCases.need
        File.WriteAllText(binding, metadata.Replace("\"cpu\"", "\"gpu\""))
        let checkedProject = ProjectChecker.checkPrepared prepared
        Assert.Equal<TargetPlatform option>(Some TargetPlatform.CPU, checkedProject.PlatformTarget)
        Assert.Equal<string>(metadata, Map.ofList checkedProject.InputFiles |> Map.find (binding.Replace('\\', '/')))
        let updated = ProjectChecker.checkProject files.Project |> WorkspaceCases.need
        Assert.Equal<TargetPlatform option>(Some TargetPlatform.GPU, updated.PlatformTarget)

    [<Fact>]
    member _.``Declaration lifetime survives changed values and unrelated preceding declarations``() =
        use files = new WorkspaceFiles()
        let workspace = ProjectWorkspace<_>(files.Project, fun result -> result.SourceFiles)
        try
            let firstRevision, firstResult = LineageCases.capture files "module App\nlet value = 42\n" workspace
            firstResult |> WorkspaceCases.need |> ignore
            let first = workspace.DeclarationLineage
            let firstEntry = LineageCases.named "value" first
            let nextRevision, nextResult = LineageCases.capture files "module App\nlet unrelated = 0\n\nlet value = 65536\n" workspace
            nextResult |> WorkspaceCases.need |> ignore
            let next = workspace.DeclarationLineage
            let nextEntry = LineageCases.named "value" next
            Assert.Equal(firstRevision, (snd nextEntry).BirthRevision)
            Assert.Equal(nextRevision, next.Revision)
            Assert.Equal(LineageCases.key first firstEntry, LineageCases.key next nextEntry)
            Assert.Empty(next.Tombstones)
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Complete observed deletion and identical reintroduction retain a tombstone and new birth``() =
        use files = new WorkspaceFiles()
        let workspace = ProjectWorkspace<_>(files.Project, fun result -> result.SourceFiles)
        try
            let _, firstResult = LineageCases.capture files "module App\nlet value = 42\n" workspace
            firstResult |> WorkspaceCases.need |> ignore
            let first = workspace.DeclarationLineage
            let address, lifetime = LineageCases.named "value" first
            let retiredRevision, removed = LineageCases.capture files "module App\nlet other = 0\n" workspace
            removed |> WorkspaceCases.need |> ignore
            let retired = workspace.DeclarationLineage
            Assert.False(retired.Active.ContainsKey address)
            Assert.Equal(Some retiredRevision, retired.Tombstones[address, lifetime.BirthRevision].RetiredAt)
            let birthRevision, restored = LineageCases.capture files "module App\nlet value = 42\n" workspace
            restored |> WorkspaceCases.need |> ignore
            let next = workspace.DeclarationLineage
            let nextEntry = LineageCases.named "value" next
            Assert.Equal(birthRevision, (snd nextEntry).BirthRevision)
            Assert.NotEqual(LineageCases.key first (address, lifetime), LineageCases.key next nextEntry)
            Assert.Equal(Some retiredRevision, next.Tombstones[address, lifetime.BirthRevision].RetiredAt)
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Renamed and moved declarations retire while tuple leaves keep distinct addresses``() =
        use files = new WorkspaceFiles()
        let workspace = ProjectWorkspace<_>(files.Project, fun result -> result.SourceFiles)
        try
            let _, initial = LineageCases.capture files "module App\nlet (left, right) = (1, 2)\n" workspace
            initial |> WorkspaceCases.need |> ignore
            let first = workspace.DeclarationLineage
            let left = LineageCases.named "left" first
            let right = LineageCases.named "right" first
            Assert.NotEqual(LineageCases.key first left, LineageCases.key first right)
            let _, moved = LineageCases.capture files "module Moved\nlet (renamed, right) = (1, 2)\n" workspace
            moved |> WorkspaceCases.need |> ignore
            let next = workspace.DeclarationLineage
            Assert.Equal(2, next.Tombstones.Count)
            Assert.NotEqual(LineageCases.key first right, LineageCases.key next (LineageCases.named "right" next))
            Assert.Equal<string list>(["Moved"], (fst (LineageCases.named "renamed" next)).Owner)
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Malformed parse cannot attest deletion or advance declaration lineage``() =
        use files = new WorkspaceFiles()
        let otherPath = Path.Combine(files.Directory, "Other.clef")
        File.WriteAllText(otherPath, "module Other\nlet dependency = 9\n")
        File.WriteAllText(files.Project,
            File.ReadAllText(files.Project).Replace("[\"App.clef\"]", "[\"Other.clef\", \"App.clef\"]"))
        let workspace = ProjectWorkspace<bool>(files.Project, ProjectChecker.hasErrors)
        try
            let _, initial = LineageCases.capture files "module App\nlet value = 42\n" workspace
            initial |> WorkspaceCases.need |> ignore
            let first = workspace.DeclarationLineage
            // A complete App parse cannot attest absence while another captured
            // unit is malformed; admission covers the entire captured manifest.
            File.WriteAllText(otherPath, "module Other\nlet dependency = (\n")
            let _, malformed = LineageCases.capture files "module App\nlet other = 0\n" workspace
            Assert.True(malformed |> WorkspaceCases.need)
            Assert.Equal(first, workspace.DeclarationLineage)
            File.WriteAllText(otherPath, "module Other\nlet dependency = 9\n")
            let _, restored = LineageCases.capture files "module App\nlet value = 43\n" workspace
            restored |> WorkspaceCases.need |> ignore
            let next = workspace.DeclarationLineage
            Assert.Equal(LineageCases.key first (LineageCases.named "value" first), LineageCases.key next (LineageCases.named "value" next))
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Complete source manifest removal retires the removed unit declarations``() =
        use files = new WorkspaceFiles()
        let removedPath = Path.Combine(files.Directory, "Removed.clef")
        File.WriteAllText(removedPath, "module Removed\nlet dependency = 9\n")
        let originalProject = File.ReadAllText files.Project
        File.WriteAllText(files.Project, originalProject.Replace("[\"App.clef\"]", "[\"Removed.clef\", \"App.clef\"]"))
        let workspace = ProjectWorkspace<_>(files.Project, fun result -> result.SourceFiles)
        try
            let _, initial = LineageCases.capture files "module App\nlet value = 42\n" workspace
            initial |> WorkspaceCases.need |> ignore
            let address, lifetime = LineageCases.named "dependency" workspace.DeclarationLineage
            let revision = WorkspaceCases.reserve workspace
            File.WriteAllText(files.Project, originalProject)
            let demand = WorkspaceCases.demand revision Map.empty workspace
            WorkspaceCases.run (demand.ObserveAsync()) |> WorkspaceCases.need |> ignore
            WorkspaceCases.run (demand.ReleaseAsync()) |> WorkspaceCases.need
            let next = workspace.DeclarationLineage
            Assert.False(next.Active.ContainsKey address)
            Assert.Equal(Some revision, next.Tombstones[address, lifetime.BirthRevision].RetiredAt)
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Superseded complete capture cannot retire declarations from a newer reservation``() =
        use files = new WorkspaceFiles()
        use entered = new ManualResetEventSlim()
        use proceed = new ManualResetEventSlim()
        let mutable captures = 0
        let prepare path overrides =
            let captured = ProjectChecker.prepare path overrides
            if Interlocked.Increment(&captures) = 2 then
                entered.Set()
                if not (proceed.Wait(10000)) then failwith "Capture barrier was not released."
            captured
        let workspace = ProjectWorkspace<_>(files.Project, (fun result -> result.SourceFiles), PhaseConfig.defaultConfig, prepare)
        try
            let _, initial = LineageCases.capture files "module App\nlet value = 42\n" workspace
            initial |> WorkspaceCases.need |> ignore
            let first = workspace.DeclarationLineage
            let stale = WorkspaceCases.demand (WorkspaceCases.reserve workspace) (Map.ofList [files.Source, "module App\nlet other = 0\n"]) workspace
            WorkspaceCases.entered entered
            let current = WorkspaceCases.demand (WorkspaceCases.reserve workspace) (Map.ofList [files.Source, "module App\nlet value = 43\n"]) workspace
            Assert.Equal<Result<_, _>>(Error ProjectWorkspaceError.Superseded, WorkspaceCases.run (stale.ObserveAsync()))
            proceed.Set()
            WorkspaceCases.run (current.ObserveAsync()) |> WorkspaceCases.need |> ignore
            let next = workspace.DeclarationLineage
            Assert.Empty(next.Tombstones)
            Assert.Equal(LineageCases.key first (LineageCases.named "value" first), LineageCases.key next (LineageCases.named "value" next))
            WorkspaceCases.run (stale.ReleaseAsync()) |> WorkspaceCases.need
            WorkspaceCases.run (current.ReleaseAsync()) |> WorkspaceCases.need
        finally
            proceed.Set()
            WorkspaceCases.close workspace

    [<Fact>]
    member _.``Duplicate canonical declarations refuse observation without changing prior lineage``() =
        use files = new WorkspaceFiles()
        let workspace = ProjectWorkspace<_>(files.Project, fun result -> result.SourceFiles)
        try
            let _, initial = LineageCases.capture files "module App\nlet value = 42\n" workspace
            initial |> WorkspaceCases.need |> ignore
            let first = workspace.DeclarationLineage
            let _, duplicate = LineageCases.capture files "module App\nlet value = 42\nlet value = 43\n" workspace
            match duplicate with
            | Error(ProjectWorkspaceError.CheckFailed reason) -> Assert.Contains("duplicate canonical declaration address", reason)
            | other -> failwithf "Duplicate declaration observation was accepted: %A" other
            Assert.Equal(first, workspace.DeclarationLineage)
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Cold workspaces never inherit a prior declaration incarnation``() =
        use files = new WorkspaceFiles()
        let first = ProjectWorkspace<_>(files.Project, fun result -> result.SourceFiles)
        let second = ProjectWorkspace<_>(files.Project, fun result -> result.SourceFiles)
        try
            let _, one = LineageCases.capture files "module App\nlet value = 42\n" first
            let _, two = LineageCases.capture files "module App\nlet value = 42\n" second
            one |> WorkspaceCases.need |> ignore
            two |> WorkspaceCases.need |> ignore
            let a, b = first.DeclarationLineage, second.DeclarationLineage
            Assert.NotEqual(a.Epoch, b.Epoch)
            Assert.NotEqual(LineageCases.key a (LineageCases.named "value" a), LineageCases.key b (LineageCases.named "value" b))
            Assert.Empty(b.Tombstones)
        finally
            WorkspaceCases.close first
            WorkspaceCases.close second

    [<Fact>]
    member _.``Retained value claim returns Pending after platform withdrawal while shared input stays open``() =
        use files = new WorkspaceFiles()
        let projectText = LibraryClaimCases.configurePlatform files
        let source = "module App\nlet publicValue = 42\nlet publicApi (x: int) = x\nlet internalCaller = publicApi 3\n"
        let workspace = ProjectWorkspace<ProjectCheckResult>(files.Project, id)
        try
            let first = LibraryClaimCases.check files source workspace
            let pending = LibraryClaimCases.carrierClaim first (LibraryClaimCases.exported "publicValue" first)
            LibraryClaimCases.pending pending
            let input = LibraryClaimCases.sharedInput first
            LibraryClaimCases.selectPlatform files projectText true
            let selected = LibraryClaimCases.check files source workspace
            let ready = LibraryClaimCases.carrierClaim selected (LibraryClaimCases.exported "publicValue" selected)
            Assert.Equal(pending.Id, ready.Id)
            Assert.Equal(ObligationBody.IntegerRepresentationCoverage(42I, 42I, 0I, 255I), ready.Body)
            Assert.Equal(input.Id, (LibraryClaimCases.sharedInput selected).Id)
            // A concrete source body is ready; no solver has discharged it.
            LibraryClaimCases.selectPlatform files projectText false
            let withdrawn = LibraryClaimCases.check files source workspace
            let again = LibraryClaimCases.carrierClaim withdrawn (LibraryClaimCases.exported "publicValue" withdrawn)
            Assert.Equal(ready.Id, again.Id)
            LibraryClaimCases.pending again
            Assert.Equal(input.Id, (LibraryClaimCases.sharedInput withdrawn).Id)
            Assert.True(Result.isError(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish withdrawn))
        finally WorkspaceCases.close workspace

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Selected platform does not infer library startup or admit an explicit entry conflict``(explicitEntry: bool) =
        use files = new WorkspaceFiles()
        let projectText = LibraryClaimCases.configurePlatform files
        LibraryClaimCases.selectPlatform files projectText true
        let workspace = ProjectWorkspace<ProjectCheckResult>(files.Project, id)
        let declaration = if explicitEntry then "[<EntryPoint>]\nlet start _ = 0\n" else "let main _ = 0\n"
        try
            let _, observed = LineageCases.capture files ("module App\nlet publicValue = 42\n" + declaration) workspace
            let result = observed |> WorkspaceCases.need
            let graph = result.CheckResult.Graph
            Assert.True(graph.Platform.IsSome)
            let exported = LibraryClaimCases.exported (if explicitEntry then "start" else "main") graph
            let conflicts = result.CheckResult.Diagnostics |> List.filter (fun diagnostic -> diagnostic.Code = "CCS8417")
            if explicitEntry then
                let conflict = Assert.Single conflicts
                Assert.Equal("An explicit EntryPoint declaration is not permitted in library output.", conflict.Message)
                Assert.Equal(Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error, conflict.Severity)
                Assert.Contains(exported.Id, conflict.RelatedNodes)
                Assert.Contains(graph.DeclarationRoots, fun (id, purpose) ->
                    purpose = DeclRoot.EntryPoint
                    && (id = exported.Id
                        || match graph.Nodes[id].Kind with
                           | SemanticKind.ModuleDef(_, members) -> List.contains exported.Id members
                           | _ -> false))
            else
                DimensionalCases.noErrors result.CheckResult
                Assert.Empty conflicts
                Assert.DoesNotContain(graph.DeclarationRoots, fun (_, purpose) -> purpose = DeclRoot.EntryPoint)
                let contracts = graph.Codata.Value.CallableContracts.Values |> Seq.toList
                Assert.DoesNotContain(contracts, fun contract -> contract.Kind = CallableKind.NativeEntry)
            Assert.DoesNotContain(graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Binding(name = "_start") -> true | _ -> false)
            Assert.True(Result.isError(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph))
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Ready division claim identities follow concrete bodies and refuse an incomplete association``() =
        use files = new WorkspaceFiles()
        let projectText = LibraryClaimCases.configurePlatform files
        LibraryClaimCases.selectPlatform files projectText true
        let workspace = ProjectWorkspace<ProjectCheckResult>(files.Project, id)
        try
            let graph = LibraryClaimCases.check files "module App\nlet quotient = 12 / 3\n" workspace
            let operation, recipe =
                graph.Nodes.Values
                |> Seq.choose (fun node ->
                    match Clef.Compiler.Baker.Ingredients.NumericOperations.operation graph node with
                    | Some(_, NumericOperationKind.Divide, [_; _], _) as recipe -> Some(node, Option.get recipe)
                    | _ -> None)
                |> Assert.Single
            let claim ordinal role =
                let key = Clef.Compiler.Baker.Ingredients.NumericOperations.claimId operation ordinal role
                graph.Nodes.Values |> Seq.choose (fun node ->
                    match node.Kind with
                    | SemanticKind.Obligation info when info.Id = key && info.Kind = "numeric-operation-proof" -> Some info
                    | _ -> None) |> Assert.Single
            let coverage = claim 0 "numeric-operation-coverage"
            let divisor = claim 1 "numeric-operation-divisor-nonzero"
            match coverage.Body, divisor.Body with
            | ObligationBody.IntegerRepresentationCoverage _, ObligationBody.IntegerDivisorNonzero(lo, hi) when lo = 3I && hi = 3I -> ()
            | bodies -> failwithf "Division semantic claim roles do not match their concrete proof bodies: %A" bodies
            let associate = Clef.Compiler.Baker.Ingredients.NumericOperations.associateBodies graph recipe
            let expected = Some ["numeric-operation-coverage", coverage.Body; "numeric-operation-divisor-nonzero", divisor.Body]
            Assert.Equal<(string * ObligationBody) list option>(expected, associate [coverage.Body; divisor.Body])
            Assert.Equal<(string * ObligationBody) list option>(expected, associate [divisor.Body; coverage.Body])
            Assert.True((associate [coverage.Body]).IsNone)
            Assert.True((associate [coverage.Body; coverage.Body]).IsNone)
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Source carrier claim survives unrelated edits and changed width but not observed recreation``() =
        use files = new WorkspaceFiles()
        let projectText = LibraryClaimCases.configurePlatform files
        LibraryClaimCases.selectPlatform files projectText true
        let workspace = ProjectWorkspace<ProjectCheckResult>(files.Project, id)
        let source prefix value = "module App\n" + prefix + "let publicValue = " + value + "\n"
        let claim text =
            let graph = LibraryClaimCases.check files text workspace
            LibraryClaimCases.carrierClaim graph (LibraryClaimCases.exported "publicValue" graph)
        try
            let first = claim (source "" "42")
            let unchanged = claim (source "" "42")
            Assert.Equal(first.Id, unchanged.Id)
            Assert.Equal(first.Body, unchanged.Body)
            let unrelated = claim (source "let unrelated = true\n\n" "42")
            Assert.Equal(first.Id, unrelated.Id)
            Assert.Equal(first.Body, unrelated.Body)
            let changed = claim (source "let unrelated = true\n\n" "65536")
            Assert.Equal(first.Id, changed.Id)
            Assert.NotEqual(first.Body, changed.Body)
            let removed = LibraryClaimCases.check files "module App\nlet unrelated = true\n" workspace
            Assert.DoesNotContain(removed.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Obligation info -> info.Id = first.Id | _ -> false)
            let recreated = claim (source "" "42")
            Assert.NotEqual(first.Id, recreated.Id)
            Assert.Equal(first.Body, recreated.Body)
        finally WorkspaceCases.close workspace

    [<Fact>]
    member _.``Concrete kernel preparation retains every Pending claim from a public library API``() =
        // The source kernel authority follows the established Composer fixture;
        // neither root nor obligation is inserted into an already checked graph.
        let authority = """namespace Fidelity.Platform.Contracts
type KernelTarget = { Device: string; Columns: int; ShimRow: int; ComputeRow: int; FifoDepth: int; Iterations: int; Inputs: string array; Result: string }
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Capability: string; Family: string; Bits: int; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Arch: string; Runtime: string; Widths: WidthDeclaration array; Representations: Representation array }
type PlatformDescription = { Id: string; Core: TargetCore option }
module KernelAuthority =
    let target: KernelTarget = { Device="npu2"; Columns=8; ShimRow=0; ComputeRow=2; FifoDepth=2; Iterations=1; Inputs=[|"int16";"int16"|]; Result="int32" }
    let description: PlatformDescription = {
        Id="kernel-witness"
        Core=Some {
            Arch="xdna2"; Runtime="xdna"
            Widths=[| {Name="Pointer";Bits=32}; {Name="Register";Bits=16} |]
            Representations=[|
                {Name="int16";Capability="native";Family="int";Bits=16;MinMagnitude="-32768";MaxMagnitude="32767";Boundary="wrap"}
                {Name="uint16";Capability="native";Family="uint";Bits=16;MinMagnitude="0";MaxMagnitude="65535";Boundary="wrap"}
                {Name="int32";Capability="native";Family="int";Bits=32;MinMagnitude="-2147483648";MaxMagnitude="2147483647";Boundary="wrap"}
                {Name="uint32";Capability="native";Family="uint";Bits=32;MinMagnitude="0";MaxMagnitude="4294967295";Boundary="wrap"} |] } }
"""
        let kernel = """module KernelComputation
type Shape = { Elements: int; Grain: int }
type ElementKernel = { Compute: int -> int -> int; Shape: Shape }
let calculate (left: int) (right: int) = left * right
[<KernelModule>]
let kernel: ElementKernel = { Compute=calculate; Shape={Elements=64;Grain=16} }
"""
        let representation name family bits minimum maximum : NumericRepresentation =
            { Name = name; Family = family; Bits = bits; Capability = "native"
              MinMagnitude = minimum; MaxMagnitude = maximum; Boundary = "wrap" }
        let representations =
            [ representation "int16" "int" 16 "-32768" "32767"
              representation "uint16" "uint" 16 "0" "65535"
              representation "int32" "int" 32 "-2147483648" "2147483647"
              representation "uint32" "uint" 32 "0" "4294967295" ]
        let context =
            { SourcePlatformFixture.platform with
                PlatformId = "kernel-witness"; Dimensions = Map.ofList ["Pointer", 32; "Register", 16]
                Representations = representations |> List.map (fun value -> value.Name, value) |> Map.ofList
                PlatformDescription = Some "Fidelity.Platform.Contracts.KernelAuthority.description"
                PlatformArchitecture = Some "xdna2"; SubstrateKind = Some SubstrateKind.NPU
                RuntimeModel = Some RuntimeModel.XDNA
                PlatformSourcePaths = Set.singleton(Path.GetFullPath "mixed-kernel-authority.clef") }
        let parse path source =
            match NativeService.parseStringWithDefaults source path with
            | NativeService.ParseSuccess input -> input
            | NativeService.ParseError errors -> failwithf "Mixed-root source failed to parse: %A" errors
        let libraryPath = Path.GetFullPath "mixed-library.clef"
        let result =
            NativeService.checkParsedInputsWithDeclarations
                [ parse "mixed-kernel-authority.clef" authority
                  parse "mixed-kernel.clef" kernel
                  parse libraryPath "module Library\nlet publicApi (x: int) = x\n" ]
                (Some context) Set.empty (Some(Set.singleton libraryPath)) None
        let graph = result.Graph
        let api = LibraryClaimCases.exported "publicApi" graph
        Assert.True(api.IsReachable)
        let kernelId =
            graph.DeclarationRoots |> List.choose (fun (id, purpose) ->
                if purpose = DeclRoot.KernelModule then Some id else None) |> Assert.Single
        Assert.True(graph.Nodes[kernelId].IsReachable)
        Assert.DoesNotContain(graph.DeclarationRoots, fun (_, purpose) -> purpose = DeclRoot.EntryPoint)
        let input = LibraryClaimCases.sharedInput graph
        let pending = graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info ->
                match info.Body with ObligationBody.Pending _ -> Some info | _ -> None
            | _ -> None) |> Seq.toList
        Assert.Contains(pending, fun claim -> claim.Id = input.Id)
        // The producer must report the same strict refusal as an explicit
        // whole-graph prepare; retention is not permission to omit these claims.
        match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare graph with
        | Ok _ -> failwith "Mixed concrete and retained roots admitted a Pending public input."
        | Error failures ->
            for claim in pending do
                Assert.Contains(failures, fun failure -> failure.Reason.Contains(claim.Id, StringComparison.Ordinal))
                Assert.Contains(result.Diagnostics, fun diagnostic ->
                    diagnostic.Code = "CCS8403"
                    && diagnostic.Severity = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error
                    && diagnostic.Message.Contains(claim.Id, StringComparison.Ordinal))

    [<Theory>]
    [<InlineData("standard", "Standard", true)>]
    [<InlineData("stack_only", "StackOnly", false)>]
    [<InlineData("static_pools", "StaticPools", false)>]
    [<InlineData("arena", "Arena", false)>]
    [<InlineData("", "StackOnly", false)>]
    member _.``Project allocation permission follows its parsed memory policy``(model, expectedName, expectedHeap) =
        use files = ProjectPolicyCases.files()
        let text = ProjectPolicyCases.configure files model
        let result = ProjectChecker.checkProject files.Project |> WorkspaceCases.need
        let path, version, name, heap = ProjectPolicyCases.policy result
        Assert.Equal(Path.GetFullPath(files.Project).Replace('\\', '/'), path)
        Assert.Equal(ProjectPolicyCases.digest text, version)
        Assert.Equal(expectedName, name)
        Assert.Equal(expectedHeap, heap)

    [<Fact>]
    member _.``Captured project policy survives a later disk edit without rereading it``() =
        use files = ProjectPolicyCases.files()
        let captured = ProjectPolicyCases.configure files "standard"
        let prepared = ProjectChecker.prepare files.Project Map.empty |> WorkspaceCases.need
        let changed = ProjectPolicyCases.configure files "stack_only"
        let oldResult = ProjectChecker.checkPrepared prepared
        let path, oldVersion, oldName, oldHeap = ProjectPolicyCases.policy oldResult
        Assert.Equal(Path.GetFullPath(files.Project).Replace('\\', '/'), path)
        Assert.Equal(ProjectPolicyCases.digest captured, oldVersion)
        Assert.Equal("Standard", oldName)
        Assert.True(oldHeap)
        let newResult = ProjectChecker.checkProject files.Project |> WorkspaceCases.need
        let newPath, newVersion, newName, newHeap = ProjectPolicyCases.policy newResult
        Assert.Equal(path, newPath)
        Assert.Equal(ProjectPolicyCases.digest changed, newVersion)
        Assert.NotEqual(oldVersion, newVersion)
        Assert.Equal("StackOnly", newName)
        Assert.False(newHeap)

    [<Fact>]
    member _.``Project phase sink records reached phases without changing checked results``() =
        use files = new WorkspaceFiles()
        let quiet = ProjectChecker.checkProject files.Project |> WorkspaceCases.need
        let observed = ResizeArray<NativeService.CheckPhaseEvent>()
        let checkedProject = ProjectChecker.checkProjectWithPhaseSink observed.Add files.Project |> WorkspaceCases.need

        let completed phase outcome =
            [ NativeService.CheckPhaseEvent.PhaseStarted phase
              NativeService.CheckPhaseEvent.PhaseCompleted(phase, outcome) ]
        let expected =
            [ yield! completed NativeService.CheckPhase.ProgramStorage NativeService.CheckPhaseOutcome.Completed
              yield! completed NativeService.CheckPhase.MemoryAndBoundarySettlement NativeService.CheckPhaseOutcome.Completed
              yield! completed NativeService.CheckPhase.FinalGraphReadiness NativeService.CheckPhaseOutcome.Completed
              yield! completed NativeService.CheckPhase.ObligationPublication NativeService.CheckPhaseOutcome.Accepted ]
        Assert.Equal<NativeService.CheckPhaseEvent list>(expected, List.ofSeq observed)
        Assert.False(ProjectChecker.hasErrors checkedProject, String.concat "\n" (ProjectChecker.getErrorMessages checkedProject))
        Assert.True(quiet.InputFiles = checkedProject.InputFiles)
        Assert.True(quiet.ParseErrors = checkedProject.ParseErrors)
        Assert.True(quiet.CheckResult.Diagnostics = checkedProject.CheckResult.Diagnostics)

        let graphFacts (project: ProjectCheckResult) =
            let graph = project.CheckResult.Graph
            let anchor id = (Map.find id graph.Nodes).Range
            let nodes =
                graph.Nodes |> Map.toList |> List.map (fun (_, node) ->
                    let kind =
                        match node.Kind with
                        | SemanticKind.Obligation claim ->
                            // Independent cold checks mint distinct declaration and claim identities.
                            Choice1Of2 (claim.Kind, claim.Logic, claim.Statement, claim.Source, claim.Refs, claim.Body)
                        | kind -> Choice2Of2 kind
                    node.Range, node.Type, node.IsReachable, kind)
            let roots = graph.DeclarationRoots |> List.map (fun (id, role) -> anchor id, role)
            let incidence =
                graph.Edges |> List.map (fun edge -> edge.Class, edge.Ordinal, List.map anchor edge.Sources, anchor edge.Target)
            roots, nodes, incidence
        Assert.False(Map.isEmpty quiet.CheckResult.Graph.Nodes)
        Assert.True(graphFacts quiet = graphFacts checkedProject)

    [<Fact>]
    member _.``clef #197: production reconcileAndAssignWithCallableRelations matches cold compile and preserves NumericDomain and SpatialModuleDomain companions under non-monotone remap``() =
        // 1. Production entry point (Rebuild.rebuildSelective -> SSAAssignment.reconcileAndAssignWithCallableRelations)
        //    vs fresh cold compile of the exact edited source.
        let previous, coldEdited, warmReconciled, _ = LibraryClaimCases.receivingEdit ()
        let warmPlan =
            warmReconciled.Codata.Value.SSAAssignment
            |> Option.defaultWith (fun () -> failwith "Expected SSAAssignment plan on warm reconciled graph.")
        Assert.NotEmpty warmPlan.ReassignedNodes
        let prevHighWater = previous.Codata.Value.SSAAssignment.Value.NodeHighWater
        Assert.True(warmPlan.NodeHighWater > prevHighWater)
        Assert.True(warmPlan.NodeRemap |> Map.exists (fun _ mapped -> NodeId.value mapped <= prevHighWater && previous.Nodes.ContainsKey mapped),
                    "Expected production reconciliation to retain unchanged baseline NodeIds.")
        Assert.True(warmPlan.NodeRemap |> Map.exists (fun _ mapped -> NodeId.value mapped > prevHighWater),
                    "Expected production reconciliation to advance reassigned NodeIds above baseline high-water.")
        // Assert actual non-monotone order inversion on the production reconcileAndAssignWithCallableRelations path
        // across all 4 domain edges (BoundaryDomain, MemoryDomain, NumericDomain, SpatialModuleDomain).
        let prodRemap id = warmPlan.NodeRemap[id]
        let domainPremiseKeys (edge: Hyperedge) =
            match edge.Role with
            | EdgeRole.BoundaryDomain d -> Some (Map.keys d.Premises |> Seq.toList)
            | EdgeRole.MemoryDomain d -> Some (Map.keys d.Premises |> Seq.toList)
            | EdgeRole.NumericDomain d -> Some (Map.keys d.Premises |> Seq.toList)
            | EdgeRole.SpatialModuleDomain d -> Some (Map.keys d.Premises |> Seq.toList)
            | _ -> None
        let coldDomains = coldEdited.Edges |> List.filter (domainPremiseKeys >> Option.isSome)
        Assert.Equal(4, coldDomains.Length)
        for original in coldDomains do
            let target = prodRemap original.Target
            let warmDomain = warmReconciled.Edges |> List.filter (fun e -> e.Target = target && (domainPremiseKeys e).IsSome) |> Assert.Single
            let expected = (domainPremiseKeys warmDomain).Value
            Assert.False(List.map prodRemap original.Sources = expected, "Production selective rebuild must exercise actual non-monotone inversion.")
            Assert.Equal<NodeId list>(expected, warmDomain.Sources)

        let warmPrepared = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare warmReconciled |> WorkspaceCases.need
        let warmRev = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish warmPrepared |> WorkspaceCases.need
        let warmDefects = Fidelity.PSG.Integrity.check warmRev
        Assert.True(warmDefects.IsEmpty, Fidelity.PSG.Integrity.describe warmDefects)

        let coldPrepared = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare coldEdited |> WorkspaceCases.need
        let coldRev = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish coldPrepared |> WorkspaceCases.need
        let coldDefects = Fidelity.PSG.Integrity.check coldRev
        Assert.True(coldDefects.IsEmpty, Fidelity.PSG.Integrity.describe coldDefects)

        // Structural cold-vs-warm published revision & boundary/premise parity (identity-independent, not counts only).
        let graphPremiseSummary (g: SemanticGraph) =
            let rangeOf id = g.Nodes.TryFind id |> Option.map _.Range
            let boundaryDomain = g.Edges |> List.pick (fun e -> match e.Role with EdgeRole.BoundaryDomain d -> Some d | _ -> None)
            let boundaryLists =
                [ boundaryDomain.WritableBufferDeclarations |> List.map rangeOf |> List.sort
                  boundaryDomain.WritableBufferUses |> List.map (fst >> rangeOf) |> List.sort
                  boundaryDomain.ReadOnlyBufferDeclarations |> List.map rangeOf |> List.sort
                  boundaryDomain.ReadOnlyBufferUses |> List.map (fst >> rangeOf) |> List.sort
                  boundaryDomain.BorrowedResultViewDeclarations |> List.map rangeOf |> List.sort
                  boundaryDomain.BorrowedResultViewUses |> List.map rangeOf |> List.sort
                  boundaryDomain.BufferAbsences |> List.map rangeOf |> List.sort
                  boundaryDomain.CountedEntryArrays |> List.map rangeOf |> List.sort
                  boundaryDomain.ResourceDeclarations |> List.map rangeOf |> List.sort
                  boundaryDomain.ResourceAccesses |> List.map rangeOf |> List.sort
                  boundaryDomain.Imports |> List.map rangeOf |> List.sort
                  boundaryDomain.Calls |> List.map rangeOf |> List.sort
                  boundaryDomain.Entries |> List.map rangeOf |> List.sort
                  boundaryDomain.CallbackInvocations |> List.map rangeOf |> List.sort
                  boundaryDomain.CallbackAbsences |> List.map rangeOf |> List.sort
                  boundaryDomain.ClosedEntries |> List.map rangeOf |> List.sort ]
            let obligationPremises =
                g.Nodes.Values
                |> Seq.choose (fun n ->
                    match n.Kind with
                    | SemanticKind.Obligation ob -> Some (n.Range, ob.Kind, ob.Logic, ob.Statement, ob.Body)
                    | _ -> None)
                |> Seq.sort
                |> Seq.toList
            let contractSummaries =
                g.Codata.Value.CallableContracts.Values
                |> Seq.map (fun c ->
                    let sourceRanges =
                        c.Participants
                        |> List.filter (fun p -> p.Role = ParticipantRole.Source)
                        |> List.map (fun p -> rangeOf p.Node)
                        |> List.sort
                    c.Kind, c.Convention, sourceRanges)
                |> Seq.sort
                |> Seq.toList
            boundaryLists, obligationPremises, contractSummaries
        let revisionSummary (rev: Fidelity.PSG.Revision) =
            let claims =
                rev.CurrentClaims.Values
                |> Seq.map (fun c -> c.Kind, c.Logic, c.Statement)
                |> Seq.sort
                |> Seq.toList
            let carriers =
                rev.Emission.Numeric.Values.Values
                |> Seq.map (fun v -> v.Slot, v.Range)
                |> Seq.sort
                |> Seq.toList
            let operations =
                rev.Emission.Numeric.Operations.Values
                |> Seq.map (fun o -> o.Kind, o.Form, o.OperationCarrier, o.Result.Slot)
                |> Seq.sort
                |> Seq.toList
            let imports = rev.Emission.Boundary.Imports.Values |> Seq.map (fun (i: Fidelity.PSG.BoundaryImport) -> i.Symbol, i.Library) |> Seq.sort |> Seq.toList
            let calls = rev.Emission.Boundary.Calls.Values |> Seq.map (fun (c: Fidelity.PSG.BoundaryCall) -> c.Arguments.Length, c.Participants.Count) |> Seq.sort |> Seq.toList
            let kernels = rev.Emission.Spatial.Kernels.Values |> Seq.map (fun (k: Fidelity.PSG.KernelModuleWitness) -> k.Name) |> Seq.sort |> Seq.toList
            claims, carriers, operations, imports, calls, kernels
        Assert.Equal(revisionSummary coldRev, revisionSummary warmRev)
        Assert.Equal(graphPremiseSummary coldPrepared, graphPremiseSummary warmPrepared)

        // Exact-reason fault-injection on production warmReconciled: reversing BoundaryDomain EnrichedWith Sources is refused.
        let prodBoundaryTarget =
            warmReconciled.Edges |> List.pick (fun e -> match e.Role with EdgeRole.BoundaryDomain _ -> Some e.Target | _ -> None)
        let mutable flippedProdBoundary = false
        let faultedProdEdges =
            warmReconciled.Edges |> List.map (fun e ->
                if not flippedProdBoundary && e.Target = prodBoundaryTarget && e.Role = EdgeRole.EnrichedWith && e.Sources.Length >= 2 then
                    flippedProdBoundary <- true
                    { e with Sources = List.rev e.Sources }
                else e)
        Assert.True(flippedProdBoundary, "Expected to flip production BoundaryDomain EnrichedWith edge.")
        match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare { warmReconciled with Edges = faultedProdEdges } with
        | Result.Ok _ -> failwith "Reversed production BoundaryDomain EnrichedWith edge was admitted."
        | Result.Error failures ->
            Assert.Contains(failures, fun f ->
                f.Reason = "BoundaryEmission: The ordered boundary relation, adaptation, rewrite record or proof outcome is missing, duplicated or inconsistent.")

        // 2. Non-monotone SSA remap on live NumericDomain + SpatialModuleDomain (2 KernelModule roots)
        //    with unconditional inversion, clean prepare/publish/Integrity.check, and companion Sources-reversal negatives.
        let authority = """namespace Fidelity.Platform.Contracts
type KernelTarget = { Device: string; Columns: int; ShimRow: int; ComputeRow: int; FifoDepth: int; Iterations: int; Inputs: string array; Result: string }
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Capability: string; Family: string; Bits: int; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Arch: string; Runtime: string; Widths: WidthDeclaration array; Representations: Representation array }
type PlatformDescription = { Id: string; Core: TargetCore option }
module KernelAuthority =
    let target: KernelTarget = { Device="npu2"; Columns=8; ShimRow=0; ComputeRow=2; FifoDepth=2; Iterations=1; Inputs=[|"int16";"int16"|]; Result="int32" }
    let description: PlatformDescription = {
        Id="kernel-witness-clef197"
        Core=Some {
            Arch="xdna2"; Runtime="xdna"
            Widths=[| {Name="Pointer";Bits=32}; {Name="Register";Bits=16} |]
            Representations=[|
                {Name="int16";Capability="native";Family="int";Bits=16;MinMagnitude="-32768";MaxMagnitude="32767";Boundary="wrap"}
                {Name="uint16";Capability="native";Family="uint";Bits=16;MinMagnitude="0";MaxMagnitude="65535";Boundary="wrap"}
                {Name="int32";Capability="native";Family="int";Bits=32;MinMagnitude="-2147483648";MaxMagnitude="2147483647";Boundary="wrap"}
                {Name="uint32";Capability="native";Family="uint";Bits=32;MinMagnitude="0";MaxMagnitude="4294967295";Boundary="wrap"} |] } }
"""
        let kernel = """module KernelComputation197
type Shape = { Elements: int; Grain: int }
type ElementKernelA = { Compute: int -> int -> int; Shape: Shape }
type ElementKernelB = { Compute: int -> int -> int; Shape: Shape }
let addCalc (left: int) (right: int) = left + right
let mulCalc (left: int) (right: int) = left * right
[<KernelModule>]
let kernelA: ElementKernelA = { Compute = addCalc; Shape = { Elements = 64; Grain = 16 } }
[<KernelModule>]
let kernelB: ElementKernelB = { Compute = mulCalc; Shape = { Elements = 64; Grain = 16 } }
"""
        let representation name family bits minimum maximum : NumericRepresentation =
            { Name = name; Family = family; Bits = bits; Capability = "native"
              MinMagnitude = minimum; MaxMagnitude = maximum; Boundary = "wrap" }
        let representations =
            [ representation "int16" "int" 16 "-32768" "32767"
              representation "uint16" "uint" 16 "0" "65535"
              representation "int32" "int" 32 "-2147483648" "2147483647"
              representation "uint32" "uint" 32 "0" "4294967295" ]
        let context =
            { SourcePlatformFixture.platform with
                PlatformId = "kernel-witness-clef197"; Dimensions = Map.ofList [ "Pointer", 32; "Register", 16 ]
                Representations = representations |> List.map (fun v -> v.Name, v) |> Map.ofList
                PlatformDescription = Some "Fidelity.Platform.Contracts.KernelAuthority.description"
                PlatformArchitecture = Some "xdna2"; SubstrateKind = Some SubstrateKind.NPU
                RuntimeModel = Some RuntimeModel.XDNA
                PlatformSourcePaths = Set.singleton (Path.GetFullPath "clef197-kernel-authority.clef") }
        let parse path source =
            match NativeService.parseStringWithDefaults source path with
            | NativeService.ParseSuccess input -> input
            | NativeService.ParseError errors -> failwithf "Kernel source failed to parse: %A" errors
        let kernelRes =
            NativeService.checkParsedInputsWithDeclarations
                [ parse "clef197-kernel-authority.clef" authority; parse "clef197-kernel.clef" kernel ]
                (Some context) Set.empty None None
        DimensionalCases.noErrors kernelRes
        let kg = kernelRes.Graph
        let kBasePlan = kg.Codata.Value.SSAAssignment |> Option.defaultWith (fun () -> failwith "Expected kernel SSA plan.")
        let numDomain = kg.Edges |> List.pick (fun e -> match e.Role with EdgeRole.NumericDomain d -> Some d | _ -> None)
        let spaDomain = kg.Edges |> List.pick (fun e -> match e.Role with EdgeRole.SpatialModuleDomain d -> Some d | _ -> None)
        Assert.True(spaDomain.Kernels.Length = 2, sprintf "Expected 2 spatial kernels, got %d" spaDomain.Kernels.Length)
        Assert.True(numDomain.Values.Length >= 2)
        Assert.True(numDomain.Operations.Length >= 2)
        let numCarrierEdge = kg.Edges |> List.find (fun e -> match e.Role with EdgeRole.NumericCarrier _ when e.Sources.Length >= 2 -> true | _ -> false)
        let numOpEdge = kg.Edges |> List.find (fun e -> match e.Role with EdgeRole.NumericOperation _ when e.Sources.Length >= 2 -> true | _ -> false)
        let spaKernelEdge = kg.Edges |> List.find (fun e -> match e.Role with EdgeRole.KernelModule _ when e.Sources.Length >= 2 -> true | _ -> false)
        let toReassign =
            [ numCarrierEdge.Sources |> List.filter kg.Nodes.ContainsKey |> List.min
              numOpEdge.Sources |> List.filter kg.Nodes.ContainsKey |> List.min
              spaKernelEdge.Sources |> List.filter kg.Nodes.ContainsKey |> List.min
              numDomain.Premises |> Map.keys |> Seq.min
              spaDomain.Premises |> Map.keys |> Seq.min ]
            |> Set.ofList
        let allIds = kg.Nodes.Keys |> Set.ofSeq
        let retained = Set.difference allIds toReassign
        let alignment = allIds |> Seq.map (fun id -> id, id) |> Map.ofSeq
        let reconciledKg, kPlan =
            match Clef.Compiler.Nanopass.SSAAssignment.reconcileAndAssign kg alignment retained kg with
            | Result.Ok pair -> pair
            | Result.Error failure -> failwithf "Non-monotone kernel SSA remap refused: %A" failure
        for name, sources in
            [ "NumericCarrier", numCarrierEdge.Sources
              "NumericOperation", numOpEdge.Sources
              "SpatialKernel", spaKernelEdge.Sources ] do
            let present = sources |> List.filter kg.Nodes.ContainsKey
            let minId = List.min present
            Assert.True(toReassign.Contains minId, sprintf "%s min was not reassigned." name)
            let peer = present |> List.find (fun id -> not (toReassign.Contains id))
            Assert.True(NodeId.value kPlan.NodeRemap[minId] > kBasePlan.NodeHighWater)
            Assert.Equal(peer, kPlan.NodeRemap[peer])
            Assert.True(kPlan.NodeRemap[minId] > kPlan.NodeRemap[peer])
        let kPrepared = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare reconciledKg |> WorkspaceCases.need
        let kRev = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish kPrepared |> WorkspaceCases.need
        let kDefects = Fidelity.PSG.Integrity.check kRev
        Assert.True(kDefects.IsEmpty, Fidelity.PSG.Integrity.describe kDefects)
        // Exact-reason Sources-reversal negatives on NumericCarrier, NumericOperation, and SpatialKernel companion edges.
        let flipAndExpect name pred expectedReason =
            let mutable flipped = false
            let edges =
                reconciledKg.Edges |> List.map (fun e ->
                    if not flipped && pred e.Role && e.Sources.Length >= 2 && e.Sources <> List.rev e.Sources then
                        flipped <- true
                        { e with Sources = List.rev e.Sources }
                    else e)
            Assert.True(flipped, sprintf "Expected to flip %s companion edge." name)
            match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare { reconciledKg with Edges = edges } with
            | Result.Ok _ -> failwithf "Reversed %s companion edge was admitted." name
            | Result.Error failures -> Assert.Contains(failures, fun f -> f.Reason = expectedReason)
        flipAndExpect "NumericCarrier" (function EdgeRole.NumericCarrier _ -> true | _ -> false)
            "NumericPublication: The numeric carrier, joint premises, rewrite record or checked coverage obligation is inconsistent."
        flipAndExpect "NumericOperation" (function EdgeRole.NumericOperation _ -> true | _ -> false)
            "NumericPublication: The numeric carrier, joint premises, rewrite record or checked coverage obligation is inconsistent."
        flipAndExpect "KernelModule" (function EdgeRole.KernelModule _ -> true | _ -> false)
            "SpatialPublication: The complete spatial plan, participants, proof census or source rewrite record is inconsistent."

        // Hardened CallableContracts controls:
        // (a) Positive: at least one CallableContract with >= 2 Source participants had its source order inverted and re-synced cleanly.
        let origContracts = kg.Codata.Value.CallableContracts
        let newContracts = reconciledKg.Codata.Value.CallableContracts
        let contractWithInvertedSources =
            origContracts
            |> Map.toList
            |> List.tryPick (fun (cid, origContract) ->
                let origSources = origContract.Participants |> List.filter (fun p -> p.Role = ParticipantRole.Source) |> List.map _.Node
                if origSources.Length >= 2 then
                    let mappedCid = kPlan.NodeRemap.TryFind cid |> Option.defaultValue cid
                    let mappedOrigOrder = origSources |> List.map (fun n -> kPlan.NodeRemap.TryFind n |> Option.defaultValue n)
                    match newContracts.TryFind mappedCid with
                    | Some newContract ->
                        let newSources = newContract.Participants |> List.filter (fun p -> p.Role = ParticipantRole.Source) |> List.map _.Node
                        if newSources <> mappedOrigOrder && List.sort newSources = List.sort mappedOrigOrder then Some (cid, origContract) else None
                    | None -> None
                else None)
        Assert.True(contractWithInvertedSources.IsSome, "Expected at least one CallableContract with >= 2 inverted Source participants.")
        let targetContractId, targetContract = contractWithInvertedSources.Value
        // (b) Exact-reason negative: pre-faulted non-canonical CallableContract.Participants is refused directly by SSA.
        let sourceParts = targetContract.Participants |> List.filter (fun p -> p.Role = ParticipantRole.Source)
        let nonSourceParts = targetContract.Participants |> List.filter (fun p -> p.Role <> ParticipantRole.Source)
        let reversedSources = List.rev sourceParts |> List.mapi (fun i p -> { p with Ordinal = i })
        Assert.NotEqual<Participant list>(sourceParts, reversedSources)
        let preFaultedContractGraph =
            let cod = kg.Codata.Value
            let badContract = { targetContract with Participants = nonSourceParts @ reversedSources }
            { kg with Codata = lazy { cod with CallableContracts = cod.CallableContracts.Add(targetContractId, badContract) } }
        match Clef.Compiler.Nanopass.SSAAssignment.reconcileAndAssign kg Map.empty Set.empty preFaultedContractGraph with
        | Result.Error (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities [ _, reason ]) ->
            Assert.Equal("SSAAssignment: Callable contract participants are not canonical before SSA remapping.", reason)
        | other -> failwithf "Expected direct SSA refusal on non-canonical CallableContract participants, got %A" other
        // (c) Exact-reason negative: ambiguous duplicate CallableCarrier with conflicting signature for one contract is refused directly by SSA.
        let sampleCarrierKey, sampleCarrier =
            kg.Codata.Value.CallableCarriers |> Map.toList |> List.find (fun (_, c) -> match c.Contract with Result.Ok _ -> true | Result.Error _ -> false)
        let syntheticCarrierKey = NodeId (kBasePlan.NodeHighWater + 999)
        let conflictingCarrier = { sampleCarrier with Occurrence = syntheticCarrierKey; Result = syntheticCarrierKey }
        Assert.NotEqual(sampleCarrier.Result, conflictingCarrier.Result)
        let ambiguousCarrierGraph =
            let cod = kg.Codata.Value
            { kg with Codata = lazy { cod with CallableCarriers = cod.CallableCarriers.Add(syntheticCarrierKey, conflictingCarrier) } }
        match Clef.Compiler.Nanopass.SSAAssignment.reconcileAndAssign kg Map.empty Set.empty ambiguousCarrierGraph with
        | Result.Error (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities [ _, reason ]) ->
            Assert.Equal("SSAAssignment: Ambiguous callable carrier for implementation during SSA remapping.", reason)
        | other -> failwithf "Expected direct SSA refusal on ambiguous CallableCarrier, got %A" other
        ignore sampleCarrierKey

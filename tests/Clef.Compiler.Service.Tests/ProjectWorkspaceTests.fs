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

type private WorkspaceFiles() =
    let directory = Path.Combine(Path.GetTempPath(), "clef-workspace-tests-" + Guid.NewGuid().ToString("N"))
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

[<CollectionDefinition("ProjectWorkspace", DisableParallelization = true)>]
type ProjectWorkspaceCollection() = class end

[<Collection("ProjectWorkspace"); Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProjectWorkspace")>]
type ProjectWorkspaceTests() =
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
            Assert.Equal<string>(source, Map.ofList inputs |> Map.find files.Source)
            Assert.Equal<string>(File.ReadAllText dependency, Map.ofList inputs |> Map.find dependency)
            Assert.Equal<string list>([dependencySource; files.Source], List.map fst sources)
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
        Assert.Equal<string>(metadata, Map.ofList checkedProject.InputFiles |> Map.find binding)
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

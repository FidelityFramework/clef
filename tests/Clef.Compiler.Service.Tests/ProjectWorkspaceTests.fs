namespace Clef.Compiler.Service.Tests

open System
open System.IO
open System.Threading
open Xunit
open Clef.Compiler
open Clef.Compiler.Project
open Clef.Compiler.NativeTypedTree.Infrastructure
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

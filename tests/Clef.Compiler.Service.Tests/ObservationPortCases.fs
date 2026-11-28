// SPDX-License-Identifier: MIT
// clef #204 controls: the driver reports through a pure Zone A observation
// port; the host edge contains a failing adapter without unwinding into
// Segmentation.fs:127-130; target-free checks incur no platform read; and the
// host tool manifest identifies cvc5 distinctly from other manifested tools.
namespace Clef.Compiler.Service.Tests

open System
open System.IO
open Xunit
open Clef.Compiler
open Clef.Compiler.NativeService
open Clef.Compiler.Project
open Clef.Compiler.ObservationPort
open Clef.Compiler.Utilities
open Clef.Compiler.PSGSaturation.SemanticGraph

type private ObservationProject(?scratchRoot: string) =
    let directory = Path.Combine(defaultArg scratchRoot (Path.GetTempPath()), "clef-observation-tests-" + Guid.NewGuid().ToString("N"))
    let project = Path.Combine(directory, "App.fidproj")
    let source = Path.Combine(directory, "App.clef")
    do
        Directory.CreateDirectory directory |> ignore
        // A console target is physically admitted, so the driver reaches the
        // checked-witness preparation that publishes the segmentation counter.
        File.WriteAllText(source, "module App\nlet main () = ()\n")
        File.WriteAllText(project,
            "[package]\nname = \"App\"\n[compilation]\ntarget = \"cpu\"\n[build]\noutput_kind = \"console\"\nsources = [\"App.clef\"]\n[platform]\nruntime_model = \"libc\"\n")
    member _.Project = project
    member _.Directory = directory
    interface IDisposable with member _.Dispose() = Directory.Delete(directory, true)

module private ObservationCases =
    let need = function Ok value -> value | Error error -> failwithf "%A" error
    let phases observations =
        observations |> List.choose (function CompilerObservation.Phase name -> Some name | _ -> None)
    let passes observations =
        observations |> List.choose (function CompilerObservation.Pass name -> Some name | _ -> None)
    let projections observations =
        observations |> List.choose (function CompilerObservation.ProjectionComputed (owner, rows) -> Some (owner, rows) | _ -> None)
    let census observations =
        observations |> List.choose (function CompilerObservation.RootCensus (hardware, kernels) -> Some (hardware, kernels) | _ -> None)

type ObservationPortCases() =

    [<Fact>]
    member _.``Driver path delivers phases, non-duplicate passes, projection counters and root census without changing the check``() =
        use files = new ObservationProject()
        let quiet = ProjectChecker.checkProject files.Project |> ObservationCases.need
        let observed = ResizeArray<CompilerObservation>()
        let checkedProject =
            ProjectChecker.checkProjectWithObservationPort { Emit = observed.Add } files.Project
            |> ObservationCases.need
        let report = List.ofSeq observed
        let reached = ObservationCases.phases report
        for phase in ["program-storage"; "memory-and-boundary-settlement"; "final-graph-readiness"; "obligation-publication"; "checked-witness-preparation"] do
            Assert.True(List.exists ((=) phase) reached, sprintf "The driver did not report phase '%s': %A" phase reached)
        let passList = ObservationCases.passes report
        // Completion Pass "program-storage" appears once; trace point uses "program-storage-settled".
        Assert.Equal(1, passList |> List.filter ((=) "program-storage") |> List.length)
        Assert.Equal(1, passList |> List.filter ((=) "program-storage-settled") |> List.length)
        let projectionEvents = ObservationCases.projections report
        let owners = projectionEvents |> List.map fst
        for owner in [ProjectionOwner.PlatformReading; ProjectionOwner.PlatformDescriptors; ProjectionOwner.Numeric;
                      ProjectionOwner.Memory; ProjectionOwner.Spatial; ProjectionOwner.Boundary;
                      ProjectionOwner.WitnessSegmentation] do
            let count = owners |> List.sumBy (fun reportedOwner -> if reportedOwner = owner then 1 else 0)
            // SpatialSettlement.normalize currently runs unconditionally on console apps until
            // Wave B4 (#186) short-circuits zero-root spatial work; report it honestly rather than
            // suppressing the counter behind the root census.
            Assert.Equal(1, count)
        Assert.True(projectionEvents |> List.forall (fun (_, rows) -> rows >= 0), "Projection row counts must be non-negative")
        // Exactly one RootCensus emitted per admitted check, reporting (0, 0) for a console fixture.
        let census = ObservationCases.census report
        Assert.Equal<(int * int) list>([(0, 0)], census)
        // Reporting is not part of the result: the same check with no port at all
        // produces the same compiled output.
        Assert.True(quiet.InputFiles = checkedProject.InputFiles, "Observation delivery changed the prepared inputs")
        Assert.True(quiet.ParseErrors = checkedProject.ParseErrors, "Observation delivery changed the parse errors")
        Assert.True(quiet.CheckResult.Diagnostics = checkedProject.CheckResult.Diagnostics,
            "Observation delivery changed the diagnostics")
        Assert.Equal(quiet.CheckResult.Graph.Nodes.Count, checkedProject.CheckResult.Graph.Nodes.Count)
        Assert.Equal(List.length quiet.CheckResult.Graph.Edges, List.length checkedProject.CheckResult.Graph.Edges)

    [<Fact>]
    member _.``Target-free check skips PlatformReading, PlatformDescriptors and WitnessSegmentation``() =
        let parsed =
            match parseStringWithDefaults "module TargetFree\nlet f x = x + 1\n" "TargetFree.clef" with
            | ParseSuccess input -> input
            | ParseError errs -> failwithf "parse failed: %A" errs
        let observed = ResizeArray<CompilerObservation>()
        let _ =
            checkParsedInputsWithDeclarationsAndPhaseSink None (Some { Emit = observed.Add }) [parsed] None Set.empty None None
        let report = List.ofSeq observed
        let owners = ObservationCases.projections report |> List.map fst
        Assert.Contains(ProjectionOwner.Numeric, owners)
        Assert.Contains(ProjectionOwner.Memory, owners)
        Assert.Contains(ProjectionOwner.Boundary, owners)
        Assert.Equal<(int * int) list>([(0, 0)], ObservationCases.census report)
        Assert.DoesNotContain(ProjectionOwner.PlatformReading, owners)
        Assert.DoesNotContain(ProjectionOwner.PlatformDescriptors, owners)
        Assert.DoesNotContain(ProjectionOwner.WitnessSegmentation, owners)

    [<Fact>]
    member _.``InvalidOperationException from a host adapter is contained at ProjectChecker and never turns into SegmentationFailure.UnsupportedInput``() =
        use files = new ObservationProject()
        let baseline = ProjectChecker.checkProject files.Project |> ObservationCases.need
        let baselinePrepared = WitnessEmission.prepare baseline.CheckResult.Graph |> ObservationCases.need
        let baselineSegmented = Segmentation.segment baselinePrepared |> ObservationCases.need

        // (a) Fault-injection control on internal Zone A entry: a raw port throwing
        // InvalidOperationException propagates that exact instance (never converted
        // into SegmentationFailure.UnsupportedInput).
        let rawFault = InvalidOperationException "raw host adapter threw InvalidOperationException"
        let rawPort = { Emit = fun _ -> raise rawFault }
        let caught =
            Assert.Throws<InvalidOperationException>(fun () ->
                WitnessEmission.prepareWithObservation (Some rawPort) baseline.CheckResult.Graph |> ignore)
        Assert.Same(rawFault, caught)

        // (b) Public Zone B entry contains the exact InvalidOperationException,
        // records every failure through onFailure, and leaves diagnostics, graph,
        // witness preparation, and Segmentation identical to baseline.
        let seen = ResizeArray<CompilerObservation>()
        let recordedFailures = ResizeArray<exn>()
        let edgeFault = InvalidOperationException "host adapter blew up at edge"
        let throwingPort =
            { Emit = fun observation ->
                seen.Add observation
                raise edgeFault }
        let checkedProject =
            ProjectChecker.checkProjectWithObservationPortAndFailures recordedFailures.Add throwingPort files.Project
            |> ObservationCases.need
        Assert.True(seen.Count > 0, "The fault-injected port received no observation to fail on.")
        Assert.Equal(seen.Count, recordedFailures.Count)
        Assert.True(recordedFailures |> Seq.forall (fun ex -> Object.ReferenceEquals(edgeFault, ex)),
            "Every recorded host failure must be the exact adapter exception instance")
        Assert.True(baseline.CheckResult.Diagnostics = checkedProject.CheckResult.Diagnostics,
            "A failing adapter altered the compiler diagnostics")
        Assert.Equal(baseline.CheckResult.Graph.Nodes.Count, checkedProject.CheckResult.Graph.Nodes.Count)
        Assert.Equal(List.length baseline.CheckResult.Graph.Edges, List.length checkedProject.CheckResult.Graph.Edges)

        let prepared = WitnessEmission.prepare checkedProject.CheckResult.Graph |> ObservationCases.need
        let segmented = Segmentation.segment prepared |> ObservationCases.need
        Assert.Equal(Map.count baselineSegmented.Regions, Map.count segmented.Regions)

        // (c) OperationCanceledException is never swallowed by containObservationPort.
        let cancelEx = OperationCanceledException "cancelled"
        let containedCancel =
            ProjectChecker.containObservationPort (Some recordedFailures.Add) { Emit = fun _ -> raise cancelEx }
        let thrownCancel =
            Assert.Throws<OperationCanceledException>(fun () ->
                emitObservation containedCancel (CompilerObservation.Phase "cancel-probe"))
        Assert.Same(cancelEx, thrownCancel)

    [<Fact>]
    member _.``Manifest-resolved ToolIdentity distinguishes cvc5 from manifested non-solvers and fails closed when unconfigured``() =
        let directory = Path.Combine(Path.GetTempPath(), "clef-tool-identity-" + Guid.NewGuid().ToString("N"))
        let manifestPath = Path.Combine(directory, "tools.manifest.tsv")
        let solverDirectory = Path.Combine(directory, "solver-bin")
        let solver = Path.Combine(solverDirectory, "libz3-cvc5-plain")
        let linkDirectory = Path.Combine(directory, "solver-link")
        let link = Path.Combine(linkDirectory, "not-cvc5")
        let clangTool = Path.Combine(directory, "clang-20")
        let unrelated = Path.Combine(directory, "other-tool")
        try
            Directory.CreateDirectory solverDirectory |> ignore
            Directory.CreateDirectory linkDirectory |> ignore
            File.WriteAllText(solver, "cvc5 version 1.3.0\n")
            File.WriteAllText(clangTool, "clang version 20.0.0\n")
            File.WriteAllText(unrelated, "some other tool\n")
            File.CreateSymbolicLink(link, solver) |> ignore
            Assert.NotNull(FileInfo(link).LinkTarget)
            // Two-tool manifest (cvc5 + clang) plus a malformed empty-executable row.
            File.WriteAllText(manifestPath,
                "cvc5\t" + solver + "\t1.3.0\n"
                + "clang\t" + clangTool + "\t20.0.0\n"
                + "cvc5\t\t1.3.0\n")
            let manifest =
                match HostTools.readToolManifestResult manifestPath with
                | Ok m -> m
                | Error err -> failwith err
            // Positive: symlinked/renamed cvc5 resolves to cvc5 and counts as solver spawn.
            match HostTools.resolveToolIdentity manifest link with
            | Some identity ->
                Assert.Equal("cvc5", identity.Name)
                Assert.Equal(Path.GetFullPath solver, identity.Executable)
                Assert.Equal(Some "1.3.0", identity.Version)
                Assert.Equal(manifestPath, identity.ManifestPath)
            | None ->
                Assert.Fail("The manifest did not resolve the symlinked solver to its recorded identity")
            Assert.True(HostTools.isSolverSpawnWith manifest link, "The renamed solver was not recognised as a solver spawn")
            // Exact-reason negative 1: manifested non-solver (clang) resolves to clang and MUST NOT count as cvc5.
            match HostTools.resolveToolIdentity manifest clangTool with
            | Some identity -> Assert.Equal("clang", identity.Name)
            | None -> Assert.Fail("The manifest did not resolve clang")
            Assert.False(HostTools.isSolverSpawnWith manifest clangTool, "A manifested non-solver (clang) was counted as a solver spawn")
            // Exact-reason negative 2: unmanifested executable stays unnamed and does not count.
            Assert.True(HostTools.resolveToolIdentity manifest unrelated = None,
                "A tool outside the manifest was identified as a manifested tool")
            Assert.False(HostTools.isSolverSpawnWith manifest unrelated, "An unrelated tool was counted as a solver spawn")
            // Exact-reason negative 3: unconfigured or missing manifest fails closed with Error.
            match HostTools.readToolManifestResult "" with
            | Error msg -> Assert.Contains("not configured", msg)
            | Ok _ -> Assert.Fail("Blank manifest path must fail closed")
            match HostTools.readToolManifestResult (Path.Combine(directory, "missing.tsv")) with
            | Error msg -> Assert.Contains("does not exist", msg)
            | Ok _ -> Assert.Fail("Missing manifest file must fail closed")
        finally
            Directory.Delete(directory, true)

    [<Fact>]
    member _.``Bare command resolved via PATH matches the manifested cvc5 identity for both solverIdentity and isSolverSpawnResult``() =
        let directory = Path.Combine(Path.GetTempPath(), "clef-bare-solver-" + Guid.NewGuid().ToString("N"))
        let binDir = Path.Combine(directory, "bin")
        let bareName = "clef-bare-cvc5-" + Guid.NewGuid().ToString("N").Substring(0, 8)
        let solverPath = Path.Combine(binDir, bareName)
        let manifestPath = Path.Combine(directory, "tools.manifest.tsv")
        let priorPath = Environment.GetEnvironmentVariable "PATH"
        let priorManifest = Environment.GetEnvironmentVariable "CLEF_TOOL_MANIFEST"
        let priorCvc5 = Environment.GetEnvironmentVariable "CLEF_CVC5"
        try
            Directory.CreateDirectory binDir |> ignore
            File.WriteAllText(solverPath, "#!/bin/sh\necho sat\n")
            if OperatingSystem.IsLinux() then
                File.SetUnixFileMode(solverPath, UnixFileMode.UserRead ||| UnixFileMode.UserWrite ||| UnixFileMode.UserExecute)
            File.WriteAllText(manifestPath, "cvc5\t" + solverPath + "\t1.3.0\n")
            let sep = string Path.PathSeparator
            Environment.SetEnvironmentVariable("PATH", binDir + (if String.IsNullOrEmpty priorPath then "" else sep + priorPath))
            Environment.SetEnvironmentVariable("CLEF_TOOL_MANIFEST", manifestPath)
            // Full path case
            Environment.SetEnvironmentVariable("CLEF_CVC5", solverPath)
            match HostTools.solverIdentity () with
            | Ok id -> Assert.Equal("cvc5", id.Name); Assert.Equal(Path.GetFullPath solverPath, id.Executable)
            | Error err -> Assert.Fail("Full path solverIdentity failed: " + err)
            Assert.Equal(Ok true, HostTools.isSolverSpawnResult solverPath)
            // Bare command via PATH case (same binary resolved once through PATH)
            Environment.SetEnvironmentVariable("CLEF_CVC5", bareName)
            match HostTools.solverIdentity () with
            | Ok id -> Assert.Equal("cvc5", id.Name); Assert.Equal(Path.GetFullPath solverPath, id.Executable)
            | Error err -> Assert.Fail("Bare command solverIdentity failed: " + err)
            Assert.Equal(Ok true, HostTools.isSolverSpawnResult bareName)
        finally
            Environment.SetEnvironmentVariable("PATH", priorPath)
            Environment.SetEnvironmentVariable("CLEF_TOOL_MANIFEST", priorManifest)
            Environment.SetEnvironmentVariable("CLEF_CVC5", priorCvc5)
            Directory.Delete(directory, true)

    [<Fact>]
    member _.``A tool manifest without a record or with unset environment resolves to no fabricated solver identity``() =
        let manifest = HostTools.parseToolManifest "empty.tsv" ["# only comments"; ""; "cvc5\t\t1.3.0"]
        Assert.Equal(0, manifest.Count)
        Assert.True(HostTools.resolveToolIdentity manifest "cvc5" = None)
        let priorManifest = Environment.GetEnvironmentVariable "CLEF_TOOL_MANIFEST"
        try
            Environment.SetEnvironmentVariable("CLEF_TOOL_MANIFEST", null)
            match HostTools.isSolverSpawnResult "/usr/bin/false" with
            | Error msg -> Assert.Contains("not configured", msg)
            | Ok _ -> Assert.Fail("isSolverSpawnResult must fail closed when CLEF_TOOL_MANIFEST is unset")
            match HostTools.solverIdentity () with
            | Error msg -> Assert.Contains("not configured", msg)
            | Ok id -> Assert.Fail(sprintf "solverIdentity must not fabricate an unmanifested identity: %A" id)
        finally
            Environment.SetEnvironmentVariable("CLEF_TOOL_MANIFEST", priorManifest)

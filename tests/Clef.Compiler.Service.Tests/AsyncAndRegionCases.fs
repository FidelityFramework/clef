namespace Clef.Compiler.Service.Tests

open System.Diagnostics
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Publication = Clef.Compiler.PSGSaturation.Publication.RevisionPublication
module Discharge = Clef.Compiler.Nanopass.ObligationDischarge

module private AsyncAndRegionFixture =
    let private byteState : NumericRepresentation =
        { Name = "uint8"; Capability = "native"; Family = "uint"; Bits = 8
          MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap" }

    let platform =
        { IntrinsicWriteFixture.platform with
            Representations = IntrinsicWriteFixture.platform.Representations.Add(byteState.Name, byteState) }

    /// The selected platform declares one region memory space: 4096-byte
    /// pages within a 1 MiB budget. Region capacity is read from it.
    let authority =
        IntrinsicWriteFixture.authority
            .Replace(
                "Representations = [| ",
                "Representations = [| { Name = \"uint8\"; Capability = \"native\"; Family = \"uint\"; Bits = 8; MinMagnitude = \"0\"; MaxMagnitude = \"255\"; Boundary = \"wrap\" }; ")
            .Replace(
                "let rodata =",
                "let regionPages = { Name = \"region\"; Kind = \"region\"; Capacity = 1048576; Alignment = 16; Granularity = 4096; Growth = \"up\"; Access = \"rw\"; Base = None }\nlet rodata =")
            .Replace("Spaces = [| rodata |]", "Spaces = [| rodata; regionPages |]")

    let checkRaw (name: string) (body: string) =
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwith (sprintf "Parse failed: %d errors" errors.Length)
        Clef.Compiler.NativeService.checkParsedInputsWithPlatform
            [ parse authority "write-authority.clef"; parse body (name + ".clef") ]
            (Some platform)

    let check (name: string) (body: string) =
        let result = checkRaw name body
        DimensionalCases.noErrors result
        result.Graph

    let publish (graph: SemanticGraph) =
        match Publication.publish graph with
        | Ok revision ->
            let violations = Fidelity.PSG.Integrity.check revision
            Assert.True(violations.IsEmpty, Fidelity.PSG.Integrity.describe violations)
            revision
        | Error failures ->
            failwith (sprintf "Publication refused: %d failures" failures.Length)

    let clefId (Fidelity.PSG.NodeId value) = NodeId value

    /// Discharge the exact settled claim the graph carries for a published
    /// obligation: the claim is read from its graph citizen, never re-encoded.
    let solveObligation (graph: SemanticGraph) (obligation: Fidelity.PSG.ObligationInfo) =
        let settled =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Obligation info when info.Id = obligation.Id -> Some info
                | _ -> None)
            |> Seq.distinct
            |> Seq.toList
        let info = Assert.Single(settled)
        let start = ProcessStartInfo("cvc5")
        start.ArgumentList.Add "--lang=smt2"
        start.ArgumentList.Add "--tlimit-per=2000"
        start.RedirectStandardInput <- true
        start.RedirectStandardOutput <- true
        start.RedirectStandardError <- true
        start.UseShellExecute <- false
        use solver = new Process(StartInfo = start)
        Assert.True(solver.Start())
        let output, errors = solver.StandardOutput.ReadToEndAsync(), solver.StandardError.ReadToEndAsync()
        solver.StandardInput.Write(Discharge.smtLib [ info ])
        solver.StandardInput.Close()
        if not (solver.WaitForExit 5000) then
            solver.Kill(true)
            failwith "cvc5 solver timed out"
        Assert.True(solver.ExitCode = 0, errors.GetAwaiter().GetResult())
        output.GetAwaiter().GetResult().Trim()

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "AsyncAndRegion")>]
type AsyncAndRegionCases() =

    [<Fact>]
    member _.``A-01 (17_BasicAsync): deferred AsyncFormation is distinct from AsyncActivation and settles captures``() =
        let source = """
module BasicAsyncSample

let simpleAsync = async {
    return 42
}

let asyncWithCapture (x: int) = async {
    return x * 2
}

[<EntryPoint>]
let main _ =
    Console.writeln "=== Basic Async Test ==="

    Console.writeln "--- Simple Async ---"
    let v1 = Async.RunSynchronously simpleAsync
    Console.write "Result: "
    Console.writeln (Format.int v1)

    Console.writeln "--- Async with Capture ---"
    let v2 = Async.RunSynchronously (asyncWithCapture 21)
    Console.write "Result: "
    Console.writeln (Format.int v2)

    0
"""
        let graph = AsyncAndRegionFixture.check "17_BasicAsync" source
        let revision = AsyncAndRegionFixture.publish graph
        Assert.Equal(2, revision.Codata.AsyncFormations.Count)
        Assert.Equal(2, revision.Codata.AsyncActivations.Count)
        let capturedFormations =
            revision.Codata.AsyncFormations.Values
            |> Seq.filter (fun f -> not f.CapturedBindings.IsEmpty)
            |> Seq.toList
        Assert.Single(capturedFormations) |> ignore
        for form in revision.Codata.AsyncFormations.Values do
            // Formation is deferred: the body belongs to a callable, not to
            // the formation's own evaluation.
            let callable = graph.Nodes[AsyncAndRegionFixture.clefId form.Callable]
            Assert.True(
                (match callable.Kind with
                 | SemanticKind.Lambda(_, body, _, _, _) -> body = AsyncAndRegionFixture.clefId form.Body
                 | SemanticKind.ClosureValue _ -> true
                 | _ -> false),
                "The formation's callable must be a deferred Lambda owning the async body.")
            let owner = graph.Nodes[AsyncAndRegionFixture.clefId form.Formation]
            Assert.DoesNotContain(AsyncAndRegionFixture.clefId form.Body, owner.Children)
            for oblId in form.Obligations do
                Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])
        for act in revision.Codata.AsyncActivations.Values do
            Assert.NotEqual(act.Site, act.Formation)
            Assert.True(revision.Codata.AsyncFormations.ContainsKey act.Formation)
            for oblId in act.Obligations do
                Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])

    [<Fact>]
    member _.``A-02 (18_AsyncAwait): let! and do! populate AsyncSuspension rows, and a frame change invalidates its dependents``() =
        let template = """
module AsyncAwaitSample

let asyncAdd a b = async {
    return a + b
}

let composed = async {
    let! x = asyncAdd 10 20
    let! y = asyncAdd 1 5
    return RETURN_TAIL
}

let withDo = async {
    do! async { Console.writeln "Step 1" }
    do! async { Console.writeln "Step 2" }
    return 42
}

[<EntryPoint>]
let main _ =
    Console.writeln "=== Async Await Test ==="

    Console.writeln "--- Composed Async ---"
    let v1 = Async.RunSynchronously composed
    Console.write "Result: "
    Console.writeln (Format.int v1)

    Console.writeln "--- Async with do! ---"
    let v2 = Async.RunSynchronously withDo
    Console.write "Result: "
    Console.writeln (Format.int v2)

    0
"""
        let source (tail: string) = template.Replace("RETURN_TAIL", tail)
        let graph = AsyncAndRegionFixture.check "18_AsyncAwait" (source "y")
        let revision = AsyncAndRegionFixture.publish graph
        Assert.Equal(4, revision.Codata.AsyncSuspensions.Count)
        let ordinals =
            revision.Codata.AsyncSuspensions.Values
            |> Seq.map _.StateOrdinal
            |> Seq.sort
            |> Seq.toList
        Assert.Equal<int list>([0; 0; 1; 1], ordinals)
        for susp in revision.Codata.AsyncSuspensions.Values do
            Assert.True(susp.LiveSlots |> List.forall susp.InitializedSlots.Contains)
            for oblId in susp.Obligations do
                Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])

        // Keeping `x` live across the second cut changes the frame; the
        // dependent suspension liveness and its settled layout claim change.
        let changedGraph = AsyncAndRegionFixture.check "18_AsyncAwait_live" (source "x + y")
        let changed = AsyncAndRegionFixture.publish changedGraph
        let secondCut (rev: Fidelity.PSG.Revision) =
            rev.Codata.AsyncSuspensions.Values
            |> Seq.filter (fun s -> s.StateOrdinal = 1)
            |> Seq.sortByDescending (fun s -> s.LiveSlots.Length)
            |> Seq.head
        let baseCut, changedCut = secondCut revision, secondCut changed
        Assert.Empty(baseCut.LiveSlots)
        Assert.Single(changedCut.LiveSlots) |> ignore
        let xSlotId = List.head changedCut.LiveSlots
        let firstCutOfComposed =
            changed.Codata.AsyncSuspensions.Values
            |> Seq.find (fun s -> s.Formation = changedCut.Formation && s.StateOrdinal = 0)
        Assert.DoesNotContain(xSlotId, firstCutOfComposed.InitializedSlots)
        Assert.Contains(xSlotId, changedCut.InitializedSlots)
        let changedOblId = List.head changedCut.Obligations
        let changedSources = changed.ObligationSources[changedOblId] |> List.concat
        Assert.Contains(changedCut.Frame, changedSources)
        Assert.Contains(xSlotId, changedSources)
        let baseFrame, changedFrame = revision.Codata.ContinuationFrames[baseCut.Frame], changed.Codata.ContinuationFrames[changedCut.Frame]
        Assert.True(changedFrame.Bytes > baseFrame.Bytes)
        let claimBody (rev: Fidelity.PSG.Revision) (cut: Fidelity.PSG.AsyncSuspension) = rev.CurrentClaims[List.head cut.Obligations].Body
        Assert.NotEqual(claimBody revision baseCut, claimBody changed changedCut)
        for oblId in changedCut.Obligations do
            Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation changedGraph changed.CurrentClaims[oblId])

    [<Fact>]
    member _.``Farscape#220 (CCS8424 & CCS8425): refuses unretained view or invalidated region handle across suspension cut and admits retained region``() =
        let ccs8424Source = """
module BorrowedViewAcrossAwait

let step (x: int) = async { return x + 1 }

[<EntryPoint>]
let main _ =
    let work = async {
        let arr = [| 10; 20; 30 |]
        let view = ReadOnlyView.ofArray arr
        let! a = step 1
        let v0 = view.[0]
        return a + v0
    }
    Async.RunSynchronously work
"""
        let res8424 = AsyncAndRegionFixture.checkRaw "ccs8424" ccs8424Source
        Assert.Contains(res8424.Diagnostics, fun d -> d.Code = "CCS8424")

        let ccs8425Source = """
module InvalidatedRegionAcrossAwait

let step (x: int) = async { return x + 1 }

[<EntryPoint>]
let main _ =
    let work = async {
        let r = Region.create 4
        let buf = Region.alloc<int> r 4
        buf.[0] <- 10
        Region.release r
        let! a = step 1
        return a + buf.[0]
    }
    Async.RunSynchronously work
"""
        let res8425 = AsyncAndRegionFixture.checkRaw "ccs8425" ccs8425Source
        Assert.Contains(res8425.Diagnostics, fun d -> d.Code = "CCS8425")

        // Released after the resumption but before the post-resumption read.
        let ccs8425AfterResume = """
module ReleasedAfterResume

let step (x: int) = async { return x + 1 }

[<EntryPoint>]
let main _ =
    let work = async {
        let r = Region.create 4
        let buf = Region.alloc<int> r 4
        buf.[0] <- 10
        let! a = step 1
        Region.release r
        return a + buf.[0]
    }
    Async.RunSynchronously work
"""
        let resAfter = AsyncAndRegionFixture.checkRaw "ccs8425_after_resume" ccs8425AfterResume
        Assert.Contains(resAfter.Diagnostics, fun d -> d.Code = "CCS8425")

        let retainedSource = """
module RetainedRegionAcrossAwait

let step (x: int) = async { return x + 1 }

[<EntryPoint>]
let main _ =
    let work = async {
        let r = Region.create 4
        let buf = Region.alloc<int> r 4
        buf.[0] <- 10
        let! a = step 1
        let res = a + buf.[0]
        Region.release r
        return res
    }
    Async.RunSynchronously work
"""
        let graphRetained = AsyncAndRegionFixture.check "retained_region_await" retainedSource
        let revRetained = AsyncAndRegionFixture.publish graphRetained
        let susp = Assert.Single(revRetained.Codata.AsyncSuspensions.Values)
        let retention = Assert.Single(susp.SpanningRetentions)
        Assert.NotEmpty(retention.InvalidatedBy)
        let reg = revRetained.Codata.RegionAllocations[retention.BackingRegion]
        Assert.True(retention.InvalidatedBy |> List.forall (fun release -> reg.ScopeExitReleases |> List.exists (fun (_, r) -> r = release)))
        Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graphRetained revRetained.CurrentClaims[retention.RetirementCheck])

    [<Fact>]
    member _.``A-03 (19_AsyncParallel & Async.Sequential): populates AsyncOrchestration with 5 children and iterates every result``() =
        let source = """
module AsyncParallelSample

let makeAsync (n: int) = async {
    Console.write "Computing "
    Console.writeln (Format.int n)
    return n * n
}

[<EntryPoint>]
let main _ =
    Console.writeln "=== Async Parallel Test ==="

    let tasks = [|
        makeAsync 1
        makeAsync 2
        makeAsync 3
        makeAsync 4
        makeAsync 5
    |]

    Console.writeln "--- Running Parallel ---"
    let results = Async.Parallel tasks |> Async.RunSynchronously

    Console.writeln "--- Results ---"
    for r in results do
        Console.writeln (Format.int r)

    let seqResults = Async.Sequential tasks |> Async.RunSynchronously
    for s in seqResults do
        Console.writeln (Format.int s)

    0
"""
        let graph = AsyncAndRegionFixture.check "19_AsyncParallel" source
        let revision = AsyncAndRegionFixture.publish graph
        Assert.Equal(2, revision.Codata.AsyncOrchestrations.Count)
        let parOrch =
            revision.Codata.AsyncOrchestrations.Values
            |> Seq.find (fun o -> o.Mode = Fidelity.PSG.AsyncOrchestrationMode.Parallel)
        Assert.Equal(5, parOrch.Children.Length)
        Assert.Equal(5, parOrch.ResultCapacity)
        Assert.True(parOrch.ElementStride > 0)
        Assert.Empty(parOrch.WorkDependencies)
        let seqOrch =
            revision.Codata.AsyncOrchestrations.Values
            |> Seq.find (fun o -> o.Mode = Fidelity.PSG.AsyncOrchestrationMode.Sequential)
        Assert.Equal(5, seqOrch.Children.Length)
        Assert.Equal(4, seqOrch.WorkDependencies.Length)
        let makeAsyncFormation = Assert.Single(revision.Codata.AsyncFormations.Values)
        for child in parOrch.Children do
            Assert.Equal(makeAsyncFormation.Formation, revision.Codata.AsyncActivations[child].Formation)
        for oblId in parOrch.SynchronizationObligations @ seqOrch.SynchronizationObligations do
            Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])
        // Each `for .. in` over a result array is a counted loop over all elements.
        let loops =
            graph.Nodes.Values
            |> Seq.filter (fun node -> node.IsReachable && (match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false))
            |> Seq.length
        Assert.True(loops >= 2, "Each array iteration must be a loop over every element.")

    [<Fact>]
    member _.``A-04 (20_BasicRegion): constructs one release on every exit path and refuses missing or excessive premises``() =
        let source = """
module BasicRegionSample

let processInRegion () =
    let region = Region.create 4
    let buffer = Region.alloc<int> region 100
    buffer.[0] <- 42
    let v = buffer.[0]
    v

let pick (flag: bool) =
    let region = Region.create 1
    let buf = Region.alloc<int> region 4
    buf.[0] <- 7
    let v = buf.[0]
    if flag then v else v + 1

[<EntryPoint>]
let main _ =
    let res = processInRegion ()
    Console.writeln (Format.int res)
    Console.writeln (Format.int (pick true))
    0
"""
        let graph = AsyncAndRegionFixture.check "20_BasicRegion" source
        let revision = AsyncAndRegionFixture.publish graph
        Assert.Equal(2, revision.Codata.RegionAllocations.Count)
        for reg in revision.Codata.RegionAllocations.Values do
            Assert.True(reg.Capacity >= reg.ByteExtent)
            Assert.True(reg.Capacity % 4096L = 0L)
            Assert.NotEmpty(reg.ScopeExitReleases)
            Assert.Equal(reg.ScopeExitPaths.Length, reg.ScopeExitReleases.Length)
            // Every constructed release is a real Region.release operation.
            for (_, release) in reg.ScopeExitReleases do
                let node = graph.Nodes[AsyncAndRegionFixture.clefId release]
                Assert.True(match node.Kind with SemanticKind.Application _ -> true | _ -> false)
            for oblId in reg.Obligations do
                Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])
        let twoExits = revision.Codata.RegionAllocations.Values |> Seq.find (fun reg -> reg.ScopeExitPaths.Length = 2)
        Assert.Equal(2, twoExits.ScopeExitReleases |> List.map snd |> List.distinct |> List.length)
        let large = revision.Codata.RegionAllocations.Values |> Seq.find (fun reg -> reg.ScopeExitPaths.Length = 1)
        Assert.Equal(16384L, large.Capacity)

        let negSource = """
module InvalidRegionAlloc

[<EntryPoint>]
let main _ =
    let r = Region.create 4
    let buf = Region.alloc<int> r 0
    Region.release r
    0
"""
        let negRes = AsyncAndRegionFixture.checkRaw "20_BasicRegion_neg" negSource
        Assert.Contains(negRes.Diagnostics, fun d -> d.Code = "CCS8405")

        let overSource = """
module OverCapacityRegion

let over () =
    let r = Region.create 1
    let buf = Region.alloc<int> r 1000
    buf.[0] <- 1
    let v = buf.[0]
    Region.release r
    v

[<EntryPoint>]
let main _ =
    Console.writeln (Format.int (over ()))
    0
"""
        let overRes = AsyncAndRegionFixture.checkRaw "20_BasicRegion_over" overSource
        Assert.Contains(overRes.Diagnostics, fun d -> d.Code = "CCS8405")

        let exitReadsSource = """
module ExitReadsRegion

let leaks () =
    let r = Region.create 1
    let b = Region.alloc<int> r 4
    b.[0] <- 1
    b.[0]

[<EntryPoint>]
let main _ =
    Console.writeln (Format.int (leaks ()))
    0
"""
        let exitRes = AsyncAndRegionFixture.checkRaw "20_BasicRegion_exit" exitReadsSource
        Assert.Contains(exitRes.Diagnostics, fun d -> d.Code = "CCS8405")

    [<Fact>]
    member _.``A-05 (21_RegionPassing): settles Borrowed RegionCallPassing for callees and refuses callee release``() =
        let source = """
module RegionPassingSample

let allocateAndFill (r: Region) (size: int) (value: int) =
    let buf = Region.alloc<int> r size
    buf.[0] <- value
    buf

let doubleValues (r: Region) (input: int array) (len: int) =
    let outBuf = Region.alloc<int> r len
    let v = input.[0]
    if v >= 0 && v <= 100 then
        outBuf.[0] <- v * 2
    else
        outBuf.[0] <- 0
    outBuf.[0]

[<EntryPoint>]
let main _ =
    let region = Region.create 4
    let data = allocateAndFill region 10 21
    let doubled = doubleValues region data 10
    Region.release region
    Console.writeln (Format.int doubled)
    0
"""
        let graph = AsyncAndRegionFixture.check "21_RegionPassing" source
        let revision = AsyncAndRegionFixture.publish graph
        let reg = Assert.Single(revision.Codata.RegionAllocations.Values)
        // Both callee allocations draw from the caller's region.
        Assert.True(reg.ByteExtent >= 160L)
        Assert.Equal(2, revision.Codata.RegionCallPassings.Count)
        for pass in revision.Codata.RegionCallPassings.Values do
            Assert.Equal(Fidelity.PSG.RegionOwnershipMode.Borrowed, pass.Mode)
            Assert.Empty(pass.CalleeReleases)
            Assert.True(pass.CalleeLifetimeDepth > pass.CallerLifetimeDepth)

        let negSource = """
module IllegalBorrowedRelease

let release2 (q: Region) =
    Region.release q

let badCallee (r: Region) =
    let alias = r
    release2 alias

[<EntryPoint>]
let main _ =
    let region = Region.create 4
    let b = Region.alloc<int> region 4
    b.[0] <- 1
    badCallee region
    0
"""
        let negRes = AsyncAndRegionFixture.checkRaw "21_RegionPassing_neg" negSource
        Assert.Contains(negRes.Diagnostics, fun d -> d.Code = "CCS8405")

    [<Fact>]
    member _.``A-06 (22_RegionEscape): settles CopyOut and CopyTo RegionCopyEndpoints and refuses uncopied region escapes``() =
        let source = """
module RegionEscapeSample

let processAndExtract (input: int array) =
    let region = Region.create 4
    let len = Array.length input
    let temp = Region.alloc<int> region len
    let v = input.[0]
    if v >= 0 && v <= 100 then
        temp.[0] <- v * v
    else
        temp.[0] <- 0
    let result = Region.copyOut<int> temp len
    Region.release region
    result

let copyBetweenRegions () =
    let dstRegion = Region.create 4
    let srcRegion = Region.create 4
    let temp = Region.alloc<int> srcRegion 4
    temp.[0] <- 99
    let copied = Region.copyTo<int> temp dstRegion 4
    Region.release srcRegion
    let v = copied.[0]
    Region.release dstRegion
    v

[<EntryPoint>]
let main _ =
    let src = [| 7; 8; 9 |]
    let outArr = processAndExtract src
    let v2 = copyBetweenRegions ()
    Console.writeln (Format.int (outArr.[0] + v2))
    0
"""
        let graph = AsyncAndRegionFixture.check "22_RegionEscape" source
        let revision = AsyncAndRegionFixture.publish graph
        Assert.Equal(2, revision.Codata.RegionCopyEndpoints.Count)
        let copyOutRow =
            revision.Codata.RegionCopyEndpoints.Values
            |> Seq.find (fun c -> c.Kind = Fidelity.PSG.RegionCopyKind.CopyOut)
        Assert.True(copyOutRow.DestinationRegion.IsNone)
        Assert.Equal(Some Fidelity.PSG.EscapeKind.EscapesViaReturn, revision.Codata.Escapes.TryFind copyOutRow.DestinationStorage)
        Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[copyOutRow.EscapeDischargeObligation])
        let copyToRow =
            revision.Codata.RegionCopyEndpoints.Values
            |> Seq.find (fun c -> c.Kind = Fidelity.PSG.RegionCopyKind.CopyTo)
        Assert.True(copyToRow.DestinationRegion.IsSome)
        Assert.Equal(32L, copyToRow.SourceByteExtent)
        Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[copyToRow.EscapeDischargeObligation])

        let negSource = """
module UncopiedRegionEscape

let dangerous (flag: bool) =
    let r = Region.create 4
    let data = Region.alloc<int> r 10
    data.[0] <- 42
    let other = [| 1 |]
    Region.release r
    if flag then data else other

[<EntryPoint>]
let main _ =
    let escaped = dangerous true
    0
"""
        let negRes = AsyncAndRegionFixture.checkRaw "22_RegionEscape_neg" negSource
        Assert.Contains(negRes.Diagnostics, fun d -> d.Code = "CCS8406")

        let overCopy = """
module OverCopy

let over () =
    let r = Region.create 1
    let temp = Region.alloc<int> r 4
    temp.[0] <- 1
    let result = Region.copyOut<int> temp 8
    Region.release r
    result

[<EntryPoint>]
let main _ =
    let a = over ()
    0
"""
        let overRes = AsyncAndRegionFixture.checkRaw "22_RegionEscape_over" overCopy
        Assert.Contains(overRes.Diagnostics, fun d -> d.Code = "CCS8405")

namespace Clef.Compiler.Service.Tests

open System
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Receipts = Clef.Compiler.Nanopass.ObligationDischarge
module BatchHost = Clef.Compiler.Utilities.HostTools

/// clef #134: the editor's design-time receipts come from ObligationDischarge
/// and carry the compiler run's reasons byte for byte.
module internal DesignTimeReceiptFixture =
    let budget = { Receipts.DesignTimeBudget.PerQuery = TimeSpan.FromSeconds 20.; Receipts.DesignTimeBudget.Total = TimeSpan.FromMinutes 2. }

    let plain id body : ObligationInfo =
        { Id = id; Kind = "capacity-positive"; Logic = "QF_LIA"; Statement = "declared capacity is positive"
          Source = "receipts.clef:3:5"; Refs = []; Body = body }

    /// The compiler run over one obligation: its error text, or None when it discharges.
    let compilerReason overrideProjection (ob: ObligationInfo) =
        match Receipts.dischargeWithProjectionOverride overrideProjection [ ob ] with
        | Ok _ -> None
        | Error reason -> Some reason

    /// The real snapshot-borrow obligation of a checked graph and its published projection.
    let snapshotBorrow () =
        let graph, domain, call = RuntimeSnapshotWriteFixture.dynamicAdmitted ()
        let snapshot = Assert.Single domain.StringBorrowSnapshots
        let copy = Assert.Single domain.StringBorrowCopies
        let allocation = Assert.Single domain.StringBorrowAllocations
        let borrow = domain.IntrinsicProofs |> List.filter (fun proof -> proof.Site = call.Site && proof.Ordinal = 1) |> Assert.Single
        let info =
            match graph.Nodes[borrow.Obligation].Kind with
            | SemanticKind.Obligation info -> info
            | _ -> failwith "Missing actual snapshot borrow obligation."
        let nodeId = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId
        let projection =
            match Fidelity.PSG.SnapshotBorrowProof.ofBounds (nodeId call.Count) (nodeId snapshot.Site) (nodeId copy.Site) (nodeId allocation.Site) 2I 3I (bigint allocation.ElementBytes) (allocation.MaximumCount * bigint allocation.ElementBytes) with
            | Ok projection -> projection
            | Error reason -> failwith reason
        graph, info, projection

type DesignTimeReceiptCases() =
    let countVar = Fidelity.PSG.ResourceProof.Expr.Variable "snapshot_count"
    let copyExtentVar = Fidelity.PSG.ResourceProof.Expr.Variable "snapshot_copy_extent"
    let capacityVar = Fidelity.PSG.ResourceProof.Expr.Variable "snapshot_allocation_capacity"
    let zero = Fidelity.PSG.ResourceProof.Expr.Integer 0I

    [<Fact>]
    member _.``Design-time receipts type every outcome of a checked snapshot and carry the compiler run's reasons byte for byte``() =
        let graph, info, projection = DesignTimeReceiptFixture.snapshotBorrow ()
        let tautological =
            { info with Id = info.Id + "_tautological" }
        let ignoring =
            { info with Id = info.Id + "_ignoring" }
        let tautologicalProjection =
            { projection with
                Conclusion =
                    Fidelity.PSG.ResourceProof.Expr.And
                        [ Fidelity.PSG.ResourceProof.Expr.LessOrEqual(zero, countVar)
                          Fidelity.PSG.ResourceProof.Expr.LessOrEqual(countVar, countVar)
                          Fidelity.PSG.ResourceProof.Expr.LessOrEqual(copyExtentVar, capacityVar) ] }
        let ignoringProjection =
            { projection with Conclusion = Fidelity.PSG.ResourceProof.Expr.LessOrEqual(zero, countVar) }
        let overrideProjection (ob: ObligationInfo) =
            if ob.Id = tautological.Id then Some tautologicalProjection
            elif ob.Id = ignoring.Id then Some ignoringProjection
            else None
        let proved = DesignTimeReceiptFixture.plain "receipts_capacity_four" (ObligationBody.CapacityPositive 4)
        let refuted = DesignTimeReceiptFixture.plain "receipts_capacity_zero" (ObligationBody.CapacityPositive 0)
        let blockers = [ "declared capacity has no settled source"; "space declaration is withdrawn" ]
        let pending = DesignTimeReceiptFixture.plain "receipts_capacity_pending" (ObligationBody.Pending blockers)
        let checkedSnapshot = Receipts.ofGraph graph
        Assert.Contains(checkedSnapshot, fun ob -> ob.Id = info.Id)
        let shared source (ob: ObligationInfo) = { ob with Id = "receipts_shared"; Source = source }
        let first = shared "receipts.clef:7:1" proved
        let occurrences = [ first; shared "receipts.clef:8:1" pending; shared "receipts.clef:9:1" refuted; first ]
        let snapshot = checkedSnapshot @ [ tautological; ignoring; proved; refuted; pending ] @ occurrences

        let receipts = Receipts.designTimeReceiptsWithProjectionOverride DesignTimeReceiptFixture.budget overrideProjection snapshot
        Assert.Equal<string list>(snapshot |> List.map _.Id, receipts |> List.map _.ObligationId)
        let singleton ob =
            Receipts.designTimeReceiptsWithProjectionOverride DesignTimeReceiptFixture.budget overrideProjection [ob] |> List.exactlyOne
        Assert.Equal<Receipts.ObligationReceipt list>(List.map singleton snapshot, receipts)
        let actual = receipts |> List.skip (snapshot.Length - occurrences.Length)
        Assert.Equal<Receipts.DesignTimeVerdict list>(
            [ Receipts.DesignTimeVerdict.Proved; Receipts.DesignTimeVerdict.Pending blockers
              Receipts.DesignTimeVerdict.Refuted; Receipts.DesignTimeVerdict.Proved ], actual |> List.map _.Verdict)
        let receiptOf id = receipts |> List.find (fun receipt -> receipt.ObligationId = id)

        // Byte identity: every receipt's reason is the compiler run's error for that obligation.
        for ob, receipt in List.zip snapshot receipts do
            Assert.Equal(DesignTimeReceiptFixture.compilerReason overrideProjection ob, receipt.Reason)
            Assert.Equal(ob.Kind, receipt.Kind)
            Assert.Equal(ob.Source, receipt.Source)

        // The checked graph's inventory proves, and its compiler run discharges.
        for ob in checkedSnapshot do
            Assert.Equal(Receipts.DesignTimeVerdict.Proved, (receiptOf ob.Id).Verdict)
        Assert.True(Result.isOk (Receipts.discharge checkedSnapshot))

        // Proved conditional obligation: SAT(H), SAT(not C_i) per clause with relevance, UNSAT(H and not C).
        let borrow = receiptOf info.Id
        Assert.Equal(None, borrow.Reason)
        Assert.Equal("sat", (Assert.Single borrow.Premises).Verdict)
        Assert.Equal<string option list>([ Some "(<= 0 snapshot_count)"; Some "(<= snapshot_copy_extent snapshot_allocation_capacity)" ], borrow.NonVacuity |> List.map _.Clause)
        Assert.All(borrow.NonVacuity, fun clause -> Assert.Equal("sat", clause.Verdict))
        Assert.Equal<string list>([ "snapshot_allocation_capacity"; "snapshot_copy_extent"; "snapshot_count" ], borrow.Participants)
        Assert.Empty borrow.IgnoredParticipants
        let evidence = Assert.Single borrow.Evidence
        Assert.Equal("unsat", evidence.Verdict)
        match Receipts.discharge [ info ] with
        | Ok compiler -> Assert.Equal<Receipts.ProofStageReceipt list>(compiler.Evidence, borrow.Evidence)
        | Error reason -> failwithf "The compiler run refused the proved obligation: %s" reason

        // Tautological clause: the per-clause SAT(not C_1) is unsat.
        let tautologicalReceipt = receiptOf tautological.Id
        Assert.Equal(Receipts.DesignTimeVerdict.ValidWithoutPremises(1, "(<= snapshot_count snapshot_count)"), tautologicalReceipt.Verdict)
        Assert.Equal(Some(sprintf "obligation %s (%s) clause 1 is valid without premises: (<= snapshot_count snapshot_count)" tautological.Id tautological.Kind), tautologicalReceipt.Reason)
        Assert.Equal<string list>([ "sat"; "unsat" ], tautologicalReceipt.NonVacuity |> List.map _.Verdict)
        Assert.Empty tautologicalReceipt.Premises
        Assert.Empty tautologicalReceipt.Evidence

        // Ignored participants: every clause is non-vacuous, relevance refuses.
        let ignoringReceipt = receiptOf ignoring.Id
        Assert.Equal(Receipts.DesignTimeVerdict.IgnoresParticipants [ "snapshot_allocation_capacity"; "snapshot_copy_extent" ], ignoringReceipt.Verdict)
        Assert.Equal(Some(sprintf "obligation %s (%s) conclusion ignores participant variables: snapshot_allocation_capacity, snapshot_copy_extent" ignoring.Id ignoring.Kind), ignoringReceipt.Reason)
        Assert.Equal<string list>([ "snapshot_allocation_capacity"; "snapshot_copy_extent" ], ignoringReceipt.IgnoredParticipants)
        Assert.All(ignoringReceipt.NonVacuity, fun clause -> Assert.Equal("sat", clause.Verdict))

        // Ordinary obligations.
        let provedReceipt = receiptOf proved.Id
        Assert.Equal(Receipts.DesignTimeVerdict.Proved, provedReceipt.Verdict)
        Assert.Equal(None, provedReceipt.Reason)
        let refutedReceipt = receiptOf refuted.Id
        Assert.Equal(Receipts.DesignTimeVerdict.Refuted, refutedReceipt.Verdict)
        Assert.Equal(Some "Obligation 'receipts_capacity_zero' (receipts.clef:3:5) was not discharged: solver returned 'sat'", refutedReceipt.Reason)
        Assert.Equal("sat", (Assert.Single refutedReceipt.Evidence).Verdict)

        // Pending keeps its blockers; its reason is the compiler run's unavailable-premise text.
        let pendingReceipt = receiptOf pending.Id
        Assert.Equal(Receipts.DesignTimeVerdict.Pending blockers, pendingReceipt.Verdict)
        Assert.Equal(Some "Required obligations have unavailable premises: 'receipts_capacity_pending' (receipts.clef:3:5): declared capacity has no settled source; space declaration is withdrawn", pendingReceipt.Reason)
        Assert.Empty pendingReceipt.Evidence

        // One refusal in an otherwise proved inventory: the whole compiler run reports that receipt's reason.
        for ob in [ tautological; ignoring; refuted; pending ] do
            match Receipts.dischargeWithProjectionOverride overrideProjection (checkedSnapshot @ [ proved; ob ]) with
            | Ok _ -> failwithf "The compiler run discharged %s" ob.Id
            | Error reason -> Assert.Equal((receiptOf ob.Id).Reason, Some reason)

    [<Fact>]
    member _.``Design-time receipts honour the caller's per-query and total budgets without recording a cut-off answer``() =
        let stamp = Guid.NewGuid().ToString("N")
        let fresh = DesignTimeReceiptFixture.plain ("receipts_budget_" + stamp) (ObligationBody.CapacityPositive 7919)
        let exhausted = { Receipts.DesignTimeBudget.PerQuery = TimeSpan.FromSeconds 20.; Receipts.DesignTimeBudget.Total = TimeSpan.Zero }
        let receipt = Receipts.designTimeReceipts exhausted [ fresh ] |> Assert.Single
        Assert.Equal(Receipts.DesignTimeVerdict.Undecided "psg", receipt.Verdict)
        Assert.Equal(Some "cvc5 was not run: the design-time budget of 0 ms was exhausted", receipt.Reason)
        Assert.Empty receipt.Evidence

        let instant = { Receipts.DesignTimeBudget.PerQuery = TimeSpan.FromMilliseconds 1.; Receipts.DesignTimeBudget.Total = TimeSpan.FromMinutes 1. }
        let cut = Receipts.designTimeReceipts instant [ fresh ] |> Assert.Single
        Assert.Equal(Receipts.DesignTimeVerdict.Undecided "psg", cut.Verdict)
        Assert.Equal(Some "cvc5 did not answer within the per-query limit of 1 ms", cut.Reason)

        // Neither limit recorded an answer: a sufficient budget decides the same query.
        let decided = Receipts.designTimeReceipts DesignTimeReceiptFixture.budget [ fresh ] |> Assert.Single
        Assert.Equal(Receipts.DesignTimeVerdict.Proved, decided.Verdict)
        Assert.Equal(None, decided.Reason)

    [<Fact>]
    member _.``Batched cvc5 checks reset shared declarations and return each query's independent verdict``() =
        let stamp = Guid.NewGuid().ToString("N")
        let prelude = sprintf "(set-logic QF_LIA)\n; %s\n(declare-const shared Int)\n" stamp
        let sat = prelude + "; \"__clef_query_0_0_begin\" \"__clef_query_1_0_begin\"\n(assert (= shared 0))\n(check-sat)"
        let unsat = prelude + "(assert (< shared shared))\n(check-sat)"
        let queries = [unsat; sat; unsat]
        let marker, framed = BatchHost.frameQueries queries
        List.iteri (fun ordinal _ ->
            for side in ["begin"; "end"] do
                let boundary = marker ordinal side
                Assert.Contains("(echo " + boundary + ")", framed)
                for query in queries do Assert.DoesNotContain(boundary, query)) queries
        let answers = BatchHost.runSolverBatch queries
        Assert.Equal<Result<string list, string> list>(
            [Ok ["unsat"]; Ok ["sat"]; Ok ["unsat"]], queries |> List.map (fun query -> answers[query]))

    [<Fact>]
    member _.``Batched cvc5 replay preserves malformed singleton output and both independent siblings``() =
        let prelude = sprintf "(set-logic QF_LIA)\n; %s\n" (Guid.NewGuid().ToString("N"))
        let sat = prelude + "(assert true)\n(check-sat)"
        let two = prelude + "(check-sat)\n(reset)\n(set-logic QF_LIA)\n(assert false)\n(check-sat)"
        let unsat = prelude + "(assert false)\n(check-sat)"
        let answers = BatchHost.runSolverBatch [sat; two; unsat]
        Assert.Equal<Result<string list, string>>(Ok ["sat"], answers[sat])
        Assert.Equal<Result<string list, string>>(Ok ["unsat"], answers[unsat])
        Assert.Equal<Result<string list, string>>(Ok ["sat"; "unsat"], answers[two])
        Assert.Equal<Result<string list, string>>(BatchHost.runSolver two, answers[two])

    [<Fact>]
    member _.``Mixed foreign readiness keeps independent refusals for occurrences sharing an anchor``() =
        let hypothesis : ForeignResultHypothesis =
            { Quote = NodeId 4; Declaration = NodeId 1; Identity = "posix-read"; Version = "profile-1"; Source = "pilot/read"
              Lower = ForeignResultBound.Constant -1I; Upper = ForeignResultBound.Argument 0 }
        let model : ForeignResultCoverageModel =
            { Application = { Declaration = NodeId 1; Call = NodeId 2; Context = [NodeId 5]; Hypothesis = Some hypothesis
                              Arguments = [{ Index = 0; Node = NodeId 3; Enclosure = ValueRange.Bounded(4I, 4I) }] }
              Role = ForeignResultProofRole.LogicalCoverage; AbiRange = ValueRange.Bounded(-8I, 7I); ResultRange = ValueRange.Bounded(-1I, 4I)
              Destination = ValueRange.Bounded(-8I, 7I); DestinationDeclaration = Some(NodeId 6); Abi = Some(NodeId 7)
              AbiIdentity = None; DestinationIdentity = None }
        let anchor = "duplicate_foreign_coverage"
        let occurrence site source coverage =
            NodeId site, { DesignTimeReceiptFixture.plain anchor (ObligationBody.ForeignResultCoverage coverage) with
                             Kind = "foreign-result-coverage"; Source = source }
        let absent = occurrence 21 "foreign.clef:1:2" { model with Application = { model.Application with Hypothesis = None } }
        let ready = occurrence 22 "foreign.clef:2:2" model
        let unbounded = occurrence 23 "foreign.clef:3:2" { model with AbiRange = ValueRange.Unbounded }
        let refusals = Receipts.unavailableByOccurrence [absent; ready; unbounded]
        Assert.Equal(2, refusals.Count)
        Assert.False(refusals.ContainsKey(fst ready))
        for (site, info), reason in [absent, "Foreign result behavior contract is missing"
                                     unbounded, "Foreign result coverage has no established finite ABI enclosure"] do
            let refusal = refusals[site]
            Assert.Equal(anchor, refusal.Anchor)
            Assert.Equal(info.Source, refusal.Source)
            Assert.Equal<string list>([reason], refusal.MissingPremises)

    [<Fact>]
    member _.``The solver resolves the exact PATH executable before host installations``() =
        let name = if OperatingSystem.IsWindows() then "cvc5.exe" else "cvc5"
        let directory = IO.Path.Combine(IO.Path.GetTempPath(), "solver tools")
        let selected = IO.Path.Combine(directory, name)
        Assert.Equal(selected, Receipts.resolveSolver directory (fun path -> path = selected || List.contains path Receipts.solverToolchainPaths))
        Assert.Equal(Receipts.solverToolchainPaths.Head, Receipts.resolveSolver "" (fun path -> List.contains path Receipts.solverToolchainPaths))
        Assert.Equal(name, Receipts.resolveSolver null (fun _ -> false))

[<CollectionDefinition("Solver environment", DisableParallelization = true)>]
type SolverEnvironmentCollection() = class end

[<Collection("Solver environment")>]
type SolverEnvironmentCases() =
    [<Fact>]
    member _.``Solver override is resolved for each call and unavailable starts do not poison cached receipts``() =
        let previous = Environment.GetEnvironmentVariable "CLEF_CVC5"
        let solver = Receipts.resolveSolver (Environment.GetEnvironmentVariable "PATH") IO.File.Exists
        let missing = IO.Path.Combine(IO.Path.GetTempPath(), "missing-cvc5-" + Guid.NewGuid().ToString("N"))
        let obligation = DesignTimeReceiptFixture.plain ("solver_override_" + Guid.NewGuid().ToString("N")) (ObligationBody.CapacityPositive 4)
        let discharge () = Receipts.designTimeReceipts DesignTimeReceiptFixture.budget [ obligation ] |> Assert.Single
        try
            Environment.SetEnvironmentVariable("CLEF_CVC5", solver)
            Assert.Equal(Receipts.DesignTimeVerdict.Proved, (discharge ()).Verdict)
            Environment.SetEnvironmentVariable("CLEF_CVC5", missing)
            let unavailable = discharge ()
            Assert.Equal(Receipts.DesignTimeVerdict.SolverUnavailable, unavailable.Verdict)
            Assert.True(unavailable.Reason.IsSome)
            Environment.SetEnvironmentVariable("CLEF_CVC5", solver)
            Assert.Equal(Receipts.DesignTimeVerdict.Proved, (discharge ()).Verdict)
        finally
            Environment.SetEnvironmentVariable("CLEF_CVC5", previous)

    [<Fact>]
    member _.``ObligationDischarge launches cvc5 with one ArgumentList item per argument and handles spaces in the query path``() =
        let previousSolver = Environment.GetEnvironmentVariable "CLEF_CVC5"
        let previousTempDir = Environment.GetEnvironmentVariable "CLEF_PROOF_TEMP_DIR"
        let solver = Receipts.resolveSolver (Environment.GetEnvironmentVariable "PATH") IO.File.Exists
        let scratchRoot = IO.Path.GetFullPath(IO.Path.Combine(__SOURCE_DIRECTORY__, "..", "..", "artifacts", "scratch", "design-time-receipt-cases"))
        let spacedDir = IO.Path.Combine(scratchRoot, "clef proof space " + Guid.NewGuid().ToString("N"))
        try
            IO.Directory.CreateDirectory spacedDir |> ignore
            let sampleTempPath = IO.Path.Combine(spacedDir, "clef-proof-sample.smt2")
            let psi = Receipts.solverStartInfo solver sampleTempPath
            Assert.Equal("", psi.Arguments)
            Assert.Equal<string list>([ "--lang"; "smt2"; sampleTempPath ], psi.ArgumentList |> Seq.toList)
            let obligation = DesignTimeReceiptFixture.plain ("solver_spaced_path_" + Guid.NewGuid().ToString("N")) (ObligationBody.CapacityPositive 4)
            Environment.SetEnvironmentVariable("CLEF_CVC5", solver)
            Environment.SetEnvironmentVariable("CLEF_PROOF_TEMP_DIR", spacedDir)
            let receipt = Receipts.designTimeReceipts DesignTimeReceiptFixture.budget [ obligation ] |> Assert.Single
            Assert.Equal(Receipts.DesignTimeVerdict.Proved, receipt.Verdict)
        finally
            Environment.SetEnvironmentVariable("CLEF_CVC5", previousSolver)
            Environment.SetEnvironmentVariable("CLEF_PROOF_TEMP_DIR", previousTempDir)
            if IO.Directory.Exists spacedDir then IO.Directory.Delete(spacedDir, true)
            if IO.Directory.Exists scratchRoot && (IO.Directory.EnumerateFileSystemEntries scratchRoot |> Seq.isEmpty) then
                IO.Directory.Delete(scratchRoot, false)

module Segments = Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation
module Rebuild = Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild

/// Small, fully indexed source graphs keep the invalidation controls independent
/// of unrelated platform settlement. Every fixture stays in the primary graph.
module internal SelectiveRebuildFixture =
    let graph shift =
        let checkedGraph = (DimensionalCases.check "let identity (value: int) = value\n").Graph
        let template = checkedGraph.Nodes.Values |> Seq.head
        let id number = NodeId(number + shift)
        let node number parent kind children =
            { template with Id = id number; Parent = parent |> Option.map id; Kind = kind
                            Type = Types.intType; Children = List.map id children
                            IsReachable = true; Metadata = Map.empty; ValueRange = None
                            SRTPResolution = None; LayoutHint = None; EmissionStrategy = EmissionStrategy.Inline }
        let lambda number parent parameters body children =
            node number (Some parent) (SemanticKind.Lambda(parameters |> List.map (fun n -> "arg", Types.intType, id n), id body, [], None, LambdaContext.RegularClosure)) children
        let nodes =
            [ node 1 None (SemanticKind.ModuleDef("Selective", [2;6;11;14;16;27] |> List.map id)) [2;6;11;14;16;27]
              node 2 (Some 1) (SemanticKind.Binding("provider", false, false, None)) [3]
              lambda 3 2 [4] 5 [4;5]
              node 4 (Some 3) (SemanticKind.PatternBinding "arg") []
              node 5 (Some 3) (SemanticKind.Sequential([20;22;25] |> List.map id)) [20;22;25]
              node 20 (Some 5) (SemanticKind.Binding("local", true, false, None)) [21]
              node 21 (Some 20) (SemanticKind.Literal(NativeLiteral.Int(1L, NTUKind.NTUint(NTUWidth.Fixed 32)))) []
              node 22 (Some 5) (SemanticKind.Set(id 23, id 24)) [23;24]
              node 23 (Some 22) (SemanticKind.VarRef("local", Some(id 20))) []
              node 24 (Some 22) (SemanticKind.Literal(NativeLiteral.Int(2L, NTUKind.NTUint(NTUWidth.Fixed 32)))) []
              node 25 (Some 5) (SemanticKind.VarRef("local", Some(id 20))) []
              node 6 (Some 1) (SemanticKind.Binding("caller", false, false, None)) [7]
              lambda 7 6 [] 8 [8]
              node 8 (Some 7) (SemanticKind.Application(id 9, [id 10])) [9;10]
              node 9 (Some 8) (SemanticKind.VarRef("provider", Some(id 2))) []
              node 10 (Some 8) (SemanticKind.VarRef("shared", Some(id 14))) []
              node 11 (Some 1) (SemanticKind.Binding("sibling", false, false, None)) [12]
              lambda 12 11 [] 13 [13]
              node 13 (Some 12) (SemanticKind.Literal(NativeLiteral.Int(99L, NTUKind.NTUint(NTUWidth.Fixed 32)))) []
              node 14 (Some 1) (SemanticKind.Binding("shared", true, false, None)) [15]
              node 15 (Some 14) (SemanticKind.Literal(NativeLiteral.Int(7L, NTUKind.NTUint(NTUWidth.Fixed 32)))) []
              node 16 (Some 1) (SemanticKind.Binding("factory", false, false, None)) [17]
              lambda 17 16 [] 18 [18]
              node 18 (Some 17) (SemanticKind.ClosureValue(id 26, id 19)) [19]
              node 19 (Some 18) (SemanticKind.EnvironmentCreate(id 26, [id 14, id 31])) [31]
              node 31 (Some 19) (SemanticKind.VarRef("shared", Some(id 14))) []
              node 27 (Some 1) (SemanticKind.Binding("capturedCode", false, false, None)) [26]
              lambda 26 27 [29] 28 [29;28]
              node 29 (Some 26) (SemanticKind.PatternBinding "__environment") []
              node 28 (Some 26) (SemanticKind.EnvironmentRead(id 30, id 14)) [30]
              node 30 (Some 28) (SemanticKind.VarRef("__environment", Some(id 29))) [] ]
            |> List.map (fun node -> node.Id, node) |> Map.ofList
        let slot =
            { Source = id 14; ValueType = Types.intType
              Field = { Name = "shared"; Slot = SettledSlot.Integer(32, None); Offset = Some 0; Size = Some 4; Align = Some 4 }
              Holds = CaptureSlotKind.Scalar(SettledSlot.Integer(32, None)); IsCapture = true }
        let layout =
            { Owner = id 26; Implementation = id 26; Formal = id 29
              Slots = [slot]; Bytes = 4; Alignment = 4; Obligations = [] }
        { checkedGraph with Nodes = nodes; Edges = []; DeclarationRoots = [id 6, DeclRoot.EntryPoint]
                            Codata = lazy { Codata.empty with EnvironmentLayouts = Map.ofList [id 26, layout];
                                                             EnvironmentOrigins = Map.ofList [id 19, id 26; id 30, id 26] }
                            WitnessProvenance = None; SequenceRangeProvenance = None; RangeContextFacts = None }

    let admitted = function Result.Ok result -> result | Result.Error errors -> failwithf "%A" errors
    let change number value (graph: SemanticGraph) =
        let node = graph.Nodes[NodeId number]
        { graph with Nodes = graph.Nodes.Add(node.Id, { node with Kind = SemanticKind.Literal(NativeLiteral.Int(int64 value, NTUKind.NTUint(NTUWidth.Fixed 32))) }) }
    let disposition name (schedule: Rebuild.RebuildSchedule) = schedule.Regions["module:Selective/binding:" + name]

type SelectiveRebuildCases() =
    [<Fact>]
    member _.``Calls and local storage invalidate their owning callable while cutting off callers unless the callable interface changes``() =
        let baseline = SelectiveRebuildFixture.graph 0
        let plan = Segments.segment baseline |> SelectiveRebuildFixture.admitted
        Assert.Contains(plan.Dependencies, fun edge ->
            edge.Consumer = "module:Selective/binding:caller" && edge.Provider = "module:Selective/binding:provider" && edge.Kind = Segments.DependencyKind.Call)
        // Body-only edit inside provider (local mutable initializer 1 -> 42) cuts off caller.
        let bodyOnlyCandidate = SelectiveRebuildFixture.change 21 42 baseline
        let bodyOnlySchedule = Rebuild.scheduleRebuild baseline bodyOnlyCandidate |> SelectiveRebuildFixture.admitted
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "provider" bodyOnlySchedule)
        Assert.Equal(
            bodyOnlySchedule.Baseline.Regions["module:Selective/binding:provider"].CallableInterfaceDigest,
            bodyOnlySchedule.Candidate.Regions["module:Selective/binding:provider"].CallableInterfaceDigest)
        Assert.NotEqual(
            bodyOnlySchedule.Baseline.Regions["module:Selective/binding:provider"].SemanticRealizationDigest,
            bodyOnlySchedule.Candidate.Regions["module:Selective/binding:provider"].SemanticRealizationDigest)
        for name in ["caller"; "sibling"; "shared"; "factory"; "capturedCode"] do
            Assert.Equal(Rebuild.RegionDisposition.Retained, SelectiveRebuildFixture.disposition name bodyOnlySchedule)
        Assert.Equal(
            bodyOnlySchedule.Baseline.Regions["module:Selective/binding:caller"].CallableInterfaceDigest,
            bodyOnlySchedule.Candidate.Regions["module:Selective/binding:caller"].CallableInterfaceDigest)
        Assert.Equal(
            bodyOnlySchedule.Baseline.Regions["module:Selective/binding:caller"].SemanticRealizationDigest,
            bodyOnlySchedule.Candidate.Regions["module:Selective/binding:caller"].SemanticRealizationDigest)
        Assert.Contains(NodeId 21, bodyOnlySchedule.Receipt.Cone.AffectedCone)
        Assert.DoesNotContain(NodeId 8, bodyOnlySchedule.Scopes)
        Assert.DoesNotContain(NodeId 13, bodyOnlySchedule.Scopes)
        // Changing provider's callable interface propagates across DependencyKind.Call to caller.
        let providerBinding = bodyOnlyCandidate.Nodes[NodeId 2]
        let ifaceCandidate =
            { bodyOnlyCandidate with
                Nodes = bodyOnlyCandidate.Nodes.Add(NodeId 2, { providerBinding with LayoutHint = Some TypeLayout.PlatformWord }) }
        let ifaceSchedule = Rebuild.scheduleRebuild baseline ifaceCandidate |> SelectiveRebuildFixture.admitted
        Assert.NotEqual(
            ifaceSchedule.Baseline.Regions["module:Selective/binding:provider"].CallableInterfaceDigest,
            ifaceSchedule.Candidate.Regions["module:Selective/binding:provider"].CallableInterfaceDigest)
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "provider" ifaceSchedule)
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "caller" ifaceSchedule)
        for name in ["sibling"; "shared"; "factory"; "capturedCode"] do
            Assert.Equal(Rebuild.RegionDisposition.Retained, SelectiveRebuildFixture.disposition name ifaceSchedule)

    [<Fact>]
    member _.``Module storage closes over callers environment formation and captured code without coupling siblings``() =
        let baseline = SelectiveRebuildFixture.graph 0
        let candidate = SelectiveRebuildFixture.change 15 12 baseline
        let schedule = Rebuild.scheduleRebuild baseline candidate |> SelectiveRebuildFixture.admitted
        for name in ["shared"; "caller"; "factory"; "capturedCode"] do
            Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition name schedule)
        for name in ["provider"; "sibling"] do
            Assert.Equal(Rebuild.RegionDisposition.Retained, SelectiveRebuildFixture.disposition name schedule)
        Assert.Contains(schedule.Candidate.SupportEdges, fun edge ->
            edge.Domain = "ClosureDomain.Layouts" && edge.SupportNodes.Contains(NodeId 14))
        // Code identity and the actual formation remain distinct regions.
        Assert.NotEqual(schedule.Candidate.NodeOwners[NodeId 19], schedule.Candidate.NodeOwners[NodeId 26])

    [<Fact>]
    member _.``Proof support layout changes invalidate consumers even when executable nodes are unchanged``() =
        let baseline = SelectiveRebuildFixture.graph 0
        let codata = baseline.Codata.Value
        let layout = codata.EnvironmentLayouts[NodeId 26]
        let candidate =
            { baseline with Codata = lazy { codata with EnvironmentLayouts = codata.EnvironmentLayouts.Add(layout.Owner, { layout with Bytes = 8; Alignment = 8 }) } }
        let schedule = Rebuild.scheduleRebuild baseline candidate |> SelectiveRebuildFixture.admitted
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "capturedCode" schedule)
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "factory" schedule)
        Assert.Equal(Rebuild.RegionDisposition.Retained, SelectiveRebuildFixture.disposition "sibling" schedule)
        Assert.Empty schedule.Receipt.Cone.AffectedCone

    [<Fact>]
    member _.``NodeId reset and renumbering preserve declaration fingerprints retention and empty recipe scheduling``() =
        let baseline = SelectiveRebuildFixture.graph 0 |> Clef.Compiler.Nanopass.SSAAssignment.normalize
        NodeId.reset()
        let candidate = SelectiveRebuildFixture.graph 1000
        let _, schedule, recipes = Rebuild.rebuildSelective baseline candidate |> SelectiveRebuildFixture.admitted
        for KeyValue(identity, region) in schedule.Baseline.Regions do
            Assert.Equal(region.CallableInterfaceDigest, schedule.Candidate.Regions[identity].CallableInterfaceDigest)
            Assert.Equal(region.SemanticRealizationDigest, schedule.Candidate.Regions[identity].SemanticRealizationDigest)
            Assert.Equal(region.CanonicalProofSupportDigest, schedule.Candidate.Regions[identity].CanonicalProofSupportDigest)
            Assert.Equal(Rebuild.RegionDisposition.Retained, schedule.Regions[identity])
        Assert.Equal(NodeId 1002, schedule.Receipt.Alignment[NodeId 2])
        Assert.Empty schedule.Scopes
        Assert.Empty recipes.Recipes
        Assert.Empty recipes.Diagnostics
        Assert.Empty schedule.Receipt.Cone.AffectedCone
        Assert.Empty schedule.Receipt.Cone.NewlyLitNodes
        Assert.Empty schedule.Receipt.Cone.ExtinguishedNodes

    [<Fact>]
    member _.``Unresolved callable targets have an exact typed refusal and never enter Baker``() =
        let baseline = SelectiveRebuildFixture.graph 0
        let target = baseline.Nodes[NodeId 9]
        let candidate =
            { baseline with Nodes = baseline.Nodes.Add(target.Id, { target with Kind = SemanticKind.VarRef("unknown", None) }) }
        let expected = Segments.SegmentationFailure.UnresolvedCallable(NodeId 8, NodeId 9)
        match Segments.segment candidate with
        | Result.Error errors -> Assert.Contains(expected, errors)
        | Result.Ok _ -> failwith "An unresolved callable target was segmented."
        match Rebuild.rebuildSelective baseline candidate with
        | Result.Error(Rebuild.RebuildFailure.InvalidCandidate errors) -> Assert.Contains(expected, errors)
        | result -> failwithf "Expected a typed refusal before recipe creation: %A" result

    [<Fact>]
    member _.``Broken environment layout and invalid baseline are refused without whole graph fallback``() =
        let baseline = SelectiveRebuildFixture.graph 0
        let candidate = { baseline with Codata = lazy { baseline.Codata.Value with EnvironmentLayouts = Map.empty } }
        let expected = Segments.SegmentationFailure.BrokenEnvironment(NodeId 19, "Environment formation requires its exact indexed layout and slots.")
        match Rebuild.rebuildSelective baseline candidate with
        | Result.Error(Rebuild.RebuildFailure.InvalidCandidate errors) -> Assert.Contains(expected, errors)
        | result -> failwithf "Expected an environment refusal: %A" result
        let broken = { baseline with Nodes = baseline.Nodes.Remove(NodeId 2) }
        match Rebuild.rebuildSelective broken baseline with
        | Result.Error(Rebuild.RebuildFailure.InvalidBaseline errors) ->
            Assert.Contains(errors, function Segments.SegmentationFailure.InvalidGraph(_, "A structural or reference target is absent from the graph.") -> true | _ -> false)
        | result -> failwithf "Expected an invalid baseline refusal: %A" result
        match Rebuild.rebuildSelective { baseline with Nodes = Map.empty } baseline with
        | Result.Error Rebuild.RebuildFailure.MissingBaseline -> ()
        | result -> failwithf "Expected a missing baseline refusal: %A" result

        let baselineWithAssignment = Clef.Compiler.Nanopass.SSAAssignment.normalize baseline
        match Rebuild.rebuildSelective baseline baselineWithAssignment with
        | Result.Error(Rebuild.RebuildFailure.InvalidBaseline
            [Segments.SegmentationFailure.InvalidGraph(None, "The accepted baseline graph has no SSA assignment plan.")]) -> ()
        | result -> failwithf "Expected refusal of a missing SSA plan: %A" result

        let codata = baselineWithAssignment.Codata.Value
        let plan = codata.SSAAssignment.Value
        let retained = NodeId 21
        Assert.NotEmpty(plan.Assignments[retained])
        let incomplete = { plan with Assignments = plan.Assignments.Remove retained }
        let prior = { baselineWithAssignment with Codata = lazy { codata with SSAAssignment = Some incomplete } }
        match Rebuild.rebuildSelective prior baselineWithAssignment with
        | Result.Error(Rebuild.RebuildFailure.InvalidBaseline
            [Segments.SegmentationFailure.InvalidGraph(Some occurrence, "The accepted baseline lacks the exact SSA assignment for a retained occurrence.")]) ->
            Assert.Equal(retained, occurrence)
        | result -> failwithf "Expected refusal of a missing retained assignment: %A" result

        let retainedWithoutAlignment =
            DimensionalCases.reconcileCheckedPhysical baselineWithAssignment Map.empty (Set.singleton retained) baselineWithAssignment
        match retainedWithoutAlignment with
        | Result.Error (DimensionalCases.CheckedPhysicalReconciliationFailure.Correspondence (Segments.PhysicalCorrespondenceFailure.MissingRetainedCorrespondence occurrence)) ->
            Assert.Equal(retained, occurrence)
        | result -> failwithf "Expected refusal of missing retained correspondence: %A" result

    [<Fact>]
    member _.``SSA reconciliation reports CCS8407 for ambiguous retained correspondence``() =
        let baseline = SelectiveRebuildFixture.graph 0 |> Clef.Compiler.Nanopass.SSAAssignment.normalize
        let incoming = SelectiveRebuildFixture.graph 1000
        let retained = NodeId 21
        let competing = NodeId 13
        let current = NodeId 1021
        let node = incoming.Nodes[current]
        let range = { node.Range with File = "retained-correspondence.clef" }
        let candidate = { incoming with Nodes = incoming.Nodes.Add(current, { node with Range = range }) }
        let family = baseline.Codata.Value.SSAAssignment.Value.Assignments
        Assert.NotEmpty(family[retained])
        Assert.NotEmpty(family[competing])
        let scope = Set.singleton current
        let alignment = Map.ofList [retained, current]
        let _, exact = DimensionalCases.reconcileCheckedPhysical baseline alignment scope candidate |> SelectiveRebuildFixture.admitted
        Assert.Equal(retained, exact.NodeRemap[current])
        Assert.True(exact.Assignments[retained] = family[retained])

        let ambiguous = alignment.Add(competing, current)
        match DimensionalCases.reconcileCheckedPhysical baseline ambiguous scope candidate with
        | Result.Error (DimensionalCases.CheckedPhysicalReconciliationFailure.Correspondence (Segments.PhysicalCorrespondenceFailure.AmbiguousRetainedCorrespondence diagnostic)) ->
            Assert.Equal("CCS8407", diagnostic.Code)
            Assert.Equal(Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error,
                         Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.Diagnostic.effectiveSeverity diagnostic)
            Assert.Equal("The retained occurrence has more than one admissible baseline identity.", diagnostic.Message)
            Assert.Equal(range, diagnostic.Range)
            Assert.Equal<NodeId list>([current], diagnostic.RelatedNodes)
        | result -> failwithf "Expected a hard diagnostic for ambiguous retained correspondence: %A" result

    [<Theory>]
    [<InlineData("address")>]
    [<InlineData("deref")>]
    [<InlineData("field-get")>]
    [<InlineData("field-set")>]
    [<InlineData("index-get")>]
    [<InlineData("index-set")>]
    [<InlineData("set")>]
    member _.``Storage forms preserve their program-storage dependency without coupling siblings`` shape =
        let source = SelectiveRebuildFixture.graph 0
        let operand = NodeId 10
        let kind =
            match shape with
            | "address" -> SemanticKind.AddressOf(operand, true)
            | "deref" -> SemanticKind.Deref operand
            | "field-get" -> SemanticKind.FieldGet(operand, "value")
            | "field-set" -> SemanticKind.FieldSet(operand, "value", operand)
            | "index-get" -> SemanticKind.IndexGet(operand, operand)
            | "index-set" -> SemanticKind.IndexSet(operand, operand, operand)
            | _ -> SemanticKind.Set(operand, operand)
        let old = source.Nodes[NodeId 8]
        let baseline = { source with Nodes = source.Nodes.Add(old.Id, { old with Kind = kind; Children = [operand] }) }
        let candidate = SelectiveRebuildFixture.change 15 16 baseline
        let schedule = Rebuild.scheduleRebuild baseline candidate |> SelectiveRebuildFixture.admitted
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "caller" schedule)
        Assert.Equal(Rebuild.RegionDisposition.Retained, SelectiveRebuildFixture.disposition "sibling" schedule)

    [<Fact>]
    member _.``Callable contract support changes schedule only its implementation and callers``() =
        let source = SelectiveRebuildFixture.graph 0
        let identity = NodeId 900
        let sourceType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType Types.intType
        let contract: CallableContract =
            { Identity = identity; Kind = CallableKind.OrdinaryFlatClosure; Convention = CallableConvention.Ordinary
              ParameterTypes = [sourceType]; OmittedParameters = []
              ParameterRepresentations = [0, ValueRepresentation.Scalar(SettledSlot.Integer(32, None))]
              ResultType = sourceType; ResultRepresentation = ValueRepresentation.Scalar(SettledSlot.Integer(32, None))
              EnvironmentBytes = None; SourcePremises = Map.empty
              Participants = [{ Node = NodeId 3; Role = ParticipantRole.CallableImplementation; Ordinal = 0; Group = identity }] }
        let baseline = { source with Codata = lazy { source.Codata.Value with CallableContracts = Map.ofList [identity, contract] } }
        let candidate = { baseline with Codata = lazy { baseline.Codata.Value with CallableContracts = Map.ofList [identity, { contract with EnvironmentBytes = Some 8 }] } }
        let schedule = Rebuild.scheduleRebuild baseline candidate |> SelectiveRebuildFixture.admitted
        Assert.Contains(schedule.Candidate.SupportEdges, fun edge -> edge.Domain = "CallableContracts" && edge.Consumer = "module:Selective/binding:provider")
        for name in ["provider"; "caller"] do
            Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition name schedule)
        Assert.Equal(Rebuild.RegionDisposition.Retained, SelectiveRebuildFixture.disposition "sibling" schedule)
        Assert.Empty schedule.Receipt.Cone.AffectedCone

        let assignedBaseline = SelectiveRebuildFixture.graph 897 |> Clef.Compiler.Nanopass.SSAAssignment.normalize
        let site = NodeId 3
        Assert.True(assignedBaseline.Nodes.ContainsKey identity)
        Assert.False(candidate.Nodes.ContainsKey identity)
        Segments.segment assignedBaseline |> SelectiveRebuildFixture.admitted |> ignore
        let alignment = Map.ofList [identity, site]
        let retained = Set.singleton site
        match DimensionalCases.reconcileCheckedPhysical assignedBaseline alignment retained candidate with
        | Result.Error (DimensionalCases.CheckedPhysicalReconciliationFailure.Reconciliation (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities failures)) ->
            Assert.Contains((identity, "A callable relation identity is misfiled or collides with another source identity."), failures)
        | result -> failwithf "Expected SSA to refuse overlapping retained and callable identities: %A" result

    [<Fact>]
    member _.``Memory domain support changes invalidate its consumer without changing the executable shadow cone``() =
        let source = SelectiveRebuildFixture.graph 0
        let domain: MemoryDomain =
            { Premises = Map.empty; Platform = None; Meets = Map.empty; Guards = [NodeId 8, [NodeId 14]]
              Requirements = []; StringRelations = []; AllocationConstructions = []; CopyConstructions = []
              ArrayCopies = []; Proofs = []; Required = Set.singleton(NodeId 8); Operations = []; Unresolved = Map.empty }
        let edge =
            { Class = EdgeClass.Provenance; Role = EdgeRole.MemoryDomain domain; Ordinal = 0; Sources = []; Target = NodeId 1 }
        let baseline = { source with Edges = [edge] }
        let candidate = { source with Edges = [{ edge with Role = EdgeRole.MemoryDomain { domain with Guards = [NodeId 8, [NodeId 2]] } }] }
        let schedule = Rebuild.scheduleRebuild baseline candidate |> SelectiveRebuildFixture.admitted
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "caller" schedule)
        Assert.Equal(Rebuild.RegionDisposition.Retained, SelectiveRebuildFixture.disposition "sibling" schedule)
        Assert.Contains(schedule.Candidate.SupportEdges, fun support -> support.Domain = "MemoryDomain" && support.Consumer = "module:Selective/binding:caller")
        Assert.Empty schedule.Receipt.Cone.AffectedCone

    [<Fact>]
    member _.``Source Lambda captures keep explicit dependencies before environment materialization``() =
        let source = SelectiveRebuildFixture.graph 0
        let implementation = source.Nodes[NodeId 26]
        let capture: CaptureInfo =
            { Name = "shared"; Type = Types.intType; IsMutable = true; SourceNodeId = Some(NodeId 14) }
        let kind =
            match implementation.Kind with
            | SemanticKind.Lambda(parameters, body, _, enclosing, context) ->
                SemanticKind.Lambda(parameters, body, [capture], enclosing, context)
            | _ -> failwith "Expected the source implementation."
        let baseline = { source with Nodes = source.Nodes.Add(implementation.Id, { implementation with Kind = kind }) }
        let candidate = SelectiveRebuildFixture.change 15 18 baseline
        let schedule = Rebuild.scheduleRebuild baseline candidate |> SelectiveRebuildFixture.admitted
        Assert.Contains(schedule.Candidate.Dependencies, fun edge ->
            edge.Kind = Segments.DependencyKind.CapturedEnvironment &&
            edge.Consumer = "module:Selective/binding:capturedCode" && edge.Provider = "module:Selective/binding:shared")
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "capturedCode" schedule)
        Assert.Equal(Rebuild.RegionDisposition.Retained, SelectiveRebuildFixture.disposition "sibling" schedule)

    [<Fact>]
    member _.``SSAAssignment reproduces identical identifiers across unchanged recompilation and starts cold on full rebuild``() =
        // Production full compilation (NativeService) populates Codata.SSAAssignment starting cold.
        Assert.Equal(512, Clef.Compiler.Nanopass.SSAAssignment.Family)
        let compiled = (DimensionalCases.check "let identity (value: int) = value\n[<EntryPoint>]\nlet main _ = identity 0\n").Graph
        let compiledPlan = compiled.Codata.Value.SSAAssignment |> Option.defaultWith (fun () -> failwith "Missing production SSAAssignment plan.")
        Assert.NotEmpty compiledPlan.Assignments
        Assert.Empty compiledPlan.RetainedNodes
        for KeyValue(id, slots) in compiledPlan.Assignments do
            let family = Clef.Compiler.Nanopass.SSAAssignment.familyValues id
            Assert.Equal(512, slots.Length)
            Assert.Equal<SSAId list>(family, slots)
            Assert.Equal(SSAId(NodeId.value id, 0), slots.Head)
            Assert.Equal(SSAId(NodeId.value id, 511), List.last slots)

        // Selective rebuild across unchanged structure (even when candidate NodeIds shifted after reset)
        // reproduces identical graph NodeIds (Alex witnessed SSA family V(node, ordinal)) and identical SSAAssignment slots.
        let baseline = SelectiveRebuildFixture.graph 0 |> Clef.Compiler.Nanopass.SSAAssignment.normalize
        let baselinePlan = baseline.Codata.Value.SSAAssignment.Value
        Assert.NotEmpty baselinePlan.Assignments
        Assert.Empty baselinePlan.RetainedNodes
        Assert.Equal<Set<NodeId>>(baselinePlan.Assignments |> Map.keys |> Set.ofSeq, baselinePlan.ReassignedNodes)

        let shiftedCandidate = SelectiveRebuildFixture.graph 1000
        let rebuilt, unchangedSchedule, _ =
            Rebuild.rebuildSelective baseline shiftedCandidate
            |> SelectiveRebuildFixture.admitted
        let unchangedPlan = rebuilt.Codata.Value.SSAAssignment |> Option.defaultWith (fun () -> failwith "Missing selective rebuild SSAAssignment plan.")
        Assert.Empty unchangedSchedule.Receipt.Cone.AffectedCone
        Assert.Equal<Set<NodeId>>(baseline.Nodes |> Map.keys |> Set.ofSeq, rebuilt.Nodes |> Map.keys |> Set.ofSeq)
        Assert.Equal<Map<NodeId, SSAId list>>(baselinePlan.Assignments, unchangedPlan.Assignments)
        Assert.Equal(baselinePlan.NodeHighWater, unchangedPlan.NodeHighWater)
        Assert.Equal<Set<NodeId>>(baselinePlan.Assignments |> Map.keys |> Set.ofSeq, unchangedPlan.RetainedNodes)
        Assert.Empty unchangedPlan.ReassignedNodes

    [<Fact>]
    member _.``SSAAssignment reassigns only affected cone identifiers advancing monotonically without reuse on an edit``() =
        let rawBaseline = SelectiveRebuildFixture.graph 0
        let rawCodata = rawBaseline.Codata.Value
        let sampleMeet : Meet = { Consumer = NodeId 8; Operand = NodeId 10; From = 32; To = 64; Adapt = MeetKind.ExtendSigned }
        let sampleDepAccount : CallableAggregateDependencyAccount =
            { Occurrence = NodeId 8
              Slots = []
              Values = []
              Carriers = []
              Contracts = []
              Flows = []
              Joins = []
              Participants = [ { Node = NodeId 9; Role = ParticipantRole.Callee; Ordinal = 0; Group = NodeId 8 } ]
              Sources = []
              Claims = []
              Symbols = []
              Inactivity = []
              MemoryPolicy = None }
        let baselineWithCodata =
            { rawBaseline with
                Codata = lazy {
                    rawCodata with
                        Meets = Map.ofList [ NodeId 8, [ sampleMeet ] ]
                        CallableAggregateDependencies = Map.ofList [ NodeId 8, sampleDepAccount ]
                        DeclarationRootLambdas = Map.ofList [ NodeId 6, DeclRoot.EntryPoint ] } }
        let baseline = Clef.Compiler.Nanopass.SSAAssignment.normalize baselineWithCodata
        let baselinePlan = baseline.Codata.Value.SSAAssignment.Value
        let bodyChanged = SelectiveRebuildFixture.change 21 42 baseline
        let candidate =
            let providerBinding = bodyChanged.Nodes[NodeId 2]
            { bodyChanged with Nodes = bodyChanged.Nodes.Add(NodeId 2, { providerBinding with LayoutHint = Some TypeLayout.PlatformWord }) }
        let rebuilt, _, _ =
            Rebuild.rebuildSelective baseline candidate
            |> SelectiveRebuildFixture.admitted
        let editedPlan = rebuilt.Codata.Value.SSAAssignment |> Option.defaultWith (fun () -> failwith "Missing selective rebuild SSAAssignment plan.")
        // Sibling, shared, factory, and capturedCode regions are outside the affected cone:
        // their NodeIds and witnessed SSAId(node, ordinal) lists must remain identical to baseline.
        for retainedNode in [NodeId 11; NodeId 12; NodeId 13; NodeId 14; NodeId 15; NodeId 16; NodeId 17; NodeId 18; NodeId 19; NodeId 26; NodeId 27; NodeId 28; NodeId 29; NodeId 30; NodeId 31] do
            Assert.True(rebuilt.Nodes.ContainsKey retainedNode)
            Assert.Contains(retainedNode, editedPlan.RetainedNodes)
            Assert.DoesNotContain(retainedNode, editedPlan.ReassignedNodes)
            Assert.Equal<SSAId list>(
                baselinePlan.Assignments[retainedNode],
                editedPlan.Assignments[retainedNode])
        // Provider and caller regions (candidate nodes 2, 3, 21, 6, 7, 8, 9, 10) are in the affected/re-elaborated cone:
        // their NodeIds and SSAId(node, ordinal) families in rebuilt must advance monotonically above
        // baselinePlan.NodeHighWater without reusing old NodeIds or SSAIds.
        for candId in [NodeId 2; NodeId 3; NodeId 21; NodeId 6; NodeId 7; NodeId 8; NodeId 9; NodeId 10] do
            let remappedId = editedPlan.NodeRemap[candId]
            Assert.True(NodeId.value remappedId > baselinePlan.NodeHighWater)
            Assert.False(baseline.Nodes.ContainsKey remappedId)
            Assert.False(rebuilt.Nodes.ContainsKey candId)
            Assert.True(rebuilt.Nodes.ContainsKey remappedId)
            Assert.Contains(remappedId, editedPlan.ReassignedNodes)
            Assert.DoesNotContain(remappedId, editedPlan.RetainedNodes)
            Assert.True(
                editedPlan.Assignments[remappedId]
                |> List.forall (fun ssa -> Clef.Compiler.Nanopass.SSAAssignment.nodeOf ssa = NodeId.value remappedId))
        let reassignedNodeIds =
            editedPlan.ReassignedNodes
            |> Set.toList
            |> List.map NodeId.value
        Assert.NotEmpty reassignedNodeIds
        Assert.True(reassignedNodeIds |> List.forall (fun id -> id > baselinePlan.NodeHighWater))
        Assert.Equal(reassignedNodeIds.Length, reassignedNodeIds |> List.distinct |> List.length)
        Assert.Equal<int list>(reassignedNodeIds |> List.sort, reassignedNodeIds)
        Assert.Equal<int list>([baselinePlan.NodeHighWater + 1 .. editedPlan.NodeHighWater], reassignedNodeIds)
        Assert.True(editedPlan.NodeHighWater > baselinePlan.NodeHighWater)
        // Node-keyed Codata fields (Meets, CallableAggregateDependencies, DeclarationRootLambdas) are remapped in step.
        let remapped8 = editedPlan.NodeRemap[NodeId 8]
        let remapped9 = editedPlan.NodeRemap[NodeId 9]
        let remapped6 = editedPlan.NodeRemap[NodeId 6]
        Assert.False(rebuilt.Codata.Value.Meets.ContainsKey(NodeId 8))
        Assert.Equal<Meet list>(
            [ { Consumer = remapped8; Operand = NodeId 14; From = 32; To = 64; Adapt = MeetKind.ExtendSigned } |> fun m -> { m with Operand = editedPlan.NodeRemap[NodeId 10] } ],
            rebuilt.Codata.Value.Meets[remapped8])
        Assert.False(rebuilt.Codata.Value.CallableAggregateDependencies.ContainsKey(NodeId 8))
        Assert.Equal(remapped8, rebuilt.Codata.Value.CallableAggregateDependencies[remapped8].Occurrence)
        Assert.Equal(remapped9, rebuilt.Codata.Value.CallableAggregateDependencies[remapped8].Participants.Head.Node)
        Assert.False(rebuilt.Codata.Value.DeclarationRootLambdas.ContainsKey(NodeId 6))
        Assert.Equal(DeclRoot.EntryPoint, rebuilt.Codata.Value.DeclarationRootLambdas[remapped6])
        // Reconciled graph remains structurally valid for subsequent segmentation and selective rebuilds.
        Assert.True(Segments.segment rebuilt |> Result.isOk)
        // A second consecutive edit advances monotonically above editedPlan.NodeHighWater without reusing
        // either baseline or first-edit identifiers, while keeping unchanged regions pinned to baseline.
        let candidate2Body = SelectiveRebuildFixture.change 42 77 rebuilt
        let candidate2 =
            let remappedProvider = editedPlan.NodeRemap[NodeId 2]
            let providerBinding = candidate2Body.Nodes[remappedProvider]
            { candidate2Body with Nodes = candidate2Body.Nodes.Add(remappedProvider, { providerBinding with LayoutHint = Some TypeLayout.Opaque }) }
        let rebuilt2, _, _ =
            Rebuild.rebuildSelective rebuilt candidate2
            |> SelectiveRebuildFixture.admitted
        let editedPlan2 = rebuilt2.Codata.Value.SSAAssignment |> Option.defaultWith (fun () -> failwith "Missing second selective rebuild SSAAssignment plan.")
        for retainedNode in [NodeId 11; NodeId 12; NodeId 13; NodeId 14; NodeId 15; NodeId 16; NodeId 17; NodeId 18; NodeId 19; NodeId 26; NodeId 27; NodeId 28; NodeId 29; NodeId 30; NodeId 31] do
            Assert.True(rebuilt2.Nodes.ContainsKey retainedNode)
            Assert.Contains(retainedNode, editedPlan2.RetainedNodes)
            Assert.DoesNotContain(retainedNode, editedPlan2.ReassignedNodes)
            Assert.Equal<SSAId list>(
                baselinePlan.Assignments[retainedNode],
                editedPlan2.Assignments[retainedNode])
        let reassignedNodeIds2 =
            editedPlan2.ReassignedNodes
            |> Set.toList
            |> List.map NodeId.value
        Assert.NotEmpty reassignedNodeIds2
        Assert.True(reassignedNodeIds2 |> List.forall (fun id -> id > editedPlan.NodeHighWater))
        Assert.Equal<int list>([editedPlan.NodeHighWater + 1 .. editedPlan2.NodeHighWater], reassignedNodeIds2)
        Assert.True(editedPlan2.NodeHighWater > editedPlan.NodeHighWater)
        let baselineAllNodeIds = baseline.Nodes.Keys |> Set.ofSeq
        let rebuiltAllNodeIds = rebuilt.Nodes.Keys |> Set.ofSeq
        Assert.Empty(Set.intersect baselineAllNodeIds editedPlan2.ReassignedNodes)
        Assert.Empty(Set.intersect rebuiltAllNodeIds editedPlan2.ReassignedNodes)
        let priorAllSsaIds =
            Seq.append baselinePlan.Assignments.Values editedPlan.Assignments.Values
            |> Seq.concat
            |> Set.ofSeq
        let reassigned2SsaIds =
            editedPlan2.ReassignedNodes
            |> Seq.collect (fun id -> editedPlan2.Assignments[id])
            |> Set.ofSeq
        Assert.Empty(Set.intersect priorAllSsaIds reassigned2SsaIds)
        // A full release rebuild through both normalize and the production NativeService entry point
        // cold-starts from 0 instead of advancing from editedPlan2.NodeHighWater.
        let releaseGraph = Clef.Compiler.Nanopass.SSAAssignment.normalize candidate
        let releasePlan = releaseGraph.Codata.Value.SSAAssignment.Value
        Assert.Equal(baselinePlan.NodeHighWater, releasePlan.NodeHighWater)
        Assert.Empty releasePlan.RetainedNodes
        let releaseCompiled = (DimensionalCases.check "let identity (value: int) = value\n[<EntryPoint>]\nlet main _ = identity 0\n").Graph
        let releaseCompiledPlan = releaseCompiled.Codata.Value.SSAAssignment.Value
        Assert.True(releaseCompiled.Nodes.ContainsKey(NodeId 0))
        Assert.True(releaseCompiledPlan.NodeHighWater < editedPlan2.NodeHighWater)
        Assert.Empty releaseCompiledPlan.RetainedNodes

    [<Fact>]
    member _.``BoundarySettlement normalize retains boundary-owned node identities across unchanged graph structure``() =
        let body = """
module BoundaryRetain
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
[<FidelityExtern("c", "toggle")>]
let toggle (value: bool) : bool = NativeDefault.zeroed ()
let toggleDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "toggle"; Parameters = [| { Name = "value"; Type = Bool; PassBy = Value } |]
    ReturnType = Bool; CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
[<EntryPoint>]
let main _ = if toggle true then 0 else 1
"""
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "Parse failed: %A" errors
        let authority = SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
        let result =
            Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                [parse authority "write-authority.clef"; parse body "boundary-retain.clef"]
                (Some { SourcePlatformFixture.platform with RuntimeModel = Some RuntimeModel.Libc })
        DimensionalCases.noErrors result
        let boundaryGraph = result.Graph
        let anchorFirst = Clef.Compiler.Baker.Ingredients.Boundaries.RetainedBoundaryNodes.capture boundaryGraph
        Assert.True anchorFirst.DomainAnchor.IsSome
        Assert.NotEmpty anchorFirst.Obligations
        let second = Clef.Compiler.Nanopass.BoundarySettlement.normalize boundaryGraph |> Clef.Compiler.Nanopass.SSAAssignment.normalize
        let anchorSecond = Clef.Compiler.Baker.Ingredients.Boundaries.RetainedBoundaryNodes.capture second
        Assert.True anchorSecond.DomainAnchor.IsSome
        Assert.Equal(anchorFirst.DomainAnchor.Value.Id, anchorSecond.DomainAnchor.Value.Id)
        Assert.Equal<Map<string, NodeId>>(anchorFirst.Obligations, anchorSecond.Obligations)
        Assert.Equal<Set<NodeId>>(boundaryGraph.Nodes |> Map.keys |> Set.ofSeq, second.Nodes |> Map.keys |> Set.ofSeq)
        let firstPlan = boundaryGraph.Codata.Value.SSAAssignment.Value
        let secondPlan = second.Codata.Value.SSAAssignment.Value
        Assert.Equal<Map<NodeId, SSAId list>>(firstPlan.Assignments, secondPlan.Assignments)

    [<Fact>]
    member _.``HostTools emits cvc5 spawn and cache telemetry only when CLEF_PHASE_TIMING=1``() =
        let previousTiming = Environment.GetEnvironmentVariable "CLEF_PHASE_TIMING"
        let previousErr = Console.Error
        let uniqueSolveQuery =
            sprintf "; hosttools-telemetry-solve-%s\n(set-logic QF_LIA)\n(assert (= 1 1))\n(check-sat)\n(reset)" (Guid.NewGuid().ToString("N"))
        let uniqueQuietQuery =
            sprintf "; hosttools-telemetry-quiet-%s\n(set-logic QF_LIA)\n(assert (= 2 2))\n(check-sat)\n(reset)" (Guid.NewGuid().ToString("N"))
        try
            // Positive control 1: CLEF_PHASE_TIMING=1 emits kind=solve on first execution.
            Environment.SetEnvironmentVariable("CLEF_PHASE_TIMING", "1")
            use solveWriter = new System.IO.StringWriter()
            Console.SetError(System.IO.TextWriter.Synchronized solveWriter)
            Assert.Equal(Ok [ "sat" ], BatchHost.runSolver uniqueSolveQuery)
            let solveErr = solveWriter.ToString()
            Assert.Contains("[HostTools.cvc5] kind=solve binary=", solveErr)
            Assert.Contains(" scopes=1 cache_entries=", solveErr)

            // Positive control 2: repeat of same query under CLEF_PHASE_TIMING=1 emits kind=cache_hit.
            use hitWriter = new System.IO.StringWriter()
            Console.SetError(System.IO.TextWriter.Synchronized hitWriter)
            Assert.Equal(Ok [ "sat" ], BatchHost.runSolver uniqueSolveQuery)
            let hitErr = hitWriter.ToString()
            Assert.Contains("[HostTools.cvc5] kind=cache_hit binary=", hitErr)
            Assert.Contains(" cache_entries=", hitErr)
            Assert.DoesNotContain("[HostTools.cvc5] kind=solve ", hitErr)

            // Negative control: with CLEF_PHASE_TIMING unset, neither solve nor cache hit writes to stderr.
            Environment.SetEnvironmentVariable("CLEF_PHASE_TIMING", null)
            use quietWriter = new System.IO.StringWriter()
            Console.SetError(System.IO.TextWriter.Synchronized quietWriter)
            Assert.Equal(Ok [ "sat" ], BatchHost.runSolver uniqueQuietQuery)
            Assert.Equal(Ok [ "sat" ], BatchHost.runSolver uniqueQuietQuery)
            Assert.Equal("", quietWriter.ToString())
        finally
            Environment.SetEnvironmentVariable("CLEF_PHASE_TIMING", previousTiming)
            Console.SetError previousErr

    [<Fact>]
    member _.``clef #197: typed NodeIdRemap eliminates SSAAssignment reflection, enforces generator drift check, invalidates stale witness caches, and refuses pre-faulted numeric facts``() =
        // 1. Source hygiene & allowance-elimination controls (zero reflection/box/:? in SSAAssignment.fs / NodeIdRemap.fs).
        let repoRoot = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../.."))
        let ssaPath = System.IO.Path.Combine(repoRoot, "src/Compiler/Nanopass/SSAAssignment.fs")
        let remapPath = System.IO.Path.Combine(repoRoot, "src/Compiler/Nanopass/NodeIdRemap.fs")
        let ssaSource = System.IO.File.ReadAllText ssaPath
        let remapSource = System.IO.File.ReadAllText remapPath
        let allowances = System.IO.File.ReadAllText(System.IO.Path.Combine(repoRoot, "build/ClefCore.allowances.tsv"))
        for forbidden in [ "System.Reflection"; "Microsoft.FSharp.Reflection"; "FSharpValue"; "FSharpType"; "ConditionalWeakTable"; ":?" ] do
            Assert.DoesNotContain(forbidden, ssaSource, StringComparison.Ordinal)
            Assert.DoesNotContain(forbidden, remapSource, StringComparison.Ordinal)
        Assert.False(System.Text.RegularExpressions.Regex.IsMatch(ssaSource, @"\b(box|unbox)\b"), "SSAAssignment.fs must not contain box/unbox.")
        Assert.False(System.Text.RegularExpressions.Regex.IsMatch(remapSource, @"\b(box|unbox)\b"), "NodeIdRemap.fs must not contain box/unbox.")
        Assert.Contains("Clef.Compiler.Nanopass.FoldIn.remapKind", remapSource, StringComparison.Ordinal)
        Assert.DoesNotContain("SSAAssignment.fs", allowances, StringComparison.Ordinal)
        Assert.DoesNotContain("NodeIdRemap.fs", allowances, StringComparison.Ordinal)

        // 2. Enforce GenerateNodeIdRemapper.fsx --check drift gate against the live compiled Clef.Compiler.Service.dll.
        let generatorScript = System.IO.Path.Combine(repoRoot, "tools/PSGContract/GenerateNodeIdRemapper.fsx")
        let ccsDll = typeof<Clef.Compiler.PSGSaturation.SemanticGraph.Types.SemanticGraph>.Assembly.Location
        Assert.True(System.IO.File.Exists generatorScript, sprintf "Missing generator script at %s" generatorScript)
        Assert.True(System.IO.File.Exists ccsDll, sprintf "Missing Clef.Compiler.Service.dll at %s" ccsDll)
        let psi = System.Diagnostics.ProcessStartInfo("dotnet", sprintf "fsi \"%s\" --check \"%s\" \"%s\"" generatorScript ccsDll remapPath)
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.UseShellExecute <- false
        use proc =
            match System.Diagnostics.Process.Start psi with
            | null -> failwith "Failed to start dotnet fsi for GenerateNodeIdRemapper.fsx --check."
            | started -> started
        let checkStdout = proc.StandardOutput.ReadToEnd()
        let checkStderr = proc.StandardError.ReadToEnd()
        proc.WaitForExit()
        Assert.True(proc.ExitCode = 0, sprintf "GenerateNodeIdRemapper.fsx --check failed (exit %d):\nstdout: %s\nstderr: %s" proc.ExitCode checkStdout checkStderr)
        Assert.Contains("matches exact closed SemanticGraph NodeId closure", checkStdout, StringComparison.Ordinal)
        Assert.Contains("FoldIn.remapKind leaf cases", checkStdout, StringComparison.Ordinal)

        // 3. Full typed SSA remap clears stale witness caches (refused by WitnessEmission.tryRead) and republishes cleanly.
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "Parse failed: %A" errors
        let authority = SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
        let compiled =
            let r =
                Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                    [ parse authority "write-authority.clef"
                      parse "module Clef197TypedRemap\nlet ignoreArg (_unused: int) = 7\nlet identity (value: int) = value\n[<EntryPoint>]\nlet main _ = identity (ignoreArg 1 - 7)\n" "clef197-remap.clef" ]
                    (Some { SourcePlatformFixture.platform with RuntimeModel = Some RuntimeModel.Libc })
            DimensionalCases.noErrors r
            r.Graph
        let preparedBaseline =
            Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare compiled
            |> Result.defaultWith (fun f -> failwithf "Baseline prepare failed: %A" f)
        Assert.True preparedBaseline.WitnessProvenance.IsSome
        Assert.True preparedBaseline.Codata.Value.WitnessEmission.IsSome
        Assert.True preparedBaseline.Codata.Value.WitnessPublishedRows.IsSome
        let sampleIds = preparedBaseline.Nodes.Keys |> Seq.sort |> Seq.take 3 |> Seq.toList

        let cleanReconciled, cleanPlan =
            match DimensionalCases.reconcileCheckedPhysical preparedBaseline Map.empty Set.empty preparedBaseline with
            | Result.Ok pair -> pair
            | Result.Error failure -> failwithf "Clean full typed SSA remap refused: %A" failure
        Assert.True cleanReconciled.WitnessProvenance.IsNone
        Assert.True cleanReconciled.Codata.Value.WitnessEmission.IsNone
        Assert.True cleanReconciled.Codata.Value.WitnessPublishedRows.IsNone
        Assert.NotEqual(sampleIds[0], cleanPlan.NodeRemap[sampleIds[0]])
        // Exact-reason negative control: cleared stale witness cache is refused by WitnessEmission.tryRead.
        match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.tryRead cleanReconciled with
        | Result.Ok _ -> failwith "Cleared witness cache was admitted by WitnessEmission.tryRead."
        | Result.Error reason ->
            Assert.Equal("The current graph has no complete source witness projection.", reason)
        let freshPrepared =
            Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare cleanReconciled
            |> Result.defaultWith (fun f -> failwithf "Post-remap prepare refused: %A" f)
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish freshPrepared
            |> Result.defaultWith (fun f -> failwithf "Post-remap publish refused: %A" f)
        let defects = Fidelity.PSG.Integrity.check revision
        Assert.True(defects.IsEmpty, Fidelity.PSG.Integrity.describe defects)

        // 4. MetadataValue.NodeId and NodeIdList are remapped accurately.
        let targetId, refA, refB = sampleIds[0], sampleIds[1], sampleIds[2]
        let annotated =
            let node = preparedBaseline.Nodes[targetId]
            let meta =
                node.Metadata
                    .Add("Test.NodeIdRef", MetadataValue.NodeId refA)
                    .Add("Test.NodeIdListRef", MetadataValue.NodeIdList [ refA; refB ])
            let edgesWithoutRangeReceipt =
                preparedBaseline.Edges |> List.map (fun e ->
                    match e.Role with
                    | EdgeRole.NumericDomain d -> { e with Role = EdgeRole.NumericDomain { d with RangeContextFacts = None } }
                    | _ -> e)
            { preparedBaseline with
                Nodes = preparedBaseline.Nodes.Add(targetId, { node with Metadata = meta })
                RangeContextFacts = None
                Edges = edgesWithoutRangeReceipt }
        let reconciled, plan =
            match DimensionalCases.reconcileCheckedPhysical preparedBaseline Map.empty Set.empty annotated with
            | Result.Ok pair -> pair
            | Result.Error failure -> failwithf "Annotated typed SSA remap refused: %A" failure
        let newTarget = plan.NodeRemap[targetId]
        let newRefA = plan.NodeRemap[refA]
        let newRefB = plan.NodeRemap[refB]
        Assert.NotEqual(targetId, newTarget)
        Assert.NotEqual(refA, newRefA)
        Assert.NotEqual(refB, newRefB)
        let remappedNode = reconciled.Nodes[newTarget]
        Assert.Equal(Some (MetadataValue.NodeId newRefA), remappedNode.Metadata.TryFind "Test.NodeIdRef")
        Assert.Equal(Some (MetadataValue.NodeIdList [ newRefA; newRefB ]), remappedNode.Metadata.TryFind "Test.NodeIdListRef")

        // 5. Pre-faulted RangeContextFacts.SourceRelations under both identity AND non-monotone remap
        //    must be refused directly by SSAAssignment before remapping (so non-monotone renumbering
        //    cannot hide a pre-remap ordering fault).
        let mutable reversedTailMin: NodeId option = None
        let corruptTail (rows: SourceRangeRelation list) =
            let mutable mutated = false
            let updated =
                rows |> List.map (fun row ->
                    if not mutated && row.Kind = SourceRangeRelationKind.Named "OrdinaryUnusedActual" && row.Sources.Length >= 6 then
                        let prefix, tail = List.splitAt 4 row.Sources
                        let reversed = List.rev tail
                        if reversed <> tail then
                            mutated <- true
                            reversedTailMin <- Some (List.min tail)
                            { row with Sources = prefix @ reversed }
                        else row
                    else row)
            Assert.True(mutated, "Expected an OrdinaryUnusedActual SourceRangeRelation row with >= 2 distinct tail nodes.")
            updated
        let corruptFacts (facts: RangeContextFacts) =
            match facts.SourceRelations with
            | Result.Ok rows -> { facts with SourceRelations = Result.Ok (corruptTail rows) }
            | Result.Error err -> failwithf "Expected Ok SourceRelations, got %s" err
        let preFaulted =
            { preparedBaseline with
                RangeContextFacts = preparedBaseline.RangeContextFacts |> Option.map corruptFacts
                Edges =
                    preparedBaseline.Edges |> List.map (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericDomain ({ RangeContextFacts = Some facts } as d) ->
                            { edge with Role = EdgeRole.NumericDomain { d with RangeContextFacts = Some (corruptFacts facts) } }
                        | _ -> edge) }
        let allIds = preFaulted.Nodes.Keys |> Set.ofSeq
        let idAlign = allIds |> Seq.map (fun id -> id, id) |> Map.ofSeq
        let tailMinId = reversedTailMin |> Option.defaultWith (fun () -> failwith "Missing reversed tail min node.")
        // Non-monotone remap reassigns the smaller tail node above high-water while retaining its peer:
        // without pre-remap validation, the reversed tail would look canonically ascending after renumbering.
        match DimensionalCases.reconcileCheckedPhysical preparedBaseline idAlign (Set.remove tailMinId allIds) preFaulted with
        | Result.Error (DimensionalCases.CheckedPhysicalReconciliationFailure.Reconciliation (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities [ _, reason ])) ->
            Assert.Equal("SSAAssignment: Invocation-context range premises are not current before SSA remapping.", reason)
        | other -> failwithf "Expected direct SSA refusal on non-monotone pre-faulted RangeContextFacts, got %A" other
        match DimensionalCases.reconcileCheckedPhysical preparedBaseline idAlign allIds preFaulted with
        | Result.Error (DimensionalCases.CheckedPhysicalReconciliationFailure.Reconciliation (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities [ _, reason ])) ->
            Assert.Equal("SSAAssignment: Invocation-context range premises are not current before SSA remapping.", reason)
        | other -> failwithf "Expected direct SSA refusal on identity pre-faulted RangeContextFacts, got %A" other

        // 6. Pre-faulted FiniteCellRelations positive and direct SSA refusal controls.
        let finiteCompiled =
            let r =
                Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                    [ parse authority "write-authority.clef"
                      parse "module Clef197FiniteCell\n[<EntryPoint>]\nlet main _ =\n    let mutable state = 0\n    let record (n: int) = state <- n\n    record 1\n    record 2\n    state\n" "clef197-fc.clef" ]
                    (Some { SourcePlatformFixture.platform with RuntimeModel = Some RuntimeModel.Libc })
            DimensionalCases.noErrors r
            r.Graph
        let fcDomain =
            finiteCompiled.Edges |> List.pick (fun e -> match e.Role with EdgeRole.NumericDomain d -> Some d | _ -> None)
        let fcRows =
            fcDomain.FiniteCellRelations
            |> Option.defaultWith (fun () -> failwith "Expected FiniteCellRelations = Some _ on mutable-cell fixture.")
        Assert.NotEmpty fcRows
        let fcAllIds = finiteCompiled.Nodes.Keys |> Set.ofSeq
        let fcAlign = fcAllIds |> Seq.map (fun id -> id, id) |> Map.ofSeq
        let fcMinId = fcAllIds |> Set.minElement
        let fcClean, _ =
            match DimensionalCases.reconcileCheckedPhysical finiteCompiled fcAlign (Set.remove fcMinId fcAllIds) finiteCompiled with
            | Result.Ok pair -> pair
            | Result.Error failure -> failwithf "Clean finite-cell non-monotone SSA remap refused: %A" failure
        let fcPrepared =
            Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare fcClean
            |> Result.defaultWith (fun f -> failwithf "Post-remap finite-cell prepare refused: %A" f)
        let fcRev =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish fcPrepared
            |> Result.defaultWith (fun f -> failwithf "Post-remap finite-cell publish refused: %A" f)
        Assert.Empty(Fidelity.PSG.Integrity.check fcRev)
        let corruptedFcRows =
            match fcRows |> List.tryFindIndex (fun row -> row.Sources.Length >= 2 && row.Sources <> List.rev row.Sources) with
            | Some idx -> fcRows |> List.mapi (fun i row -> if i = idx then { row with Sources = List.rev row.Sources } else row)
            | None -> List.rev fcRows
        Assert.NotEqual<FiniteCellSourceRelation list>(fcRows, corruptedFcRows)
        let preFaultedFinite =
            { finiteCompiled with
                Edges =
                    finiteCompiled.Edges |> List.map (fun e ->
                        match e.Role with
                        | EdgeRole.NumericDomain d -> { e with Role = EdgeRole.NumericDomain { d with FiniteCellRelations = Some corruptedFcRows } }
                        | _ -> e) }
        match DimensionalCases.reconcileCheckedPhysical finiteCompiled fcAlign (Set.remove fcMinId fcAllIds) preFaultedFinite with
        | Result.Error (DimensionalCases.CheckedPhysicalReconciliationFailure.Reconciliation (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities [ _, reason ])) ->
            Assert.Equal("SSAAssignment: Finite-cell relation premises are not current before SSA remapping.", reason)
        | other -> failwithf "Expected direct SSA refusal on pre-faulted FiniteCellRelations, got %A" other

        // 7. Pre-faulted StringOriginRelations positive and direct SSA refusal controls.
        let originCompiled =
            let r =
                Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                    [ parse authority "write-authority.clef"
                      parse "module Clef197StringOrigin\n[<EntryPoint>]\nlet main _ =\n    let delayed = lazy \"\"\n    if Lazy.force delayed = \"\" then 0 else 1\n" "clef197-so.clef" ]
                    (Some { SourcePlatformFixture.platform with RuntimeModel = Some RuntimeModel.Libc })
            DimensionalCases.noErrors r
            r.Graph
        let soDomain =
            originCompiled.Edges |> List.pick (fun e -> match e.Role with EdgeRole.BoundaryDomain d -> Some d | _ -> None)
        let soRows =
            soDomain.StringOriginRelations
            |> Option.defaultWith (fun () -> failwith "Expected StringOriginRelations = Some _ on lazy-string fixture.")
        Assert.NotEmpty soRows
        let soAllIds = originCompiled.Nodes.Keys |> Set.ofSeq
        let soAlign = soAllIds |> Seq.map (fun id -> id, id) |> Map.ofSeq
        let soMinId = soAllIds |> Set.minElement
        let soClean, _ =
            match DimensionalCases.reconcileCheckedPhysical originCompiled soAlign (Set.remove soMinId soAllIds) originCompiled with
            | Result.Ok pair -> pair
            | Result.Error failure -> failwithf "Clean string-origin non-monotone SSA remap refused: %A" failure
        let soPrepared =
            Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare soClean
            |> Result.defaultWith (fun f -> failwithf "Post-remap string-origin prepare refused: %A" f)
        let soRev =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish soPrepared
            |> Result.defaultWith (fun f -> failwithf "Post-remap string-origin publish refused: %A" f)
        Assert.Empty(Fidelity.PSG.Integrity.check soRev)
        let corruptedSoRows =
            match soRows |> List.tryFindIndex (fun row -> row.Sources.Length >= 2 && row.Sources <> List.rev row.Sources) with
            | Some idx -> soRows |> List.mapi (fun i row -> if i = idx then { row with Sources = List.rev row.Sources } else row)
            | None -> List.rev soRows
        Assert.NotEqual<StringOriginRelation list>(soRows, corruptedSoRows)
        let preFaultedOrigin =
            { originCompiled with
                Edges =
                    originCompiled.Edges |> List.map (fun e ->
                        match e.Role with
                        | EdgeRole.BoundaryDomain d -> { e with Role = EdgeRole.BoundaryDomain { d with StringOriginRelations = Some corruptedSoRows } }
                        | _ -> e) }
        match DimensionalCases.reconcileCheckedPhysical originCompiled soAlign (Set.remove soMinId soAllIds) preFaultedOrigin with
        | Result.Error (DimensionalCases.CheckedPhysicalReconciliationFailure.Reconciliation (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities [ _, reason ])) ->
            Assert.Equal("SSAAssignment: String-origin relation premises are not current before SSA remapping.", reason)
        | other -> failwithf "Expected direct SSA refusal on pre-faulted StringOriginRelations, got %A" other

        // 8. Ambiguous companion hyperedge correspondence controls (identical duplicate accepted,
        //    conflicting non-monotone companion correspondence refused with exact reason, monotone control accepted).
        let carrierEdge =
            preparedBaseline.Edges |> List.find (fun e -> match e.Role with EdgeRole.NumericCarrier _ -> true | _ -> false)
        let dupIdenticalGraph = { preparedBaseline with Edges = carrierEdge :: preparedBaseline.Edges }
        match Clef.Compiler.Nanopass.SSAAssignment.remapGraph id dupIdenticalGraph with
        | Result.Ok _ -> ()
        | Result.Error err -> failwithf "Identical duplicate companion row should be accepted, got %A" err
        let numDomainEdge, numDomainPayload =
            preparedBaseline.Edges |> List.pick (fun e -> match e.Role with EdgeRole.NumericDomain d -> Some (e, d) | _ -> None)
        let premiseKeys = numDomainPayload.Premises |> Map.keys |> Seq.toList
        Assert.True(premiseKeys.Length >= 2, "Expected >= 2 NumericDomain premises for ambiguity control.")
        let minPremise = List.min premiseKeys
        let syntheticForeignUse : ForeignResultUse =
            { Application =
                { Declaration = numDomainEdge.Target
                  Call = numDomainEdge.Target
                  Context = []
                  Hypothesis = None
                  Arguments = [] }
              Participants =
                ParticipantEvidence.Established
                    (premiseKeys |> List.mapi (fun i n -> { Node = n; Role = ParticipantRole.Source; Ordinal = i; Group = numDomainEdge.Target }))
              Claims = [ ForeignResultProofRole.LogicalCoverage, numDomainEdge.Target ] }
        let ambiguousGraph =
            { preparedBaseline with
                Edges =
                    preparedBaseline.Edges |> List.map (fun e ->
                        match e.Role with
                        | EdgeRole.NumericDomain _ when e.Target = numDomainEdge.Target ->
                            { e with Role = EdgeRole.NumericDomain { numDomainPayload with ForeignResultUses = syntheticForeignUse :: numDomainPayload.ForeignResultUses } }
                        | _ -> e) }
        // Fault-injection monotone control: under identity remap, both producers emit identical source order so no ambiguity occurs.
        match Clef.Compiler.Nanopass.SSAAssignment.remapGraph id ambiguousGraph with
        | Result.Ok _ -> ()
        | Result.Error err -> failwithf "Monotone identical companion order should not trigger ambiguity, got %A" err
        // Exact-reason negative control: non-monotone remap causes sorted domainRewrite and positional foreignProofRows to conflict.
        match DimensionalCases.reconcileCheckedPhysical preparedBaseline idAlign (Set.remove minPremise allIds) ambiguousGraph with
        | Result.Error (DimensionalCases.CheckedPhysicalReconciliationFailure.Reconciliation (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities [ _, reason ])) ->
            Assert.Equal("SSAAssignment: Ambiguous companion hyperedge correspondence during SSA remapping.", reason)
        | other -> failwithf "Expected exact ambiguous companion correspondence refusal, got %A" other

        // 9. Node-ID collision refusal controls (injective remap accepted, colliding remap refused with exact reason).
        let collideA, collideB = sampleIds[0], sampleIds[1]
        let freshNodeId = NodeId (preparedBaseline.Codata.Value.SSAAssignment.Value.NodeHighWater + 1)
        match Clef.Compiler.Nanopass.SSAAssignment.remapGraph (fun id -> if id = collideB then freshNodeId else id) preparedBaseline with
        | Result.Ok g -> Assert.Equal(preparedBaseline.Nodes.Count, g.Nodes.Count)
        | Result.Error err -> failwithf "Injective remap should be accepted, got %A" err
        match Clef.Compiler.Nanopass.SSAAssignment.remapGraph (fun id -> if id = collideB then collideA else id) preparedBaseline with
        | Result.Error (site, reason) ->
            Assert.Equal(collideA, site)
            Assert.Equal("SSAAssignment: NodeId remapping collided distinct graph nodes.", reason)
        | Result.Ok _ -> failwith "Colliding NodeId remap was admitted."

    [<Fact>]
    member _.``clef #175: selective SSA requires Segmentation checked pairs and enforces correspondence and cutoff controls``() =
        // 1. Live assembly + source ownership guard:
        //    - No public reconcile* entry point exists on SSAAssignment.
        //    - ScopedRebuildPair and CheckedPhysicalPair expose no public constructors.
        //    - Both internal SSA reconciliation entry points accept ONLY a single checked pair
        //      (no raw retainedCandidateNodes or alignment parameter).
        //    - Rebuild.fs is the sole src/ caller of reconcileAndAssignWithCallableRelations;
        //      zero src/ callers invoke reconcileAndAssign or reconcileCheckedPhysical.
        //    - Segmentation.fs is the sole src/ author of CCS8407.
        let ssaModule =
            match typeof<Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure>.DeclaringType with
            | null -> failwith "Expected SSAAssignment module declaring type."
            | t -> t
        let publicReconcileMethods =
            ssaModule.GetMethods(System.Reflection.BindingFlags.Public ||| System.Reflection.BindingFlags.Static)
            |> Array.filter (fun m -> m.Name.StartsWith("reconcile", StringComparison.Ordinal))
        Assert.Empty publicReconcileMethods
        let internalStatic = System.Reflection.BindingFlags.NonPublic ||| System.Reflection.BindingFlags.Static
        let callableMethod =
            match ssaModule.GetMethod("reconcileAndAssignWithCallableRelations", internalStatic) with
            | null -> failwith "Expected internal reconcileAndAssignWithCallableRelations method."
            | m -> m
        let callableParams = callableMethod.GetParameters()
        Assert.Equal(1, callableParams.Length)
        Assert.Equal(typeof<Segments.ScopedRebuildPair>, callableParams[0].ParameterType)
        let physicalMethod =
            match ssaModule.GetMethod("reconcileCheckedPhysical", internalStatic) with
            | null -> failwith "Expected internal reconcileCheckedPhysical method."
            | m -> m
        let physicalParams = physicalMethod.GetParameters()
        Assert.Equal(1, physicalParams.Length)
        Assert.Equal(typeof<Segments.CheckedPhysicalPair>, physicalParams[0].ParameterType)
        Assert.Empty(typeof<Segments.ScopedRebuildPair>.GetConstructors(System.Reflection.BindingFlags.Public ||| System.Reflection.BindingFlags.Instance))
        Assert.Empty(typeof<Segments.CheckedPhysicalPair>.GetConstructors(System.Reflection.BindingFlags.Public ||| System.Reflection.BindingFlags.Instance))
        let repoRoot = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../.."))
        let srcFiles = System.IO.Directory.GetFiles(System.IO.Path.Combine(repoRoot, "src/Compiler"), "*.fs", System.IO.SearchOption.AllDirectories)
        let relPath (p: string) = System.IO.Path.GetRelativePath(repoRoot, p).Replace('\\', '/')
        let callableCallers =
            srcFiles
            |> Array.filter (fun p ->
                let rel = relPath p
                rel <> "src/Compiler/Nanopass/SSAAssignment.fs"
                && (System.IO.File.ReadAllText p).Contains("reconcileAndAssignWithCallableRelations", StringComparison.Ordinal))
            |> Array.map relPath
        Assert.Equal<string array>([| "src/Compiler/PSGSaturation/SemanticGraph/Rebuild.fs" |], callableCallers)
        let rawOrPhysicalCallers =
            srcFiles
            |> Array.filter (fun p ->
                let rel = relPath p
                let text = System.IO.File.ReadAllText p
                rel <> "src/Compiler/Nanopass/SSAAssignment.fs"
                && (text.Contains("reconcileAndAssign ", StringComparison.Ordinal)
                    || text.Contains("reconcileCheckedPhysical", StringComparison.Ordinal)))
            |> Array.map relPath
        Assert.Empty rawOrPhysicalCallers
        let ccs8407Authors =
            srcFiles
            |> Array.filter (fun p -> (System.IO.File.ReadAllText p).Contains("\"CCS8407\"", StringComparison.Ordinal))
            |> Array.map relPath
        Assert.Equal<string array>([| "src/Compiler/PSGSaturation/SemanticGraph/Segmentation.fs" |], ccs8407Authors)

        // 2. Checked-pair positive control: Segmentation.checkPhysicalCorrespondence admits exact physical alignment.
        let baseline = SelectiveRebuildFixture.graph 0 |> Clef.Compiler.Nanopass.SSAAssignment.normalize
        let candidate = SelectiveRebuildFixture.graph 1000
        let retainedBase = NodeId 21
        let retainedCand = NodeId 1021
        let validAlign = Map.ofList [ retainedBase, retainedCand ]
        let scope = Set.singleton retainedCand
        let checkedPair =
            match Segments.checkPhysicalCorrespondence baseline validAlign scope candidate with
            | Result.Ok pair -> pair
            | Result.Error failure -> failwithf "Valid checked physical correspondence was refused: %A" failure
        let _, plan =
            Clef.Compiler.Nanopass.SSAAssignment.reconcileCheckedPhysical checkedPair
            |> SelectiveRebuildFixture.admitted
        Assert.Equal(retainedBase, plan.NodeRemap[retainedCand])

        // 3. Exact-reason negative controls at the single Segmentation correspondence boundary:
        //    (a) MissingRetainedCorrespondence
        match Segments.checkPhysicalCorrespondence baseline Map.empty scope candidate with
        | Result.Error (Segments.PhysicalCorrespondenceFailure.MissingRetainedCorrespondence id) ->
            Assert.Equal(retainedCand, id)
        | other -> failwithf "Expected MissingRetainedCorrespondence, got %A" other
        //    (b) CCS8407 AmbiguousRetainedCorrespondence
        let ambiguousAlign = validAlign.Add(NodeId 13, retainedCand)
        match Segments.checkPhysicalCorrespondence baseline ambiguousAlign scope candidate with
        | Result.Error (Segments.PhysicalCorrespondenceFailure.AmbiguousRetainedCorrespondence diagnostic) ->
            Assert.Equal("CCS8407", diagnostic.Code)
            Assert.Equal("The retained occurrence has more than one admissible baseline identity.", diagnostic.Message)
            Assert.Equal<NodeId list>([ retainedCand ], diagnostic.RelatedNodes)
        | other -> failwithf "Expected CCS8407 AmbiguousRetainedCorrespondence, got %A" other
        //    (c) InvalidBaseline & InvalidCandidate on malformed graphs (including empty retained set!)
        let brokenBaseline =
            let n = baseline.Nodes[retainedBase]
            { baseline with Nodes = baseline.Nodes.Add(retainedBase, { n with Children = NodeId -99 :: n.Children }) }
        let expectedMissingTarget =
            Segments.SegmentationFailure.InvalidGraph(Some retainedBase, "A structural or reference target is absent from the graph.")
        match Segments.checkPhysicalCorrespondence brokenBaseline validAlign scope candidate with
        | Result.Error (Segments.PhysicalCorrespondenceFailure.InvalidBaseline failures) ->
            Assert.Contains(expectedMissingTarget, failures)
        | other -> failwithf "Expected InvalidBaseline on broken baseline, got %A" other
        match Segments.checkPhysicalCorrespondence brokenBaseline Map.empty Set.empty candidate with
        | Result.Error (Segments.PhysicalCorrespondenceFailure.InvalidBaseline failures) ->
            Assert.Contains(expectedMissingTarget, failures)
        | other -> failwithf "Expected InvalidBaseline even when retained set is empty, got %A" other
        let brokenCandidate =
            let n = candidate.Nodes[retainedCand]
            { candidate with Nodes = candidate.Nodes.Add(retainedCand, { n with Children = NodeId -99 :: n.Children }) }
        let expectedCandMissingTarget =
            Segments.SegmentationFailure.InvalidGraph(Some retainedCand, "A structural or reference target is absent from the graph.")
        match Segments.checkPhysicalCorrespondence baseline validAlign scope brokenCandidate with
        | Result.Error (Segments.PhysicalCorrespondenceFailure.InvalidCandidate failures) ->
            Assert.Contains(expectedCandMissingTarget, failures)
        | other -> failwithf "Expected InvalidCandidate on broken candidate, got %A" other
        //    (d) Exact-reason negative: wrong predecessor from another source occurrence refused before SSA runs.
        let wrongPredecessor = Map.ofList [ NodeId 13, retainedCand ]
        match Segments.checkPhysicalCorrespondence baseline wrongPredecessor scope candidate with
        | Result.Error (Segments.PhysicalCorrespondenceFailure.MissingRetainedCorrespondence id) ->
            Assert.Equal(retainedCand, id)
        | other -> failwithf "Expected wrong predecessor alignment to refuse at checked-pair boundary, got %A" other

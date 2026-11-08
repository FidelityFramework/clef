namespace Clef.Compiler.Service.Tests

open System
open Xunit
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Receipts = Clef.Compiler.Nanopass.ObligationDischarge

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
        let snapshot = checkedSnapshot @ [ tautological; ignoring; proved; refuted; pending ]

        let receipts = Receipts.designTimeReceiptsWithProjectionOverride DesignTimeReceiptFixture.budget overrideProjection snapshot
        Assert.Equal<string list>(snapshot |> List.map _.Id, receipts |> List.map _.ObligationId)
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
    member _.``The solver resolves from PATH first and then from the pinned parity toolchains``() =
        let separator = string IO.Path.PathSeparator
        let onPath = String.Join(separator, [ "/opt/none"; "/usr/local/solver/bin" ])
        let exists (found: string list) (path: string) = List.contains path found
        Assert.Equal("cvc5", Receipts.resolveSolver onPath (exists [ IO.Path.Combine("/usr/local/solver/bin", "cvc5"); "/mnt/apps/gpu-two/toolchains/cvc5-1.3.0/bin/cvc5" ]))
        Assert.Equal("/mnt/apps/gpu-two/toolchains/cvc5-1.3.0/bin/cvc5", Receipts.resolveSolver onPath (exists [ "/mnt/apps/gpu-two/toolchains/cvc5-1.3.0/bin/cvc5"; "/tmp/cvc5-toolchain/bin/cvc5" ]))
        Assert.Equal("/home/hhh/.local/toolchains/cvc5-1.3.0/bin/cvc5", Receipts.resolveSolver "" (exists Receipts.solverToolchainPaths))
        Assert.Equal("/tmp/cvc5-toolchain/bin/cvc5", Receipts.resolveSolver null (exists [ "/tmp/cvc5-toolchain/bin/cvc5" ]))
        Assert.Equal("cvc5", Receipts.resolveSolver onPath (exists []))

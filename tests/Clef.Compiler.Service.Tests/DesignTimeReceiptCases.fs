namespace Clef.Compiler.Service.Tests

open System
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
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
    member _.``Calls and local storage invalidate their owning callable and dependent caller while retaining siblings``() =
        let baseline = SelectiveRebuildFixture.graph 0
        let plan = Segments.segment baseline |> SelectiveRebuildFixture.admitted
        Assert.Contains(plan.Dependencies, fun edge ->
            edge.Consumer = "module:Selective/binding:caller" && edge.Provider = "module:Selective/binding:provider" && edge.Kind = Segments.DependencyKind.Call)
        let candidate = SelectiveRebuildFixture.change 21 42 baseline
        let schedule = Rebuild.scheduleRebuild baseline candidate |> SelectiveRebuildFixture.admitted
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "provider" schedule)
        Assert.Equal(Rebuild.RegionDisposition.Reelaborate, SelectiveRebuildFixture.disposition "caller" schedule)
        for name in ["sibling"; "shared"; "factory"; "capturedCode"] do
            Assert.Equal(Rebuild.RegionDisposition.Retained, SelectiveRebuildFixture.disposition name schedule)
        Assert.Contains(NodeId 21, schedule.Receipt.Cone.AffectedCone)
        Assert.DoesNotContain(NodeId 13, schedule.Scopes)

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
        let baseline = SelectiveRebuildFixture.graph 0
        NodeId.reset()
        let candidate = SelectiveRebuildFixture.graph 1000
        let _, schedule, recipes = Rebuild.rebuildSelective baseline candidate |> SelectiveRebuildFixture.admitted
        for KeyValue(identity, region) in schedule.Baseline.Regions do
            Assert.Equal(region.Fingerprint, schedule.Candidate.Regions[identity].Fingerprint)
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
        let candidate = SelectiveRebuildFixture.change 21 42 baseline
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
        let candidate2 = SelectiveRebuildFixture.change 42 77 rebuilt
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

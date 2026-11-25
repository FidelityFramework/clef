// SPDX-License-Identifier: MIT
/// Cross-revision Baker scheduling. Invalid baselines are refusals, never a full rebuild request.
module Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

[<RequireQualifiedAccess>]
type RegionDisposition = Retained | Reelaborate | Retired | Dormant
[<RequireQualifiedAccess>]
type RebuildFailure =
    | InvalidBaseline of SegmentationFailure list
    | InvalidCandidate of SegmentationFailure list
    | MissingBaseline
    | RecipeRefused of NodeId * string
    | SSAAssignmentRefused of Diagnostic
    /// Failure identities belong to the reconciled graph.
    | InvalidReturnedGraph of SegmentationFailure list

/// Reachability uses a common declaration address space, then the receipt is
/// transported back into the two source graphs. Extinguished identities belong
/// to the baseline; live identities belong to the candidate.
type ShadowConeReceipt =
    { Alignment: Map<NodeId, NodeId>
      Cone: Reachability.ReachableDeltaCone
      InvalidatedRegions: Set<string>
      RetiredRegions: Set<string> }

type RebuildSchedule =
    { Baseline: SegmentationPlan
      Candidate: SegmentationPlan
      Receipt: ShadowConeReceipt
      Regions: Map<string, RegionDisposition>
      Scopes: Set<NodeId>
      RelationAlignment: Map<NodeId, NodeId> }

/// A comparison-only view for Reachability. It is never elaborated or published.
/// Node payloads are exact stable source fingerprints; source incidence remains
/// directed, ModuleDef remains a lexical container rather than a sibling hub,
/// and immutable callable declaration roots expose their executable signature
/// across VarRef call edges so internal body edits cut off when the interface holds.
let private shadowView (graph: SemanticGraph) (plan: SegmentationPlan) (canonical: Map<string, NodeId>) =
    let translate id = canonical[plan.NodeIdentities[id]]
    let encode = WitnessSegmentation.encoder plan.NodeIdentities
    let callableBoundaries =
        graph.Nodes.Keys
        |> Seq.filter (isCallableBoundary graph)
        |> Set.ofSeq
    let detachedCallableLambdas =
        callableBoundaries
        |> Seq.choose (fun bid -> graph.Nodes[bid].Children |> List.tryHead)
        |> Set.ofSeq
    let nodes =
        graph.Nodes |> Map.toSeq |> Seq.map (fun (id, node) ->
            let kind, children, parent =
                match node.Kind with
                | SemanticKind.ModuleDef(name, members) ->
                    SemanticKind.ModuleDef(name, members |> List.map translate),
                    node.Children |> List.map translate,
                    node.Parent |> Option.map translate
                | _ when callableBoundaries.Contains id ->
                    let lambdaNode = graph.Nodes[node.Children.Head]
                    let signature =
                        match lambdaNode.Kind with
                        | SemanticKind.Lambda(parameters, _, captures, _, context) ->
                            let parameters = parameters |> List.map (fun (name, ty, pid) ->
                                let parameter = graph.Nodes[pid]
                                name, ty, parameter.ArenaAffinity, parameter.LayoutHint)
                            box (parameters, captures, context)
                        | _ -> box lambdaNode.Kind
                    let payload =
                        encode (box (plan.NodeFingerprints[id], lambdaNode.Type, lambdaNode.SRTPResolution,
                                     lambdaNode.ArenaAffinity, lambdaNode.LayoutHint, lambdaNode.EmissionStrategy,
                                     WitnessSegmentation.normalizeMetadata lambdaNode.Metadata, signature))
                    SemanticKind.Literal(NativeLiteral.String payload),
                    [],
                    node.Parent |> Option.map translate
                | _ when detachedCallableLambdas.Contains id ->
                    SemanticKind.Literal(NativeLiteral.String plan.NodeFingerprints[id]),
                    node.Children |> List.map translate,
                    None
                | _ ->
                    SemanticKind.Literal(NativeLiteral.String plan.NodeFingerprints[id]),
                    node.Children |> List.map translate,
                    node.Parent |> Option.map translate
            translate id,
                { node with Id = translate id; Kind = kind
                            Children = children
                            Parent = parent
                            // Range movement and fresh checker cells do not change source meaning.
                            Range = dummyRange
                            Type = Types.unitType
                            SRTPResolution = None; LayoutHint = None; Metadata = Map.empty })
        |> Map.ofSeq
    let edges =
        [ for node in graph.Nodes.Values do
            for edge in kindEdges node.Id node.Kind do
                if Hyperedge.isReference edge && edge.Role <> EdgeRole.Member then
                    yield { edge with Target = translate edge.Target; Sources = edge.Sources |> List.map translate }
          for edge in graph.Edges do
            // Cross-region proof/domain causality is compared via SupportEdges and
            // CanonicalProofSupportDigest so Cone.AffectedCone stays strictly executable.
            let involvedOwners =
                edge.Target :: edge.Sources
                |> List.choose plan.NodeOwners.TryFind
                |> List.distinct
            if involvedOwners.Length <= 1 then
                yield { edge with Role = EdgeRole.Definition; Target = translate edge.Target
                                  Sources = edge.Sources |> List.map translate } ]
    { graph with Nodes = nodes; Edges = edges
                 DeclarationRoots = graph.DeclarationRoots |> List.map (fun (id, flavor) -> translate id, flavor) }

let private scheduleCheckedRebuild (baseline: SemanticGraph) (candidate: SemanticGraph) =
    if baseline.Nodes.IsEmpty then Result.Error RebuildFailure.MissingBaseline else
    match checkRebuildPair baseline candidate with
    | Result.Error (RebuildPairFailure.Baseline failures) -> Result.Error(RebuildFailure.InvalidBaseline failures)
    | Result.Error (RebuildPairFailure.Candidate failures) -> Result.Error(RebuildFailure.InvalidCandidate failures)
    | Result.Ok pair ->
        let oldPlan, newPlan, alignment, relations = rebuildPairPlans pair
        let addresses =
            Seq.append oldPlan.NodeIdentities.Values newPlan.NodeIdentities.Values |> Set.ofSeq
        let canonical = addresses |> Seq.mapi (fun index identity -> identity, NodeId(index + 1)) |> Map.ofSeq
        let oldView = shadowView baseline oldPlan canonical
        let newView = shadowView candidate newPlan canonical
        let cone = Reachability.computeShadowCone oldView newView
        let touched = Set.unionMany [cone.AffectedCone; cone.NewlyLitNodes; cone.ExtinguishedNodes]
        let overlaps (plan: SegmentationPlan) (region: Region) =
            region.Members |> Seq.exists (fun id -> touched.Contains canonical[plan.NodeIdentities[id]])
        let supports (plan: SegmentationPlan) identity =
            supportEdges identity plan |> List.map (fun edge -> edge.Domain, edge.Identity, edge.Fingerprint) |> List.sort
        let changed =
            newPlan.Regions |> Map.toSeq |> Seq.choose (fun (identity, region) ->
                match oldPlan.Regions.TryFind identity with
                | Some old when old.CallableInterfaceDigest = region.CallableInterfaceDigest &&
                                old.SemanticRealizationDigest = region.SemanticRealizationDigest &&
                                old.CanonicalProofSupportDigest = region.CanonicalProofSupportDigest &&
                                not (overlaps newPlan region) &&
                                not (overlaps oldPlan old) &&
                                supports oldPlan identity = supports newPlan identity -> None
                | _ -> Some identity) |> Set.ofSeq
        let removed = oldPlan.Regions.Keys |> Set.ofSeq |> fun old -> Set.difference old (newPlan.Regions.Keys |> Set.ofSeq)
        let allDependencies = oldPlan.Dependencies @ newPlan.Dependencies
        let callableInterfaceChanged providerIdentity =
            match oldPlan.Regions.TryFind providerIdentity, newPlan.Regions.TryFind providerIdentity with
            | Some oldProvider, Some newProvider ->
                oldProvider.CallableInterfaceDigest <> newProvider.CallableInterfaceDigest
            | _ -> true
        let shouldPropagate (invalid: Set<string>) (edge: RegionDependency) =
            if not (Set.contains edge.Provider invalid) then false
            else
                match edge.Kind with
                | DependencyKind.Call -> callableInterfaceChanged edge.Provider
                | DependencyKind.Storage
                | DependencyKind.CapturedEnvironment
                | DependencyKind.ProofSupport -> true
        let rec close invalid =
            let next =
                allDependencies |> List.fold (fun state edge ->
                    if shouldPropagate state edge then Set.add edge.Consumer state else state) invalid
            if next = invalid then invalid else close next
        let invalid = close (Set.union changed removed)
        let isRegionReachable (graph: SemanticGraph) (region: Region) =
            region.Members |> Set.exists (fun id -> graph.Nodes.TryFind id |> Option.exists _.IsReachable)
        // Regions unreachable in the candidate contribute no executable Baker scopes;
        // off-spine metadata support changes already propagated via `close` above.
        // Regions reachable in the baseline that are absent or unreachable in the
        // candidate are Retired; changed or newly introduced unreachable regions
        // are Dormant and excluded from retainedRegions, while unchanged off-spine
        // declaration regions remain Retained.
        let retiredRegions =
            oldPlan.Regions
            |> Map.toSeq
            |> Seq.choose (fun (identity, oldRegion) ->
                if isRegionReachable baseline oldRegion then
                    match newPlan.Regions.TryFind identity with
                    | Some newRegion when isRegionReachable candidate newRegion -> None
                    | _ -> Some identity
                else None)
            |> Set.ofSeq
        let executableInvalid =
            invalid
            |> Set.filter (fun identity ->
                match newPlan.Regions.TryFind identity with
                | Some region -> isRegionReachable candidate region
                | None -> false)
        let dispositions = newPlan.Regions |> Map.map (fun identity region ->
            if executableInvalid.Contains identity then RegionDisposition.Reelaborate
            elif retiredRegions.Contains identity then RegionDisposition.Retired
            elif invalid.Contains identity && not (isRegionReachable candidate region) then RegionDisposition.Dormant
            else RegionDisposition.Retained)
        let scopes =
            newPlan.Regions.Values
            |> Seq.filter (fun region -> executableInvalid.Contains region.Identity)
            |> Seq.collect (fun region ->
                region.Members |> Seq.filter (fun id -> candidate.Nodes.TryFind id |> Option.exists _.IsReachable))
            |> Set.ofSeq
        let transport (plan: SegmentationPlan) ids =
            plan.NodeIdentities |> Map.toSeq |> Seq.choose (fun (id, address) ->
                if Set.contains canonical[address] ids then Some id else None) |> Set.ofSeq
        let receipt =
            { cone with SeedRoots = transport newPlan cone.SeedRoots
                        AffectedCone = transport newPlan cone.AffectedCone
                        NewlyLitNodes = transport newPlan cone.NewlyLitNodes
                        ExtinguishedNodes = transport oldPlan cone.ExtinguishedNodes
                        RetainedReachable = transport newPlan cone.RetainedReachable }
        let schedule =
            { Baseline = oldPlan; Candidate = newPlan; Regions = dispositions; Scopes = scopes
              RelationAlignment = relations
              Receipt = { Alignment = alignment; Cone = receipt; InvalidatedRegions = executableInvalid; RetiredRegions = retiredRegions } }
        Result.Ok(schedule, pair)

let scheduleRebuild baseline candidate =
    scheduleCheckedRebuild baseline candidate |> Result.map fst

/// Program Hypergraph §5.1 defines scoped evaluation and witness authorization.
/// https://clef-lang.com/spec/draft/program-hypergraph/#51-scoped-re-evaluation-and-witness-authorization
/// The shadow pass selects the reachable causal cone before Baker runs pure
/// nanopasses. The existing fan-out and fold-in compose their authored results.
/// Only admitted scopes enter Baker fan-out. Retained nodes stay in the full
/// graph for recipe lookups and fold-in; there is no reduced-graph fallback.
/// Unchanged structure outside the delta cone retains its baseline NodeIds and
/// SSA assignments; re-elaborated or newly introduced nodes advance monotonically.
let rebuildSelective baseline candidate =
    scheduleCheckedRebuild baseline candidate
    |> Result.bind (fun (schedule, pair) ->
        let retainedRegions =
            schedule.Regions
            |> Map.fold (fun acc identity disposition ->
                if disposition = RegionDisposition.Retained then Set.add identity acc else acc) Set.empty
        Core.SemanticGraph.withSettledEnrichment baseline (fun () ->
            Core.SemanticGraph.withSettledEnrichment candidate (fun () ->
                match settleRebuildScopes pair schedule.Scopes schedule.Receipt.Cone.AffectedCone retainedRegions with
                | Result.Error (ScopedSettlementFailure.RecipeRefused(id, reason)) ->
                    Result.Error(RebuildFailure.RecipeRefused(id, reason))
                | Result.Error ScopedSettlementFailure.MissingCallableSettlement ->
                    let reason = "Scoped Baker folding requires callable settlement before returning a graph."
                    Result.Error(RebuildFailure.InvalidReturnedGraph [SegmentationFailure.InvalidGraph(None, reason)])
                | Result.Error (ScopedSettlementFailure.SentinelSettlementRefused(site, reason)) ->
                    Result.Error(RebuildFailure.InvalidReturnedGraph [SegmentationFailure.InvalidGraph(site, reason)])
                | Result.Error (ScopedSettlementFailure.CorrespondenceRefused (PhysicalCorrespondenceFailure.InvalidBaseline failures)) ->
                    Result.Error(RebuildFailure.InvalidBaseline failures)
                | Result.Error (ScopedSettlementFailure.CorrespondenceRefused (PhysicalCorrespondenceFailure.InvalidCandidate failures)) ->
                    Result.Error(RebuildFailure.InvalidCandidate failures)
                | Result.Error (ScopedSettlementFailure.CorrespondenceRefused (PhysicalCorrespondenceFailure.MissingRetainedCorrespondence id)) ->
                    let reason = "The retained occurrence has no admissible identity correspondence."
                    Result.Error(RebuildFailure.InvalidCandidate [SegmentationFailure.InvalidGraph(Some id, reason)])
                | Result.Error (ScopedSettlementFailure.CorrespondenceRefused (PhysicalCorrespondenceFailure.AmbiguousRetainedCorrespondence diagnostic)) ->
                    Result.Error(RebuildFailure.SSAAssignmentRefused diagnostic)
                | Result.Ok (scoped, recipes) ->
                    let _, _, _, relations = scopedRebuildInputs scoped
                    match Clef.Compiler.Nanopass.SSAAssignment.reconcileAndAssignWithCallableRelations scoped with
                    | Result.Error Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.MissingBaselinePlan ->
                        let reason = "The accepted baseline graph has no SSA assignment plan."
                        Result.Error(RebuildFailure.InvalidBaseline [SegmentationFailure.InvalidGraph(None, reason)])
                    | Result.Error (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.MissingRetainedAssignment id) ->
                        let reason = "The accepted baseline lacks the exact SSA assignment for a retained occurrence."
                        Result.Error(RebuildFailure.InvalidBaseline [SegmentationFailure.InvalidGraph(Some id, reason)])
                    | Result.Error (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities failures) ->
                        let invalid =
                            failures
                            |> List.map (fun (id, reason) -> SegmentationFailure.InvalidGraph(Some id, reason))
                        Result.Error(RebuildFailure.InvalidReturnedGraph invalid)
                    | Result.Ok (reconciled, _) ->
                        match Clef.Compiler.Nanopass.PremiseEstablishment.settleRebuildSentinels (scopedRebuildRefolded scoped) reconciled with
                        | Result.Ok settled ->
                            Result.Ok(settled, { schedule with RelationAlignment = relations }, recipes)
                        | Result.Error (site, reason) ->
                            Result.Error(RebuildFailure.InvalidReturnedGraph [SegmentationFailure.InvalidGraph(site, reason)]))))

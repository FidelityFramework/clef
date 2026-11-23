// SPDX-License-Identifier: MIT
/// Cross-revision Baker scheduling. Invalid baselines are refusals, never a full rebuild request.
module Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

[<RequireQualifiedAccess>]
type RegionDisposition = Retained | Reelaborate
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
      InvalidatedRegions: Set<string> }

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

let private alignRelations (baseline: SemanticGraph) (candidate: SemanticGraph)
                           (oldPlan: SegmentationPlan) (newPlan: SegmentationPlan) (physical: Map<NodeId, NodeId>) =
    let prior = baseline.Codata.Value
    let current = candidate.Codata.Value
    let unique pairs =
        pairs |> Seq.groupBy fst |> Seq.choose (fun (_, values) ->
            match Seq.toList values with [pair] -> Some pair | _ -> None) |> Map.ofSeq
    let slots =
        current.CallableAggregateSlots |> Map.toSeq |> Seq.choose (fun (id, slot) ->
            let previous = Clef.Compiler.Baker.Recipes.CallableAggregateRecipes.tryPreviousSlotIdentity
                                slot.AggregateType slot.Path prior.CallableAggregateSlots
            previous |> Option.bind (fun old ->
                if oldPlan.CallableRelationIdentities.ContainsKey old && newPlan.CallableRelationIdentities.ContainsKey id
                then Some(old, id) else None))
        |> unique
    let contracts =
        current.CallableCarriers.Values
        |> Seq.choose (fun carrier -> carrier.Contract |> Result.toOption |> Option.map (fun id -> id, carrier))
        |> Seq.groupBy fst
        |> Seq.choose (fun (id, occurrences) ->
            let previous = occurrences |> Seq.map (fun (_, carrier) ->
                Clef.Compiler.Baker.Ingredients.CallableContracts.tryIdentityAcross physical.TryFind slots.TryFind candidate
                    current.EnvironmentLayouts prior.CallableContracts carrier) |> Seq.distinct |> Seq.toList
            match previous, newPlan.CallableRelationIdentities.TryFind id with
            | [Some old], Some address when oldPlan.CallableRelationIdentities.TryFind old = Some address -> Some(old, id)
            | _ -> None)
    Seq.append contracts (Map.toSeq slots) |> unique

let scheduleRebuild (baseline: SemanticGraph) (candidate: SemanticGraph) : Result<RebuildSchedule, RebuildFailure> =
    if baseline.Nodes.IsEmpty then Result.Error RebuildFailure.MissingBaseline else
    match segment baseline, segment candidate with
    | Result.Error failures, _ -> Result.Error(RebuildFailure.InvalidBaseline failures)
    | _, Result.Error failures -> Result.Error(RebuildFailure.InvalidCandidate failures)
    | Result.Ok oldPlan, Result.Ok newPlan ->
        let addresses =
            Seq.append oldPlan.NodeIdentities.Values newPlan.NodeIdentities.Values |> Set.ofSeq
        let canonical = addresses |> Seq.mapi (fun index identity -> identity, NodeId(index + 1)) |> Map.ofSeq
        let oldView = shadowView baseline oldPlan canonical
        let newView = shadowView candidate newPlan canonical
        let cone = Reachability.computeShadowCone oldView newView
        let newByAddress = newPlan.NodeIdentities |> Map.toSeq |> Seq.map (fun (id, address) -> address, id) |> Map.ofSeq
        let alignment =
            oldPlan.NodeIdentities |> Map.toSeq |> Seq.choose (fun (id, address) ->
                newByAddress.TryFind address |> Option.map (fun target -> id, target)) |> Map.ofSeq
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
        let dispositions = newPlan.Regions |> Map.map (fun identity _ ->
            if invalid.Contains identity then RegionDisposition.Reelaborate else RegionDisposition.Retained)
        let scopes =
            newPlan.Regions.Values |> Seq.filter (fun region -> invalid.Contains region.Identity)
            |> Seq.map _.Members |> Set.unionMany
        let transport (plan: SegmentationPlan) ids =
            plan.NodeIdentities |> Map.toSeq |> Seq.choose (fun (id, address) ->
                if Set.contains canonical[address] ids then Some id else None) |> Set.ofSeq
        let receipt =
            { cone with SeedRoots = transport newPlan cone.SeedRoots
                        AffectedCone = transport newPlan cone.AffectedCone
                        NewlyLitNodes = transport newPlan cone.NewlyLitNodes
                        ExtinguishedNodes = transport oldPlan cone.ExtinguishedNodes
                        RetainedReachable = transport newPlan cone.RetainedReachable }
        Result.Ok { Baseline = oldPlan; Candidate = newPlan; Regions = dispositions; Scopes = scopes
                    RelationAlignment = alignRelations baseline candidate oldPlan newPlan alignment
                    Receipt = { Alignment = alignment; Cone = receipt; InvalidatedRegions = invalid } }

let private retainedCandidateNodes (alignment: Map<NodeId, NodeId>) (schedule: RebuildSchedule) (graph: SemanticGraph) : Set<NodeId> =
    let affected = schedule.Receipt.Cone.AffectedCone
    let codata = graph.Codata.Value
    let obligationIncidentOwners =
        graph.Edges
        |> List.groupBy _.Target
        |> List.map (fun (target, edges) ->
            let owners =
                edges
                |> List.collect _.Sources
                |> List.choose schedule.Candidate.NodeOwners.TryFind
                |> Set.ofList
            target, owners)
        |> Map.ofList
    alignment
    |> Map.fold (fun acc _ candId ->
        if Set.contains candId schedule.Scopes || Set.contains candId affected then
            acc
        else
            match schedule.Candidate.NodeOwners.TryFind candId with
            | Some owner when schedule.Regions.TryFind owner = Some RegionDisposition.Retained ->
                Set.add candId acc
            | None ->
                match graph.Nodes.TryFind candId with
                | Some { Kind = SemanticKind.ModuleDef _ } -> Set.add candId acc
                | Some { Kind = SemanticKind.Obligation _ } ->
                    let incident = obligationIncidentOwners |> Map.tryFind candId |> Option.defaultValue Set.empty
                    if incident |> Set.forall (fun owner -> schedule.Regions.TryFind owner = Some RegionDisposition.Retained) then
                        Set.add candId acc
                    else
                        acc
                | _ ->
                    match codata.CallableContracts.TryFind candId with
                    | Some contract ->
                        let retainedContract =
                            contract.Participants
                            |> List.tryFind (fun p -> p.Role = ParticipantRole.CallableImplementation)
                            |> Option.bind (fun p -> schedule.Candidate.NodeOwners.TryFind p.Node)
                            |> Option.exists (fun owner -> schedule.Regions.TryFind owner = Some RegionDisposition.Retained)
                        if retainedContract then Set.add candId acc else acc
                    | None ->
                        if codata.CallableAggregateSlots.ContainsKey candId then
                            Set.add candId acc
                        else
                            acc
            | _ -> acc) Set.empty

/// Program Hypergraph §5.1 defines scoped evaluation and witness authorization.
/// https://clef-lang.com/spec/draft/program-hypergraph/#51-scoped-re-evaluation-and-witness-authorization
/// The shadow pass selects the reachable causal cone before Baker runs pure
/// nanopasses. The existing fan-out and fold-in compose their authored results.
/// Only admitted scopes enter Baker fan-out. Retained nodes stay in the full
/// graph for recipe lookups and fold-in; there is no reduced-graph fallback.
/// Unchanged structure outside the delta cone retains its baseline NodeIds and
/// SSA assignments; re-elaborated or newly introduced nodes advance monotonically.
let rebuildSelective baseline candidate =
    scheduleRebuild baseline candidate
    |> Result.bind (fun schedule ->
        Core.SemanticGraph.withSettledEnrichment baseline (fun () ->
            Core.SemanticGraph.withSettledEnrichment candidate (fun () ->
                let recipes = Clef.Compiler.Nanopass.BakerSaturation.fanOutScopes schedule.Scopes candidate
                let refusal =
                    recipes.Diagnostics |> List.tryPick (fun diagnostic ->
                        match diagnostic.Result with
                        | Clef.Compiler.Nanopass.Recipe.CreationFailed(reason, _) -> Some(RebuildFailure.RecipeRefused(diagnostic.NodeId, reason))
                        | _ -> None)
                match refusal with
                | Some refusal -> Result.Error refusal
                | None ->
                    let saturated =
                        if recipes.Recipes.IsEmpty then candidate
                        else Clef.Compiler.Nanopass.BakerSaturation.foldIn recipes candidate
                    let candidateFacts = candidate.Codata.Value
                    let saturatedFacts = saturated.Codata.Value
                    if (not candidateFacts.CallableContracts.IsEmpty && saturatedFacts.CallableContracts.IsEmpty)
                       || (not candidateFacts.CallableAggregateSlots.IsEmpty && saturatedFacts.CallableAggregateSlots.IsEmpty) then
                        let reason = "Scoped Baker folding requires callable settlement before returning a graph."
                        Result.Error(RebuildFailure.InvalidReturnedGraph [SegmentationFailure.InvalidGraph(None, reason)])
                    else
                    let relations =
                        if recipes.Recipes.IsEmpty then schedule.RelationAlignment
                        else alignRelations baseline saturated schedule.Baseline schedule.Candidate schedule.Receipt.Alignment
                    let alignment = Map.fold (fun acc old current -> Map.add old current acc) schedule.Receipt.Alignment relations
                    let retained = retainedCandidateNodes alignment schedule saturated
                    match Clef.Compiler.Nanopass.SSAAssignment.reconcileAndAssignWithCallableRelations baseline alignment retained saturated with
                    | Result.Error Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.MissingBaselinePlan ->
                        let reason = "The accepted baseline graph has no SSA assignment plan."
                        Result.Error(RebuildFailure.InvalidBaseline [SegmentationFailure.InvalidGraph(None, reason)])
                    | Result.Error (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.MissingRetainedAssignment id) ->
                        let reason = "The accepted baseline lacks the exact SSA assignment for a retained occurrence."
                        Result.Error(RebuildFailure.InvalidBaseline [SegmentationFailure.InvalidGraph(Some id, reason)])
                    | Result.Error (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.MissingRetainedCorrespondence id) ->
                        let reason = "The retained occurrence has no admissible identity correspondence."
                        Result.Error(RebuildFailure.InvalidCandidate [SegmentationFailure.InvalidGraph(Some id, reason)])
                    | Result.Error (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.AmbiguousRetainedCorrespondence diagnostic) ->
                        Result.Error(RebuildFailure.SSAAssignmentRefused diagnostic)
                    | Result.Error (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities failures) ->
                        let invalid =
                            failures
                            |> List.map (fun (id, reason) -> SegmentationFailure.InvalidGraph(Some id, reason))
                        Result.Error(RebuildFailure.InvalidReturnedGraph invalid)
                    | Result.Ok (reconciled, _) ->
                        Result.Ok(reconciled, { schedule with RelationAlignment = relations }, recipes))))

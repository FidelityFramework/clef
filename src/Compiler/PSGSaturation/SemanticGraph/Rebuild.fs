// SPDX-License-Identifier: MIT
/// Cross-revision Baker scheduling. Invalid baselines are refusals, never a full rebuild request.
module Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation

[<RequireQualifiedAccess>]
type RegionDisposition = Retained | Reelaborate
[<RequireQualifiedAccess>]
type RebuildFailure =
    | InvalidBaseline of SegmentationFailure list
    | InvalidCandidate of SegmentationFailure list
    | MissingBaseline
    | RecipeRefused of NodeId * string

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
      Scopes: Set<NodeId> }

/// A comparison-only view for Reachability. It is never elaborated or published.
/// Node payloads are exact stable source fingerprints; source incidence remains
/// directed, and ModuleDef remains a lexical container rather than a sibling hub.
let private shadowView (graph: SemanticGraph) (plan: SegmentationPlan) (canonical: Map<string, NodeId>) =
    let translate id = canonical[plan.NodeIdentities[id]]
    let nodes =
        graph.Nodes |> Map.toSeq |> Seq.map (fun (id, node) ->
            let kind =
                match node.Kind with
                | SemanticKind.ModuleDef(name, members) -> SemanticKind.ModuleDef(name, members |> List.map translate)
                | _ -> SemanticKind.Literal(NativeLiteral.String plan.NodeFingerprints[id])
            translate id,
                { node with Id = translate id; Kind = kind
                            Children = node.Children |> List.map translate
                            Parent = node.Parent |> Option.map translate
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
            // The role payload is compared in support fingerprints. This edge
            // retains its complete source/target causality without stale IDs.
            yield { edge with Role = EdgeRole.Definition; Target = translate edge.Target
                              Sources = edge.Sources |> List.map translate } ]
    { graph with Nodes = nodes; Edges = edges
                 DeclarationRoots = graph.DeclarationRoots |> List.map (fun (id, flavor) -> translate id, flavor) }

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
                | Some old when old.Fingerprint = region.Fingerprint && not (overlaps newPlan region) &&
                                not (overlaps oldPlan old) && supports oldPlan identity = supports newPlan identity -> None
                | _ -> Some identity) |> Set.ofSeq
        let removed = oldPlan.Regions.Keys |> Set.ofSeq |> fun old -> Set.difference old (newPlan.Regions.Keys |> Set.ofSeq)
        let allDependencies = oldPlan.Dependencies @ newPlan.Dependencies
        let rec close invalid =
            let next =
                allDependencies |> List.fold (fun state edge ->
                    if Set.contains edge.Provider state then Set.add edge.Consumer state else state) invalid
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
                    Receipt = { Alignment = alignment; Cone = receipt; InvalidatedRegions = invalid } }

/// Only admitted scopes enter Baker fan-out. Retained nodes stay in the full
/// graph for recipe lookups and fold-in; there is no reduced-graph fallback.
let rebuildSelective baseline candidate =
    scheduleRebuild baseline candidate
    |> Result.bind (fun schedule ->
        let recipes = Clef.Compiler.Nanopass.BakerSaturation.fanOutScopes schedule.Scopes candidate
        let refusal =
            recipes.Diagnostics |> List.tryPick (fun diagnostic ->
                match diagnostic.Result with
                | Clef.Compiler.Nanopass.Recipe.CreationFailed(reason, _) -> Some(RebuildFailure.RecipeRefused(diagnostic.NodeId, reason))
                | _ -> None)
        match refusal with
        | Some refusal -> Result.Error refusal
        | None ->
            let graph =
                if recipes.Recipes.IsEmpty then candidate
                else Clef.Compiler.Nanopass.BakerSaturation.foldIn recipes candidate
            Result.Ok(graph, schedule, recipes))

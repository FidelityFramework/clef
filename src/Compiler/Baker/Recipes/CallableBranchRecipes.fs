// SPDX-License-Identifier: MIT
/// Baker owns final branch observations and their conservative joint authority.
/// This recipe does not authorize selective proof reuse. Every validation reads
/// the whole current origin fixed point, including absence and membership.
module Clef.Compiler.Baker.Recipes.CallableBranchRecipes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins

/// Resolve the final graph, after source rewrites. This is called by the owning
/// settlement and again for validation; witness/publication readers never call it.
let private current (graph: SemanticGraph) : CallableBranchAuthority =
    let resolution = Origins.resolveCallableBranches graph
    if resolution.Branches.IsEmpty then CallableBranchAuthority.empty else
    let codata = graph.Codata.Value
    { Scope = CallableBranchScope.WholeRevision
      Observations = resolution.Branches
      CarrierUses = codata.CallableCarriers |> Map.keys |> Set.ofSeq
      FlowUses = codata.CallableFlows |> Map.keys |> Set.ofSeq
      CallUses = resolution.Calls |> Map.keys |> Set.ofSeq }

let settle graph = current graph

/// Preserve held facts on failure. Reconstructing a missing observation here
/// would turn witness preparation into a semantic author and hide stale facts.
let validate (graph: SemanticGraph) : Result<CallableBranchAuthority, WitnessProjectionFailure list> =
    let held = graph.Codata.Value.CallableBranches
    let expected = current graph
    if held = expected then Result.Ok held else
    let participants (authority: CallableBranchAuthority) =
        authority.Observations.Values
        |> Seq.collect _.Participants
        |> Seq.collect (fun participant -> [participant.Node; participant.Group])
        |> Set.ofSeq
    Result.Error [{
        Kind = WitnessProjectionFailureKind.Settlement; Occurrence = None
        Participants = Set.union (participants held) (participants expected)
        Reason = "Callable branch authority is missing or differs from the current whole-revision origin census; Baker branch settlement is required."
    }]

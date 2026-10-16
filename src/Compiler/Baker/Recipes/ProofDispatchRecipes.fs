// SPDX-License-Identifier: MIT
/// Source-owned inventory and rendering of the complete solver dispatch.
/// Grouping here preserves the existing source inventory; it does not establish
/// complete semantic support or permission to partition or reuse proofs.
module Clef.Compiler.Baker.Recipes.ProofDispatchRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Graph = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph
module Discharge = Clef.Compiler.Nanopass.ObligationDischarge

/// Only this source-owned per-use conversion may retain Pending in a complete
/// published ledger. The current boundary projection supplies its exact anchor.
let private optionalEntryPendingInCalls (graph: SemanticGraph) (calls: BoundaryCall list) (id: NodeId, info: ObligationInfo) =
    Clef.Compiler.Baker.Recipes.BoundaryRecipes.optionalEntryClaimRows graph calls (id, info) |> Result.isOk

let optionalEntryPending graph (boundary: BoundaryEmissionProjection) claim =
    optionalEntryPendingInCalls graph (boundary.Calls.Values |> Seq.toList) claim

/// Already authored boundary rows, available before final Codata installation.
let boundaryCalls (graph: SemanticGraph) =
    graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCall call -> Some call | _ -> None)

let private admittedPending (graph: SemanticGraph) (required: (NodeId * ObligationInfo) list) =
    if required |> List.exists (fun (_, info) -> match info.Body with ObligationBody.Pending _ -> true | _ -> false) then
        required |> List.filter (fun ((_, info) as claim) ->
            match info.Body with
            | ObligationBody.Pending _ -> optionalEntryPendingInCalls graph (boundaryCalls graph) claim
            | _ -> false) |> List.map fst |> Set.ofList
    else Set.empty

let private inventory (graph: SemanticGraph) =
    let required = Graph.obligations graph |> List.map (fun (node, info) -> node.Id, info)
    let constrains = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains)
    let sources =
        constrains |> List.groupBy _.Target
        |> List.map (fun (target, rows) -> target, rows |> List.map _.Sources)
        |> Map.ofList
    required, constrains, sources

let materialize (graph: SemanticGraph) : Result<ProofDispatchPlan, WitnessProjectionFailure list> =
    let required, constrains, sources = inventory graph
    let failure occurrence reason =
        { Kind = WitnessProjectionFailureKind.Settlement; Occurrence = occurrence
          Participants =
            constrains |> List.filter (fun edge -> Some edge.Target = occurrence)
            |> List.collect _.Sources |> Set.ofList
          Reason = "Proof dispatch rendering failed: " + reason }
    try
        let admitted = admittedPending graph required
        let solverRequired = required |> List.filter (fun (id, _) -> not (admitted.Contains id))
        let stalePlans = required |> List.choose (fun ((id, info) as claim) ->
            match info.Body with
            | ObligationBody.OptionalEntryArgumentConversion _ | ObligationBody.OptionalEntryAbsenceArgumentConversion _ ->
                match BoundaryRecipes.optionalEntryClaimRows graph (boundaryCalls graph) claim with
                | Ok _ -> None
                | Error reason -> Some(id, [reason])
            | _ -> None)
        let query =
            match stalePlans, Discharge.trySmtLib (List.map snd solverRequired) with
            | failures, _ when not failures.IsEmpty -> Error failures
            | _, Ok text -> Ok text
            | _, Error _ ->
                // Preserve exact node identities, even if anchor strings repeat.
                Error (solverRequired |> List.choose (fun (id, info) ->
                    match info.Body with
                    | ObligationBody.Pending reasons -> Some (id, reasons)
                    | _ ->
                        match Discharge.trySmtLib [info] with
                        | Ok _ -> None
                        | Error unavailable -> Some(id, unavailable |> List.collect _.MissingPremises)))
        Ok { Required = required; Constrains = constrains; SourceGroups = sources; Query = query }
    with error ->
        // Locate malformed bodies at their source obligation. Pending bodies are
        // unavailable evidence, not a rendering failure or a false predicate.
        let failures = required |> List.choose (fun (id, info) ->
            try Discharge.trySmtLib [info] |> ignore; None
            with error -> Some (failure (Some id) error.Message))
        Error (if List.isEmpty failures then [failure None error.Message] else failures)

/// Hyperedges deliberately have no generic equality. Compare every stored
/// field and its position, including details absent from the rendered query.
let matches (expected: ProofDispatchPlan) (actual: ProofDispatchPlan) =
    let rows (edges: Hyperedge list) = edges |> List.map (fun edge -> edge.Sources, edge.Target, edge.Class, edge.Role, edge.Ordinal)
    expected.Required = actual.Required &&
    rows expected.Constrains = rows actual.Constrains &&
    expected.SourceGroups = actual.SourceGroups && expected.Query = actual.Query

/// Publication checks its supplied complete source inventory without rendering
/// another query or waiting for the future Codata installation.
let matchesInventory graph (dispatch: ProofDispatchPlan) =
    let required, constrains, sources = inventory graph
    matches {dispatch with Required=required; Constrains=constrains; SourceGroups=sources} dispatch

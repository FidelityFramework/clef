// SPDX-License-Identifier: MIT
/// Source-owned inventory and rendering of the complete solver dispatch.
/// Grouping here preserves the existing source inventory; it does not establish
/// complete semantic support or permission to partition or reuse proofs.
module Clef.Compiler.Baker.Recipes.ProofDispatchRecipes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Graph = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph
module Discharge = Clef.Compiler.Nanopass.ObligationDischarge

let materialize (graph: SemanticGraph) : Result<ProofDispatchPlan, WitnessProjectionFailure list> =
    let required = Graph.obligations graph |> List.map (fun (node, info) -> node.Id, info)
    let constrains = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains)
    let sources =
        constrains |> List.groupBy _.Target
        |> List.map (fun (target, rows) -> target, rows |> List.map _.Sources)
        |> Map.ofList
    let failure occurrence reason =
        { Kind = WitnessProjectionFailureKind.Settlement; Occurrence = occurrence
          Participants =
            constrains |> List.filter (fun edge -> Some edge.Target = occurrence)
            |> List.collect _.Sources |> Set.ofList
          Reason = "Proof dispatch rendering failed: " + reason }
    try
        let query =
            match Discharge.trySmtLib (List.map snd required) with
            | Ok text -> Ok text
            | Error _ ->
                // Preserve exact node identities, even if anchor strings repeat.
                Error (required |> List.choose (fun (id, info) ->
                    match info.Body with
                    | ObligationBody.Pending reasons -> Some (id, reasons)
                    | _ -> None))
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

// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Refresh successful-pull and element provenance before range saturation.
/// Recipes supply incidence; the range fixed point owns the resulting bounds.
module Clef.Compiler.Nanopass.SequenceElements

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Recipes = Clef.Compiler.Baker.Recipes.SequenceElementRecipes

let normalize (graph: SemanticGraph) =
    let _, certificates = SequenceCurrentAdmission.certify graph
    let retained = graph.Edges |> List.filter (fun edge ->
        match edge.Class, edge.Role with
        | EdgeClass.Suspension, (EdgeRole.IteratorCurrentAdmitted
                              | EdgeRole.SequenceElementAdmission
                              | EdgeRole.SequenceElementOwner
                              | EdgeRole.SequenceElementPayload
                              | EdgeRole.SequenceElementUnknown) -> false
        | _ -> true)
    let admitted = { graph with Edges = retained @ certificates }
    let elements = Recipes.elaborate admitted
    { admitted with Edges = admitted.Edges @ elements }

// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Refresh iterator effect dependencies before the range/effect fixed points.
module Clef.Compiler.Nanopass.SequenceEffects

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Recipes = Clef.Compiler.Baker.Recipes.SequenceEffectRecipes

let normalize (graph: SemanticGraph) =
    let retained = graph.Edges |> List.filter (fun edge ->
        match edge.Class, edge.Role with
        | EdgeClass.Suspension, (EdgeRole.SequencePullBody | EdgeRole.SequenceInitialize | EdgeRole.SequenceEffectUnknown) -> false
        | _ -> true)
    let source = { graph with Edges = retained }
    { source with Edges = retained @ Recipes.elaborate source }

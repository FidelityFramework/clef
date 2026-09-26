// SPDX-License-Identifier: MIT
/// Fold only this demand owner's projection into the existing source graph.
module Clef.Compiler.Nanopass.OrdinaryDemand

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Recipes = Clef.Compiler.Baker.Recipes.OrdinaryDemandRecipes

let elaborate graph = Recipes.elaborate graph
let foldIn (enrichment: Enrichment) graph =
    let retained = graph.Edges |> List.filter (fun edge ->
        edge.Role <> EdgeRole.OrdinaryUnusedFormal && edge.Role <> EdgeRole.OrdinaryUnusedActual)
    { graph with Edges = retained @ enrichment.NewEdges }
let normalize graph = foldIn (elaborate graph) graph

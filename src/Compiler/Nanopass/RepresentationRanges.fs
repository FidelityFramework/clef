// SPDX-License-Identifier: MIT
/// Maintain finite support at one owning representation rewrite boundary.
/// No prepared state crosses passes, and no missing proof is repaired here.
module Clef.Compiler.Nanopass.RepresentationRanges

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
module Recipes = Clef.Compiler.Baker.Recipes.RepresentationRangeRecipes

let foldIn (replacement: Recipes.Replacement) (graph: SemanticGraph) =
    if replacement.RetiredEdges.IsEmpty then graph
    else
        let graph = ObligationElaboration.retireAnchors replacement.Obligations graph
        let retained = graph.Edges |> List.filter (fun edge -> not (replacement.RetiredEdges.Contains(Recipes.edgeKey edge)))
        { graph with Edges = retained }
        |> ObligationElaboration.foldIn replacement.Enrichment
        |> SemanticGraph.invalidateWitness

let preserve before after = foldIn (Recipes.elaborate before after) after

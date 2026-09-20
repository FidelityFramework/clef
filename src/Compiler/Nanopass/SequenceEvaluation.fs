// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Fan out local evaluation recipes on the final sequence owners. Re-firing
/// replaces this projection alone. This is whole-graph recomputation for now;
/// explicit incidence supports later dependency-directed invalidation.
module Clef.Compiler.Nanopass.SequenceEvaluation

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Recipes = Clef.Compiler.Baker.Recipes.SequenceEvaluationRecipes

let elaborate (graph: SemanticGraph) =
    graph.Nodes.Values
    |> Seq.filter _.IsReachable
    |> Seq.choose (fun node ->
        match node.Kind with
        | SemanticKind.SeqExpr _ -> Some (Recipes.forOwner graph node)
        | _ -> None)
    |> Seq.toList |> Enrichment.concat

let foldIn (enrichment: Enrichment) (graph: SemanticGraph) =
    { graph with
        Edges = (graph.Edges |> List.filter (fun edge -> edge.Class <> EdgeClass.Evaluation)) @ enrichment.NewEdges }

let normalize graph = foldIn (elaborate graph) graph

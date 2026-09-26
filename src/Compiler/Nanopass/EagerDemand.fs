// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Fan out local activation recipes and fold in only their owned projection.
/// Re-firing retracts premises removed by edits or structural elaboration.
module Clef.Compiler.Nanopass.EagerDemand

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Recipes = Clef.Compiler.Baker.Recipes.EagerDemandRecipes

let private owned (edge: Hyperedge) =
    edge.Class = EdgeClass.Demand &&
    match edge.Role with
    | EdgeRole.EagerDemand _ | EdgeRole.EagerDemandPending -> true
    | _ -> false

let elaborate (graph: SemanticGraph) =
    let inputs = Recipes.inputs graph
    graph.Nodes.Values
    |> Seq.filter _.IsReachable
    |> Seq.map (Recipes.forNode graph inputs)
    |> Seq.toList |> Enrichment.concat

let foldIn (enrichment: Enrichment) (graph: SemanticGraph) =
    { graph with Edges = (graph.Edges |> List.filter (owned >> not)) @ enrichment.NewEdges }

let normalize graph = foldIn (elaborate graph) graph

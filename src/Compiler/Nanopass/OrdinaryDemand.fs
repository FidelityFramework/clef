// SPDX-License-Identifier: MIT
/// Fold only this demand owner's projection into the existing source graph.
module Clef.Compiler.Nanopass.OrdinaryDemand

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.Baker.Ingredients.Obligations
module Recipes = Clef.Compiler.Baker.Recipes.OrdinaryDemandRecipes

let elaborate graph = Recipes.elaborate graph
let foldIn (enrichment: Enrichment) graph =
    let owned edge = edge.Role = EdgeRole.OrdinaryUnusedFormal || edge.Role = EdgeRole.OrdinaryUnusedActual
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    if (graph.Edges |> List.filter owned |> List.map key) = (enrichment.NewEdges |> List.map key) then graph
    else
        let retained = graph.Edges |> List.filter (owned >> not)
        { graph with Edges = retained @ enrichment.NewEdges } |> SemanticGraph.invalidateWitness
let normalize graph =
    let graph = BoundaryDeclarations.normalize graph
    foldIn (elaborate graph) graph

// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.BoundaryDeclarations

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
module Recipes = Clef.Compiler.Baker.Recipes.BoundaryDeclarations

let normalize graph =
    let rows = (Recipes.elaborate graph).NewEdges
    let owned edge = match edge.Role with EdgeRole.BoundaryDeclaration _ -> true | _ -> false
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    if (graph.Edges |> List.filter owned |> List.map key) = (rows |> List.map key) then graph
    else
        let retained = graph.Edges |> List.filter (owned >> not)
        { graph with Edges = retained @ rows } |> SemanticGraph.invalidateWitness

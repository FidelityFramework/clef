// SPDX-License-Identifier: MIT
/// Retire this boundary owner's previous firing, then fold its replacement.
module Clef.Compiler.Nanopass.BoundarySettlement

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.Baker.Ingredients.Obligations
module Ingredients = Clef.Compiler.Baker.Ingredients.Boundaries
module Recipes = Clef.Compiler.Baker.Recipes.BoundaryRecipes

let private retract graph =
    let retired = graph.Nodes |> Map.fold (fun ids id node -> if Ingredients.ownedNode node then Set.add id ids else ids) Set.empty
    let nodes = graph.Nodes |> Map.filter (fun id _ -> not (retired.Contains id))
    let edges = graph.Edges |> List.filter (fun edge ->
        let boundary = match edge.Role with EdgeRole.BoundaryDeclaration _ -> false | _ -> edge.Class = EdgeClass.Boundary
        not boundary && not (retired.Contains edge.Target) && not (edge.Sources |> List.exists retired.Contains))
    { graph with Nodes = nodes; Edges = edges } |> SemanticGraph.invalidateWitness

let elaborate = Recipes.elaborate
let foldIn (enrichment: Enrichment) graph =
    graph |> SemanticGraph.addNodes enrichment.Annotated |> SemanticGraph.addNodes enrichment.NewNodes
          |> SemanticGraph.addEdges enrichment.NewEdges

let normalize graph =
    let graph = graph |> retract |> BoundaryDeclarations.normalize
    foldIn (elaborate graph) graph

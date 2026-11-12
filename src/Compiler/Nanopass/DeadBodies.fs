// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.DeadBodies

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe
module Recipes = Clef.Compiler.Baker.Recipes.DeadBodyRecipes

let fanOut graph =
    FanOut.fanOut "Source.dead-body" (fun node -> node.IsReachable && match node.Kind with SemanticKind.IfThenElse _ | SemanticKind.WhileLoop _ -> true | _ -> false) (fun node current ->
        match Recipes.replacement current node with
        | None -> NotApplicable "No current constant exclusion"
        | Some selection ->
            RecipeCreated {OriginalNodeId=node.Id; ReplacementRootId=node.Id
                           NewNodes=Recipes.materialize node selection; NewEdges=[]
                           ElaborationKind="Baker"; ElaborationSource="Source.dead-body"}) graph

let normalizeWith emit graph =
    let recipes = fanOut graph
    emit recipes
    if recipes.Recipes.IsEmpty then graph else
    FoldIn.foldIn recipes graph |> Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable

let normalize graph = normalizeWith ignore graph

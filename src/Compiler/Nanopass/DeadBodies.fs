// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.DeadBodies

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe
module Reachability = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability
module Recipes = Clef.Compiler.Baker.Recipes.DeadBodyRecipes

let private fanOutUsing select graph =
    select "Source.dead-body" (fun node -> node.IsReachable && match node.Kind with SemanticKind.IfThenElse _ | SemanticKind.WhileLoop _ -> true | _ -> false) (fun node current ->
        match Recipes.replacement current node with
        | None -> NotApplicable "No current constant exclusion"
        | Some selection ->
            RecipeCreated {OriginalNodeId=node.Id; ReplacementRootId=node.Id
                           NewNodes=Recipes.materialize node selection; NewEdges=[]
                           ElaborationKind="Baker"; ElaborationSource="Source.dead-body"}) graph

let fanOut graph = fanOutUsing FanOut.fanOut graph

let private foldChanged emit graph recipes =
    emit recipes
    if recipes.Recipes.IsEmpty then None
    else Some (FoldIn.foldIn recipes graph)

let normalizeWith emit graph =
    foldChanged emit graph (fanOut graph)
    |> Option.map Reachability.markUnreachable
    |> Option.defaultValue graph

let internal normalizeReachedWithStatus emit (graph, reached) =
    let recipes = fanOutUsing (FanOut.fanOutAt reached) graph
    match foldChanged emit graph recipes with
    | None -> graph, reached, false
    | Some folded ->
        let marked, scope = Reachability.markUnreachableWithScope folded
        marked, scope, true

let normalizeReachedWith emit (graph, reached) =
    let marked, scope, _ = normalizeReachedWithStatus emit (graph, reached)
    marked, scope

let normalize graph = normalizeWith ignore graph

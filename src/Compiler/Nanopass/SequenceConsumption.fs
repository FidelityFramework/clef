// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Expose sequence consumption as ordinary iteration before ownership,
/// delegation and evaluation contracts are settled. Names are not identities.
module Clef.Compiler.Nanopass.SequenceConsumption

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Nanopass.Recipe
module Recipes = Clef.Compiler.Baker.Recipes.SequenceConsumptionRecipes

let normalize (graph: SemanticGraph) =
    let plans =
        graph.Nodes |> Map.toList |> List.choose (fun (id, source) ->
            match source.Kind with
            | SemanticKind.ForEach (_, formalId, collection, body) when source.IsReachable ->
                match graph.Nodes.TryFind formalId, graph.Nodes.TryFind collection, graph.Nodes.TryFind body with
                | _, Some { Kind = SemanticKind.Error _ }, _ -> None
                | Some ({ Kind = SemanticKind.PatternBinding _; IsReachable = true } as formal),
                  Some { Type = NativeType.TSeq elementType; IsReachable = true },
                  Some { Type = bodyType; IsReachable = true }
                    when formal.Type = elementType && bodyType = Types.unitType ->
                    let ctx = mkContext source.Range elementType graph.Platform "Seq.consume" source.Id
                    Some (id, Recipes.expand ctx source formal collection body elementType)
                | _ -> None
            | _ -> None) |> Map.ofList
    if Map.isEmpty plans then graph
    else
        let create (source: SemanticNode) _ =
            let plan = plans[source.Id]
            RecipeCreated {
                OriginalNodeId = source.Id; NewNodes = plan.NewNodes
                ReplacementRootId = plan.ResultNodeId
                ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Seq.consume" }
        let recipes = FanOut.fanOut "SequenceConsumption" (fun node -> plans.ContainsKey node.Id) create graph
        FoldIn.foldIn recipes graph

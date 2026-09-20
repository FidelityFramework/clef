// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Expand admitted delegation after producers and ownership are established.
/// The recipe introduces no new YieldBang, so one fan-out/fold-in reaches this
/// rule's fixed point. Ownership is re-established for the resulting Yield sites.
module Clef.Compiler.Nanopass.SequenceDelegation

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Suspensions
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Nanopass.Recipe
module Recipes = Clef.Compiler.Baker.Recipes.SequenceDelegationRecipes

let normalize (graph: SemanticGraph) =
    let owned =
        graph.Edges |> List.filter isDelimiter |> List.groupBy _.Target
        |> List.choose (fun (site, edges) ->
            match edges with
            | [{ Sources = [owner; generator] }] ->
                match graph.Nodes.TryFind owner, graph.Nodes.TryFind generator with
                | Some { Kind = SemanticKind.SeqExpr (actual, _); IsReachable = true },
                  Some { Kind = SemanticKind.Lambda (_, _, _, _, LambdaContext.SeqGenerator); IsReachable = true }
                    when actual = generator -> Some site
                | _ -> None
            | _ -> None) |> Set.ofList
    let plans =
        graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with
            | SemanticKind.YieldBang input when node.IsReachable && owned.Contains id ->
                match graph.Nodes.TryFind input with
                | Some { Type = NativeType.TSeq elementType } ->
                    let ctx = mkContext node.Range elementType graph.Platform "Seq.delegate" node.Id
                    Some (id, Recipes.expand ctx node input elementType)
                // Invalid source operands retain their original type diagnostic
                // and site; no sequence element type is guessed for a scalar.
                | _ -> None
            | _ -> None) |> Map.ofList
    if Map.isEmpty plans then graph
    else
        let create (node: SemanticNode) _ =
            let plan = plans[node.Id]
            RecipeCreated {
                OriginalNodeId = node.Id; NewNodes = plan.Structure.NewNodes
                ReplacementRootId = plan.Structure.ResultNodeId
                ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Seq.delegate" }
        let recipes = FanOut.fanOut "SequenceDelegation" (fun node -> plans.ContainsKey node.Id) create graph
        let folded = FoldIn.foldIn recipes graph
        let provenance = plans.Values |> Seq.collect _.Edges |> Seq.toList
        let delimiters =
            provenance |> List.map (fun origin ->
                // The wrapper retains the source site's identity and position.
                // Transfer its established owner to the yield introduced beneath
                // it; the delegated input's own delimiter edges stay separate.
                let previous = graph.Edges |> List.find (fun edge -> isDelimiter edge && edge.Target = List.head origin.Sources)
                { previous with Target = origin.Target })
        { folded with
            Edges = (folded.Edges |> List.filter (fun edge -> not (isDelimiter edge && plans.ContainsKey edge.Target)))
                    @ provenance @ delimiters }

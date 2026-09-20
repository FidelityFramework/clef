// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Fan out ownership recipes after producer/capture elaboration; fold only
/// their delimiter relation into F. Evaluation segments and frames are later
/// contracts. Re-firing replaces this projection, retaining all other edges.
module Clef.Compiler.Nanopass.SequenceOwnership

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
open Clef.Compiler.Baker.Ingredients.Suspensions
module Recipes = Clef.Compiler.Baker.Recipes.SequenceOwnershipRecipes

let elaborate (graph: SemanticGraph) =
    let additions, recipeDiagnostics =
        graph.Nodes.Values
        |> Seq.filter (fun node -> node.IsReachable)
        |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.SeqExpr _ -> Some (Recipes.forOwner graph node)
            | _ -> None)
        |> Seq.toList |> List.unzip
    let enrichment = Enrichment.concat additions
    let incidence = enrichment.NewEdges |> List.groupBy _.Target |> Map.ofList
    let malformed =
        graph.Nodes.Values |> Seq.choose (fun node ->
            if not node.IsReachable then None
            else
                match node.Kind with
                | SemanticKind.Yield _ | SemanticKind.YieldBang _ ->
                    match Map.tryFind node.Id incidence with
                    | Some [_] -> None
                    | Some edges ->
                        Some (Recipes.invalid node (edges |> List.collect _.Sources)
                            "A sequence suspension site belongs to more than one delimiter.")
                    | None -> Some (Recipes.invalid node [] "A sequence suspension site has no owning delimiter.")
                | _ -> None) |> Seq.toList
    let invalidSites = malformed |> List.collect _.RelatedNodes |> Set.ofList
    let accepted = enrichment.NewEdges |> List.filter (fun edge -> not (invalidSites.Contains edge.Target))
    { enrichment with NewEdges = accepted }, List.concat recipeDiagnostics @ malformed

let foldIn (enrichment: Enrichment) (graph: SemanticGraph) =
    { graph with Edges = (graph.Edges |> List.filter (isDelimiter >> not)) @ enrichment.NewEdges }

let normalize graph =
    let enrichment, diagnostics = elaborate graph
    foldIn enrichment graph, diagnostics

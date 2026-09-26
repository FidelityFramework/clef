// SPDX-License-Identifier: MIT

/// Baker recurrence fan-out/fold-in. Structural recognition and numeric
/// saturation remain separate; range analysis supplies its existing facts.
module Clef.Compiler.Nanopass.LoopRanges

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.Baker.Ingredients.Obligations
module Recipes = Clef.Compiler.Baker.Recipes.LoopRangeRecipes

let private isOurs = function
    | SemanticKind.Obligation { Body = ObligationBody.FiniteLoopTrip _ | ObligationBody.AdditiveLoopInvariant _ | ObligationBody.FiniteLinearRecurrence _ } -> true
    | _ -> false

let recognize inputs (graph: SemanticGraph) =
    let old = graph.Nodes |> Map.filter (fun _ node -> isOurs node.Kind)
    let ids = old |> Map.keys |> Set.ofSeq
    let anchors = old.Values |> Seq.choose (fun node -> match node.Kind with SemanticKind.Obligation info -> Some info.Id | _ -> None) |> Set.ofSeq
    let graph = { graph with
                    Nodes = graph.Nodes |> Map.filter (fun id _ -> not (ids.Contains id)) |> Map.map (fun _ node ->
                        match node.Metadata.TryFind ObligationMetadata.Anchors with
                        | Some(MetadataValue.StringList names) -> { node with Metadata = node.Metadata.Add(ObligationMetadata.Anchors, MetadataValue.StringList(names |> List.filter (fun name -> not (anchors.Contains name)))) }
                        | _ -> node)
                    Edges = graph.Edges |> List.filter (fun edge -> not (ids.Contains edge.Target) && not (edge.Sources |> List.exists ids.Contains)) }
    let recognition = Recipes.recognize graph inputs
    Recipes.foldRelations recognition graph, recognition

let saturate range (recognition: Recipes.Recognition) (graph: SemanticGraph) =
    let settled, residuals = recognition.Accumulations |> List.fold (fun (settled, residuals) item ->
        match Recipes.saturate range item with
        | Ok result -> result :: settled, residuals
        | Error reason ->
            let edge = { Class = EdgeClass.Range; Role = EdgeRole.LoopRangePending reason; Sources = [item.Induction.Owner; item.Induction.Loop]; Target = item.Cell; Ordinal = 0 }
            settled, edge :: residuals) ([], [])
    let linear, linearResiduals = recognition.Linear |> List.fold (fun (settled, residuals) item ->
        match Recipes.saturateLinear range item with
        | Ok result -> result :: settled, residuals
        | Error reason ->
            let pending = item.Cells |> List.map (fun cell ->
                { Class = EdgeClass.Range; Role = EdgeRole.LoopRangePending reason
                  Sources = Recipes.linearSources item; Target = cell; Ordinal = 0 })
            settled, pending @ residuals) ([], [])
    let enrichment = Enrichment.combine (Recipes.obligations graph settled) (Recipes.linearObligations graph linear)
    let anchors = enrichment.NewNodes |> List.choose (fun node -> match node.Kind with SemanticKind.Obligation info -> Some(node.Id, info.Id) | _ -> None) |> Map.ofList
    let annotations =
        enrichment.NewEdges |> List.collect (fun edge ->
            anchors.TryFind edge.Target |> Option.map (fun name -> edge.Sources |> List.map (fun id -> id, name)) |> Option.defaultValue [])
        |> List.groupBy fst |> List.choose (fun (id, names) -> graph.Nodes.TryFind id |> Option.map (fun node ->
            let existing = match node.Metadata.TryFind ObligationMetadata.Anchors with Some(MetadataValue.StringList names) -> names | _ -> []
            { node with Metadata = node.Metadata.Add(ObligationMetadata.Anchors, MetadataValue.StringList(List.distinct (existing @ List.map snd names))) }))
    graph
    |> SemanticGraph.addNodes annotations
    |> SemanticGraph.addNodes enrichment.NewNodes
    |> SemanticGraph.addEdges (enrichment.NewEdges @ residuals @ linearResiduals)

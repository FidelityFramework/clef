// SPDX-License-Identifier: MIT

/// Re-fire only the finite-sequence accumulation projection. Stale proofs and
/// anchors are retired in the owning fold, including loss of any source premise.
module Clef.Compiler.Nanopass.SequenceAccumulations

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Recipes = Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes

let recognize inputs (graph: SemanticGraph) =
    // Recognition reads the current graph-owned representation correspondence
    // before its old projection is retired. The recipe derives fresh bounds;
    // it never treats held proof bodies or range annotations as source facts.
    let recognized = Recipes.recognize graph inputs
    let old = graph.Nodes |> Map.filter (fun _ node -> Recipes.hasProof node)
    let ids = old |> Map.keys |> Set.ofSeq
    let graph = Clef.Compiler.Baker.Recipes.ObligationRecipes.retireAnchors ids graph
    let nodes = graph.Nodes |> Map.filter (fun id _ -> not (ids.Contains id))
    let edges = graph.Edges |> List.filter (fun edge ->
        not (ids.Contains edge.Target) && not (edge.Sources |> List.exists ids.Contains) &&
        not (Recipes.isRelation edge))
    // A new source recognition must earn a new representation handoff. Old
    // range annotations or the prior numeric domain cannot renew this receipt.
    let graph = { graph with Nodes = nodes; Edges = edges; SequenceRangeProvenance = None }
    { graph with Edges = graph.Edges @ Recipes.relations recognized }, recognized

let saturate range items (graph: SemanticGraph) =
    let enrichment = Recipes.obligations graph range items
    let anchors = enrichment.NewNodes |> List.choose (fun node ->
        match node.Kind with SemanticKind.Obligation info -> Some(node.Id, info.Id) | _ -> None) |> Map.ofList
    let annotations =
        enrichment.NewEdges
        |> List.collect (fun edge ->
            match anchors.TryFind edge.Target with
            | Some name -> edge.Sources |> List.map (fun id -> id, name)
            | None -> [])
        |> List.groupBy fst
    let nodes = annotations |> List.fold (fun (nodes: Map<NodeId, SemanticNode>) (id, names) ->
        match nodes.TryFind id with
        | None -> nodes
        | Some node ->
            let existing = match node.Metadata.TryFind ObligationMetadata.Anchors with Some(MetadataValue.StringList names) -> names | _ -> []
            nodes.Add(id, { node with Metadata = node.Metadata.Add(ObligationMetadata.Anchors, MetadataValue.StringList(List.distinct (existing @ List.map snd names))) })) graph.Nodes
    { graph with Nodes = enrichment.NewNodes |> List.fold (fun nodes node -> Map.add node.Id node nodes) nodes
                 Edges = graph.Edges @ enrichment.NewEdges }

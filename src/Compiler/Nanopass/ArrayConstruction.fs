// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.ArrayConstruction

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe
module Recipes = Clef.Compiler.Baker.Recipes.ArrayConstructionRecipes

let normalize (graph: SemanticGraph) =
    // Demand is settled for the incoming graph. Preserve that complete census
    // through this batch; the owning demand pass runs again after all rewrites.
    let candidates=Recipes.candidates graph |> List.map _.Id
    (graph,candidates) ||> List.fold(fun graph id ->
        let source=graph.Nodes[id]
        try
            let expansion = Recipes.materialize graph source
            let recipe = RecipeCreated {
                OriginalNodeId=source.Id;NewNodes=expansion.Nodes;ReplacementRootId=source.Id
                NewEdges=[];ElaborationKind="Baker";ElaborationSource="Array.construction" }
            let folded = FoldIn.foldIn (FanOut.fanOut "Array.construction" (fun node -> node.Id=source.Id) (fun _ _ -> recipe) graph) graph
            {folded with Edges=expansion.Edges} |> Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable
        with Recipes.MissingConstruction reason ->
            let marked={source with Metadata=source.Metadata.Add("Baker.ArrayConstructionError",MetadataValue.String reason)}
            {graph with Nodes=graph.Nodes.Add(source.Id,marked)})

// SPDX-License-Identifier: MIT
/// Source bounds enter before demand/range/numeric settlement. The original
/// access becomes its guard frontier; successful access remains its continuation.
module Clef.Compiler.Nanopass.MemoryAccessElaboration

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Recipes.MemoryAccessRecipes
open Clef.Compiler.Nanopass.Recipe

let rec private elaborate (graph: SemanticGraph) =
    match candidates graph |> List.tryHead with
    | None -> graph
    | Some source ->
        let name = "Memory.bounds"
        let context = mkContext source.Range source.Type graph.Platform name source.Id
        let expansion = materialize context graph source
        let create (node: SemanticNode) _ =
            RecipeCreated { OriginalNodeId = node.Id; NewNodes = expansion.Structure.NewNodes
                            ReplacementRootId = node.Id; ElaborationKind = "Baker"; NewEdges = []
                            ElaborationSource = name }
        let folded = FoldIn.foldIn (FanOut.fanOut name (fun node -> node.Id = source.Id) create graph) graph
        elaborate { folded with Edges = expansion.Edges }

let normalize graph =
    let result = elaborate graph
    if obj.ReferenceEquals(graph, result) || result.DeclarationRoots.IsEmpty then result
    else Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable result

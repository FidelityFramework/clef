// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.StringComparisons

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe
module Recipes = Clef.Compiler.Baker.Recipes.StringComparisonRecipes

let rec private elaborate graph =
    match Recipes.candidates graph |> List.tryHead with
    | None -> graph
    | Some((source,_,_,_,_) as candidate) ->
        let structure, edges = Recipes.materialize graph candidate
        let create (node: SemanticNode) _ =
            RecipeCreated { OriginalNodeId=node.Id; NewNodes=structure.NewNodes; ReplacementRootId=node.Id
                            ElaborationKind="Baker"; NewEdges=[]; ElaborationSource="String.equality" }
        let folded = FoldIn.foldIn (FanOut.fanOut "String.equality" (fun node -> node.Id=source.Id) create graph) graph
        elaborate { folded with Edges=edges }

let normalize graph =
    let result = elaborate graph
    if obj.ReferenceEquals(graph,result) || result.DeclarationRoots.IsEmpty then result
    else Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable result

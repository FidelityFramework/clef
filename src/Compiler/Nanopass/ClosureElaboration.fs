// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Direct named captures are settled before range, layout and obligations.
/// Every firing is a Baker recipe folded into a fresh graph. No storage form
/// is selected for mutable captures by this immutable-only increment.
module Clef.Compiler.Nanopass.ClosureElaboration

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.DirectCaptures
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Recipes.ClosureRecipes
open Clef.Compiler.Nanopass.Recipe

let rec normalize (graph: SemanticGraph) =
    match plans graph |> List.tryHead with
    | None -> graph
    | Some plan ->
        let name = "DirectCapture"
        let ctx = mkContext plan.Lambda.Range plan.Lambda.Type graph.Platform name plan.Lambda.Id
        let result = direct ctx graph plan
        let create (node: SemanticNode) _ =
            RecipeCreated { OriginalNodeId = node.Id; NewNodes = result.Structure.NewNodes
                            ReplacementRootId = result.Structure.ResultNodeId
                            ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = name }
        let recipes = FanOut.fanOut name (fun node -> node.Id = plan.Lambda.Id) create graph
        let folded = FoldIn.foldIn recipes graph
        normalize { folded with Edges = result.Edges }

// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Settle returned-function application boundaries after Baker exposes concrete
/// callables and before range, layout or witness consumers commit to their calls.
module Clef.Compiler.Nanopass.CallableApplications

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Recipes.ApplicationRecipes
open Clef.Compiler.Nanopass.Recipe

let normalize (graph: SemanticGraph) =
    let plans = applicationStages graph
    let create (node: SemanticNode) (graph: SemanticGraph) =
        match node.Kind, plans.TryFind node.Id with
        | SemanticKind.Application (callee, arguments), Some stages ->
            let name = "CallableApplication"
            let ctx = mkContext node.Range node.Type graph.Platform name node.Id
            let result = stage ctx node callee arguments stages
            RecipeCreated {
                OriginalNodeId = node.Id
                NewNodes = result.NewNodes @ result.AuxFunctions
                ReplacementRootId = result.ResultNodeId
                ElaborationKind = "Baker"
                NewEdges = []; ElaborationSource = name }
        | _ -> NotApplicable "Application does not cross a settled callable boundary"
    let recipes = FanOut.fanOut "CallableApplications" (fun node -> plans.ContainsKey node.Id) create graph
    FoldIn.foldIn recipes graph

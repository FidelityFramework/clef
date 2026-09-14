// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Actual callable boundaries are settled by the PSG; this recipe only composes
/// the corresponding calls and preserves eager source operand evaluation.
module Clef.Compiler.Baker.Recipes.ApplicationRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Recipes.Decomposition

let stage (ctx: Context) (source: SemanticNode) (callee: NodeId) (arguments: NodeId list) (stages: Stage list) =
    let rec calls current stages =
        saturation {
            match stages with
            | [] -> return current
            | stage :: rest ->
                let! next = app current stage.Arguments stage.ResultType
                return! calls next rest
        }
    let state = SaturationState.create ctx.SourceRange ctx.OriginalHOF ctx.ExpansionId ctx.InspiringNode ctx.Platform
    let result, nodes = run state (saturation {
        let! result = calls callee stages
        let! value = evaluateBefore (callee :: arguments) result (List.last stages).ResultType
        return! inheritContext source value
    })
    match result with
    | Matched root -> mkResultNoShadow nodes root []
    | NoMatch reason -> failwithf "Callable application saturation failed: %s" reason

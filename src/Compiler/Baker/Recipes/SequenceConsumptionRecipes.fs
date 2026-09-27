// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Native sequence consumption preserves its source declaration identity.
/// Each successful pull initializes that immutable binding before the body.
module Clef.Compiler.Baker.Recipes.SequenceConsumptionRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Baker.Ingredients.Sequences
open Clef.Compiler.Baker.Recipes.Decomposition

let expand (ctx: Context) (source: SemanticNode) (formal: SemanticNode) collection body elementType : Result =
    let point = { source.Range with End = source.Range.Start }
    let state = SaturationState.create point ctx.OriginalHOF ctx.ExpansionId ctx.InspiringNode ctx.Platform
    let result, nodes = run state (saturation {
        let! name =
            match formal.Kind with
            | SemanticKind.PatternBinding name -> XParsec.Parsers.preturn name
            | other ->
                XParsec.Parsers.fail (XParsec.ErrorType.Message (sprintf "CCS source checking did not settle the source formal for sequence consumption %d: formal %d is %A" (NodeId.value source.Id) (NodeId.value formal.Id) other))
        let! iteration = iterate collection elementType (fun current -> saturation {
            do! enrich formal (SemanticKind.Binding(name, false, false, None)) elementType [current] formal.EmissionStrategy false
            return! evaluateBefore [formal.Id] body Types.unitType
        })
        do! enrich source (SemanticKind.Sequential [iteration]) Types.unitType [iteration] source.EmissionStrategy false
        return source.Id
    })
    match result with
    | Matched root -> mkResultNoShadow nodes root []
    | NoMatch reason -> failwithf "Sequence consumption saturation failed: %s" reason

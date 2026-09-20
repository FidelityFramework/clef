// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Delegation becomes an ordinary owner-local iteration protocol before cuts
/// are segmented. Pulling an empty input follows the loop's false edge without
/// suspending; each successful pull yields its single bound current value.
module Clef.Compiler.Baker.Recipes.SequenceDelegationRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Sequences
open Clef.Compiler.Baker.Recipes.Decomposition

type Delegation = { Structure: Result; Edges: Hyperedge list }

let expand (ctx: Context) (source: SemanticNode) input elementType : Delegation =
    // Only the source wrapper owns the original expression's range. Synthesized
    // names and protocol nodes must not hide the user's operands in the editor.
    let point = { source.Range with End = source.Range.Start }
    let state = SaturationState.create point ctx.OriginalHOF ctx.ExpansionId ctx.InspiringNode ctx.Platform
    let result, nodes = run state (delegateAt source input elementType)
    match result with
    | Matched root ->
        let edges = nodes |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Yield _ -> Some (delegationOrigin source.Id input node.Id)
            | _ -> None)
        { Structure = mkResultNoShadow nodes root []; Edges = edges }
    | NoMatch reason -> failwithf "Sequence delegation saturation failed: %s" reason

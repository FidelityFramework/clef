// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// String function values use ordinary source function construction. Descriptor
/// observations subsequently receive the same extent and carrier settlement as
/// a source property or direct intrinsic application.
module Clef.Compiler.Baker.Recipes.StringRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

let tryReifyValue (ctx: Context) operation functionType enclosing : Result option =
    match applySubst functionType with
    | NativeType.TFun(domain, resultType) when operation = "length" && Types.isStringType domain ->
        let body parameters _ =
            match parameters with
            | [source] -> fieldGet source "Length" resultType
            | _ -> fail (XParsec.ErrorType.Message "String.length requires its one declared string parameter.")
        let state =
            { EmittedNodes = []; Bindings = Map.empty; ExpansionId = ctx.ExpansionId
              OriginalHOF = ctx.OriginalHOF; SourceRange = ctx.SourceRange
              InspiringNode = ctx.InspiringNode; Platform = ctx.Platform }
        match run state (closure [("__text", domain)] [] enclosing body resultType) with
        | Matched result, nodes -> Some(mkResultNoShadow nodes result [])
        | NoMatch reason, _ -> failwithf "String.length function construction failed: %s" reason
    | _ -> None

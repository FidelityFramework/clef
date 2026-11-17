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
        | NoMatch reason, _ -> Some(mkFailedResult ctx.InspiringNode ("String.length function construction failed: " + reason))
    | _ -> None

/// A finite integer formatting domain can be represented entirely by source
/// selections and immutable decimal literals. The argument remains evaluated
/// once before selection; the bound is read from its current range fact.
let tryFormatInteger (ctx: Context) (graph: SemanticGraph) argument : Result option =
    match graph.Nodes.TryFind argument with
    | Some input ->
        match input.ValueRange with
        | Some(ValueRange.Bounded(lower, upper)) when lower <= upper && upper - lower < 256I
                                                    && lower >= bigint System.Int64.MinValue && upper <= bigint System.Int64.MaxValue ->
            let state = SaturationState.create ctx.SourceRange ctx.OriginalHOF ctx.ExpansionId ctx.InspiringNode ctx.Platform
            let recipe = saturation {
                let! binding = letBind "__format_integer" argument input.Type
                let rec select (current: bigint) = saturation {
                    let! text = createWithChildren (SemanticKind.Literal(NativeLiteral.String(current.ToString(System.Globalization.CultureInfo.InvariantCulture)))) Types.stringType []
                    if current = upper then return text else
                    let! value = varRef "__format_integer" (Some binding) input.Type
                    let! expected = numLit (int64 current) input.Type
                    let! equal = eq value expected input.Type
                    let! remaining = select (current + 1I)
                    return! ifThenElse equal text remaining Types.stringType
                }
                let! selected = select lower
                let! value = varRef "__format_integer" (Some binding) input.Type
                let! demanded = createWithChildren (SemanticKind.EagerExpr value) input.Type [value]
                return! evaluateBefore [binding; demanded] selected Types.stringType
            }
            match run state recipe with
            | Matched root, nodes -> Some(mkResultNoShadow nodes root [])
            | NoMatch reason, _ -> Some(mkFailedResult ctx.InspiringNode reason)
        | _ -> None
    | None -> None

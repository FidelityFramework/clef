// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Baker Numeric Recipes: the library schemes of design (c) decomposed to the atomic operations
/// the five dialects express (Dimensional_Range_Design.md §5, "intended loss is arithmetic";
/// sequence CS-9).
///
///   abs x          = if x < 0 then -x else x
///   sign x         = if x > 0 then 1 elif x < 0 then -1 else 0
///   min a b        = if a < b then a else b
///   max a b        = if a > b then a else b
///   clamp lo hi x  = min hi (max lo x)
///   floor x        = if x < float (truncate x) then truncate x - 1 else truncate x
///   ceiling x      = if x > float (truncate x) then truncate x + 1 else truncate x
///   round x        = if x >= 0 then truncate (x + 0.5) else truncate (x - 0.5)   (half away from zero)
///
/// `truncate` and `float` are atomic (fptosi and sitofp, witnessed in Composer); `sqrt`, `atan2`
/// and the transcendentals have no recipe and no witness yet: they type-check and a reachable use
/// fails loudly at the witness. The literals 0, 1, -1 and 0.5 are typed at the operand's carrier
/// and dimension. A value used more than once (`truncate x` in `floor`) is one node referenced
/// from the guard and the branches; Alex witnesses a node once, at its first visit, which is the
/// guard, so its SSA dominates both regions. A value used only inside the branches (the 0.5 of
/// `round`) is one node per branch, since a node first visited inside one region is defined there.
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
module Clef.Compiler.Baker.Recipes.NumericRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

//=============================================================================
// BRIDGE: Convert SaturationParser results to Decomposition.Result
//=============================================================================

let private toSaturationState (ctx: Context) : SaturationState =
    { EmittedNodes = []
      Bindings = Map.empty
      ExpansionId = ctx.ExpansionId
      OriginalHOF = ctx.OriginalHOF
      SourceRange = ctx.SourceRange
      InspiringNode = ctx.InspiringNode
      Platform = ctx.Platform }

let private runSaturation (ctx: Context) (parser: SaturationParser<NodeId>) : Result =
    let result, nodes = run (toSaturationState ctx) parser
    match result with
    | Matched resultNodeId -> mkResultNoShadow nodes resultNodeId []
    | NoMatch reason -> failwithf "Saturation failed: %s" reason

//=============================================================================
// RECIPES
//=============================================================================

/// abs x = if x < 0 then -x else x
let private absRecipe (x: NodeId) (t: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! zero = numLit 0L t
        let! negative = lt x zero t
        let! negated = neg x t
        return! ifThenElse negative negated x t
    }

/// sign x = if x > 0 then 1 elif x < 0 then -1 else 0, at `int<1>`
let private signRecipe (x: NodeId) (t: NativeType) (resultType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! zero = numLit 0L t
        let! positive = gt x zero t
        let! negative = lt x zero t
        let! one = numLit 1L resultType
        let! minusOne = numLit -1L resultType
        let! zeroResult = numLit 0L resultType
        let! inner = ifThenElse negative minusOne zeroResult resultType
        return! ifThenElse positive one inner resultType
    }

/// min a b = if a < b then a else b
let private minRecipe (a: NodeId) (b: NodeId) (t: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! less = lt a b t
        return! ifThenElse less a b t
    }

/// max a b = if a > b then a else b
let private maxRecipe (a: NodeId) (b: NodeId) (t: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! greater = gt a b t
        return! ifThenElse greater a b t
    }

/// clamp lo hi x = min hi (max lo x)
let private clampRecipe (lo: NodeId) (hi: NodeId) (x: NodeId) (t: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! raised = maxRecipe lo x t
        return! minRecipe hi raised t
    }

/// floor x = let t = truncate x in if x < float t then t - 1 else t
let private floorRecipe (x: NodeId) (realType: NativeType) (intType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! truncated = truncate x realType intType
        let! back = toFloat truncated intType realType
        let! below = lt x back realType
        let! one = numLit 1L intType
        let! lowered = sub truncated one intType
        return! ifThenElse below lowered truncated intType
    }

/// ceiling x = let t = truncate x in if x > float t then t + 1 else t
let private ceilingRecipe (x: NodeId) (realType: NativeType) (intType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! truncated = truncate x realType intType
        let! back = toFloat truncated intType realType
        let! above = gt x back realType
        let! one = numLit 1L intType
        let! raised = add truncated one intType
        return! ifThenElse above raised truncated intType
    }

/// round x = if x >= 0 then truncate (x + 0.5) else truncate (x - 0.5), half away from zero.
/// Each branch has its own 0.5: a node first visited inside one region of the conditional is
/// defined there, and the other region could not see it.
let private roundRecipe (x: NodeId) (realType: NativeType) (intType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! zero = numLit 0L realType
        let! nonNegative = ge x zero realType
        let! halfUp = floatLit 0.5 realType
        let! up = add x halfUp realType
        let! roundedUp = truncate up realType intType
        let! halfDown = floatLit 0.5 realType
        let! down = sub x halfDown realType
        let! roundedDown = truncate down realType intType
        return! ifThenElse nonNegative roundedUp roundedDown intType
    }

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// Try to decompose a library scheme application. `argTypes` are the resolved types of the
/// arguments in order; `resultType` the application's. An operation with no recipe (truncate,
/// sqrt, atan2, the transcendentals) returns None: it is atomic to Alex, witnessed or not.
/// Saturation runs before the checker's diagnostics are surfaced, so an application whose
/// operand is not a numeric type with a resolved carrier (`abs true`, CCS8000; an operand whose
/// kind is undetermined, CCS8001) is left alone here: the diagnostic already minted is the
/// failure, and a recipe that threw would hide it.
let tryDecompose
    (ctx: Context)
    (operation: string)
    (args: NodeId list)
    (argTypes: NativeType list)
    (resultType: NativeType)
    : Result option =

    let resolvedNumeric (ty: NativeType) = Types.isNumericType ty && (Types.tryGetNTUKind ty).IsSome
    if not (List.forall resolvedNumeric argTypes && resolvedNumeric resultType) then None else
    match operation, args, argTypes with
    | "abs", [x], [t] -> Some (runSaturation ctx (absRecipe x t))
    | "sign", [x], [t] -> Some (runSaturation ctx (signRecipe x t resultType))
    | "min", [a; b], [t; _] -> Some (runSaturation ctx (minRecipe a b t))
    | "max", [a; b], [t; _] -> Some (runSaturation ctx (maxRecipe a b t))
    | "clamp", [lo; hi; x], [t; _; _] -> Some (runSaturation ctx (clampRecipe lo hi x t))
    | "floor", [x], [realType] -> Some (runSaturation ctx (floorRecipe x realType resultType))
    | "ceiling", [x], [realType] -> Some (runSaturation ctx (ceilingRecipe x realType resultType))
    | "round", [x], [realType] -> Some (runSaturation ctx (roundRecipe x realType resultType))
    | _ -> None

// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Baker Option Recipes - Decomposition of Option HOFs to primitives.
///
/// Option operations are simpler than List/Map/Set since Option is a discriminated union
/// with just two cases (None, Some). Most operations decompose to conditionals.
///
/// COMBINATOR MODEL:
/// Each recipe is 5-10 lines composing patterns from Ingredients/.
/// The verbose 100+ line manual node construction is eliminated.
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
module Clef.Compiler.Baker.Recipes.OptionRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

//=============================================================================
// BRIDGE: Convert SaturationParser results to Decomposition.Result
//=============================================================================

/// Convert a Decomposition.Context to a SaturationState
let private toSaturationState (ctx: Context) : SaturationState =
    { EmittedNodes = []
      Bindings = Map.empty
      ExpansionId = ctx.ExpansionId
      OriginalHOF = ctx.OriginalHOF
      SourceRange = ctx.SourceRange
      InspiringNode = ctx.InspiringNode
      Platform = ctx.Platform }

/// Run a saturation parser and convert to Decomposition.Result
let private runSaturation (ctx: Context) (parser: SaturationParser<NodeId>) : Result =
    let initialState = toSaturationState ctx
    let result, nodes = run initialState parser
    match result with
    | Matched resultNodeId ->
        mkResultNoShadow nodes resultNodeId []
    | NoMatch reason ->
        failwithf "Saturation failed: %s" reason

//=============================================================================
// OPTION STRUCTURE: compose the same DU ingredients as an explicit source match.
// Baker emits the complete decomposition in this firing: generated nodes are not
// sent through a second recipe pass. Preserve the payload type, including measures.
//=============================================================================

let private optionType innerType = NativeType.TApp (Types.optionTyCon, [innerType])

let private optionCaseTest optionNodeId innerType caseIndex =
    saturation {
        let! tag = duGetTag optionNodeId (optionType innerType)
        let! expected = int8Lit caseIndex
        return! compareEq tag expected Types.int8Type
    }

let private optionHasValue optionNodeId innerType = optionCaseTest optionNodeId innerType 1

let private optionValue optionNodeId innerType =
    duEliminate optionNodeId "Some" 1 innerType

let private optionSome valueNodeId innerType =
    duConstruct "Some" 1 (Some valueNodeId) None (optionType innerType)

let private optionNone innerType =
    duConstruct "None" 0 None None (optionType innerType)

//=============================================================================
// OPTION.MAP: map f opt → if isSome then Some (f (get opt)) else None
//=============================================================================

let private optionMapRecipe
    (mapperNodeId: NodeId)
    (optionNodeId: NodeId)
    (inputType: NativeType)
    (outputType: NativeType)
    : SaturationParser<NodeId> =

    let outputOptionType = NativeType.TApp (Types.optionTyCon, [outputType])

    saturation {
        // Check if option has value
        let! isSomeResult = optionHasValue optionNodeId inputType

        // Then branch: Some (f (get opt))
        let! value = optionValue optionNodeId inputType
        let! mapped = app1 mapperNodeId value outputType
        let! someResult = optionSome mapped outputType

        // Else branch: None
        let! noneResult = optionNone outputType

        // Conditional: if isSome then Some(f(get)) else None
        return! ifThenElse isSomeResult someResult noneResult outputOptionType
    }

//=============================================================================
// OPTION.BIND: bind f opt → if isSome then f (get opt) else None
//=============================================================================

let private optionBindRecipe
    (binderNodeId: NodeId)
    (optionNodeId: NodeId)
    (inputType: NativeType)
    (outputType: NativeType)
    : SaturationParser<NodeId> =

    let outputOptionType = NativeType.TApp (Types.optionTyCon, [outputType])

    saturation {
        // Check if option has value
        let! isSomeResult = optionHasValue optionNodeId inputType

        // Then branch: f (get opt) - binder returns Option<'U>
        let! value = optionValue optionNodeId inputType
        let! boundResult = app1 binderNodeId value outputOptionType

        // Else branch: None
        let! noneResult = optionNone outputType

        // Conditional: if isSome then f(get) else None
        return! ifThenElse isSomeResult boundResult noneResult outputOptionType
    }

//=============================================================================
// OPTION.FILTER: filter p opt → if isSome && p (get opt) then opt else None
//=============================================================================

let private optionFilterRecipe
    (predicateNodeId: NodeId)
    (optionNodeId: NodeId)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    let optionType = NativeType.TApp (Types.optionTyCon, [valueType])

    saturation {
        // Check if option has value
        let! isSomeResult = optionHasValue optionNodeId valueType

        // Get the value
        let! value = optionValue optionNodeId valueType

        // Apply predicate
        let! predicateResult = app1 predicateNodeId value Types.boolType

        // None for else branches
        let! noneResult = optionNone valueType

        // Reuse the expression value. Fold-in remaps this structural reference
        // if the input is itself decomposed (a constructor or another HOF).
        let! innerIf = ifThenElse predicateResult optionNodeId noneResult optionType

        // Outer if: if isSome then innerIf else None
        let! noneOuter = optionNone valueType
        return! ifThenElse isSomeResult innerIf noneOuter optionType
    }

/// exists and forall differ only at absence. The payload extraction and callback
/// belong to the Some branch; the None branch is the specified boolean literal.
let private optionPredicateRecipe predicate optionNodeId valueType absentResult =
    saturation {
        let! present = optionHasValue optionNodeId valueType
        let! value = optionValue optionNodeId valueType
        let! tested = app1 predicate value Types.boolType
        let! absent = boolLit absentResult
        return! ifThenElse present tested absent Types.boolType
    }

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// The operation body is shared by direct applications and reified function values.
/// No body emits another Option HOF that would require a second saturation firing.
let private operationRecipe operation args inputType outputType =
    match operation, args with
    | "map", [mapper; opt] ->
        let outType = outputType |> Option.defaultValue inputType
        Some (optionMapRecipe mapper opt inputType outType, optionType outType)
    | "bind", [binder; opt] ->
        let outType = outputType |> Option.defaultValue inputType
        Some (optionBindRecipe binder opt inputType outType, optionType outType)
    | "filter", [predicate; opt] ->
        Some (optionFilterRecipe predicate opt inputType, optionType inputType)
    | "exists", [predicate; opt] ->
        Some (optionPredicateRecipe predicate opt inputType false, Types.boolType)
    | "forall", [predicate; opt] ->
        Some (optionPredicateRecipe predicate opt inputType true, Types.boolType)
    | "isSome", [opt] -> Some (optionCaseTest opt inputType 1, Types.boolType)
    | "isNone", [opt] -> Some (optionCaseTest opt inputType 0, Types.boolType)
    | "get", [opt] -> Some (optionValue opt inputType, inputType)
    | "get", opt :: remaining ->
        // get consumes one option. Any remaining source arguments apply to its
        // function payload; preserve that boundary in this same recipe firing.
        let resultType =
            remaining |> List.fold (fun current _ ->
                current |> Option.bind (function NativeType.TFun (_, result) -> Some result | _ -> None)) (Some inputType)
        resultType |> Option.map (fun resultType ->
            let recipe = saturation {
                let! value = optionValue opt inputType
                let! result = app value remaining resultType
                return! evaluateBefore (opt :: remaining) result resultType
            }
            recipe, resultType)
    | _ -> None

let private innerType = function
    | NativeType.TApp (constructor, [payload]) when constructor = Types.optionTyCon -> Some payload
    | _ -> None

let private hasCallback = function
    | "map" | "bind" | "filter" | "exists" | "forall" -> true
    | _ -> false

/// Try to decompose a fully applied Option operation.
let tryDecompose ctx operation args inputType outputType : Result option =
    operationRecipe operation args inputType outputType
    |> Option.map (fun (recipe, resultType) ->
        runSaturation ctx (saturation {
            let! result = recipe
            if hasCallback operation then return! evaluateBefore args result resultType
            else return result
        }))

/// Snapshot the supplied function at partial formation. The closure captures the
/// immutable snapshot, while any mutable cells inside that function remain shared.
let private partialRecipe (ctx: Context) operation callback callbackType inputType resultType enclosing =
    let name = sprintf "__option_callback_%d" ctx.ExpansionId
    saturation {
        let! snapshot = letBind name callback callbackType
        let capture = { Name = name; Type = callbackType; IsMutable = false; SourceNodeId = Some snapshot }
        let body parameters captures =
            match parameters, captures with
            | [opt], [fn] -> operationRecipe operation [fn; opt] inputType (innerType resultType) |> Option.get |> fst
            | _ -> failwith "An Option partial requires one option parameter and one callback capture"
        let! value = closure [("__option", optionType inputType)] [capture] enclosing body resultType
        return! evaluateBefore [snapshot] value (NativeType.TFun (optionType inputType, resultType))
    }

/// A supplied callback leaves exactly one option parameter, even when its payload
/// or the operation result contains function types.
let tryDecomposePartial (ctx: Context) operation callback callbackType residualType enclosing : Result option =
    match residualType with
    | NativeType.TFun (domain, resultType) when hasCallback operation ->
        innerType domain |> Option.map (fun inputType ->
            runSaturation ctx (partialRecipe ctx operation callback callbackType inputType resultType enclosing))
    | _ -> None

/// Bare library operations become ordinary function values after their source type
/// scheme has been instantiated (and a generic alias specialized). Declared arity,
/// not the entire TFun spine, determines the operation's parameter boundary.
let tryReifyValue (ctx: Context) operation functionType enclosing : Result option =
    match functionType with
    | NativeType.TFun (callbackType, (NativeType.TFun (domain, resultType) as residual)) when hasCallback operation ->
        innerType domain |> Option.map (fun inputType ->
            let body parameters _ =
                match parameters with
                | [callback] -> partialRecipe ctx operation callback callbackType inputType resultType enclosing
                | _ -> failwith "An Option HOF value requires one callback parameter"
            runSaturation ctx (closure [("__callback", callbackType)] [] enclosing body residual))
    | NativeType.TFun (domain, resultType) ->
        innerType domain |> Option.bind (fun inputType ->
            match operation with
            | "isSome" | "isNone" | "get" ->
                let body parameters _ = operationRecipe operation parameters inputType None |> Option.get |> fst
                Some (runSaturation ctx (closure [("__option", domain)] [] enclosing body resultType))
            | _ -> None)
    | _ -> None

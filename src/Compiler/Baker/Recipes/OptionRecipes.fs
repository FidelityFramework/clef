// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Baker Option Recipes - Decomposition of Option HOFs to primitives.
///
/// Option operations are simpler than List/Map/Set since Option is a discriminated union
/// with just two cases (None, Some). Most operations decompose to conditionals.
///
/// Recipes compose the shared typed Option structure and explicit eager
/// operand snapshots; generated operations are complete in this firing.
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
module Options = Clef.Compiler.Baker.Ingredients.Options

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
        let! isSomeResult = Options.hasValue optionNodeId inputType

        // Then branch: Some (f (get opt))
        let! value = Options.value optionNodeId inputType
        let! mapped = app1 mapperNodeId value outputType
        let! someResult = Options.some mapped outputType

        // Else branch: None
        let! noneResult = Options.none outputType

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
        let! isSomeResult = Options.hasValue optionNodeId inputType

        // Then branch: f (get opt) - binder returns Option<'U>
        let! value = Options.value optionNodeId inputType
        let! boundResult = app1 binderNodeId value outputOptionType

        // Else branch: None
        let! noneResult = Options.none outputType

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
        let! isSomeResult = Options.hasValue optionNodeId valueType

        // Get the value
        let! value = Options.value optionNodeId valueType

        // Apply predicate
        let! predicateResult = app1 predicateNodeId value Types.boolType

        // None for else branches
        let! noneResult = Options.none valueType

        // Reuse the expression value. Fold-in remaps this structural reference
        // if the input is itself decomposed (a constructor or another HOF).
        let! innerIf = ifThenElse predicateResult optionNodeId noneResult optionType

        // Outer if: if isSome then innerIf else None
        let! noneOuter = Options.none valueType
        return! ifThenElse isSomeResult innerIf noneOuter optionType
    }

/// exists and forall differ only at absence. The payload extraction and callback
/// belong to the Some branch; the None branch is the specified boolean literal.
let private optionPredicateRecipe predicate optionNodeId valueType absentResult =
    saturation {
        let! present = Options.hasValue optionNodeId valueType
        let! value = Options.value optionNodeId valueType
        let! tested = app1 predicate value Types.boolType
        let! absent = boolLit absentResult
        return! ifThenElse present tested absent Types.boolType
    }

/// The action consumes the payload only in Some. Both paths return unit;
/// a function-valued payload is passed to the action without being invoked.
let private optionIterRecipe action optionNodeId valueType =
    saturation {
        let! present = Options.hasValue optionNodeId valueType
        let! value = Options.value optionNodeId valueType
        let! invoked = app1 action value Types.unitType
        let! absent = createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        return! ifThenElse present invoked absent Types.unitType
    }

/// Select the original fallback or the Some payload. Argument evaluation is
/// preserved by the application recipe; extraction belongs to the Some branch.
let private optionDefaultValueRecipe fallback optionNodeId valueType =
    saturation {
        let! present = Options.hasValue optionNodeId valueType
        let! value = Options.value optionNodeId valueType
        return! ifThenElse present value fallback valueType
    }

/// Evaluate the thunk value eagerly, but invoke it only in the None branch.
/// A function-valued payload is the result of this selection, not an extra
/// parameter of the Option operation or an additional thunk invocation.
let private optionDefaultWithRecipe fallback optionNodeId valueType =
    saturation {
        let! present = Options.hasValue optionNodeId valueType
        let! value = Options.value optionNodeId valueType
        let! unitArgument = createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        let! absent = app1 fallback unitArgument valueType
        return! ifThenElse present value absent valueType
    }

/// Alternatives retain the selected option itself, including its payload.
/// The thunk-valued alternative is invoked only in the None branch.
let private optionAlternativeRecipe lazyFallback fallback optionNodeId valueType =
    saturation {
        let! present = Options.hasValue optionNodeId valueType
        let resultType = Options.typeOf valueType
        let! absent = saturation {
            if lazyFallback then
                let! unitArgument = createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
                return! app1 fallback unitArgument resultType
            else return fallback
        }
        return! ifThenElse present optionNodeId absent resultType
    }

/// A single optional fold: the None branch is the original state value.
let private optionFoldRecipe operation folder state optionNodeId inputType stateType =
    saturation {
        let! present = Options.hasValue optionNodeId inputType
        let! value = Options.value optionNodeId inputType
        let arguments = if operation = "fold" then [state; value] else [value; state]
        let! folded = app folder arguments stateType
        return! ifThenElse present folded state stateType
    }

/// Read exactly the two folder arguments. A function-valued state remains a
/// state; neither its own domains nor an optional state changes the operation arity.
let private foldShape operation callbackType =
    match operation, callbackType with
    | "fold", NativeType.TFun (stateType, NativeType.TFun (inputType, _)) ->
        Some (inputType, stateType, [("__folder", callbackType); ("__state", stateType); ("__option", Options.typeOf inputType)])
    | "foldBack", NativeType.TFun (inputType, NativeType.TFun (stateType, _)) ->
        Some (inputType, stateType, [("__folder", callbackType); ("__option", Options.typeOf inputType); ("__state", stateType)])
    | _ -> None

let private foldBody operation arguments inputType stateType =
    match operation, arguments with
    | "fold", [folder; state; optionId]
    | "foldBack", [folder; optionId; state] -> optionFoldRecipe operation folder state optionId inputType stateType
    | _ -> failwith "An Option fold requires its three declared arguments"

/// A completed residual has the same eager operands as a direct invocation.
/// Establish its local capture and parameter references before either branch:
/// the state is shared by the folder call and the unchanged None result.
let private foldResidualBody operation arguments inputType stateType =
    saturation {
        let! result = foldBody operation arguments inputType stateType
        return! evaluateBefore arguments result stateType
    }

/// Each formation frontier snapshots precisely the values supplied so far.
/// One logical parameter per residual closure preserves the next frontier even
/// when a supplied state or the ultimate result is itself a function.
let rec private foldPartialRecipe (ctx: Context) operation supplied parameters inputType stateType enclosing =
    saturation {
        let! snapshots =
            supplied |> List.mapi (fun index (id, ty) ->
                saturation {
                    let name = sprintf "__option_fold_%d_%d_%d" supplied.Length index ctx.ExpansionId
                    let! snapshot = letBind name id ty
                    return snapshot, { Name = name; Type = ty; IsMutable = false; SourceNodeId = Some snapshot }
                }) |> sequence
        match parameters with
        | (name, parameterType) :: remaining ->
            let resultType = List.foldBack (fun (_, ty) result -> NativeType.TFun(ty, result)) remaining stateType
            let body arguments captures =
                let values = List.zip captures (List.map snd supplied) @ List.zip arguments [parameterType]
                if List.isEmpty remaining then foldResidualBody operation (List.map fst values) inputType stateType
                else foldPartialRecipe ctx operation values remaining inputType stateType enclosing
            let! value = closure [(name, parameterType)] (List.map snd snapshots) enclosing body resultType
            if List.isEmpty snapshots then return value
            else return! evaluateBefore (List.map fst snapshots) value (NativeType.TFun(parameterType, resultType))
        | [] -> return! foldResidualBody operation (List.map fst supplied) inputType stateType
    }

/// Fold applications have a declared three-argument boundary. Any further
/// arguments apply to the selected function-valued state, after every supplied
/// source operand has been evaluated in written order.
let tryDecomposeFold ctx operation supplied returnType enclosing : Result option =
    match supplied with
    | (_, callbackType) :: _ ->
        foldShape operation callbackType |> Option.map (fun (inputType, stateType, parameters) ->
            let recipe =
                if supplied.Length < 3 then
                    foldPartialRecipe ctx operation supplied (List.skip supplied.Length parameters) inputType stateType enclosing
                else saturation {
                    let arguments = List.map fst supplied
                    let! folded = foldBody operation (List.take 3 arguments) inputType stateType
                    let! result =
                        match List.skip 3 arguments with
                        | [] -> saturation { return folded }
                        | remaining -> app folded remaining returnType
                    return! evaluateBefore arguments result returnType
                }
            runSaturation ctx recipe)
    | [] -> None

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// The operation body is shared by direct applications and reified function values.
/// No body emits another Option HOF that would require a second saturation firing.
let private operationRecipe operation args inputType outputType =
    match operation, args with
    | "map", [mapper; opt] ->
        let outType = outputType |> Option.defaultValue inputType
        Some (optionMapRecipe mapper opt inputType outType, Options.typeOf outType)
    | "bind", [binder; opt] ->
        let outType = outputType |> Option.defaultValue inputType
        Some (optionBindRecipe binder opt inputType outType, Options.typeOf outType)
    | "filter", [predicate; opt] ->
        Some (optionFilterRecipe predicate opt inputType, Options.typeOf inputType)
    | "exists", [predicate; opt] ->
        Some (optionPredicateRecipe predicate opt inputType false, Types.boolType)
    | "forall", [predicate; opt] ->
        Some (optionPredicateRecipe predicate opt inputType true, Types.boolType)
    | "iter", [action; opt] ->
        Some (optionIterRecipe action opt inputType, Types.unitType)
    | ("orElse" | "orElseWith"), [fallback; opt] ->
        Some (optionAlternativeRecipe (operation = "orElseWith") fallback opt inputType, Options.typeOf inputType)
    | ("defaultValue" | "defaultWith"), fallback :: opt :: remaining ->
        // Two arguments eliminate the option. Further source arguments apply
        // its selected function payload, in this same saturation firing.
        let resultType =
            remaining |> List.fold (fun current _ ->
                current |> Option.bind (function NativeType.TFun (_, result) -> Some result | _ -> None)) (Some inputType)
        resultType |> Option.map (fun resultType ->
            let recipe = saturation {
                let! value =
                    if operation = "defaultWith" then optionDefaultWithRecipe fallback opt inputType
                    else optionDefaultValueRecipe fallback opt inputType
                if List.isEmpty remaining then return value
                else return! app value remaining resultType
            }
            recipe, resultType)
    | "isSome", [opt] -> Some (Options.caseTest opt inputType 1, Types.boolType)
    | "isNone", [opt] -> Some (Options.caseTest opt inputType 0, Types.boolType)
    | "get", [opt] -> Some (Options.value opt inputType, inputType)
    | "get", opt :: remaining ->
        // get consumes one option. Any remaining source arguments apply to its
        // function payload; preserve that boundary in this same recipe firing.
        let resultType =
            remaining |> List.fold (fun current _ ->
                current |> Option.bind (function NativeType.TFun (_, result) -> Some result | _ -> None)) (Some inputType)
        resultType |> Option.map (fun resultType ->
            let recipe = saturation {
                let! value = Options.value opt inputType
                let! result = app value remaining resultType
                return! evaluateBefore (opt :: remaining) result resultType
            }
            recipe, resultType)
    | _ -> None

let private innerType = function
    | NativeType.TApp (constructor, [payload]) when constructor = Types.optionTyCon -> Some payload
    | _ -> None

let private hasLeadingArgument = function
    | "map" | "bind" | "filter" | "exists" | "forall" | "iter" | "defaultValue" | "defaultWith" | "orElse" | "orElseWith" -> true
    | _ -> false

/// Try to decompose a fully applied Option operation.
let tryDecompose ctx operation args inputType outputType : Result option =
    operationRecipe operation args inputType outputType
    |> Option.map (fun (recipe, resultType) ->
        runSaturation ctx (saturation {
            let! result = recipe
            // expressions.md: an application evaluates all supplied operands
            // before entering the body, including arguments subsequently applied
            // to a returned function. Thunk invocation remains in the None arm.
            if hasLeadingArgument operation then return! evaluateBefore args result resultType
            else return result
        }))

/// Snapshot the supplied argument at partial formation. The closure captures the
/// immutable value, while referenced storage and mutable cells remain shared.
let private partialRecipe (ctx: Context) operation supplied suppliedType inputType resultType enclosing =
    let role = if operation = "defaultValue" || operation = "orElse" then "fallback" else "callback"
    let name = sprintf "__option_%s_%d" role ctx.ExpansionId
    saturation {
        let! snapshot = letBind name supplied suppliedType
        let capture = { Name = name; Type = suppliedType; IsMutable = false; SourceNodeId = Some snapshot }
        let body parameters captures =
            match parameters, captures with
            | [opt], [argument] -> operationRecipe operation [argument; opt] inputType (innerType resultType) |> Option.get |> fst
            | _ -> failwith "An Option partial requires one option parameter and one supplied argument capture"
        let! value = closure [("__option", Options.typeOf inputType)] [capture] enclosing body resultType
        return! evaluateBefore [snapshot] value (NativeType.TFun (Options.typeOf inputType, resultType))
    }

/// A supplied leading argument leaves exactly one option parameter, even when its payload
/// or the operation result contains function types.
let tryDecomposePartial (ctx: Context) operation supplied suppliedType residualType enclosing : Result option =
    match residualType with
    | NativeType.TFun (domain, resultType) when hasLeadingArgument operation ->
        innerType domain |> Option.map (fun inputType ->
            runSaturation ctx (partialRecipe ctx operation supplied suppliedType inputType resultType enclosing))
    | _ -> None

/// Bare library operations become ordinary function values after their source type
/// scheme has been instantiated (and a generic alias specialized). Declared arity,
/// not the entire TFun spine, determines the operation's parameter boundary.
let tryReifyValue (ctx: Context) operation functionType enclosing : Result option =
    match functionType with
    | NativeType.TFun (callbackType, _) when operation = "fold" || operation = "foldBack" ->
        foldShape operation callbackType |> Option.map (fun (inputType, stateType, parameters) ->
            runSaturation ctx (foldPartialRecipe ctx operation [] parameters inputType stateType enclosing))
    | NativeType.TFun (suppliedType, (NativeType.TFun (domain, resultType) as residual)) when hasLeadingArgument operation ->
        innerType domain |> Option.map (fun inputType ->
            let body parameters _ =
                match parameters with
                | [supplied] -> partialRecipe ctx operation supplied suppliedType inputType resultType enclosing
                | _ -> failwith "An Option operation value requires one leading parameter"
            let parameterName = if operation = "defaultValue" || operation = "orElse" then "__fallback" else "__callback"
            runSaturation ctx (closure [(parameterName, suppliedType)] [] enclosing body residual))
    | NativeType.TFun (domain, resultType) ->
        innerType domain |> Option.bind (fun inputType ->
            match operation with
            | "isSome" | "isNone" | "get" ->
                let body parameters _ = operationRecipe operation parameters inputType None |> Option.get |> fst
                Some (runSaturation ctx (closure [("__option", domain)] [] enclosing body resultType))
            | _ -> None)
    | _ -> None

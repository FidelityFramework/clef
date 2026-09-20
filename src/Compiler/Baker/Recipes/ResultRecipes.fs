// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Native Result operations compose the ordinary typed DU and closure ingredients.
/// See clef-lang-spec/spec/error-handling.md, Native Result Operations.
module Clef.Compiler.Baker.Recipes.ResultRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

let private runRecipe (ctx: Context) parser : Result =
    let initial =
        { EmittedNodes = []; Bindings = Map.empty; ExpansionId = ctx.ExpansionId
          OriginalHOF = ctx.OriginalHOF; SourceRange = ctx.SourceRange
          InspiringNode = ctx.InspiringNode; Platform = ctx.Platform }
    match run initial parser with
    | Matched root, nodes -> mkResultNoShadow nodes root []
    | NoMatch reason, _ -> failwithf "Result saturation failed: %s" reason

let private payloadTypes = function
    | NativeType.TApp (tycon, [ok; error])
        when tycon = Clef.Compiler.NativeTypedTree.Expressions.Types.resultTycon -> Some (ok, error)
    | _ -> None

/// Observe only the established case discriminant. Payload construction remains
/// part of the eager input; no payload extraction or invocation is introduced.
let private predicateBody operation input inputType =
    saturation {
        let! tag = duGetTag input inputType
        let! expected = int8Lit (if operation = "isOk" then 0 else 1)
        let! result = compareEq tag expected Types.int8Type
        return! evaluateBefore [input] result Types.boolType
    }

/// Both cases retain their own extraction type. A changed Result type may need
/// reconstruction; the untouched payload is passed through without conversion.
let private operationBody operation callback input inputType outputType okType errorType =
    saturation {
        let! tag = duGetTag input inputType
        let! okTag = int8Lit 0
        let! isOk = compareEq tag okTag Types.int8Type
        let! okValue = duEliminate input "Ok" 0 okType
        let! errorValue = duEliminate input "Error" 1 errorType
        let outputOk, outputError = payloadTypes outputType |> Option.get
        let! okBranch = saturation {
            match operation with
            | "map" ->
                let! mapped = app1 callback okValue outputOk
                return! duConstruct "Ok" 0 (Some mapped) None outputType
            | "bind" -> return! app1 callback okValue outputType
            | _ -> return! duConstruct "Ok" 0 (Some okValue) None outputType
        }
        let! errorBranch = saturation {
            if operation = "mapError" then
                let! mapped = app1 callback errorValue outputError
                return! duConstruct "Error" 1 (Some mapped) None outputType
            else return! duConstruct "Error" 1 (Some errorValue) None outputType
        }
        return! ifThenElse isOk okBranch errorBranch outputType
    }

/// Elimination retains each payload's logical type, including unit and functions.
/// defaultWith receives the Error payload; it is not a unit thunk.
let private eliminationBody operation supplied input inputType outputType okType errorType =
    saturation {
        let! tag = duGetTag input inputType
        let! okTag = int8Lit 0
        let! isOk = compareEq tag okTag Types.int8Type
        let! okBranch = saturation {
            let! value = duEliminate input "Ok" 0 okType
            if operation = "iter" then return! app1 supplied value Types.unitType
            else return value
        }
        let! errorBranch = saturation {
            match operation with
            | "defaultWith" ->
                let! error = duEliminate input "Error" 1 errorType
                return! app1 supplied error outputType
            | "defaultValue" -> return supplied
            | _ -> return! createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        }
        return! ifThenElse isOk okBranch errorBranch outputType
    }

let private body operation supplied input inputType outputType =
    match payloadTypes inputType, operation with
    | Some (okType, errorType), ("defaultValue" | "defaultWith" | "iter") ->
        Some (eliminationBody operation supplied input inputType outputType okType errorType)
    | Some (okType, errorType), _ when (payloadTypes outputType).IsSome ->
        Some (operationBody operation supplied input inputType outputType okType errorType)
    | _ -> None

/// Formation snapshots the callback value, preserving any storage it references.
let private partialRecipe (ctx: Context) operation callback callbackType inputType outputType enclosing =
    saturation {
        let role = if operation = "defaultValue" then "fallback" else "callback"
        let name = sprintf "__result_%s_%d" role ctx.ExpansionId
        let! snapshot = letBind name callback callbackType
        let capture = { Name = name; Type = callbackType; IsMutable = false; SourceNodeId = Some snapshot }
        let closureBody parameters captures =
            match parameters, captures with
            | [input], [callback] -> saturation {
                let! result = body operation callback input inputType outputType |> Option.get
                // Shared operands must dominate both case arms, including in
                // residual closures. Payload reads stay in the selected case.
                return! evaluateBefore [callback; input] result outputType
              }
            | _ -> failwith "A Result partial requires one input and one callback capture"
        let! value = closure [("__result", inputType)] [capture] enclosing closureBody outputType
        return! evaluateBefore [snapshot] value (NativeType.TFun(inputType, outputType))
    }

let tryDecompose ctx operation arguments returnType enclosing : Result option =
    match arguments with
    | [input, inputType] when (operation = "isOk" || operation = "isError") && (payloadTypes inputType).IsSome ->
        Some (runRecipe ctx (predicateBody operation input inputType))
    | [callback, callbackType] ->
        match returnType with
        | NativeType.TFun (inputType, outputType)
            when (payloadTypes inputType).IsSome ->
            Some (runRecipe ctx (partialRecipe ctx operation callback callbackType inputType outputType enclosing))
        | _ -> None
    | (supplied, _) :: (input, inputType) :: remaining ->
        // A default consumes two operands even if the selected payload is a
        // function. All supplied source operands precede that selection.
        let isDefault = operation = "defaultValue" || operation = "defaultWith"
        if not isDefault && not remaining.IsEmpty then None
        else
            let operationType =
                if isDefault then payloadTypes inputType |> Option.map fst
                else Some returnType
            operationType |> Option.bind (fun outputType ->
                body operation supplied input inputType outputType |> Option.map (fun parser ->
                    runRecipe ctx (saturation {
                        let! value = parser
                        let! result =
                            if remaining.IsEmpty then saturation { return value }
                            else app value (List.map fst remaining) returnType
                        return! evaluateBefore (List.map fst arguments) result returnType
                    })))
    | _ -> None

let tryReifyValue ctx operation functionType enclosing : Result option =
    match functionType with
    | NativeType.TFun (inputType, outputType)
        when (operation = "isOk" || operation = "isError") && (payloadTypes inputType).IsSome && outputType = Types.boolType ->
        let closureBody parameters _ =
            match parameters with
            | [input] -> predicateBody operation input inputType
            | _ -> failwith "A Result predicate value requires one input parameter"
        Some (runRecipe ctx (closure [("__result", inputType)] [] enclosing closureBody Types.boolType))
    | NativeType.TFun (callbackType, (NativeType.TFun (inputType, outputType) as residual))
        when (payloadTypes inputType).IsSome ->
        let closureBody parameters _ =
            match parameters with
            | [callback] -> partialRecipe ctx operation callback callbackType inputType outputType enclosing
            | _ -> failwith "A Result operation value requires one callback parameter"
        Some (runRecipe ctx (closure [("__callback", callbackType)] [] enclosing closureBody residual))
    | _ -> None

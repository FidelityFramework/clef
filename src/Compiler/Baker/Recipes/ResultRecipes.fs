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
        let! choice = ifThenElse isOk okBranch errorBranch outputType
        // Only operand values are eager. Payload extraction and callback
        // invocation remain within their established case.
        return! evaluateBefore [callback; input] choice outputType
    }

let private body operation callback input inputType outputType =
    match payloadTypes inputType, payloadTypes outputType with
    | Some (okType, errorType), Some _ ->
        Some (operationBody operation callback input inputType outputType okType errorType)
    | _ -> None

/// Formation snapshots the callback value, preserving any storage it references.
let private partialRecipe (ctx: Context) operation callback callbackType inputType outputType enclosing =
    saturation {
        let name = sprintf "__result_callback_%d" ctx.ExpansionId
        let! snapshot = letBind name callback callbackType
        let capture = { Name = name; Type = callbackType; IsMutable = false; SourceNodeId = Some snapshot }
        let closureBody parameters captures =
            match parameters, captures with
            | [input], [callback] -> body operation callback input inputType outputType |> Option.get
            | _ -> failwith "A Result partial requires one input and one callback capture"
        let! value = closure [("__result", inputType)] [capture] enclosing closureBody outputType
        return! evaluateBefore [snapshot] value (NativeType.TFun(inputType, outputType))
    }

let tryDecompose ctx operation arguments returnType enclosing : Result option =
    match arguments with
    | [callback, callbackType] ->
        match returnType with
        | NativeType.TFun (inputType, outputType)
            when (payloadTypes inputType).IsSome && (payloadTypes outputType).IsSome ->
            Some (runRecipe ctx (partialRecipe ctx operation callback callbackType inputType outputType enclosing))
        | _ -> None
    | [callback, _; input, inputType] ->
        body operation callback input inputType returnType |> Option.map (runRecipe ctx)
    | _ -> None

let tryReifyValue ctx operation functionType enclosing : Result option =
    match functionType with
    | NativeType.TFun (callbackType, (NativeType.TFun (inputType, outputType) as residual))
        when (payloadTypes inputType).IsSome && (payloadTypes outputType).IsSome ->
        let closureBody parameters _ =
            match parameters with
            | [callback] -> partialRecipe ctx operation callback callbackType inputType outputType enclosing
            | _ -> failwith "A Result operation value requires one callback parameter"
        Some (runRecipe ctx (closure [("__callback", callbackType)] [] enclosing closureBody residual))
    | _ -> None

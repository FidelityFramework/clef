// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Literal and constant handling for F# Native expression checking.
/// This module handles SynConst → NativeLiteral and type inference for literals,
/// and interpolated string expression checking.
module Clef.Compiler.NativeTypedTree.Expressions.Literals

open Clef.Compiler.Syntax
open Clef.Compiler.Text
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Builder
open Clef.Compiler.NativeTypedTree.Expressions.Types

//-------------------------------------------------------------------------
// Constant Type Inference
//-------------------------------------------------------------------------

/// Get the NativeType of a SynConst
let rec typeOfConst (env: TypeEnv) (c: SynConst) (range: range) : NativeType =
    match c with
    | SynConst.Unit -> Types.unitType
    | SynConst.Bool _ -> Types.boolType
    | SynConst.SByte _ | SynConst.Byte _ | SynConst.Int16 _ | SynConst.UInt16 _
    | SynConst.UInt32 _ | SynConst.Int64 _ | SynConst.UInt64 _
    | SynConst.IntPtr _ | SynConst.UIntPtr _ | SynConst.Single _ | SynConst.Decimal _ ->
        addNativeError "CCS8018" range "Numeric literal suffixes cannot select a width or representation in Clef; use an unsuffixed int or float literal." env
        NativeType.TError "Width-bearing numeric literal suffix"
    | SynConst.Int32 _ -> Types.intType
    | SynConst.Double _ -> Types.floatType
    | SynConst.Char _ -> Types.charType
    | SynConst.String _ -> Types.stringType
    | SynConst.Bytes _ -> NativeType.TApp(Types.arrayTyCon, [Types.uint8Type])
    | SynConst.UInt16s _ -> NativeType.TApp(Types.arrayTyCon, [Types.uint16Type])
    | SynConst.Measure(innerConst, _, synMeasure, _) ->
        match resolveSynMeasure env synMeasure with
        | NativeType.TMeasure measure ->
            let ty =
                match typeOfConst env innerConst range with
                | NativeType.TError _ as error -> error
                | kind -> withMeasure kind measure
            match ty with
            | NativeType.TError message -> addError synMeasure.Range message env
            | _ -> ()
            ty
        | ty -> ty
    | SynConst.UserNum(_, suffix) ->
        addNativeError "CCS8018" range $"Numeric suffix '{suffix}' is not supported in Clef; use an unsuffixed int or float literal." env
        NativeType.TError "Unsupported numeric suffix"
    | SynConst.SourceIdentifier _ -> Types.stringType

//-------------------------------------------------------------------------
// Constant to NativeLiteral Conversion
//-------------------------------------------------------------------------

/// Convert SynConst to SemanticGraph NativeLiteral
let rec constToLiteral (c: SynConst) : NativeLiteral =
    match c with
    | SynConst.Unit -> NativeLiteral.Unit
    | SynConst.Bool b -> NativeLiteral.Bool b
    | SynConst.SByte v -> NativeLiteral.Int(int64 v, NTUKind.NTUint (NTUWidth.Fixed 8))
    | SynConst.Byte v -> NativeLiteral.Int(int64 v, NTUKind.NTUuint (NTUWidth.Fixed 8))
    | SynConst.Int16 v -> NativeLiteral.Int(int64 v, NTUKind.NTUint (NTUWidth.Fixed 16))
    | SynConst.UInt16 v -> NativeLiteral.Int(int64 v, NTUKind.NTUuint (NTUWidth.Fixed 16))
    | SynConst.Int32 v -> NativeLiteral.Int(int64 v, NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register))
    | SynConst.UInt32 v -> NativeLiteral.Int(int64 v, NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register))
    | SynConst.Int64 v -> NativeLiteral.Int(v, NTUKind.NTUint (NTUWidth.Fixed 64))
    | SynConst.UInt64 v -> NativeLiteral.UInt(v, NTUKind.NTUuint (NTUWidth.Fixed 64))
    | SynConst.IntPtr v -> NativeLiteral.Int(int64 v, NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer))
    | SynConst.UIntPtr v -> NativeLiteral.UInt(uint64 v, NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer))
    | SynConst.Single v -> NativeLiteral.Float(float v, NTUKind.NTUfloat (NTUWidth.Fixed 32))
    | SynConst.Double v -> NativeLiteral.Float(v, NTUKind.NTUfloat (NTUWidth.Fixed 64))
    | SynConst.Char v -> NativeLiteral.Char v
    | SynConst.Decimal v -> NativeLiteral.Decimal v
    | SynConst.String(s, _, _) -> NativeLiteral.String s
    | SynConst.Measure(innerConst, _, _, _) -> constToLiteral innerConst
    | SynConst.UserNum(value, suffix) ->
        match suffix with
        | "I" -> NativeLiteral.BigInt value
        | _ -> NativeLiteral.String value  // Fallback
    | SynConst.SourceIdentifier(_, value, _) -> NativeLiteral.String value
    | SynConst.Bytes(bytes, _, _) -> NativeLiteral.ByteArray bytes
    | SynConst.UInt16s values -> NativeLiteral.UInt16Array values


//-------------------------------------------------------------------------
// Interpolated Strings
//-------------------------------------------------------------------------

/// Callback type for expression checking
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// Check InterpolatedString: $"Hello {name}!"
/// Converts to String.concat2 applications
let checkInterpolatedString
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (contents: SynInterpolatedStringPart list)
    (synRange: range)
    (range: SourceRange)
    : SemanticNode =
    let partExprs =
        contents |> List.choose (fun part ->
            match part with
            | SynInterpolatedStringPart.String(value, partRange) ->
                if System.String.IsNullOrEmpty(value) then None
                else Some (SynExpr.Const(SynConst.String(value, SynStringKind.Regular, partRange), partRange))
            | SynInterpolatedStringPart.FillExpr(fillExpr, _qualifiers) ->
                Some fillExpr)

    match partExprs with
    | [] ->
        builder.Create(
            SemanticKind.Literal(NativeLiteral.String ""),
            Types.stringType,
            range)
    | [single] ->
        checkExpr env builder single
    | first :: rest ->
        let concat2Ident =
            SynExpr.LongIdent(
                false,
                SynLongIdent([Ident("String", synRange); Ident("concat2", synRange)], [synRange], [None; None]),
                None,
                synRange)
        let resultExpr =
            rest |> List.fold (fun accExpr nextExpr ->
                let app1 = SynExpr.App(ExprAtomicFlag.NonAtomic, false, concat2Ident, accExpr, synRange)
                SynExpr.App(ExprAtomicFlag.NonAtomic, false, app1, nextExpr, synRange)
            ) first
        checkExpr env builder resultExpr

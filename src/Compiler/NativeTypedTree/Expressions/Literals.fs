// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Literal and constant handling for Clef expression checking.
/// This module handles SynConst → NativeLiteral and type inference for literals,
/// and interpolated string expression checking.
module Clef.Compiler.NativeTypedTree.Expressions.Literals

open Clef.Compiler.Syntax
open Clef.Compiler.Text
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.NativeTypedTree.Expressions.Types

//-------------------------------------------------------------------------
// Constant Checking
//-------------------------------------------------------------------------

/// The type and the NativeLiteral of a SynConst, decided together in one place so the two
/// projections cannot disagree, or the message of the one diagnostic a constant can raise.
///
/// The parser folds every literal suffix it does not itself carry into `SynConst.UserNum`;
/// the bigint suffix `I` is among them. None of these names a representation Clef supports,
/// so the constant is refused with CCS8018 (design note (f); plan L-3). No representation is
/// fabricated in its place: the caller records the diagnostic through
/// `addUnsupportedLiteralSuffix` and recovers the way its own surrounding code recovers.
let rec checkConst (c: SynConst) : Result<NativeType * NativeLiteral, string> =
    match c with
    | SynConst.Unit -> Ok (Types.unitType, NativeLiteral.Unit)
    | SynConst.Bool b -> Ok (Types.boolType, NativeLiteral.Bool b)
    | SynConst.SByte v -> Ok (Types.int8Type, NativeLiteral.Int(int64 v, NTUKind.NTUint (NTUWidth.Fixed 8)))
    | SynConst.Byte v -> Ok (Types.uint8Type, NativeLiteral.Int(int64 v, NTUKind.NTUuint (NTUWidth.Fixed 8)))
    | SynConst.Int16 v -> Ok (Types.int16Type, NativeLiteral.Int(int64 v, NTUKind.NTUint (NTUWidth.Fixed 16)))
    | SynConst.UInt16 v -> Ok (Types.uint16Type, NativeLiteral.Int(int64 v, NTUKind.NTUuint (NTUWidth.Fixed 16)))
    | SynConst.Int32 v -> Ok (Types.intType, NativeLiteral.Int(int64 v, NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)))
    | SynConst.UInt32 v -> Ok (Types.uintType, NativeLiteral.Int(int64 v, NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register)))
    | SynConst.Int64 v -> Ok (Types.int64Type, NativeLiteral.Int(v, NTUKind.NTUint (NTUWidth.Fixed 64)))
    | SynConst.UInt64 v -> Ok (Types.uint64Type, NativeLiteral.UInt(v, NTUKind.NTUuint (NTUWidth.Fixed 64)))
    | SynConst.IntPtr v -> Ok (Types.nintType, NativeLiteral.Int(int64 v, NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer)))
    | SynConst.UIntPtr v -> Ok (Types.unintType, NativeLiteral.UInt(uint64 v, NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer)))
    | SynConst.Single v -> Ok (Types.float32Type, NativeLiteral.Float(float v, NTUKind.NTUfloat (NTUWidth.Fixed 32)))
    | SynConst.Double v -> Ok (Types.floatType, NativeLiteral.Float(v, NTUKind.NTUfloat (NTUWidth.Fixed 64)))
    | SynConst.Char v -> Ok (Types.charType, NativeLiteral.Char v)
    | SynConst.Decimal v -> Ok (Types.decimalType, NativeLiteral.Decimal v)
    | SynConst.String(s, _, _) -> Ok (Types.stringType, NativeLiteral.String s)
    | SynConst.Bytes(bytes, _, _) -> Ok (NativeType.TApp(Types.arrayTyCon, [Types.uint8Type]), NativeLiteral.ByteArray bytes)
    | SynConst.UInt16s values -> Ok (NativeType.TApp(Types.arrayTyCon, [Types.uint16Type]), NativeLiteral.UInt16Array values)
    | SynConst.Measure(innerConst, _, _, _) ->
        // The measure annotation is not yet carried on the literal (plan L-2, step 1).
        checkConst innerConst
    | SynConst.UserNum(_, suffix) ->
        Error $"Literal suffix '{suffix}' is not a representation Clef supports"
    | SynConst.SourceIdentifier(_, value, _) -> Ok (Types.stringType, NativeLiteral.String value)

/// Record CCS8018 for a constant `checkConst` refused, at the constant's own range.
let addUnsupportedLiteralSuffix (r: range) (message: string) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.CCS8018_UnsupportedLiteralSuffix r message env


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

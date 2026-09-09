// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Literal and constant handling for Clef expression checking.
/// This module handles SynConst → NativeLiteral and type inference for literals,
/// and interpolated string expression checking.
module Clef.Compiler.NativeTypedTree.Expressions.Literals

open Clef.Compiler.Syntax
open Clef.Compiler.Text
open Clef.Compiler.NativeTypedTree.MeasureEnvironment
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.NativeTypedTree.Expressions.Types

//-------------------------------------------------------------------------
// Constant Checking
//-------------------------------------------------------------------------

/// Why a constant is refused: a literal suffix that selects a width or representation
/// (CCS8018, plan L-3), or a measure annotation the one translator refuses (CCS804x, design a.4).
[<RequireQualifiedAccess>]
type ConstFailure =
    | UnsupportedSuffix of message: string
    | UnsupportedInteger of message: string
    | UnsupportedReal of message: string
    | Measure of MeasureFailure

/// The type and the NativeLiteral of a SynConst, decided together in one place so the two
/// projections cannot disagree, or the failure the constant carries.
///
/// The parser folds every literal suffix it does not itself carry into `SynConst.UserNum`;
/// the bigint suffix `I` is among them. Source suffixes cannot select a numeric representation,
/// so the constant is refused with CCS8018 (design note (f); plan L-3). A measured constant,
/// `1.0<m>`, is its inner constant's carrier at the annotation's dimension, read through
/// `dimensionOfSyntax` (design a.4): a bare literal is `one`, `_` mints a variable, `'u` is
/// CCS8044. Nothing is fabricated in place of a refused constant: the caller records the
/// diagnostic through `addConstFailure` and recovers the way its own surrounding code recovers.
let rec checkConst (env: TypeEnv) (c: SynConst) : Result<NativeType * NativeLiteral, ConstFailure> =
    match c with
    | SynConst.Unit -> Ok (Types.unitType, NativeLiteral.Unit)
    | SynConst.Bool b -> Ok (Types.boolType, NativeLiteral.Bool b)
    | SynConst.SByte _ | SynConst.Byte _ | SynConst.Int16 _ | SynConst.UInt16 _
    | SynConst.UInt32 _ | SynConst.Int64 _ | SynConst.UInt64 _
    | SynConst.IntPtr _ | SynConst.UIntPtr _ | SynConst.Single _ | SynConst.Decimal _ ->
        Error (ConstFailure.UnsupportedSuffix "Numeric literal suffixes cannot select a width or representation in Clef; use an unsuffixed int or float literal.")
    | SynConst.Int32 v -> Ok (Types.intType, NativeLiteral.Int(int64 v, NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)))
    | SynConst.Double (v, sourceText) ->
        let literal = Types.floatType, NativeLiteral.Float(v, NTUKind.NTUfloat (NTUWidth.Fixed 64))
        match sourceText with
        | None -> Ok literal
        | Some source ->
            ExactRational.tryParseDecimal source
            |> Result.map (fun _ -> literal)
            |> Result.mapError ConstFailure.UnsupportedReal
    | SynConst.Char v -> Ok (Types.charType, NativeLiteral.Char v)
    | SynConst.String(s, _, _) -> Ok (Types.stringType, NativeLiteral.String s)
    | SynConst.Bytes(bytes, _, _) -> Ok (NativeType.TApp(Types.arrayTyCon, [Types.uint8Type]), NativeLiteral.ByteArray bytes)
    | SynConst.UInt16s values -> Ok (NativeType.TApp(Types.arrayTyCon, [Types.uint16Type]), NativeLiteral.UInt16Array values)
    | SynConst.Measure(innerConst, _, synMeasure, _) ->
        checkConst env innerConst
        |> Result.bind (fun (innerTy, literal) ->
            match innerTy with
            | NativeType.TNum(carrier, _) ->
                match translateDimension env (MeasureSyntax.Measure synMeasure) with
                | Ok dim -> Ok (NativeType.TNum(carrier, dim), literal)
                | Error failure -> Error (ConstFailure.Measure failure)
            | other ->
                // A measure on a constant that carries no dimension (design (f), CCS8046).
                Error (ConstFailure.Measure (MeasureFailure.NoDimension(formatType other, synMeasure.Range))))
    | SynConst.UserNum(text, "") ->
        // Empty suffix is the parser's lossless unsuffixed-integer path. This
        // hosted graph currently stores integer literal values in an Int64;
        // reject a larger value explicitly instead of truncating or wrapping it.
        let negative = text.StartsWith("-", System.StringComparison.Ordinal)
        let magnitude = if negative then text.Substring(1) else text
        let radix, digits =
            if magnitude.StartsWith("0x", System.StringComparison.OrdinalIgnoreCase) then 16, magnitude.Substring(2)
            elif magnitude.StartsWith("0o", System.StringComparison.OrdinalIgnoreCase) then 8, magnitude.Substring(2)
            elif magnitude.StartsWith("0b", System.StringComparison.OrdinalIgnoreCase) then 2, magnitude.Substring(2)
            else 10, magnitude
        let magnitude =
            digits |> Seq.fold (fun (value: System.Numerics.BigInteger) digit ->
                let number = if digit >= '0' && digit <= '9' then int digit - int '0' else int (System.Char.ToLowerInvariant digit) - int 'a' + 10
                value * bigint radix + bigint number) System.Numerics.BigInteger.Zero
        let value = if negative then -magnitude else magnitude
        if value < bigint System.Int64.MinValue || value > bigint System.Int64.MaxValue then
            Error (ConstFailure.UnsupportedInteger "This integer literal exceeds the current hosted graph's exact literal storage; larger integer literals require compiler support.")
        else Ok (Types.intType, NativeLiteral.Int(int64 value, NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)))
    | SynConst.UserNum(_, suffix) ->
        Error (ConstFailure.UnsupportedSuffix $"Numeric suffix '{suffix}' is not supported in Clef; use an unsuffixed int or float literal.")
    | SynConst.SourceIdentifier(_, value, _) -> Ok (Types.stringType, NativeLiteral.String value)

/// Retained for existing expression/pattern call sites. Suffixes are rejected by
/// checkConst and diagnosed through addConstFailure, rather than admitted with an alias warning.
let warnSuffix (_r: range) (_c: SynConst) (_env: TypeEnv) : unit = ()

/// Read the checked source value, including a measured literal's inner decimal spelling.
/// Missing spelling stays missing: the hosted double cannot reconstruct source evidence.
let rec realLiteralMetadata (constant: SynConst) : MetadataValue option =
    match constant with
    | SynConst.Measure(inner, _, _, _) -> realLiteralMetadata inner
    | SynConst.Double (_, Some source) ->
        match ExactRational.tryParseDecimal source with
        | Ok value -> Some (MetadataValue.RealLiteral(source, value))
        | Error _ -> None // checkConst reports the unsupported source at its own range.
    | _ -> None

/// Record the diagnostic a refused constant carries: CCS8018 at the constant's own range for a
/// suffix; the measure failure's own code and range for a measure annotation.
let addConstFailure (r: range) (failure: ConstFailure) (env: TypeEnv) : unit =
    match failure with
    | ConstFailure.UnsupportedSuffix message ->
        addNativeError DiagnosticCodes.CCS8018_UnsupportedLiteralSuffix r message env
    | ConstFailure.UnsupportedInteger message | ConstFailure.UnsupportedReal message ->
        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct r message env
    | ConstFailure.Measure measureFailure ->
        addMeasureFailure measureFailure env

/// The message of a refused constant, for the error node that stands in its place.
let constFailureMessage (failure: ConstFailure) : string =
    match failure with
    | ConstFailure.UnsupportedSuffix message | ConstFailure.UnsupportedInteger message
    | ConstFailure.UnsupportedReal message -> message
    | ConstFailure.Measure measureFailure ->
        let _, message, _ = describeMeasureFailure measureFailure
        message


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

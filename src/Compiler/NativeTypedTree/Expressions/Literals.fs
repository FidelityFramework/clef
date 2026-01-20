// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Literal and constant handling for F# Native expression checking.
/// This module handles SynConst → NativeLiteral and type inference for literals.
module FSharp.Native.Compiler.NativeTypedTree.Expressions.Literals

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types

//-------------------------------------------------------------------------
// Constant Type Inference
//-------------------------------------------------------------------------

/// Get the NativeType of a SynConst
let rec typeOfConst (globals: NativeGlobals) (c: SynConst) : NativeType =
    match c with
    | SynConst.Unit -> globals.UnitType
    | SynConst.Bool _ -> globals.BoolType
    | SynConst.SByte _ -> Types.int8Type
    | SynConst.Byte _ -> Types.uint8Type
    | SynConst.Int16 _ -> Types.int16Type
    | SynConst.UInt16 _ -> Types.uint16Type
    | SynConst.Int32 _ -> globals.IntType
    | SynConst.UInt32 _ -> Types.uintType
    | SynConst.Int64 _ -> globals.Int64Type
    | SynConst.UInt64 _ -> Types.uint64Type
    | SynConst.IntPtr _ -> Types.nintType
    | SynConst.UIntPtr _ -> Types.unintType
    | SynConst.Single _ -> Types.float32Type
    | SynConst.Double _ -> globals.FloatType
    | SynConst.Char _ -> globals.CharType
    | SynConst.Decimal _ -> Types.decimalType
    | SynConst.String _ -> globals.StringType
    | SynConst.Bytes _ -> mkArrayType Types.uint8Type
    | SynConst.UInt16s _ -> mkArrayType Types.uint16Type
    | SynConst.Measure(innerConst, _, synMeasure, _) ->
        // For now, just use the base type; measure annotation is tracked separately
        let baseType = typeOfConst globals innerConst
        let _ = synMeasure  // Suppress warning
        baseType
    | SynConst.UserNum(_, suffix) ->
        // UserNum with suffix - "I" is bigint, others are user-defined
        match suffix with
        | "I" -> globals.IntType  // Treat bigint as int for now
        | _ -> globals.IntType  // Fallback
    | SynConst.SourceIdentifier _ -> globals.StringType

//-------------------------------------------------------------------------
// Constant to NativeLiteral Conversion
//-------------------------------------------------------------------------

/// Convert SynConst to SemanticGraph NativeLiteral
let rec constToLiteral (c: SynConst) : NativeLiteral =
    match c with
    | SynConst.Unit -> NativeLiteral.Unit
    | SynConst.Bool b -> NativeLiteral.Bool b
    | SynConst.SByte v -> NativeLiteral.Int(int64 v, NTUKind.NTUint8)
    | SynConst.Byte v -> NativeLiteral.Int(int64 v, NTUKind.NTUuint8)
    | SynConst.Int16 v -> NativeLiteral.Int(int64 v, NTUKind.NTUint16)
    | SynConst.UInt16 v -> NativeLiteral.Int(int64 v, NTUKind.NTUuint16)
    | SynConst.Int32 v -> NativeLiteral.Int(int64 v, NTUKind.NTUint)
    | SynConst.UInt32 v -> NativeLiteral.Int(int64 v, NTUKind.NTUuint)
    | SynConst.Int64 v -> NativeLiteral.Int(v, NTUKind.NTUint64)
    | SynConst.UInt64 v -> NativeLiteral.UInt(v, NTUKind.NTUuint64)
    | SynConst.IntPtr v -> NativeLiteral.Int(int64 v, NTUKind.NTUnint)
    | SynConst.UIntPtr v -> NativeLiteral.UInt(uint64 v, NTUKind.NTUunint)
    | SynConst.Single v -> NativeLiteral.Float(float v, NTUKind.NTUfloat32)
    | SynConst.Double v -> NativeLiteral.Float(v, NTUKind.NTUfloat64)
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

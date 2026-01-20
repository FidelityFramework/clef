// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Literal and constant handling for F# Native expression checking.
/// This module handles SynConst → LiteralValue and type inference for literals.
module FSharp.Native.Compiler.Checking.Native.Expressions.Literals

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph

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
// Constant to LiteralValue Conversion
//-------------------------------------------------------------------------

/// Convert SynConst to SemanticGraph LiteralValue
let rec constToLiteral (c: SynConst) : LiteralValue =
    match c with
    | SynConst.Unit -> LiteralValue.Unit
    | SynConst.Bool b -> LiteralValue.Bool b
    | SynConst.SByte v -> LiteralValue.Int8 v
    | SynConst.Byte v -> LiteralValue.UInt8 v
    | SynConst.Int16 v -> LiteralValue.Int16 v
    | SynConst.UInt16 v -> LiteralValue.UInt16 v
    | SynConst.Int32 v -> LiteralValue.Int32 v
    | SynConst.UInt32 v -> LiteralValue.UInt32 v
    | SynConst.Int64 v -> LiteralValue.Int64 v
    | SynConst.UInt64 v -> LiteralValue.UInt64 v
    | SynConst.IntPtr v -> LiteralValue.NativeInt(nativeint v)
    | SynConst.UIntPtr v -> LiteralValue.UNativeInt(unativeint v)
    | SynConst.Single v -> LiteralValue.Float32 v
    | SynConst.Double v -> LiteralValue.Float64 v
    | SynConst.Char v -> LiteralValue.Char v
    | SynConst.Decimal v -> LiteralValue.Decimal v
    | SynConst.String(s, _, _) -> LiteralValue.String s
    | SynConst.Measure(innerConst, _, _, _) -> constToLiteral innerConst
    | SynConst.UserNum(value, suffix) ->
        match suffix with
        | "I" -> LiteralValue.BigInt value
        | _ -> LiteralValue.String value  // Fallback
    | SynConst.SourceIdentifier(_, value, _) -> LiteralValue.String value
    | SynConst.Bytes(bytes, _, _) -> LiteralValue.ByteArray bytes
    | SynConst.UInt16s values -> LiteralValue.UInt16Array values

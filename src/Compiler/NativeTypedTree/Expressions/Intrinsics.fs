// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Intrinsic resolution for F# Native.
/// This module provides proper discriminated union dispatch for intrinsics,
/// replacing the string prefix matching anti-pattern.
///
/// ARCHITECTURAL PRINCIPLE: No `name.StartsWith("X.")` dispatch.
/// Intrinsic modules are matched via proper pattern matching on IntrinsicModule.
module Clef.Compiler.NativeTypedTree.Expressions.Intrinsics

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Builder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

//-------------------------------------------------------------------------
// Result Type for Intrinsic Resolution
//-------------------------------------------------------------------------

/// Result of attempting to resolve an intrinsic
type IntrinsicResolution =
    | Resolved of IntrinsicInfo * NativeType
    | NotAnIntrinsic
    | UnknownOperation of string  // Error message for unknown op in known module

//-------------------------------------------------------------------------
// Helper to create IntrinsicInfo
//-------------------------------------------------------------------------

let private mkIntrinsic (modl: IntrinsicModule) (op: string) (cat: IntrinsicCategory) (fullName: string) : IntrinsicInfo =
    { Module = modl; Operation = op; Category = cat; FullName = fullName }

//-------------------------------------------------------------------------
// Qualified Intrinsic Parsing
//-------------------------------------------------------------------------

/// Parse "Prefix.operation" into (IntrinsicModule, operation) tuple.
/// Returns None if not a recognized intrinsic prefix.
let tryParseModuleQualified (name: string) : (IntrinsicModule * string) option =
    match name.IndexOf('.') with
    | -1 -> None
    | idx ->
        let modulePart = name.Substring(0, idx)
        let opPart = name.Substring(idx + 1)
        match modulePart with
        | "NativePtr" -> Some (IntrinsicModule.NativePtr, opPart)
        | "MemRef" -> Some (IntrinsicModule.MemRef, opPart)
        | "Sys" -> Some (IntrinsicModule.Sys, opPart)
        | "String" -> Some (IntrinsicModule.String, opPart)
        | "Array" -> Some (IntrinsicModule.Array, opPart)
        // Parse.int/float and Format.int/float are platform library functions,
        // resolved as VarRef by FCS, not as CCS intrinsics.
        | "Crypto" -> Some (IntrinsicModule.Crypto, opPart)
        | "Bits" -> Some (IntrinsicModule.Bits, opPart)
        | "FnPtr" -> Some (IntrinsicModule.FnPtr, opPart)
        | "Lazy" -> Some (IntrinsicModule.Lazy, opPart)
        | "Seq" -> Some (IntrinsicModule.Seq, opPart)
        | "NativeStr" -> Some (IntrinsicModule.NativeStr, opPart)
        | "NativeDefault" -> Some (IntrinsicModule.NativeDefault, opPart)
        | "Math" -> Some (IntrinsicModule.Math, opPart)
        | "Arena" -> Some (IntrinsicModule.Arena, opPart)
        | "DateTime" -> Some (IntrinsicModule.DateTime, opPart)
        | "TimeSpan" -> Some (IntrinsicModule.TimeSpan, opPart)
        | "Platform" -> Some (IntrinsicModule.Platform, opPart)
        // PRD-13a: Core Collections
        | "Map" -> Some (IntrinsicModule.Map, opPart)
        | "Set" -> Some (IntrinsicModule.Set, opPart)
        | "List" -> Some (IntrinsicModule.List, opPart)
        | "Option" -> Some (IntrinsicModule.Option, opPart)
        | "Result" -> Some (IntrinsicModule.Result, opPart)
        | _ -> None

//-------------------------------------------------------------------------
// Intrinsic Resolvers by Category
//-------------------------------------------------------------------------

/// Resolve NativePtr.* operations
let private resolveNativePtrOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
    let tyParam = NativeType.TVar tyParamSpec
    let fullName = "NativePtr." + op
    match op with
    | "toNativeInt" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, Types.nintType))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "ofNativeInt" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.nintType, NativeType.TNativePtr tyParam))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "toVoidPtr" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TApp(voidptrTyCon, [])))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "ofVoidPtr" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TApp(voidptrTyCon, []), NativeType.TNativePtr tyParam))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "get" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(Types.intType, tyParam)))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "set" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(Types.intType, NativeType.TFun(tyParam, Types.unitType))))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "stackalloc" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.intType, NativeType.TNativePtr tyParam))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "read" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "write" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(tyParam, Types.unitType)))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "add" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(Types.intType, NativeType.TNativePtr tyParam)))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "copy" ->
        let ty = NativeType.TForall([tyParamSpec],
            NativeType.TFun(NativeType.TNativePtr tyParam,
                NativeType.TFun(NativeType.TNativePtr tyParam,
                    NativeType.TFun(Types.intType, Types.unitType))))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "fill" ->
        let ty = NativeType.TForall([tyParamSpec],
            NativeType.TFun(NativeType.TNativePtr tyParam,
                NativeType.TFun(tyParam,
                    NativeType.TFun(Types.intType, Types.unitType))))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown NativePtr intrinsic: NativePtr.{unknown}"

/// Resolve MemRef.* operations (MLIR memref semantics)
/// These are TARGET OPERATIONS created by Baker during NativePtr transformation.
/// Alex witnesses these directly as memref dialect operations.
let private resolveMemRefOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
    let tyParam = NativeType.TVar tyParamSpec
    let fullName = "MemRef." + op
    match op with
    | "alloca" ->
        // nativeint -> memref<?x'T> (dynamic alloca, size at runtime)
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.nintType, NativeType.TNativePtr tyParam))
        Resolved (mkIntrinsic IntrinsicModule.MemRef op IntrinsicCategory.Memory fullName, ty)
    | "load" ->
        // memref<?x'T> -> nativeint -> 'T (indexed load)
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(Types.nintType, tyParam)))
        Resolved (mkIntrinsic IntrinsicModule.MemRef op IntrinsicCategory.Memory fullName, ty)
    | "store" ->
        // 'T -> memref<?x'T> -> nativeint -> unit (indexed store)
        let ty = NativeType.TForall([tyParamSpec],
            NativeType.TFun(tyParam,
                NativeType.TFun(NativeType.TNativePtr tyParam,
                    NativeType.TFun(Types.nintType, Types.unitType))))
        Resolved (mkIntrinsic IntrinsicModule.MemRef op IntrinsicCategory.Memory fullName, ty)
    | "copy" ->
        // dest:memref -> src:memref -> count:nativeint -> unit
        let ty = NativeType.TForall([tyParamSpec],
            NativeType.TFun(NativeType.TNativePtr tyParam,
                NativeType.TFun(NativeType.TNativePtr tyParam,
                    NativeType.TFun(Types.nintType, Types.unitType))))
        Resolved (mkIntrinsic IntrinsicModule.MemRef op IntrinsicCategory.Memory fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown MemRef intrinsic: MemRef.{unknown}"

/// Resolve Sys.* operations (system calls)
let private resolveSysOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Sys." + op
    match op with
    | "write" ->
        // fd:int -> buffer:string -> int (bytes written)
        let ty = NativeType.TFun(Types.intType,
            NativeType.TFun(Types.stringType, Types.intType))
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "read" ->
        // fd:int -> buffer:string -> int (bytes read)
        let ty = NativeType.TFun(Types.intType,
            NativeType.TFun(Types.stringType, Types.intType))
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "readline" ->
        // fd:int -> string (reads until newline/EOF)
        let ty = NativeType.TFun(Types.intType, Types.stringType)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "exit" ->
        // code:int -> 'a (never returns, polymorphic return type)
        let tyParamSpec = freshTypeParam "'a" TypeParamKind.Type range
        let tyParam = NativeType.TVar tyParamSpec
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.intType, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "clock_gettime" ->
        // unit -> int64
        let ty = NativeType.TFun(Types.unitType, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "clock_monotonic" ->
        // unit -> int64
        let ty = NativeType.TFun(Types.unitType, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "tick_frequency" ->
        // unit -> int64
        let ty = NativeType.TFun(Types.unitType, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "nanosleep" ->
        // int64 -> unit (nanoseconds require 64-bit precision)
        let ty = NativeType.TFun(Types.int64Type, Types.unitType)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)

    // Freestanding entry point intrinsics
    // These are used by IntrinsicElaboration to build the _start wrapper
    | "stackArgc" ->
        // unit -> int (load argc from stack at program entry)
        let ty = NativeType.TFun(Types.unitType, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "stackArgv" ->
        // unit -> nativeptr<nativeptr<byte>> (load argv from stack at program entry)
        let argvType = NativeType.TNativePtr (NativeType.TNativePtr Types.uint8Type)
        let ty = NativeType.TFun(Types.unitType, argvType)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "emptyStringArray" ->
        // unit -> string array (returns empty string array for _start wrapper)
        // Used by IntrinsicElaboration to provide an empty argv for F# main functions
        let stringArrayType = NativeType.TApp(Types.arrayTyCon, [Types.stringType])
        let ty = NativeType.TFun(Types.unitType, stringArrayType)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)

    | unknown ->
        UnknownOperation $"Unknown Sys intrinsic: Sys.{unknown}"

/// Resolve String.* operations
let private resolveStringOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "String." + op
    let stringType = Types.stringType
    match op with
    | "concat2" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(stringType, stringType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "length" ->
        let ty = NativeType.TFun(stringType, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "isEmpty" ->
        let ty = NativeType.TFun(stringType, Types.boolType)
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "contains" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(Types.charType, Types.boolType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "startsWith" | "endsWith" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(stringType, Types.boolType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "substring" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(Types.intType, NativeType.TFun(Types.intType, stringType)))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "trim" | "trimStart" | "trimEnd" | "toUpper" | "toLower" ->
        let ty = NativeType.TFun(stringType, stringType)
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "charAt" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(Types.intType, Types.charType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "indexOf" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(Types.charType, Types.intType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "replace" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(stringType, NativeType.TFun(stringType, stringType)))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "concat" ->
        // string -> string list -> string (separator, strings)
        let stringListType = NativeType.TList stringType
        let ty = NativeType.TFun(stringType, NativeType.TFun(stringListType, stringType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "toBytes" ->
        // string -> byte[] (UTF-8 encoding)
        let ty = NativeType.TFun(stringType, NativeType.TApp(Types.arrayTyCon, [Types.uint8Type]))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "fromBytes" ->
        // byte[] -> string (UTF-8 decoding)
        let ty = NativeType.TFun(NativeType.TApp(Types.arrayTyCon, [Types.uint8Type]), stringType)
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown String intrinsic: String.{unknown}. Available: concat2, concat, length, isEmpty, contains, startsWith, endsWith, substring, trim, trimStart, trimEnd, toUpper, toLower, charAt, indexOf, replace, toBytes, fromBytes"

/// Resolve Array.* operations
let private resolveArrayOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
    let tyParam = NativeType.TVar tyParamSpec
    let arrayType = NativeType.TApp(Types.arrayTyCon, [tyParam])
    let fullName = "Array." + op
    match op with
    | "zeroCreate" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.intType, arrayType))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "create" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.intType, NativeType.TFun(tyParam, arrayType)))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "init" ->
        let initFunc = NativeType.TFun(Types.intType, tyParam)
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.intType, NativeType.TFun(initFunc, arrayType)))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "copy" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, arrayType))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "length" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, Types.intType))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "get" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, NativeType.TFun(Types.intType, tyParam)))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "set" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, NativeType.TFun(Types.intType, NativeType.TFun(tyParam, Types.unitType))))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "tryItem" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.intType, NativeType.TFun(arrayType, NativeType.TApp(Types.voptionTyCon, [tyParam]))))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "isEmpty" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, Types.boolType))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "blit" ->
        // 'T[] -> int -> 'T[] -> int -> int -> unit
        // (source, sourceIndex, target, targetIndex, count)
        let ty = NativeType.TForall([tyParamSpec],
            NativeType.TFun(arrayType,
                NativeType.TFun(Types.intType,
                    NativeType.TFun(arrayType,
                        NativeType.TFun(Types.intType,
                            NativeType.TFun(Types.intType, Types.unitType))))))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "sub" ->
        // 'T[] -> int -> int -> 'T[] (source, startIndex, count)
        let ty = NativeType.TForall([tyParamSpec],
            NativeType.TFun(arrayType,
                NativeType.TFun(Types.intType,
                    NativeType.TFun(Types.intType, arrayType))))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "collect" ->
        // ('T -> 'U[]) -> 'T[] -> 'U[]
        let tyParamSpecU = freshTypeParam "'U" TypeParamKind.Type range
        let tyParamU = NativeType.TVar tyParamSpecU
        let arrayTypeU = NativeType.TApp(Types.arrayTyCon, [tyParamU])
        let mapperFn = NativeType.TFun(tyParam, arrayTypeU)
        let ty = NativeType.TForall([tyParamSpec; tyParamSpecU],
            NativeType.TFun(mapperFn, NativeType.TFun(arrayType, arrayTypeU)))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Array intrinsic: Array.{unknown}. Available: zeroCreate, create, init, copy, length, get, set, sub, tryItem, isEmpty, blit, collect"

/// Resolve Parse.* operations (string → numeric)
let private resolveParseOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Parse." + op
    match op with
    | "int" ->
        let ty = NativeType.TFun(Types.stringType, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.Parse op IntrinsicCategory.Conversion fullName, ty)
    | "int64" ->
        let ty = NativeType.TFun(Types.stringType, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.Parse op IntrinsicCategory.Conversion fullName, ty)
    | "float" ->
        let ty = NativeType.TFun(Types.stringType, Types.floatType)
        Resolved (mkIntrinsic IntrinsicModule.Parse op IntrinsicCategory.Conversion fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Parse intrinsic: Parse.{unknown}. Available: int, int64, float"

/// Resolve Format.* operations (numeric → string)
let private resolveFormatOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Format." + op
    match op with
    | "int" ->
        let ty = NativeType.TFun(Types.intType, Types.stringType)
        Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
    | "int64" ->
        let ty = NativeType.TFun(Types.int64Type, Types.stringType)
        Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
    | "float" | "float64" | "double" ->
        let ty = NativeType.TFun(Types.floatType, Types.stringType)
        Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
    | "bool" ->
        let ty = NativeType.TFun(Types.boolType, Types.stringType)
        Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Format intrinsic: Format.{unknown}. Available: int, int64, float, bool"

/// Resolve NativeStr.* operations
let private resolveNativeStrOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "NativeStr." + op
    match op with
    | "fromPointer" ->
        // ptr:nativeptr<byte> -> len:nativeint -> string
        // In MLIR: creates a new memref<?xi8> with specified length (NOT fat pointer struct)
        // len is nativeint (maps to index) since it represents a buffer size/offset
        let ty = NativeType.TFun(NativeType.TNativePtr Types.uint8Type, NativeType.TFun(Types.nintType, Types.stringType))
        Resolved (mkIntrinsic IntrinsicModule.NativeStr op IntrinsicCategory.StringOp fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown NativeStr intrinsic: NativeStr.{unknown}"

/// Resolve NativeDefault.* operations
let private resolveNativeDefaultOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "NativeDefault." + op
    match op with
    | "zeroed" ->
        // unit -> 'T
        let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
        let tyParam = NativeType.TVar tyParamSpec
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.unitType, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.NativeDefault op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown NativeDefault intrinsic: NativeDefault.{unknown}"

/// Resolve Crypto.* operations
let private resolveCryptoOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Crypto." + op
    let byteArrayType = NativeType.TApp(Types.arrayTyCon, [Types.uint8Type])
    match op with
    | "sha1" ->
        let ty = NativeType.TFun(byteArrayType, byteArrayType)
        Resolved (mkIntrinsic IntrinsicModule.Crypto op IntrinsicCategory.Pure fullName, ty)
    | "base64Encode" ->
        let ty = NativeType.TFun(byteArrayType, Types.stringType)
        Resolved (mkIntrinsic IntrinsicModule.Crypto op IntrinsicCategory.Pure fullName, ty)
    | "base64Decode" ->
        let ty = NativeType.TFun(Types.stringType, byteArrayType)
        Resolved (mkIntrinsic IntrinsicModule.Crypto op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Crypto intrinsic: Crypto.{unknown}. Available: sha1, base64Encode, base64Decode"

/// Resolve Bits.* operations - byte order and bit manipulation intrinsics
let private resolveBitsOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Bits." + op
    match op with
    // Byte order conversions (host to network / network to host)
    | "htons" | "ntohs" ->
        let ty = NativeType.TFun(Types.uint16Type, Types.uint16Type)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    | "htonl" | "ntohl" ->
        let ty = NativeType.TFun(Types.uintType, Types.uintType)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    | "htonll" | "ntohll" ->
        let ty = NativeType.TFun(Types.uint64Type, Types.uint64Type)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    // Bit casting between float and int representations
    | "float32ToInt32Bits" ->
        let ty = NativeType.TFun(Types.float32Type, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    | "int32BitsToFloat32" ->
        let ty = NativeType.TFun(Types.intType, Types.float32Type)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    | "float64ToInt64Bits" ->
        let ty = NativeType.TFun(Types.floatType, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    | "int64BitsToFloat64" ->
        let ty = NativeType.TFun(Types.int64Type, Types.floatType)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Bits intrinsic: Bits.{unknown}. Available: htons, ntohs, htonl, ntohl, float32ToInt32Bits, int32BitsToFloat32, float64ToInt64Bits, int64BitsToFloat64"

/// Resolve FnPtr.* operations
let private resolveFnPtrOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "FnPtr." + op
    let freshF = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
    match op with
    | "fromSymbol" ->
        // string -> FnPtr<'F>
        let fnPtrType = NativeType.TApp(Types.fnPtrTyCon, [freshF])
        let ty = NativeType.TFun(Types.stringType, fnPtrType)
        Resolved (mkIntrinsic IntrinsicModule.FnPtr op IntrinsicCategory.Pure fullName, ty)
    | "invoke" ->
        // FnPtr<'F> -> 'F
        let fnPtrType = NativeType.TApp(Types.fnPtrTyCon, [freshF])
        let ty = NativeType.TFun(fnPtrType, freshF)
        Resolved (mkIntrinsic IntrinsicModule.FnPtr op IntrinsicCategory.Pure fullName, ty)
    | "ofFunction" ->
        // 'F -> FnPtr<'F>
        let fnPtrType = NativeType.TApp(Types.fnPtrTyCon, [freshF])
        let ty = NativeType.TFun(freshF, fnPtrType)
        Resolved (mkIntrinsic IntrinsicModule.FnPtr op IntrinsicCategory.Pure fullName, ty)
    | "isNull" | "null" ->
        // REMOVED: Violates null-safety principle
        UnknownOperation $"FnPtr.{op} has been removed. Use Option<FnPtr<'F>> for nullable function pointers."
    | unknown ->
        UnknownOperation $"Unknown FnPtr intrinsic: FnPtr.{unknown}. Available: fromSymbol, invoke, ofFunction"

/// Resolve Lazy.* operations (PRD-14: Deferred computation with memoization)
let private resolveLazyOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Lazy." + op
    let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
    let tyParam = NativeType.TVar tyParamSpec
    let lazyType = NativeType.TLazy tyParam
    match op with
    | "create" ->
        // (unit -> 'T) -> Lazy<'T>
        let thunkFn = NativeType.TFun(Types.unitType, tyParam)
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(thunkFn, lazyType))
        Resolved (mkIntrinsic IntrinsicModule.Lazy op IntrinsicCategory.Pure fullName, ty)
    | "force" ->
        // Lazy<'T> -> 'T
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(lazyType, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.Lazy op IntrinsicCategory.Pure fullName, ty)
    | "isValueCreated" ->
        // Lazy<'T> -> bool
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(lazyType, Types.boolType))
        Resolved (mkIntrinsic IntrinsicModule.Lazy op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Lazy intrinsic: Lazy.{unknown}. Available: create, force, isValueCreated"

/// Resolve Seq.* operations (PRD-15: Sequence generation and consumption)
let private resolveSeqOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Seq." + op
    let tyParamSpecT = freshTypeParam "'T" TypeParamKind.Type range
    let tyParamT = NativeType.TVar tyParamSpecT
    let seqT = NativeType.TSeq tyParamT
    match op with
    | "empty" ->
        // seq<'T> - Returns an empty sequence (polymorphic value)
        // PRD-16: Foundational sequence producer, added early to unblock BAREWire
        let ty = NativeType.TForall([tyParamSpecT], seqT)
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "toArray" ->
        // seq<'T> -> 'T[]
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, NativeType.TApp(Types.arrayTyCon, [tyParamT])))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "toList" ->
        // seq<'T> -> 'T list
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, NativeType.TList tyParamT))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "iter" ->
        // ('T -> unit) -> seq<'T> -> unit
        let actionFn = NativeType.TFun(tyParamT, Types.unitType)
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(actionFn, NativeType.TFun(seqT, Types.unitType)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "map" ->
        // ('T -> 'U) -> seq<'T> -> seq<'U>
        let tyParamSpecU = freshTypeParam "'U" TypeParamKind.Type range
        let tyParamU = NativeType.TVar tyParamSpecU
        let mapFn = NativeType.TFun(tyParamT, tyParamU)
        let seqU = NativeType.TSeq tyParamU
        let ty = NativeType.TForall([tyParamSpecT; tyParamSpecU], NativeType.TFun(mapFn, NativeType.TFun(seqT, seqU)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "filter" ->
        // ('T -> bool) -> seq<'T> -> seq<'T>
        let predFn = NativeType.TFun(tyParamT, Types.boolType)
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(predFn, NativeType.TFun(seqT, seqT)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "fold" ->
        // ('S -> 'T -> 'S) -> 'S -> seq<'T> -> 'S
        let tyParamSpecS = freshTypeParam "'S" TypeParamKind.Type range
        let tyParamS = NativeType.TVar tyParamSpecS
        let foldFn = NativeType.TFun(tyParamS, NativeType.TFun(tyParamT, tyParamS))
        let ty = NativeType.TForall([tyParamSpecS; tyParamSpecT], NativeType.TFun(foldFn, NativeType.TFun(tyParamS, NativeType.TFun(seqT, tyParamS))))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "take" ->
        // int -> seq<'T> -> seq<'T>
        // PRD-16: Returns a wrapper sequence that limits to first N elements
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(Types.intType, NativeType.TFun(seqT, seqT)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "collect" ->
        // ('T -> seq<'U>) -> seq<'T> -> seq<'U>
        // PRD-16: flatMap - maps each element to a sequence, then flattens
        let tyParamSpecU = freshTypeParam "'U" TypeParamKind.Type range
        let tyParamU = NativeType.TVar tyParamSpecU
        let mapperFn = NativeType.TFun(tyParamT, NativeType.TSeq tyParamU)
        let seqU = NativeType.TSeq tyParamU
        let ty = NativeType.TForall([tyParamSpecT; tyParamSpecU], NativeType.TFun(mapperFn, NativeType.TFun(seqT, seqU)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "isEmpty" ->
        // seq<'T> -> bool
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, Types.boolType))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "head" ->
        // seq<'T> -> 'T
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, tyParamT))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "length" ->
        // seq<'T> -> int
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, Types.intType))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "append" ->
        // seq<'T> -> seq<'T> -> seq<'T>
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, NativeType.TFun(seqT, seqT)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "tryPick" ->
        // ('T -> 'U option) -> seq<'T> -> 'U option
        let tyParamSpecU = freshTypeParam "'U" TypeParamKind.Type range
        let tyParamU = NativeType.TVar tyParamSpecU
        let optionU = NativeType.TApp(Types.optionTyCon, [tyParamU])
        let pickerFn = NativeType.TFun(tyParamT, optionU)
        let ty = NativeType.TForall([tyParamSpecT; tyParamSpecU],
            NativeType.TFun(pickerFn, NativeType.TFun(seqT, optionU)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "minBy" ->
        // ('T -> 'U) -> seq<'T> -> 'T
        let tyParamSpecU = freshTypeParam "'U" TypeParamKind.Type range
        let tyParamU = NativeType.TVar tyParamSpecU
        let projFn = NativeType.TFun(tyParamT, tyParamU)
        let ty = NativeType.TForall([tyParamSpecT; tyParamSpecU],
            NativeType.TFun(projFn, NativeType.TFun(seqT, tyParamT)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "max" ->
        // seq<'T> -> 'T
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, tyParamT))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "min" ->
        // seq<'T> -> 'T
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, tyParamT))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Seq intrinsic: Seq.{unknown}. Available: empty, toArray, toList, iter, map, filter, fold, take, collect, isEmpty, head, length, append, tryPick, minBy, max, min"

/// Resolve SeqEnumerator.* operations (PRD-15/16: Sequence iteration state machine)
let private resolveSeqEnumeratorOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "SeqEnumerator." + op
    let tyParamSpecT = freshTypeParam "'T" TypeParamKind.Type range
    let tyParamT = NativeType.TVar tyParamSpecT
    let enumT = NativeType.TSeqEnumerator tyParamT
    match op with
    | "moveNext" ->
        // SeqEnumerator<'T> -> bool
        // Advances the enumerator to the next element, returns false if at end
        // Memory category because it mutates enumerator state
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(enumT, Types.boolType))
        Resolved (mkIntrinsic IntrinsicModule.SeqEnumerator op IntrinsicCategory.Memory fullName, ty)
    | "current" ->
        // SeqEnumerator<'T> -> 'T
        // Gets the current element (undefined behavior if moveNext not called or returned false)
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(enumT, tyParamT))
        Resolved (mkIntrinsic IntrinsicModule.SeqEnumerator op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown SeqEnumerator intrinsic: SeqEnumerator.{unknown}. Available: moveNext, current"

/// Resolve Math.* operations
let private resolveMathOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Math." + op
    match op with
    | "sqrt" ->
        let measure = MVar(freshMeasureVar range)
        let ty = NativeType.TFun(withMeasure Types.floatType (MProd(measure, measure)), withMeasure Types.floatType measure)
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | "abs" ->
        let number = withMeasure (freshTypeVar range) (MVar(freshMeasureVar range))
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, NativeType.TFun(number, number))
    | "atan2" ->
        let number = withMeasure Types.floatType (MVar(freshMeasureVar range))
        let ty = NativeType.TFun(number, NativeType.TFun(number, Types.floatType))
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | "floor" | "ceiling" | "round" | "truncate" ->
        let measure = MVar(freshMeasureVar range)
        let ty = NativeType.TFun(withMeasure Types.floatType measure, withMeasure Types.intType measure)
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | "min" | "max" ->
        let number = withMeasure (freshTypeVar range) (MVar(freshMeasureVar range))
        let ty = NativeType.TFun(number, NativeType.TFun(number, number))
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "exp" | "log" | "log10" ->
        let ty = NativeType.TFun(Types.floatType, Types.floatType)
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | "pow" ->
        let ty = NativeType.TFun(Types.floatType, NativeType.TFun(Types.floatType, Types.floatType))
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Math intrinsic: Math.{unknown}"

/// Resolve Arena.* operations (deterministic memory allocation)
let private resolveArenaOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Arena." + op
    // Create fresh measure parameter for lifetime tracking
    let lifetimeParam = freshTypeParam "'lifetime" TypeParamKind.Measure range
    let lifetimeMeasure = NativeType.TMeasure (MVar lifetimeParam)
    let arenaType = NativeType.TApp(Types.arenaTyCon, [lifetimeMeasure])
    let arenaByrefType = NativeType.TByref(arenaType, ByrefKind.InOut)
    match op with
    | "fromPointer" ->
        // nativeint -> int -> Arena<'lifetime>
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(Types.nintType,
                NativeType.TFun(Types.intType, arenaType)))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | "alloc" ->
        // Arena<'lifetime> byref -> int -> nativeint
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(arenaByrefType,
                NativeType.TFun(Types.intType, Types.nintType)))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | "allocAligned" ->
        // Arena<'lifetime> byref -> int -> int -> nativeint
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(arenaByrefType,
                NativeType.TFun(Types.intType,
                    NativeType.TFun(Types.intType, Types.nintType))))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | "remaining" ->
        // Arena<'lifetime> -> int
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(arenaType, Types.intType))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | "reset" ->
        // Arena<'lifetime> byref -> unit
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(arenaByrefType, Types.unitType))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Arena intrinsic: Arena.{unknown}. Available: fromPointer, alloc, allocAligned, remaining, reset"

/// Resolve DateTime.* operations (BCL-compatible date/time)
let private resolveDateTimeOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "DateTime." + op
    match op with
    // Static constructors
    | "now" ->
        // unit -> int64 (milliseconds since Unix epoch)
        let ty = NativeType.TFun(Types.unitType, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    | "utcNow" ->
        // unit -> int64 (milliseconds since Unix epoch, same as now for UTC)
        let ty = NativeType.TFun(Types.unitType, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    // Component extractors (from milliseconds since epoch)
    | "hour" ->
        // int64 -> int (0-23)
        let ty = NativeType.TFun(Types.int64Type, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Arithmetic fullName, ty)
    | "minute" ->
        // int64 -> int (0-59)
        let ty = NativeType.TFun(Types.int64Type, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Arithmetic fullName, ty)
    | "second" ->
        // int64 -> int (0-59)
        let ty = NativeType.TFun(Types.int64Type, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Arithmetic fullName, ty)
    | "millisecond" ->
        // int64 -> int (0-999)
        let ty = NativeType.TFun(Types.int64Type, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Arithmetic fullName, ty)
    // Timezone / Local time
    | "utcOffset" ->
        // unit -> int (local timezone offset in seconds from UTC, e.g., -18000 for EST)
        // Uses platform localtime_r() to get tm_gmtoff
        let ty = NativeType.TFun(Types.unitType, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    | "toLocal" ->
        // int64 -> int64 (converts UTC milliseconds to local milliseconds)
        // Mirrors BCL DateTime.ToLocalTime() pattern
        let ty = NativeType.TFun(Types.int64Type, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    | "toUtc" ->
        // int64 -> int64 (converts local milliseconds to UTC milliseconds)
        // Mirrors BCL DateTime.ToUniversalTime() pattern
        let ty = NativeType.TFun(Types.int64Type, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    // Formatting
    | "toTimeString" ->
        // int64 -> int -> string (ms since epoch, tzOffset -> "HH:MM:SS.mmm")
        let ty = NativeType.TFun(Types.int64Type, NativeType.TFun(Types.intType, Types.stringType))
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.StringOp fullName, ty)
    | "toDateString" ->
        // int64 -> int -> string (ms since epoch, tzOffset -> "YYYY-MM-DD")
        let ty = NativeType.TFun(Types.int64Type, NativeType.TFun(Types.intType, Types.stringType))
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.StringOp fullName, ty)
    | "toString" ->
        // int64 -> int -> string (ms since epoch, tzOffset -> "YYYY-MM-DD HH:MM:SS")
        let ty = NativeType.TFun(Types.int64Type, NativeType.TFun(Types.intType, Types.stringType))
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.StringOp fullName, ty)
    | "toDateTimeString" ->
        // int64 -> int -> string (ms since epoch, tzOffset -> "YYYY-MM-DDTHH:MM:SS.mmm")
        // Full ISO 8601 style datetime with milliseconds
        let ty = NativeType.TFun(Types.int64Type, NativeType.TFun(Types.intType, Types.stringType))
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.StringOp fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown DateTime intrinsic: DateTime.{unknown}. Available: now, utcNow, hour, minute, second, millisecond, utcOffset, toLocal, toUtc, toTimeString, toDateString, toString, toDateTimeString"

/// Resolve TimeSpan.* operations
let private resolveTimeSpanOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "TimeSpan." + op
    match op with
    // Constructors (return milliseconds as int64)
    | "fromMilliseconds" ->
        // int64 -> int64
        let ty = NativeType.TFun(Types.int64Type, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "fromSeconds" ->
        // int64 -> int64 (converts to milliseconds)
        let ty = NativeType.TFun(Types.int64Type, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "fromMinutes" ->
        // int64 -> int64 (converts to milliseconds)
        let ty = NativeType.TFun(Types.int64Type, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "fromHours" ->
        // int64 -> int64 (converts to milliseconds)
        let ty = NativeType.TFun(Types.int64Type, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    // Component extractors (from milliseconds)
    | "totalMilliseconds" ->
        // int64 -> int64 (identity for internal representation)
        let ty = NativeType.TFun(Types.int64Type, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "totalSeconds" ->
        // int64 -> int64 (ms / 1000)
        let ty = NativeType.TFun(Types.int64Type, Types.int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "hours" ->
        // int64 -> int (hours component)
        let ty = NativeType.TFun(Types.int64Type, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "minutes" ->
        // int64 -> int (minutes component 0-59)
        let ty = NativeType.TFun(Types.int64Type, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "seconds" ->
        // int64 -> int (seconds component 0-59)
        let ty = NativeType.TFun(Types.int64Type, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "milliseconds" ->
        // int64 -> int (milliseconds component 0-999)
        let ty = NativeType.TFun(Types.int64Type, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown TimeSpan intrinsic: TimeSpan.{unknown}. Available: fromMilliseconds, fromSeconds, fromMinutes, fromHours, totalMilliseconds, totalSeconds, hours, minutes, seconds, milliseconds"

/// Resolve Platform.* operations (compile-time platform introspection)
let private resolvePlatformOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Platform." + op
    match op with
    | "sizeof" ->
        // sizeof<'T> : int - returns size of type in bytes
        // Polymorphic: forall 'T. unit -> int
        // Alex resolves 'T to compute size based on target architecture
        let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(Types.unitType, Types.intType))
        Resolved (mkIntrinsic IntrinsicModule.Platform op IntrinsicCategory.Pure fullName, ty)
    | "wordSize" ->
        // wordSize : unit -> int - returns platform word size in bytes (8 on x86_64, 4 on 32-bit)
        // Function form for consistency with other intrinsics and Architecture integration
        let ty = NativeType.TFun(Types.unitType, Types.intType)
        Resolved (mkIntrinsic IntrinsicModule.Platform op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Platform intrinsic: Platform.{unknown}. Available: sizeof, wordSize"

//-------------------------------------------------------------------------
// PRD-13a: Core Collection Intrinsics (Unified Lookup)
//-------------------------------------------------------------------------

/// Collection intrinsics (Map, Set, List, Option, Result) are handled through Baker elaboration.
/// They don't need intrinsic type definitions - Baker saturation recipes provide the semantics.
/// Return NotAnIntrinsic to let normal binding resolution handle these.
let private resolveCollectionOp (_modl: IntrinsicModule) (_moduleName: string) (_op: string) (_range: SourceRange) : IntrinsicResolution =
    // Collection operations are resolved through Baker elaboration, not as raw intrinsics.
    // The type resolution happens through SRTP and Baker recipes.
    NotAnIntrinsic

//-------------------------------------------------------------------------
// Intrinsic Dispatcher
//-------------------------------------------------------------------------

/// Resolve a qualified intrinsic using proper pattern matching.
/// This is the main dispatch function - NO string prefix matching.
let resolveModuleIntrinsic
    (modl: IntrinsicModule)
    (op: string)
    (range: SourceRange)
    : IntrinsicResolution =

    match modl with
    | IntrinsicModule.NativePtr -> resolveNativePtrOp op range
    | IntrinsicModule.MemRef -> resolveMemRefOp op range
    | IntrinsicModule.Sys -> resolveSysOp op range
    | IntrinsicModule.String -> resolveStringOp op range
    | IntrinsicModule.Array -> resolveArrayOp op range
    | IntrinsicModule.Parse -> resolveParseOp op range
    | IntrinsicModule.Format -> resolveFormatOp op range
    | IntrinsicModule.NativeStr -> resolveNativeStrOp op range
    | IntrinsicModule.NativeDefault -> resolveNativeDefaultOp op range
    | IntrinsicModule.Crypto -> resolveCryptoOp op range
    | IntrinsicModule.Bits -> resolveBitsOp op range
    | IntrinsicModule.FnPtr -> resolveFnPtrOp op range
    | IntrinsicModule.Lazy -> resolveLazyOp op range
    | IntrinsicModule.Seq -> resolveSeqOp op range
    | IntrinsicModule.SeqEnumerator -> resolveSeqEnumeratorOp op range
    | IntrinsicModule.Arena -> resolveArenaOp op range
    | IntrinsicModule.Math -> resolveMathOp op range
    | IntrinsicModule.DateTime -> resolveDateTimeOp op range
    | IntrinsicModule.TimeSpan -> resolveTimeSpanOp op range
    | IntrinsicModule.Platform -> resolvePlatformOp op range
    // PRD-13a: Core Collections - handled through Baker elaboration
    | IntrinsicModule.Map -> resolveCollectionOp IntrinsicModule.Map "Map" op range
    | IntrinsicModule.Set -> resolveCollectionOp IntrinsicModule.Set "Set" op range
    | IntrinsicModule.List -> resolveCollectionOp IntrinsicModule.List "List" op range
    | IntrinsicModule.Option -> resolveCollectionOp IntrinsicModule.Option "Option" op range
    | IntrinsicModule.Result -> resolveCollectionOp IntrinsicModule.Result "Result" op range
    | IntrinsicModule.Convert -> NotAnIntrinsic  // Conversions handled separately (float, int, etc.)
    | IntrinsicModule.Operators -> NotAnIntrinsic  // Operators handled separately
    | IntrinsicModule.Unchecked -> NotAnIntrinsic  // Rejected via BCL check

//-------------------------------------------------------------------------
// Operator Intrinsics
//-------------------------------------------------------------------------

/// Try to resolve an operator intrinsic (not, op_BooleanAnd, op_Addition, etc.)
let tryResolveOperator (name: string) (range: SourceRange) : (IntrinsicInfo * NativeType) option =
    match name with
    | "not" ->
        let info = mkIntrinsic IntrinsicModule.Operators "not" IntrinsicCategory.Comparison name
        let ty = NativeType.TFun(Types.boolType, Types.boolType)
        Some (info, ty)
    | "op_BooleanAnd" ->
        let info = mkIntrinsic IntrinsicModule.Operators "op_BooleanAnd" IntrinsicCategory.Comparison name
        let ty = NativeType.TFun(Types.boolType, NativeType.TFun(Types.boolType, Types.boolType))
        Some (info, ty)
    | "op_BooleanOr" ->
        let info = mkIntrinsic IntrinsicModule.Operators "op_BooleanOr" IntrinsicCategory.Comparison name
        let ty = NativeType.TFun(Types.boolType, NativeType.TFun(Types.boolType, Types.boolType))
        Some (info, ty)
    | "op_Multiply" | "op_Division" ->
        let kind = freshTypeVar range
        let left, right = MVar(freshMeasureVar range), MVar(freshMeasureVar range)
        let result = if name = "op_Multiply" then MProd(left, right) else MProd(left, MInv right)
        let ty = NativeType.TFun(withMeasure kind left, NativeType.TFun(withMeasure kind right, withMeasure kind result))
        Some (mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name, ty)
    | "op_Addition" | "op_Subtraction" | "op_Modulus" ->
        // Polymorphic arithmetic: 'T -> 'T -> 'T
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(tyParam, NativeType.TFun(tyParam, tyParam))
        Some (info, ty)
    | "op_LessThan" | "op_GreaterThan" | "op_LessThanOrEqual" | "op_GreaterThanOrEqual" | "op_Equality" | "op_Inequality" ->
        // Polymorphic comparison: 'T -> 'T -> bool
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Comparison name
        let ty = NativeType.TFun(tyParam, NativeType.TFun(tyParam, Types.boolType))
        Some (info, ty)
    | "op_UnaryNegation" ->
        // Polymorphic negation: 'T -> 'T
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(tyParam, tyParam)
        Some (info, ty)
    | "op_BitwiseAnd" | "op_BitwiseOr" | "op_ExclusiveOr" ->
        // Polymorphic bitwise: 'T -> 'T -> 'T
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(tyParam, NativeType.TFun(tyParam, tyParam))
        Some (info, ty)
    | "op_LogicalNot" ->
        // Bitwise complement (~~~): 'T -> 'T
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "op_LogicalNot" IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(tyParam, tyParam)
        Some (info, ty)
    | "op_LeftShift" | "op_RightShift" ->
        // Shift: 'T -> int -> 'T
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(tyParam, NativeType.TFun(Types.intType, tyParam))
        Some (info, ty)
    // Pipe operators - these are eta-reduced away in nanopass but need types during checking
    | "op_PipeRight" ->
        // 'T -> ('T -> 'U) -> 'U  (forward pipe: x |> f)
        let tyT = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let tyU = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "op_PipeRight" IntrinsicCategory.Pure name
        let ty = NativeType.TFun(tyT, NativeType.TFun(NativeType.TFun(tyT, tyU), tyU))
        Some (info, ty)
    | "op_PipeLeft" ->
        // ('T -> 'U) -> 'T -> 'U  (backward pipe: f <| x)
        let tyT = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let tyU = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "op_PipeLeft" IntrinsicCategory.Pure name
        let ty = NativeType.TFun(NativeType.TFun(tyT, tyU), NativeType.TFun(tyT, tyU))
        Some (info, ty)
    | "op_PipeRight2" ->
        // ('T1 * 'T2) -> ('T1 -> 'T2 -> 'U) -> 'U  (||>)
        let tyT1 = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let tyT2 = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let tyU = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "op_PipeRight2" IntrinsicCategory.Pure name
        let tupleTy = NativeType.TTuple([tyT1; tyT2], false)
        let funcTy = NativeType.TFun(tyT1, NativeType.TFun(tyT2, tyU))
        let ty = NativeType.TFun(tupleTy, NativeType.TFun(funcTy, tyU))
        Some (info, ty)
    | "op_PipeRight3" ->
        // ('T1 * 'T2 * 'T3) -> ('T1 -> 'T2 -> 'T3 -> 'U) -> 'U  (|||>)
        let tyT1 = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let tyT2 = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let tyT3 = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let tyU = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "op_PipeRight3" IntrinsicCategory.Pure name
        let tupleTy = NativeType.TTuple([tyT1; tyT2; tyT3], false)
        let funcTy = NativeType.TFun(tyT1, NativeType.TFun(tyT2, NativeType.TFun(tyT3, tyU)))
        let ty = NativeType.TFun(tupleTy, NativeType.TFun(funcTy, tyU))
        Some (info, ty)
    // PRD-13a: Tuple accessors and comparison functions
    | "fst" ->
        // ('T1 * 'T2) -> 'T1
        let tyT1 = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let tyT2 = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "fst" IntrinsicCategory.Pure name
        let tupleTy = NativeType.TTuple([tyT1; tyT2], false)
        let ty = NativeType.TFun(tupleTy, tyT1)
        Some (info, ty)
    | "snd" ->
        // ('T1 * 'T2) -> 'T2
        let tyT1 = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let tyT2 = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "snd" IntrinsicCategory.Pure name
        let tupleTy = NativeType.TTuple([tyT1; tyT2], false)
        let ty = NativeType.TFun(tupleTy, tyT2)
        Some (info, ty)
    | "max" ->
        // 'T -> 'T -> 'T (polymorphic comparison)
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "max" IntrinsicCategory.Comparison name
        let ty = NativeType.TFun(tyParam, NativeType.TFun(tyParam, tyParam))
        Some (info, ty)
    | "min" ->
        // 'T -> 'T -> 'T (polymorphic comparison)
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "min" IntrinsicCategory.Comparison name
        let ty = NativeType.TFun(tyParam, NativeType.TFun(tyParam, tyParam))
        Some (info, ty)
    // PRD-13a: List cons operator
    | "op_ColonColon" ->
        // ('T * list<'T>) -> list<'T> (cons: prepend element to list - takes tuple, not curried)
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let listTy = NativeType.TList(tyParam)
        let tupleTy = NativeType.TTuple([tyParam; listTy], false)
        let info = mkIntrinsic IntrinsicModule.List "cons" IntrinsicCategory.Pure name
        let ty = NativeType.TFun(tupleTy, listTy)
        Some (info, ty)
    // PRD-13a: List append operator (@)
    | "op_Append" ->
        // list<'T> -> list<'T> -> list<'T> (concatenate two lists)
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let listTy = NativeType.TList(tyParam)
        let info = mkIntrinsic IntrinsicModule.List "append" IntrinsicCategory.Pure name
        let ty = NativeType.TFun(listTy, NativeType.TFun(listTy, listTy))
        Some (info, ty)
    | "ignore" ->
        // 'T -> unit (discard value)
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators "ignore" IntrinsicCategory.Pure name
        let ty = NativeType.TFun(tyParam, Types.unitType)
        Some (info, ty)
    | _ -> None

/// Check if a name is an operator that should be an intrinsic
/// Used for hard error reporting when an operator is not recognized
let isOperatorName (name: string) : bool =
    name.StartsWith("op_") || name = "not" || name = "ignore"

//-------------------------------------------------------------------------
// Conversion Intrinsics
//-------------------------------------------------------------------------

/// Kind-changing arithmetic, with dimensions preserved (Width Inference §7).
/// Representation conversion names are deliberately absent from Clef's intrinsics.
let tryResolveConversion (name: string) (range: SourceRange) : (IntrinsicInfo * NativeType) option =
    match name with
    | "float" ->
        let measure = MVar(freshMeasureVar range)
        let ty = NativeType.TFun(withMeasure Types.intType measure, withMeasure Types.floatType measure)
        Some(mkIntrinsic IntrinsicModule.Convert "toFloat" IntrinsicCategory.Arithmetic name, ty)
    | "char" ->
        let ty = NativeType.TFun(Types.intType, Types.charType)
        Some(mkIntrinsic IntrinsicModule.Convert "toChar" IntrinsicCategory.Conversion name, ty)
    | _ -> None

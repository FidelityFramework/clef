// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Intrinsic resolution for Clef.
/// This module provides proper discriminated union dispatch for intrinsics,
/// replacing the string prefix matching anti-pattern.
///
/// ARCHITECTURAL PRINCIPLE: No `name.StartsWith("X.")` dispatch.
/// Intrinsic modules are matched via proper pattern matching on IntrinsicModule.
module Clef.Compiler.NativeTypedTree.Expressions.Intrinsics

open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
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
        | "Sys" -> Some (IntrinsicModule.Sys, opPart)
        | "String" -> Some (IntrinsicModule.String, opPart)
        | "Array" -> Some (IntrinsicModule.Array, opPart)
        // Parse.int/float and Format.int/float are platform library functions,
        // resolved as VarRef by FCS, not as CCS intrinsics.
        | "Crypto" -> Some (IntrinsicModule.Crypto, opPart)
        | "Bits" -> Some (IntrinsicModule.Bits, opPart)
        | "FnPtr" -> Some (IntrinsicModule.FnPtr, opPart)
        | "Mmio" -> Some (IntrinsicModule.Mmio, opPart)
        | "BorrowedView" -> Some (IntrinsicModule.BorrowedView, opPart)
        | "Lazy" -> Some (IntrinsicModule.Lazy, opPart)
        | "Seq" -> Some (IntrinsicModule.Seq, opPart)
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
    // The parsers the native library provides; the target type is read from the one spelling
    // table (sequence CS-5).
    match op with
    | "int" | "int64" | "float" ->
        match Types.tryNumericTyConOfName op with
        | Some carrier ->
            let ty = NativeType.TFun(Types.stringType, Types.numericType carrier)
            Resolved (mkIntrinsic IntrinsicModule.Parse op IntrinsicCategory.Conversion fullName, ty)
        | None -> UnknownOperation $"Parse.{op}: no numeric carrier is spelled '{op}'"
    | unknown ->
        UnknownOperation $"Unknown Parse intrinsic: Parse.{unknown}. Available: int, int64, float"

/// Resolve Format.* operations (numeric → string)
let private resolveFormatOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Format." + op
    // The formatters the native library provides; the source type is read from the one spelling
    // table (sequence CS-5).
    match op with
    | "int" | "int64" | "float" | "float64" | "double" ->
        match Types.tryNumericTyConOfName op with
        | Some carrier ->
            let ty = NativeType.TFun(Types.numericType carrier, Types.stringType)
            Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
        | None -> UnknownOperation $"Format.{op}: no numeric carrier is spelled '{op}'"
    | "bool" ->
        let ty = NativeType.TFun(Types.boolType, Types.stringType)
        Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Format intrinsic: Format.{unknown}. Available: int, int64, float, bool"

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

/// Resolve hardware access operations. A bound handle selects declaration
/// identities; its permissions and address are settled by CCS.
let private resolveMmioOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let integer = Types.intType
    let signature =
        [8, Types.mmio8TyCon; 16, Types.mmio16TyCon; 32, Types.mmio32TyCon]
        |> List.tryPick (fun (bits, tc) ->
            let handle = NativeType.TApp(tc, [])
            if op = "reg" + string bits then Some (NativeType.TFun(integer, handle))
            elif op = "bind" + string bits then Some (NativeType.TFun(Types.stringType, NativeType.TFun(Types.stringType, handle)))
            elif op = "read" + string bits then Some (NativeType.TFun(handle, integer))
            elif op = "write" + string bits then Some (NativeType.TFun(handle, NativeType.TFun(integer, Types.unitType)))
            else None)
    match signature with
    | Some ty -> Resolved (mkIntrinsic IntrinsicModule.Mmio op IntrinsicCategory.Memory ("Mmio." + op), ty)
    | None -> UnknownOperation ("Unknown Mmio operation: " + op)

let private resolveBorrowedViewOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let schema = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
    let view = NativeType.TApp (Types.borrowedViewTyCon, [schema])
    let integer = Types.intType
    let signature =
        match op with
        | "length" | "stride" -> Some (NativeType.TFun (view, integer))
        | "get" -> Some (NativeType.TFun (view, NativeType.TFun (integer, integer)))
        | "set" -> Some (NativeType.TFun (view, NativeType.TFun (integer, NativeType.TFun (integer, Types.unitType))))
        | _ -> None
    match signature with
    | Some ty -> Resolved (mkIntrinsic IntrinsicModule.BorrowedView op IntrinsicCategory.Memory ("BorrowedView." + op), ty)
    | None -> UnknownOperation ("Unknown BorrowedView operation: " + op + ". Available: length, stride, get, set. Views are supplied only by declared mapping scopes.")

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
        // The callback signature supplies no guarantee about external effects.
        Resolved (mkIntrinsic IntrinsicModule.FnPtr op IntrinsicCategory.Platform fullName, ty)
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

//-------------------------------------------------------------------------
// Numeric schemes: the carrier and measure variables, fresh per use
//-------------------------------------------------------------------------

/// A fresh carrier variable for an operand position of operator `op` (design a.2, c.1): the
/// variable carries the operator it was minted for, so CCS8000 can name it.
let private freshCarrierFor (op: string) (range: SourceRange) : CarrierRef =
    let k = freshTypeParamAuto TypeParamKind.Carrier range
    k.Constraints <- [ Constraint.OperandOf(op, range) ]
    CarrierRef.CVar k

/// A fresh measure variable as a dimension.
let private freshDimension () : Dimension = Dimension.ofVar (freshMeasureVar None)

/// The numeric type at a carrier position and a dimension: `κ<'u>`.
let private numeric (k: CarrierRef) (d: Dimension) : NativeType = NativeType.TNum(k, d)

/// `ρ<'u>`: the real carrier at a dimension (design (c): `ρ` is the float carrier, D10).
let private real (d: Dimension) : NativeType = NativeType.TNum(CarrierRef.Carrier Types.floatTyCon, d)

/// `int<'u>`: the integer carrier at a dimension.
let private integer (d: Dimension) : NativeType = NativeType.TNum(CarrierRef.Carrier Types.intTyCon, d)

/// The library schemes (design (c) table; units-of-measure.md, the measure-aware functions;
/// Dimensional_Range_Design.md §5), each stated once and instantiated with fresh carrier and
/// measure variables at every use, as `tryResolveOperator` does for the operators. They are
/// resolved only after binding lookup fails (Identity.fs), so a user's `abs` is never shadowed.
///   abs                             κ<'u> -> κ<'u>
///   sign                            κ<'u> -> int<1>
///   min, max                        κ<'u> -> κ<'u> -> κ<'u>
///   clamp lo hi x                   κ<'u> -> κ<'u> -> κ<'u> -> κ<'u>
///   sqrt                            ρ<'u^2> -> ρ<'u>     (`sqrt 1.0<m>` is CCS8041 through solveDim)
///   atan2                           ρ<'u> -> ρ<'u> -> ρ<1>
///   floor, ceiling, round, truncate ρ<'u> -> int<'u>     (a real becomes an integer through these, §5)
let private librarySchemeType (name: string) (range: SourceRange) : NativeType option =
    match name with
    | "abs" ->
        let k = freshCarrierFor name range
        let u = freshDimension ()
        Some (NativeType.TFun(numeric k u, numeric k u))
    | "sign" ->
        let k = freshCarrierFor name range
        let u = freshDimension ()
        Some (NativeType.TFun(numeric k u, integer Dimension.one))
    | "min" | "max" ->
        let k = freshCarrierFor name range
        let u = freshDimension ()
        Some (NativeType.TFun(numeric k u, NativeType.TFun(numeric k u, numeric k u)))
    | "clamp" ->
        let k = freshCarrierFor name range
        let u = freshDimension ()
        Some (NativeType.TFun(numeric k u, NativeType.TFun(numeric k u, NativeType.TFun(numeric k u, numeric k u))))
    | "sqrt" ->
        let u = freshDimension ()
        Some (NativeType.TFun(real (Dimension.pow 2 u), real u))
    | "atan2" ->
        let u = freshDimension ()
        Some (NativeType.TFun(real u, NativeType.TFun(real u, real Dimension.one)))
    | "floor" | "ceiling" | "round" | "truncate" ->
        let u = freshDimension ()
        Some (NativeType.TFun(real u, integer u))
    | _ -> None

/// Try to resolve a bare library name to its intrinsic and scheme: the step after binding
/// lookup fails, so a binding of the same name wins (the CS-6 review's shadowing rule).
let tryResolveLibraryScheme (name: string) (range: SourceRange) : (IntrinsicInfo * NativeType) option =
    librarySchemeType name range
    |> Option.map (fun ty -> (mkIntrinsic IntrinsicModule.Math name IntrinsicCategory.Arithmetic name, ty))

/// Resolve Math.* operations. `Math.abs`, `Math.sqrt`, `Math.atan2`, `Math.floor`, `Math.ceiling`
/// and `Math.round` are the qualified spelling of the library schemes below (one definition, two
/// spellings; design (c), sequence CS-9); the transcendentals keep their dimensionless typing.
let private resolveMathOp (op: string) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Math." + op
    match op with
    | "abs" | "sqrt" | "atan2" | "floor" | "ceiling" | "round" | "truncate" | "min" | "max" ->
        match librarySchemeType op range with
        | Some ty -> Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
        | None -> UnknownOperation $"Unknown Math intrinsic: Math.{op}"
    | "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "exp" | "log" | "log10" ->
        let ty = NativeType.TFun(Types.floatType, Types.floatType)
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | "pow" ->
        let ty = NativeType.TFun(Types.floatType, NativeType.TFun(Types.floatType, Types.floatType))
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Math intrinsic: Math.{unknown}"

/// Resolve Arena.* operations (deterministic memory allocation)
let private resolveArenaOp (op: string) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Arena." + op
    // Create fresh measure parameter for lifetime tracking
    let lifetime = freshMeasureVar (Some "lifetime")
    let lifetimeParam = measureCellOf lifetime
    // The lifetime is a measure variable in a measure-sorted position (design a.2, sequence CS-4).
    let lifetimeMeasure = NativeType.TMeasure (Dimension.ofVar lifetime)
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
    | IntrinsicModule.Sys -> resolveSysOp op range
    | IntrinsicModule.String -> resolveStringOp op range
    | IntrinsicModule.Array -> resolveArrayOp op range
    | IntrinsicModule.Parse -> resolveParseOp op range
    | IntrinsicModule.Format -> resolveFormatOp op range
    | IntrinsicModule.NativeDefault -> resolveNativeDefaultOp op range
    | IntrinsicModule.Crypto -> resolveCryptoOp op range
    | IntrinsicModule.Bits -> resolveBitsOp op range
    | IntrinsicModule.FnPtr -> resolveFnPtrOp op range
    | IntrinsicModule.Mmio -> resolveMmioOp op range
    | IntrinsicModule.BorrowedView -> resolveBorrowedViewOp op range
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
    // The measure-aware operator schemes (design (c), units-of-measure.md §Type Definitions with
    // Measures), each stated once here and instantiated with fresh carrier and measure variables
    // at every use. `κ` is a carrier variable, the numeric constraint itself (c.1): a `bool`
    // operand fails to unify with it and is CCS8000.
    | "op_Addition" ->
        // `+` dispatches on the kind of its operands (c.3, D5): both numeric, the scheme
        // `κ<'u> -> κ<'u> -> κ<'u>` realised by one shared operand type; both string, concat.
        // The dispatch is attached to the operand variable and fires when it binds.
        let operand = freshTypeParamAuto TypeParamKind.Type range
        operand.Constraints <- [ Constraint.OperandOf(name, range) ]
        let tyParam = NativeType.TVar operand
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(tyParam, NativeType.TFun(tyParam, tyParam))
        Some (info, ty)
    | "op_Subtraction" | "op_Modulus" ->
        // `κ<'u> -> κ<'u> -> κ<'u>` (spec: `N<'U> -> N<'U> -> N<'U>`)
        let k = freshCarrierFor name range
        let u = freshDimension ()
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(numeric k u, NativeType.TFun(numeric k u, numeric k u))
        Some (info, ty)
    | "op_Multiply" ->
        // `κ<'u> -> κ<'v> -> κ<'u 'v>` (spec: `N<'U> -> N<'V> -> N<'U 'V>`)
        let k = freshCarrierFor name range
        let u = freshDimension ()
        let v = freshDimension ()
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(numeric k u, NativeType.TFun(numeric k v, numeric k (Dimension.mul u v)))
        Some (info, ty)
    | "op_Division" ->
        // `κ<'u> -> κ<'v> -> κ<'u 'v^-1>` (spec: `N<'U> -> N<'V> -> N<'U/'V>`)
        let k = freshCarrierFor name range
        let u = freshDimension ()
        let v = freshDimension ()
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(numeric k u, NativeType.TFun(numeric k v, numeric k (Dimension.mul u (Dimension.inv v))))
        Some (info, ty)
    | "op_LessThan" | "op_GreaterThan" | "op_LessThanOrEqual" | "op_GreaterThanOrEqual" | "op_Equality" | "op_Inequality" ->
        // Polymorphic comparison: 'T -> 'T -> bool
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Comparison name
        let ty = NativeType.TFun(tyParam, NativeType.TFun(tyParam, Types.boolType))
        Some (info, ty)
    | "op_UnaryNegation" | "op_UnaryPlus" ->
        // `κ<'u> -> κ<'u>` (spec: `N<'U> -> N<'U>`). `abs` and `sign` are library functions
        // with these schemes (design (c) "if in scope", step 3), not operator names: an
        // operator name pre-empts binding lookup, and a user's `abs` must not be shadowed.
        let k = freshCarrierFor name range
        let u = freshDimension ()
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(numeric k u, numeric k u)
        Some (info, ty)
    | "op_BitwiseAnd" | "op_BitwiseOr" | "op_ExclusiveOr" ->
        // Bitwise: `κ<'u> -> κ<'u> -> κ<'u>` (`x &&& mask` keeps x's carrier and dimension,
        // Dimensional_Range_Design.md §5; sequence CS-9)
        let k = freshCarrierFor name range
        let u = freshDimension ()
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(numeric k u, NativeType.TFun(numeric k u, numeric k u))
        Some (info, ty)
    | "op_LogicalNot" ->
        // Bitwise complement (~~~): `κ<'u> -> κ<'u>`
        let k = freshCarrierFor name range
        let u = freshDimension ()
        let info = mkIntrinsic IntrinsicModule.Operators "op_LogicalNot" IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(numeric k u, numeric k u)
        Some (info, ty)
    | "op_LeftShift" | "op_RightShift" ->
        // Shift: `κ<'u> -> int<1> -> κ<'u>` (plan L-8): the amount is a dimensionless int typed
        // by the front end; the shifted operand keeps its carrier. Composer still casts the
        // amount to the operand's width at emission until CS-10 supplies widths from the node.
        let k = freshCarrierFor name range
        let u = freshDimension ()
        let info = mkIntrinsic IntrinsicModule.Operators name IntrinsicCategory.Arithmetic name
        let ty = NativeType.TFun(numeric k u, NativeType.TFun(Types.intType, numeric k u))
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
    // `min` and `max` are library schemes (`tryResolveLibraryScheme`), resolved after binding
    // lookup with the numeric scheme `κ<'u> -> κ<'u> -> κ<'u>` (sequence CS-9).
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

/// Kind-changing arithmetic preserves dimensions. Width/representation conversion
/// spellings are not Clef source intrinsics; rounding operations select the integer kind.
let tryResolveConversion (name: string) (_range: SourceRange) : (IntrinsicInfo * NativeType) option =
    match name with
    | "float" ->
        let u = freshDimension ()
        let info = mkIntrinsic IntrinsicModule.Convert "toFloat" IntrinsicCategory.Arithmetic name
        Some (info, NativeType.TFun(integer u, real u))
    | "char" ->
        let info = mkIntrinsic IntrinsicModule.Convert "toChar" IntrinsicCategory.Conversion name
        Some (info, NativeType.TFun(Types.intType, Types.charType))
    | _ -> None

//-------------------------------------------------------------------------
// The declared range sources (Dimensional_Range_Design.md §1.1 last bullet, §3.3, §4.1; CS-11)
//-------------------------------------------------------------------------

/// The ranges the compiler declares for itself, in one table beside the intrinsic definitions,
/// read by the range pass (`RangeAnalysis`) and by nothing else. Three sources live here:
///
/// 1. The result range of an intrinsic application (`intrinsic`): a length is at most the
///    largest extent the platform's declared Pointer width addresses, `[0, 2^(Pointer-1) - 1]`;
///    `Sys.read` and `Sys.write` return the range the platform's endpoint contract declares as
///    data, `[Floor, hi(count)]` (the x86_64 description's `readBound` and `writeBound`, their
///    `Floor` the errno floor and their `AtMost` the `count` parameter; BAREWire docs/11), read
///    into `PlatformContext.EndpointReturns` by PlatformDeclaration, and are unobservable on a
///    description that declares no such contract; the operators are
///    interval arithmetic (`ValueRange`); a conversion to a width-named carrier is the meet of the
///    argument's range with the target representation's declared range where that covers the
///    argument (exact) and the declared range otherwise, the image of the wrap the description
///    declares for that representation (an interim rule: CS-12 deletes the width-named spellings
///    and the conversions with them); a conversion to the bare kind, `int` of a `char` included,
///    is the identity on the range (a code point is `[0, 1114111]` by the char node's own range);
///    `sign`, `abs`, `min`, `max` and `clamp` have their images; the `DateTime` component
///    extractors the ranges their definitions state; `Math.*`, the rounding intrinsics and every
///    parse of an input are not tabled (the real domain is CS-13's; an input's range is a
///    declaration, CS-12).
/// 2. The interim declared boundary of a width-named carrier (`declaredRangeOfKind`): the range
///    the platform description declares for the representation the carrier's spelling names
///    (`Types.numericSpellings`, the representation column), or on a context declaring none the
///    two's-complement or unsigned range of its bits. This rule is deleted in CS-12 with the
///    spellings; the bare kind (`int`, `uint`) never takes it.
/// 3. What an intrinsic supplies to a function it is handed (`calls`): `Array.init n f` calls `f`
///    at every index in `[0, n - 1]`; a sequence intrinsic hands its function a value the pass
///    does not model.
module RangeSources =

    /// What the table says of an intrinsic application's integer result.
    [<RequireQualifiedAccess>]
    type Result =
        /// The compiler's own fact.
        | Fact of ValueRange
        /// The element range of the array argument at that position (a graph fact the reader holds).
        | ElementOf of argIndex: int
        /// No fact here: the result is unobservable unless the carrier declares a boundary.
        | Untabled

    /// What an intrinsic supplies to one parameter of a function it calls.
    [<RequireQualifiedAccess>]
    type Seed =
        /// `[0, n - 1]` for the integer argument `n` at that position of the intrinsic's own call.
        | IndexBelow of argIndex: int
        /// A value the pass does not model (a sequence element).
        | Unknown

    /// One argument of an intrinsic application as the table reads it: its range (unbounded for
    /// an argument the pass does not range, a real or a buffer), its type, and its literal if it
    /// is one (a string literal's byte length bounds a write of it).
    type Argument = { Range: ValueRange; Type: NativeType; Literal: NativeLiteral option }

    /// The exact range a declared representation states, from its decimal text; `None` when the
    /// text is not an integer, which is the declaration's defect (CCS8207), never a range.
    let declaredRange (r: NumericRepresentation) : ValueRange option =
        match bigint.TryParse r.MinMagnitude, bigint.TryParse r.MaxMagnitude with
        | (true, lo), (true, hi) when lo <= hi -> Some (ValueRange.Bounded (lo, hi))
        | _ -> None

    /// The representation a width-named integer kind names on this context, through the one
    /// spelling table (`Types.numericSpellings`): `None` for the bare kind, whose representation
    /// is the range's choice, and for a kind the context does not offer.
    let representationOfKind (ctx: PlatformContext) (kind: NTUKind) : NumericRepresentation option =
        match kind with
        | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)
        | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register) -> None
        | NTUKind.NTUint _ | NTUKind.NTUuint _ ->
            Types.numericSpellings
            |> List.tryPick (fun (_, tc, _, seal) -> if tc.NTUKind = Some kind then Some seal else None)
            |> Option.bind (fun seal ->
                match PlatformContext.tryRepresentationOfSeal ctx seal with
                | Result.Ok r -> Some r
                | Result.Error _ -> None)
        | _ -> None

    /// The two's-complement or unsigned range of an integer kind's bits, for a context that
    /// declares no representation for it: the width the spelling itself states.
    let private rangeOfBits (kind: NTUKind) (bits: int) : ValueRange =
        match kind with
        | NTUKind.NTUuint _ -> ValueRange.unsignedOf bits
        | _ -> ValueRange.twosComplement bits

    /// The interim declared boundary a width-named spelling writes (CS-12 step 5a, the alias;
    /// ruling 5): the shape the descriptor reader produces for a wire field or a C parameter, a
    /// declared representation and its exact range. `Repr` and `Bits` are the platform
    /// description's representation of the spelling's name, or, on a context declaring none, the
    /// spelling's own name and bits; `Range` is that representation's declared range.
    type Declaration = { Repr: string; Bits: int; Range: ValueRange }

    /// The declaration of a width-named integer kind (source 2 above): `None` for the bare kind
    /// (`int`, `uint`: the range is the analysis's own) and for a pointer-width spelling on a
    /// context that declares no Pointer (CCS8203 at the site that needs it). Every read of the
    /// spelled representation, `RangeAnalysis.selectedWidth`, `selectedRepresentation`,
    /// `boundByCarrier`, `Placement`'s slot and Composer's type mapping, comes through here.
    let declarationOfKind (ctx: PlatformContext option) (kind: NTUKind) : Declaration option =
        let declared () =
            ctx
            |> Option.bind (fun c -> representationOfKind c kind)
            |> Option.bind (fun r -> declaredRange r |> Option.map (fun d -> { Repr = r.Name; Bits = r.Bits; Range = d }))
        let spelled (bits: int) = { Repr = NTUKind.name kind; Bits = bits; Range = rangeOfBits kind bits }
        match kind with
        | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)
        | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register) -> None
        | NTUKind.NTUint (NTUWidth.Fixed bits)
        | NTUKind.NTUuint (NTUWidth.Fixed bits) ->
            match declared () with
            | Some d -> Some d
            | None -> Some (spelled bits)
        | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer)
        | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer) ->
            match declared () with
            | Some d -> Some d
            | None ->
                ctx
                |> Option.bind (fun c -> PlatformContext.tryWidth c (WidthDimension.name WidthDimension.Pointer) |> Result.toOption)
                |> Option.map spelled
        | _ -> None

    /// The declared range of a width-named integer kind: its declaration's.
    let declaredRangeOfKind (ctx: PlatformContext option) (kind: NTUKind) : ValueRange option =
        declarationOfKind ctx kind |> Option.map (fun d -> d.Range)

    /// The range of a length or an offset: `[0, 2^(Pointer - 1) - 1]`, the largest extent the
    /// declared Pointer width addresses; unobservable on a context declaring no Pointer.
    let lengthRange (ctx: PlatformContext option) : ValueRange =
        match ctx |> Option.bind (fun c -> PlatformContext.tryWidth c (WidthDimension.name WidthDimension.Pointer) |> Result.toOption) with
        | Some bits -> ValueRange.Bounded (bigint.Zero, bigint.Pow (bigint 2, bits - 1) - bigint.One)
        | None -> ValueRange.Unbounded

    /// The length range of a buffer argument: a string literal's byte length exactly, any other
    /// buffer the platform's length range.
    let private bufferLength (ctx: PlatformContext option) (buffer: Argument) : ValueRange =
        match buffer.Literal with
        | Some (NativeLiteral.String s) -> ValueRange.point (bigint (System.Text.Encoding.UTF8.GetByteCount s))
        | _ -> lengthRange ctx

    /// The result of the platform's read or write, from the endpoint's declared contract alone
    /// (Dimensional_Range_Design.md, ruling 2 of CS-12): `[Floor, hi(count)]`, the contract's
    /// declared floor (the errno floor, since a negative return is an errno) and the parameter the
    /// return is at most. `count` is the one parameter this intrinsic supplies, as the buffer's
    /// length (`Sys.read fd buffer` reads at most the buffer's length: the intrinsic's own
    /// definition above). A description that declares no such contract, or whose contract names a
    /// parameter the intrinsic does not supply, leaves the result unobservable; no number is held
    /// here.
    let private declaredReturn (ctx: PlatformContext option) (endpoint: string) (count: ValueRange) : Result =
        match ctx |> Option.bind (fun c -> Map.tryFind endpoint c.EndpointReturns) with
        | Some { AtMost = "count"; Floor = floor } ->
            match count with
            | ValueRange.Bounded (_, hi) -> Result.Fact (ValueRange.bounded floor (max hi bigint.Zero))
            | ValueRange.Empty -> Result.Fact (ValueRange.bounded floor bigint.Zero)
            | _ -> Result.Untabled
        | _ -> Result.Untabled

    /// A conversion's image (source 1, the conversion row): the target carrier by the conversion
    /// operation's name in the spelling table, its declared range on this context; the meet where
    /// that range covers the argument (exact), otherwise the declared range, the wrap's image. A
    /// conversion to the bare kind is the identity on the range.
    let private conversion (ctx: PlatformContext option) (operation: string) (argument: ValueRange) : ValueRange =
        let target =
            Types.numericSpellings
            |> List.tryPick (fun (_, tc, op, _) -> if op = operation then tc.NTUKind else None)
        match target |> Option.bind (declaredRangeOfKind ctx) with
        | Some declared -> if ValueRange.contains declared argument then argument else declared
        | None -> argument

    /// The result range of an intrinsic application (source 1).
    let intrinsic (ctx: PlatformContext option) (info: IntrinsicInfo) (args: Argument list) : Result =
        let ranges = args |> List.map (fun a -> a.Range)
        match info.Category, info.Module, info.Operation, ranges with
        | IntrinsicCategory.Comparison, _, _, _ -> Result.Fact ValueRange.boolean
        | _, IntrinsicModule.Operators, "op_Addition", [ x; y ] -> Result.Fact (ValueRange.add x y)
        | _, IntrinsicModule.Operators, "op_Subtraction", [ x; y ] -> Result.Fact (ValueRange.sub x y)
        | _, IntrinsicModule.Operators, "op_Multiply", [ x; y ] -> Result.Fact (ValueRange.mul x y)
        | _, IntrinsicModule.Operators, "op_Division", [ x; y ] -> Result.Fact (ValueRange.div x y)
        | _, IntrinsicModule.Operators, "op_Modulus", [ x; y ] -> Result.Fact (ValueRange.rem x y)
        | _, IntrinsicModule.Operators, "op_UnaryNegation", [ x ] -> Result.Fact (ValueRange.neg x)
        | _, IntrinsicModule.Operators, "op_UnaryPlus", [ x ] -> Result.Fact x
        | _, IntrinsicModule.Operators, "op_BitwiseAnd", [ x; y ] -> Result.Fact (ValueRange.band x y)
        | _, IntrinsicModule.Operators, ("op_BitwiseOr" | "op_ExclusiveOr"), [ x; y ] -> Result.Fact (ValueRange.bor x y)
        | _, IntrinsicModule.Operators, "op_LogicalNot", [ x ] -> Result.Fact (ValueRange.bnot x)
        | _, IntrinsicModule.Operators, "op_LeftShift", [ x; n ] -> Result.Fact (ValueRange.shl x n)
        | _, IntrinsicModule.Operators, "op_RightShift", [ x; n ] -> Result.Fact (ValueRange.shr x n)
        | _, IntrinsicModule.Operators, ("not" | "op_BooleanAnd" | "op_BooleanOr"), _ -> Result.Fact ValueRange.boolean
        // lengths and offsets
        | _, (IntrinsicModule.Array | IntrinsicModule.String | IntrinsicModule.Seq | IntrinsicModule.List), "length", _ ->
            Result.Fact (lengthRange ctx)
        | _, IntrinsicModule.String, "indexOf", _ ->
            match lengthRange ctx with
            | ValueRange.Bounded (_, hi) -> Result.Fact (ValueRange.Bounded (bigint.MinusOne, hi))
            | _ -> Result.Untabled
        // element reads
        | _, IntrinsicModule.Array, "get", _ -> Result.ElementOf 0
        // the platform's read and write: the endpoint's declared return bound over the buffer's length
        | _, IntrinsicModule.Sys, (("read" | "write") as endpoint), _ ->
            match args with
            | [ _; buffer ] -> declaredReturn ctx endpoint (bufferLength ctx buffer)
            | _ -> declaredReturn ctx endpoint (lengthRange ctx)
        // conversions between numeric carriers
        | IntrinsicCategory.Conversion, IntrinsicModule.Convert, op, [ x ] -> Result.Fact (conversion ctx op x)
        // the library schemes with an image (the CS-9 recipes decompose most of these before the pass)
        | _, IntrinsicModule.Math, "sign", _ -> Result.Fact (ValueRange.Bounded (bigint.MinusOne, bigint.One))
        | _, IntrinsicModule.Math, "abs", [ x ] -> Result.Fact (ValueRange.abs x)
        | _, IntrinsicModule.Math, "min", [ x; y ] -> Result.Fact (ValueRange.minOf x y)
        | _, IntrinsicModule.Math, "max", [ x; y ] -> Result.Fact (ValueRange.maxOf x y)
        | _, IntrinsicModule.Math, "clamp", [ lo; hi; x ] -> Result.Fact (ValueRange.minOf hi (ValueRange.maxOf lo x))
        // the date components, the ranges their definitions state
        | _, IntrinsicModule.DateTime, "hour", _ -> Result.Fact (ValueRange.bounded bigint.Zero (bigint 23))
        | _, IntrinsicModule.DateTime, ("minute" | "second"), _ -> Result.Fact (ValueRange.bounded bigint.Zero (bigint 59))
        | _, IntrinsicModule.DateTime, "millisecond", _ -> Result.Fact (ValueRange.bounded bigint.Zero (bigint 999))
        // Math.* and the rounding intrinsics (CS-13), parses of input (CS-12), everything else
        | _ -> Result.Untabled

    /// The function-valued arguments an intrinsic calls, by position, with what it supplies to
    /// each parameter of that function (source 3).
    /// The array intrinsics whose result elements are elements of the argument array itself
    /// (the element rule's same-key operations, CS-11): any other array-producing intrinsic builds
    /// elements the store fold does not see and seeds its element type unbounded.
    let sameElements (info: IntrinsicInfo) : bool =
        let sameKeyOperations =
            [ "sub"; "copy"; "append"; "filter"; "rev"; "sort"; "sortBy"; "sortWith"; "sortDescending"
              "take"; "skip"; "truncate"; "concat"; "distinct"; "set"; "create"; "zeroCreate"
              "blit"; "fill"; "get"; "length"; "isEmpty"; "contains"; "exists"; "forall"; "iter"; "iteri"
              "fold"; "sum"; "max"; "min"; "tryFind"; "find"; "tryFindIndex"; "findIndex"; "head"; "last" ]
        info.Module = IntrinsicModule.Array && List.contains info.Operation sameKeyOperations

    /// The array intrinsics whose elements are a function value's results, with the position
    /// of that function among the arguments.
    let elementsFromFunction (info: IntrinsicInfo) : bool =
        match info.Module, info.Operation with
        | IntrinsicModule.Array, ("init" | "map" | "mapi" | "collect" | "choose") -> true
        | _ -> false

    let functionArgument (info: IntrinsicInfo) (args: NodeId list) : NodeId option =
        match info.Module, info.Operation with
        | IntrinsicModule.Array, "init" -> List.tryItem 1 args
        | IntrinsicModule.Array, ("map" | "mapi" | "collect" | "choose") -> List.tryHead args
        | _ -> None

    let calls (info: IntrinsicInfo) : (int * Seed list) list =
        match info.Module, info.Operation with
        | IntrinsicModule.Array, "init" -> [ (1, [ Seed.IndexBelow 0 ]) ]
        | IntrinsicModule.Array, "collect" -> [ (0, [ Seed.Unknown ]) ]
        | (IntrinsicModule.Seq | IntrinsicModule.List), ("iter" | "map" | "filter" | "collect" | "tryPick" | "minBy" | "exists" | "forall" | "tryFind" | "find" | "choose") -> [ (0, [ Seed.Unknown ]) ]
        | (IntrinsicModule.Seq | IntrinsicModule.List), "fold" -> [ (0, [ Seed.Unknown; Seed.Unknown ]) ]
        | IntrinsicModule.Option, ("map" | "bind" | "iter" | "defaultWith") -> [ (0, [ Seed.Unknown ]) ]
        | _ -> []

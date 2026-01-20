// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Intrinsic resolution for F# Native.
/// This module provides proper discriminated union dispatch for intrinsics,
/// replacing the string prefix matching anti-pattern.
///
/// ARCHITECTURAL PRINCIPLE: No `name.StartsWith("X.")` dispatch.
/// Intrinsic modules are matched via proper pattern matching on IntrinsicModule.
module FSharp.Native.Compiler.NativeTypedTree.Expressions.Intrinsics

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.NativeTypedTree.UnionFind
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Core
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Builder
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Diagnostics

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
// Module-Qualified Intrinsic Parsing
//-------------------------------------------------------------------------

/// Parse "Module.operation" into (IntrinsicModule, operation) tuple.
/// Returns None if not a recognized intrinsic module prefix.
let tryParseModuleQualified (name: string) : (IntrinsicModule * string) option =
    match name.IndexOf('.') with
    | -1 -> None
    | idx ->
        let modulePart = name.Substring(0, idx)
        let opPart = name.Substring(idx + 1)
        match modulePart with
        | "NativePtr" -> Some (IntrinsicModule.NativePtr, opPart)
        | "Sys" -> Some (IntrinsicModule.Sys, opPart)
        | "String" -> Some (IntrinsicModule.String, opPart)
        | "Array" -> Some (IntrinsicModule.Array, opPart)
        | "Parse" -> Some (IntrinsicModule.Parse, opPart)
        | "Format" -> Some (IntrinsicModule.Format, opPart)
        | "Crypto" -> Some (IntrinsicModule.Crypto, opPart)
        | "Bits" -> Some (IntrinsicModule.Bits, opPart)
        | "FnPtr" -> Some (IntrinsicModule.FnPtr, opPart)
        | "Signal" -> Some (IntrinsicModule.Signal, opPart)
        | "Effect" -> Some (IntrinsicModule.Effect, opPart)
        | "Memo" -> Some (IntrinsicModule.Memo, opPart)
        | "Batch" -> Some (IntrinsicModule.Batch, opPart)
        | "Lazy" -> Some (IntrinsicModule.Lazy, opPart)
        | "Seq" -> Some (IntrinsicModule.Seq, opPart)
        | "NativeStr" -> Some (IntrinsicModule.NativeStr, opPart)
        | "NativeDefault" -> Some (IntrinsicModule.NativeDefault, opPart)
        | "Math" -> Some (IntrinsicModule.Math, opPart)
        | "Arena" -> Some (IntrinsicModule.Arena, opPart)
        | "DateTime" -> Some (IntrinsicModule.DateTime, opPart)
        | "TimeSpan" -> Some (IntrinsicModule.TimeSpan, opPart)
        | "Platform" -> Some (IntrinsicModule.Platform, opPart)
        | _ -> None

//-------------------------------------------------------------------------
// Per-Module Intrinsic Resolvers
//-------------------------------------------------------------------------

/// Resolve NativePtr.* operations
let private resolveNativePtrOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
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
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(globals.IntType, tyParam)))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "set" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(globals.IntType, NativeType.TFun(tyParam, globals.UnitType))))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "stackalloc" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(globals.IntType, NativeType.TNativePtr tyParam))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "read" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "write" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(tyParam, globals.UnitType)))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "add" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(globals.IntType, NativeType.TNativePtr tyParam)))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "copy" ->
        let ty = NativeType.TForall([tyParamSpec],
            NativeType.TFun(NativeType.TNativePtr tyParam,
                NativeType.TFun(NativeType.TNativePtr tyParam,
                    NativeType.TFun(globals.IntType, globals.UnitType))))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | "fill" ->
        let ty = NativeType.TForall([tyParamSpec],
            NativeType.TFun(NativeType.TNativePtr tyParam,
                NativeType.TFun(tyParam,
                    NativeType.TFun(globals.IntType, globals.UnitType))))
        Resolved (mkIntrinsic IntrinsicModule.NativePtr op IntrinsicCategory.Memory fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown NativePtr intrinsic: NativePtr.{unknown}"

/// Resolve Sys.* operations (system calls)
let private resolveSysOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Sys." + op
    match op with
    | "write" ->
        // fd:int -> buffer:nativeptr<byte> -> count:int -> int
        let ty = NativeType.TFun(globals.IntType,
            NativeType.TFun(NativeType.TNativePtr Types.uint8Type,
                NativeType.TFun(globals.IntType, globals.IntType)))
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "read" ->
        // fd:int -> buffer:nativeptr<byte> -> maxCount:int -> int
        let ty = NativeType.TFun(globals.IntType,
            NativeType.TFun(NativeType.TNativePtr Types.uint8Type,
                NativeType.TFun(globals.IntType, globals.IntType)))
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "exit" ->
        // code:int -> 'a (never returns, polymorphic return type)
        let tyParamSpec = freshTypeParam "'a" TypeParamKind.Type range
        let tyParam = NativeType.TVar tyParamSpec
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(globals.IntType, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "clock_gettime" ->
        // unit -> int64
        let ty = NativeType.TFun(globals.UnitType, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "clock_monotonic" ->
        // unit -> int64
        let ty = NativeType.TFun(globals.UnitType, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "tick_frequency" ->
        // unit -> int64
        let ty = NativeType.TFun(globals.UnitType, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | "nanosleep" ->
        // int -> unit
        let ty = NativeType.TFun(globals.IntType, globals.UnitType)
        Resolved (mkIntrinsic IntrinsicModule.Sys op IntrinsicCategory.Platform fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Sys intrinsic: Sys.{unknown}"

/// Resolve String.* operations
let private resolveStringOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "String." + op
    let stringType = globals.StringType
    match op with
    | "concat2" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(stringType, stringType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "length" ->
        let ty = NativeType.TFun(stringType, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "isEmpty" ->
        let ty = NativeType.TFun(stringType, globals.BoolType)
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "contains" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(globals.CharType, globals.BoolType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "startsWith" | "endsWith" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(stringType, globals.BoolType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "substring" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(globals.IntType, NativeType.TFun(globals.IntType, stringType)))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "trim" | "trimStart" | "trimEnd" | "toUpper" | "toLower" ->
        let ty = NativeType.TFun(stringType, stringType)
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "charAt" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(globals.IntType, globals.CharType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "indexOf" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(globals.CharType, globals.IntType))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | "replace" ->
        let ty = NativeType.TFun(stringType, NativeType.TFun(stringType, NativeType.TFun(stringType, stringType)))
        Resolved (mkIntrinsic IntrinsicModule.String op IntrinsicCategory.StringOp fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown String intrinsic: String.{unknown}. Available: concat2, length, isEmpty, contains, startsWith, endsWith, substring, trim, trimStart, trimEnd, toUpper, toLower, charAt, indexOf, replace"

/// Resolve Array.* operations
let private resolveArrayOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
    let tyParam = NativeType.TVar tyParamSpec
    let arrayType = mkArrayType tyParam
    let fullName = "Array." + op
    match op with
    | "zeroCreate" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(globals.IntType, arrayType))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "create" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(globals.IntType, NativeType.TFun(tyParam, arrayType)))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "init" ->
        let initFunc = NativeType.TFun(globals.IntType, tyParam)
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(globals.IntType, NativeType.TFun(initFunc, arrayType)))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "copy" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, arrayType))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "length" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, globals.IntType))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "get" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, NativeType.TFun(globals.IntType, tyParam)))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "set" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, NativeType.TFun(globals.IntType, NativeType.TFun(tyParam, globals.UnitType))))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "tryItem" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(globals.IntType, NativeType.TFun(arrayType, mkValueOptionType tyParam)))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | "isEmpty" ->
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(arrayType, globals.BoolType))
        Resolved (mkIntrinsic IntrinsicModule.Array op IntrinsicCategory.Memory fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Array intrinsic: Array.{unknown}. Available: zeroCreate, create, init, copy, length, get, set, tryItem, isEmpty"

/// Resolve Parse.* operations (string → numeric)
let private resolveParseOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Parse." + op
    match op with
    | "int" ->
        let ty = NativeType.TFun(globals.StringType, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.Parse op IntrinsicCategory.Conversion fullName, ty)
    | "int64" ->
        let ty = NativeType.TFun(globals.StringType, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.Parse op IntrinsicCategory.Conversion fullName, ty)
    | "float" ->
        let ty = NativeType.TFun(globals.StringType, globals.FloatType)
        Resolved (mkIntrinsic IntrinsicModule.Parse op IntrinsicCategory.Conversion fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Parse intrinsic: Parse.{unknown}. Available: int, int64, float"

/// Resolve Format.* operations (numeric → string)
let private resolveFormatOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Format." + op
    match op with
    | "int" ->
        let ty = NativeType.TFun(globals.IntType, globals.StringType)
        Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
    | "int64" ->
        let ty = NativeType.TFun(globals.Int64Type, globals.StringType)
        Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
    | "float" | "float64" | "double" ->
        let ty = NativeType.TFun(globals.FloatType, globals.StringType)
        Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
    | "bool" ->
        let ty = NativeType.TFun(globals.BoolType, globals.StringType)
        Resolved (mkIntrinsic IntrinsicModule.Format op IntrinsicCategory.Conversion fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Format intrinsic: Format.{unknown}. Available: int, int64, float, bool"

/// Resolve NativeStr.* operations
let private resolveNativeStrOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "NativeStr." + op
    match op with
    | "fromPointer" ->
        // ptr:nativeptr<byte> -> len:int -> string
        let ty = NativeType.TFun(NativeType.TNativePtr Types.uint8Type, NativeType.TFun(globals.IntType, globals.StringType))
        Resolved (mkIntrinsic IntrinsicModule.NativeStr op IntrinsicCategory.StringOp fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown NativeStr intrinsic: NativeStr.{unknown}"

/// Resolve NativeDefault.* operations
let private resolveNativeDefaultOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let fullName = "NativeDefault." + op
    match op with
    | "zeroed" ->
        // unit -> 'T
        let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
        let tyParam = NativeType.TVar tyParamSpec
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(globals.UnitType, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.NativeDefault op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown NativeDefault intrinsic: NativeDefault.{unknown}"

/// Resolve Crypto.* operations
let private resolveCryptoOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Crypto." + op
    let byteArrayType = mkArrayType Types.uint8Type
    match op with
    | "sha1" ->
        let ty = NativeType.TFun(byteArrayType, byteArrayType)
        Resolved (mkIntrinsic IntrinsicModule.Crypto op IntrinsicCategory.Pure fullName, ty)
    | "base64Encode" ->
        let ty = NativeType.TFun(byteArrayType, globals.StringType)
        Resolved (mkIntrinsic IntrinsicModule.Crypto op IntrinsicCategory.Pure fullName, ty)
    | "base64Decode" ->
        let ty = NativeType.TFun(globals.StringType, byteArrayType)
        Resolved (mkIntrinsic IntrinsicModule.Crypto op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Crypto intrinsic: Crypto.{unknown}. Available: sha1, base64Encode, base64Decode"

/// Resolve Bits.* operations
let private resolveBitsOp (op: string) (_globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Bits." + op
    match op with
    | "htons" | "ntohs" ->
        let ty = NativeType.TFun(Types.uint16Type, Types.uint16Type)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    | "htonl" | "ntohl" ->
        let ty = NativeType.TFun(Types.uint32Type, Types.uint32Type)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    | "float32ToInt32Bits" ->
        let ty = NativeType.TFun(Types.float32Type, Types.int32Type)
        Resolved (mkIntrinsic IntrinsicModule.Bits op IntrinsicCategory.Pure fullName, ty)
    | "int32BitsToFloat32" ->
        let ty = NativeType.TFun(Types.int32Type, Types.float32Type)
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
let private resolveFnPtrOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let fullName = "FnPtr." + op
    let freshF = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
    match op with
    | "fromSymbol" ->
        // string -> FnPtr<'F>
        let fnPtrType = mkFnPtrType freshF
        let ty = NativeType.TFun(globals.StringType, fnPtrType)
        Resolved (mkIntrinsic IntrinsicModule.FnPtr op IntrinsicCategory.Pure fullName, ty)
    | "invoke" ->
        // FnPtr<'F> -> 'F
        let fnPtrType = mkFnPtrType freshF
        let ty = NativeType.TFun(fnPtrType, freshF)
        Resolved (mkIntrinsic IntrinsicModule.FnPtr op IntrinsicCategory.Pure fullName, ty)
    | "ofFunction" ->
        // 'F -> FnPtr<'F>
        let fnPtrType = mkFnPtrType freshF
        let ty = NativeType.TFun(freshF, fnPtrType)
        Resolved (mkIntrinsic IntrinsicModule.FnPtr op IntrinsicCategory.Pure fullName, ty)
    | "isNull" | "null" ->
        // REMOVED: Violates null-safety principle
        UnknownOperation $"FnPtr.{op} has been removed. Use Option<FnPtr<'F>> for nullable function pointers."
    | unknown ->
        UnknownOperation $"Unknown FnPtr intrinsic: FnPtr.{unknown}. Available: fromSymbol, invoke, ofFunction"

/// Resolve Signal.* operations (reactive signals)
let private resolveSignalOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Signal." + op
    let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
    let tyParam = NativeType.TVar tyParamSpec
    let signalType = mkSignalType tyParam
    match op with
    | "create" ->
        // 'T -> Signal<'T>
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(tyParam, signalType))
        Resolved (mkIntrinsic IntrinsicModule.Signal op IntrinsicCategory.Pure fullName, ty)
    | "get" ->
        // Signal<'T> -> 'T
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(signalType, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.Signal op IntrinsicCategory.Pure fullName, ty)
    | "set" ->
        // Signal<'T> -> 'T -> unit
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(signalType, NativeType.TFun(tyParam, globals.UnitType)))
        Resolved (mkIntrinsic IntrinsicModule.Signal op IntrinsicCategory.Pure fullName, ty)
    | "update" ->
        // Signal<'T> -> ('T -> 'T) -> unit
        let updateFn = NativeType.TFun(tyParam, tyParam)
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(signalType, NativeType.TFun(updateFn, globals.UnitType)))
        Resolved (mkIntrinsic IntrinsicModule.Signal op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Signal intrinsic: Signal.{unknown}. Available: create, get, set, update"

/// Resolve Effect.* operations
let private resolveEffectOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Effect." + op
    match op with
    | "create" ->
        // (unit -> unit) -> Effect
        let effectFn = NativeType.TFun(globals.UnitType, globals.UnitType)
        let effectType = NativeType.TApp(effectTyCon, [])
        let ty = NativeType.TFun(effectFn, effectType)
        Resolved (mkIntrinsic IntrinsicModule.Effect op IntrinsicCategory.Pure fullName, ty)
    | "createWithCleanup" ->
        // (unit -> unit) -> (unit -> unit) -> Effect
        let effectFn = NativeType.TFun(globals.UnitType, globals.UnitType)
        let cleanupFn = NativeType.TFun(globals.UnitType, globals.UnitType)
        let effectType = NativeType.TApp(effectTyCon, [])
        let ty = NativeType.TFun(effectFn, NativeType.TFun(cleanupFn, effectType))
        Resolved (mkIntrinsic IntrinsicModule.Effect op IntrinsicCategory.Pure fullName, ty)
    | "dispose" ->
        // Effect -> unit
        let effectType = NativeType.TApp(effectTyCon, [])
        let ty = NativeType.TFun(effectType, globals.UnitType)
        Resolved (mkIntrinsic IntrinsicModule.Effect op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Effect intrinsic: Effect.{unknown}. Available: create, createWithCleanup, dispose"

/// Resolve Memo.* operations
let private resolveMemoOp (op: string) (_globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Memo." + op
    let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
    let tyParam = NativeType.TVar tyParamSpec
    let memoType = mkMemoType tyParam
    match op with
    | "create" ->
        // (unit -> 'T) -> Memo<'T>
        let computeFn = NativeType.TFun(NativeType.TApp(Primitives.unitTyCon, []), tyParam)
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(computeFn, memoType))
        Resolved (mkIntrinsic IntrinsicModule.Memo op IntrinsicCategory.Pure fullName, ty)
    | "get" ->
        // Memo<'T> -> 'T
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(memoType, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.Memo op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Memo intrinsic: Memo.{unknown}. Available: create, get"

/// Resolve Batch.* operations
let private resolveBatchOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Batch." + op
    match op with
    | "run" ->
        // (unit -> unit) -> unit
        let batchFn = NativeType.TFun(globals.UnitType, globals.UnitType)
        let ty = NativeType.TFun(batchFn, globals.UnitType)
        Resolved (mkIntrinsic IntrinsicModule.Batch op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Batch intrinsic: Batch.{unknown}. Available: run"

/// Resolve Lazy.* operations (PRD-14: Deferred computation with memoization)
let private resolveLazyOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Lazy." + op
    let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
    let tyParam = NativeType.TVar tyParamSpec
    let lazyType = mkLazyType tyParam
    match op with
    | "create" ->
        // (unit -> 'T) -> Lazy<'T>
        let thunkFn = NativeType.TFun(globals.UnitType, tyParam)
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(thunkFn, lazyType))
        Resolved (mkIntrinsic IntrinsicModule.Lazy op IntrinsicCategory.Pure fullName, ty)
    | "force" ->
        // Lazy<'T> -> 'T
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(lazyType, tyParam))
        Resolved (mkIntrinsic IntrinsicModule.Lazy op IntrinsicCategory.Pure fullName, ty)
    | "isValueCreated" ->
        // Lazy<'T> -> bool
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(lazyType, globals.BoolType))
        Resolved (mkIntrinsic IntrinsicModule.Lazy op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Lazy intrinsic: Lazy.{unknown}. Available: create, force, isValueCreated"

/// Resolve Seq.* operations (PRD-15: Sequence generation and consumption)
let private resolveSeqOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Seq." + op
    let tyParamSpecT = freshTypeParam "'T" TypeParamKind.Type range
    let tyParamT = NativeType.TVar tyParamSpecT
    let seqT = mkSeqType tyParamT
    match op with
    | "empty" ->
        // seq<'T> - Returns an empty sequence (polymorphic value)
        // PRD-16: Foundational sequence producer, added early to unblock BAREWire
        let ty = NativeType.TForall([tyParamSpecT], seqT)
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "toArray" ->
        // seq<'T> -> 'T[]
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, mkArrayType tyParamT))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "toList" ->
        // seq<'T> -> 'T list
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, mkListType tyParamT))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "iter" ->
        // ('T -> unit) -> seq<'T> -> unit
        let actionFn = NativeType.TFun(tyParamT, globals.UnitType)
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(actionFn, NativeType.TFun(seqT, globals.UnitType)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "map" ->
        // ('T -> 'U) -> seq<'T> -> seq<'U>
        let tyParamSpecU = freshTypeParam "'U" TypeParamKind.Type range
        let tyParamU = NativeType.TVar tyParamSpecU
        let mapFn = NativeType.TFun(tyParamT, tyParamU)
        let seqU = mkSeqType tyParamU
        let ty = NativeType.TForall([tyParamSpecT; tyParamSpecU], NativeType.TFun(mapFn, NativeType.TFun(seqT, seqU)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "filter" ->
        // ('T -> bool) -> seq<'T> -> seq<'T>
        let predFn = NativeType.TFun(tyParamT, globals.BoolType)
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
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(globals.IntType, NativeType.TFun(seqT, seqT)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "collect" ->
        // ('T -> seq<'U>) -> seq<'T> -> seq<'U>
        // PRD-16: flatMap - maps each element to a sequence, then flattens
        let tyParamSpecU = freshTypeParam "'U" TypeParamKind.Type range
        let tyParamU = NativeType.TVar tyParamSpecU
        let mapperFn = NativeType.TFun(tyParamT, mkSeqType tyParamU)
        let seqU = mkSeqType tyParamU
        let ty = NativeType.TForall([tyParamSpecT; tyParamSpecU], NativeType.TFun(mapperFn, NativeType.TFun(seqT, seqU)))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "isEmpty" ->
        // seq<'T> -> bool
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, globals.BoolType))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "head" ->
        // seq<'T> -> 'T
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, tyParamT))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | "length" ->
        // seq<'T> -> int
        let ty = NativeType.TForall([tyParamSpecT], NativeType.TFun(seqT, globals.IntType))
        Resolved (mkIntrinsic IntrinsicModule.Seq op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Seq intrinsic: Seq.{unknown}. Available: empty, toArray, toList, iter, map, filter, fold, take, collect, isEmpty, head, length"

/// Resolve Math.* operations
let private resolveMathOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "Math." + op
    match op with
    | "abs" | "sqrt" | "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "exp" | "log" | "log10" | "floor" | "ceiling" | "round" ->
        let ty = NativeType.TFun(globals.FloatType, globals.FloatType)
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | "pow" | "atan2" | "min" | "max" ->
        let ty = NativeType.TFun(globals.FloatType, NativeType.TFun(globals.FloatType, globals.FloatType))
        Resolved (mkIntrinsic IntrinsicModule.Math op IntrinsicCategory.Arithmetic fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Math intrinsic: Math.{unknown}"

/// Resolve Arena.* operations (deterministic memory allocation)
let private resolveArenaOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Arena." + op
    // Create fresh measure parameter for lifetime tracking
    let lifetimeParam = freshTypeParam "'lifetime" TypeParamKind.Measure range
    let lifetimeMeasure = NativeType.TMeasure (MVar lifetimeParam)
    let arenaType = mkArenaType lifetimeMeasure
    let arenaByrefType = NativeType.TByref(arenaType, ByrefKind.InOut)
    match op with
    | "fromPointer" ->
        // nativeint -> int -> Arena<'lifetime>
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(Types.nintType,
                NativeType.TFun(globals.IntType, arenaType)))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | "alloc" ->
        // Arena<'lifetime> byref -> int -> nativeint
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(arenaByrefType,
                NativeType.TFun(globals.IntType, Types.nintType)))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | "allocAligned" ->
        // Arena<'lifetime> byref -> int -> int -> nativeint
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(arenaByrefType,
                NativeType.TFun(globals.IntType,
                    NativeType.TFun(globals.IntType, Types.nintType))))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | "remaining" ->
        // Arena<'lifetime> -> int
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(arenaType, globals.IntType))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | "reset" ->
        // Arena<'lifetime> byref -> unit
        let ty = NativeType.TForall([lifetimeParam],
            NativeType.TFun(arenaByrefType, globals.UnitType))
        Resolved (mkIntrinsic IntrinsicModule.Arena op IntrinsicCategory.Memory fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Arena intrinsic: Arena.{unknown}. Available: fromPointer, alloc, allocAligned, remaining, reset"

/// Resolve DateTime.* operations (BCL-compatible date/time)
let private resolveDateTimeOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "DateTime." + op
    match op with
    // Static constructors
    | "now" ->
        // unit -> int64 (milliseconds since Unix epoch)
        let ty = NativeType.TFun(globals.UnitType, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    | "utcNow" ->
        // unit -> int64 (milliseconds since Unix epoch, same as now for UTC)
        let ty = NativeType.TFun(globals.UnitType, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    // Component extractors (from milliseconds since epoch)
    | "hour" ->
        // int64 -> int (0-23)
        let ty = NativeType.TFun(globals.Int64Type, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Arithmetic fullName, ty)
    | "minute" ->
        // int64 -> int (0-59)
        let ty = NativeType.TFun(globals.Int64Type, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Arithmetic fullName, ty)
    | "second" ->
        // int64 -> int (0-59)
        let ty = NativeType.TFun(globals.Int64Type, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Arithmetic fullName, ty)
    | "millisecond" ->
        // int64 -> int (0-999)
        let ty = NativeType.TFun(globals.Int64Type, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Arithmetic fullName, ty)
    // Timezone / Local time
    | "utcOffset" ->
        // unit -> int (local timezone offset in seconds from UTC, e.g., -18000 for EST)
        // Uses platform localtime_r() to get tm_gmtoff
        let ty = NativeType.TFun(globals.UnitType, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    | "toLocal" ->
        // int64 -> int64 (converts UTC milliseconds to local milliseconds)
        // Mirrors BCL DateTime.ToLocalTime() pattern
        let ty = NativeType.TFun(globals.Int64Type, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    | "toUtc" ->
        // int64 -> int64 (converts local milliseconds to UTC milliseconds)
        // Mirrors BCL DateTime.ToUniversalTime() pattern
        let ty = NativeType.TFun(globals.Int64Type, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.Platform fullName, ty)
    // Formatting
    | "toTimeString" ->
        // int64 -> int -> string (ms since epoch, tzOffset -> "HH:MM:SS.mmm")
        let ty = NativeType.TFun(globals.Int64Type, NativeType.TFun(globals.IntType, globals.StringType))
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.StringOp fullName, ty)
    | "toDateString" ->
        // int64 -> int -> string (ms since epoch, tzOffset -> "YYYY-MM-DD")
        let ty = NativeType.TFun(globals.Int64Type, NativeType.TFun(globals.IntType, globals.StringType))
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.StringOp fullName, ty)
    | "toString" ->
        // int64 -> int -> string (ms since epoch, tzOffset -> "YYYY-MM-DD HH:MM:SS")
        let ty = NativeType.TFun(globals.Int64Type, NativeType.TFun(globals.IntType, globals.StringType))
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.StringOp fullName, ty)
    | "toDateTimeString" ->
        // int64 -> int -> string (ms since epoch, tzOffset -> "YYYY-MM-DDTHH:MM:SS.mmm")
        // Full ISO 8601 style datetime with milliseconds
        let ty = NativeType.TFun(globals.Int64Type, NativeType.TFun(globals.IntType, globals.StringType))
        Resolved (mkIntrinsic IntrinsicModule.DateTime op IntrinsicCategory.StringOp fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown DateTime intrinsic: DateTime.{unknown}. Available: now, utcNow, hour, minute, second, millisecond, utcOffset, toLocal, toUtc, toTimeString, toDateString, toString, toDateTimeString"

/// Resolve TimeSpan.* operations
let private resolveTimeSpanOp (op: string) (globals: NativeGlobals) (_range: SourceRange) : IntrinsicResolution =
    let fullName = "TimeSpan." + op
    match op with
    // Constructors (return milliseconds as int64)
    | "fromMilliseconds" ->
        // int64 -> int64
        let ty = NativeType.TFun(globals.Int64Type, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "fromSeconds" ->
        // int64 -> int64 (converts to milliseconds)
        let ty = NativeType.TFun(globals.Int64Type, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "fromMinutes" ->
        // int64 -> int64 (converts to milliseconds)
        let ty = NativeType.TFun(globals.Int64Type, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "fromHours" ->
        // int64 -> int64 (converts to milliseconds)
        let ty = NativeType.TFun(globals.Int64Type, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    // Component extractors (from milliseconds)
    | "totalMilliseconds" ->
        // int64 -> int64 (identity for internal representation)
        let ty = NativeType.TFun(globals.Int64Type, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "totalSeconds" ->
        // int64 -> int64 (ms / 1000)
        let ty = NativeType.TFun(globals.Int64Type, globals.Int64Type)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "hours" ->
        // int64 -> int (hours component)
        let ty = NativeType.TFun(globals.Int64Type, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "minutes" ->
        // int64 -> int (minutes component 0-59)
        let ty = NativeType.TFun(globals.Int64Type, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "seconds" ->
        // int64 -> int (seconds component 0-59)
        let ty = NativeType.TFun(globals.Int64Type, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | "milliseconds" ->
        // int64 -> int (milliseconds component 0-999)
        let ty = NativeType.TFun(globals.Int64Type, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.TimeSpan op IntrinsicCategory.Arithmetic fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown TimeSpan intrinsic: TimeSpan.{unknown}. Available: fromMilliseconds, fromSeconds, fromMinutes, fromHours, totalMilliseconds, totalSeconds, hours, minutes, seconds, milliseconds"

/// Resolve Platform.* operations (compile-time platform introspection)
let private resolvePlatformOp (op: string) (globals: NativeGlobals) (range: SourceRange) : IntrinsicResolution =
    let fullName = "Platform." + op
    match op with
    | "sizeof" ->
        // sizeof<'T> : int - returns size of type in bytes
        // Polymorphic: forall 'T. unit -> int
        // Alex resolves 'T to compute size based on target architecture
        let tyParamSpec = freshTypeParam "'T" TypeParamKind.Type range
        let ty = NativeType.TForall([tyParamSpec], NativeType.TFun(globals.UnitType, globals.IntType))
        Resolved (mkIntrinsic IntrinsicModule.Platform op IntrinsicCategory.Pure fullName, ty)
    | "wordSize" ->
        // wordSize : unit -> int - returns platform word size in bytes (8 on x86_64, 4 on 32-bit)
        // Function form for consistency with other intrinsics and Architecture integration
        let ty = NativeType.TFun(globals.UnitType, globals.IntType)
        Resolved (mkIntrinsic IntrinsicModule.Platform op IntrinsicCategory.Pure fullName, ty)
    | unknown ->
        UnknownOperation $"Unknown Platform intrinsic: Platform.{unknown}. Available: sizeof, wordSize"

//-------------------------------------------------------------------------
// Main Module Intrinsic Dispatcher
//-------------------------------------------------------------------------

/// Resolve a module-qualified intrinsic using proper pattern matching.
/// This is the main dispatch function - NO string prefix matching.
let resolveModuleIntrinsic
    (modl: IntrinsicModule)
    (op: string)
    (globals: NativeGlobals)
    (range: SourceRange)
    : IntrinsicResolution =

    match modl with
    | IntrinsicModule.NativePtr -> resolveNativePtrOp op globals range
    | IntrinsicModule.Sys -> resolveSysOp op globals range
    | IntrinsicModule.String -> resolveStringOp op globals range
    | IntrinsicModule.Array -> resolveArrayOp op globals range
    | IntrinsicModule.Parse -> resolveParseOp op globals range
    | IntrinsicModule.Format -> resolveFormatOp op globals range
    | IntrinsicModule.NativeStr -> resolveNativeStrOp op globals range
    | IntrinsicModule.NativeDefault -> resolveNativeDefaultOp op globals range
    | IntrinsicModule.Crypto -> resolveCryptoOp op globals range
    | IntrinsicModule.Bits -> resolveBitsOp op globals range
    | IntrinsicModule.FnPtr -> resolveFnPtrOp op globals range
    | IntrinsicModule.Signal -> resolveSignalOp op globals range
    | IntrinsicModule.Effect -> resolveEffectOp op globals range
    | IntrinsicModule.Memo -> resolveMemoOp op globals range
    | IntrinsicModule.Batch -> resolveBatchOp op globals range
    | IntrinsicModule.Lazy -> resolveLazyOp op globals range
    | IntrinsicModule.Seq -> resolveSeqOp op globals range
    | IntrinsicModule.Arena -> resolveArenaOp op globals range
    | IntrinsicModule.Math -> resolveMathOp op globals range
    | IntrinsicModule.DateTime -> resolveDateTimeOp op globals range
    | IntrinsicModule.TimeSpan -> resolveTimeSpanOp op globals range
    | IntrinsicModule.Platform -> resolvePlatformOp op globals range
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
    | "op_Addition" | "op_Subtraction" | "op_Multiply" | "op_Division" | "op_Modulus" ->
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
    | _ -> None

/// Check if a name is an operator that should be an intrinsic
/// Used for hard error reporting when an operator is not recognized
let isOperatorName (name: string) : bool =
    name.StartsWith("op_") || name = "not"

//-------------------------------------------------------------------------
// Conversion Intrinsics
//-------------------------------------------------------------------------

/// Try to resolve a type conversion intrinsic (float, int, int64, byte, etc.)
let tryResolveConversion (name: string) (globals: NativeGlobals) (range: SourceRange) : (IntrinsicInfo * NativeType) option =
    let mkConvIntrinsic op resultType =
        let tyParam = NativeType.TVar (freshTypeParamAuto TypeParamKind.Type range)
        let info = mkIntrinsic IntrinsicModule.Convert op IntrinsicCategory.Conversion name
        let ty = NativeType.TFun(tyParam, resultType)
        Some (info, ty)

    match name with
    | "float" | "float64" | "double" -> mkConvIntrinsic "toFloat" globals.FloatType
    | "int" | "int32" -> mkConvIntrinsic "toInt" globals.IntType
    | "int64" -> mkConvIntrinsic "toInt64" globals.Int64Type
    | "byte" | "uint8" -> mkConvIntrinsic "toByte" Types.uint8Type
    | "sbyte" | "int8" -> mkConvIntrinsic "toSByte" Types.int8Type
    | "int16" -> mkConvIntrinsic "toInt16" Types.int16Type
    | "uint16" -> mkConvIntrinsic "toUInt16" Types.uint16Type
    | "uint32" -> mkConvIntrinsic "toUInt32" Types.uint32Type
    | "uint64" -> mkConvIntrinsic "toUInt64" Types.uint64Type
    | "float32" | "single" -> mkConvIntrinsic "toFloat32" Types.float32Type
    | "char" -> mkConvIntrinsic "toChar" globals.CharType
    | "nativeint" -> mkConvIntrinsic "toNativeInt" Types.nintType
    | "unativeint" -> mkConvIntrinsic "toUNativeInt" Types.unintType
    | _ -> None

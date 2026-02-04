// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker String Recipes - Decomposition of String operations to primitives.
///
/// MEMREF SEMANTICS (January 2026):
/// Strings ARE memrefs (memref<?xi8>), not fat pointer structs.
/// Simple operations (length, isEmpty) remain ATOMIC - witnessed directly by Alex.
/// Complex operations (concat2) decompose to memory primitives.
///
/// COMBINATOR MODEL:
/// String.concat2 expands to: String.length calls, stackalloc, memcpy, pointer arithmetic,
/// and NativeStr.fromPointer (identity in MLIR - buffer IS the string).
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
/// See: Serena memory "mlir_memref_strings_no_llvm_cruft"
module FSharp.Native.Compiler.Baker.Recipes.StringRecipes

open XParsec.Parsers
open FSharp.Native.Compiler.NativeTypedTree.NativeTypes

open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Baker.Recipes.Decomposition
open FSharp.Native.Compiler.Baker.Ingredients.SaturationCombinators
open FSharp.Native.Compiler.Baker.Ingredients.Primitives

//=============================================================================
// BRIDGE: Convert SaturationParser results to Decomposition.Result
//=============================================================================

/// Convert a Decomposition.Context to a SaturationState
let private toSaturationState (ctx: Context) : SaturationState =
    { EmittedNodes = []
      Bindings = Map.empty
      ExpansionId = ctx.ExpansionId
      OriginalHOF = ctx.OriginalHOF
      SourceRange = ctx.SourceRange
      InspiringNode = ctx.InspiringNode
      Platform = ctx.Platform }

/// Run a saturation parser and convert to Decomposition.Result
let private runSaturation (ctx: Context) (parser: SaturationParser<NodeId>) : Result =
    let initialState = toSaturationState ctx
    let result, nodes = run initialState parser
    match result with
    | Matched resultNodeId ->
        mkResultNoShadow nodes resultNodeId []
    | NoMatch reason ->
        failwithf "Saturation failed: %s" reason

//=============================================================================
// STRING.CONCAT2: lhs + rhs → allocate buffer, copy both strings
//=============================================================================

let private stringConcat2Recipe
    (lhsId: NodeId)
    (rhsId: NodeId)
    (stringType: NativeType)
    : SaturationParser<NodeId> =

    saturation {
        // MEMREF SEMANTICS (January 2026):
        // Input strings ARE memrefs (memref<?xi8>), not fat pointer structs.
        // No field extraction needed - use memrefs directly as source buffers.
        // Result is also a memref - no struct wrapping.

        // Get lengths via String.length intrinsic (generates memref.dim in MLIR)
        // Create String.length Application for lhs
        let! lhsState = getUserState
        let lengthFuncType = NativeType.TFun(Types.stringType, Types.intType)
        let lengthInfo = { Module = IntrinsicModule.String; Operation = "length"; Category = IntrinsicCategory.Pure; FullName = "String.length" }
        let lhsLengthFunc = mkNode lhsState (SemanticKind.Intrinsic lengthInfo) lengthFuncType []
        do! emit lhsLengthFunc
        let! lhsState' = getUserState
        let lhsLengthApp = mkNode lhsState' (SemanticKind.Application (lhsLengthFunc.Id, [lhsId])) Types.intType [lhsLengthFunc.Id; lhsId]
        do! emit lhsLengthApp
        let lhsLen = lhsLengthApp.Id

        // Create String.length Application for rhs
        let! rhsState = getUserState
        let rhsLengthFunc = mkNode rhsState (SemanticKind.Intrinsic lengthInfo) lengthFuncType []
        do! emit rhsLengthFunc
        let! rhsState' = getUserState
        let rhsLengthApp = mkNode rhsState' (SemanticKind.Application (rhsLengthFunc.Id, [rhsId])) Types.intType [rhsLengthFunc.Id; rhsId]
        do! emit rhsLengthApp
        let rhsLen = rhsLengthApp.Id

        // Compute combined length
        let! combinedLen = add lhsLen rhsLen Types.intType

        // Allocate result buffer (stackalloc creates memref<?xi8> with combinedLen)
        let! resultPtr = stackAlloc combinedLen Types.uint8Type

        // Copy lhs memref to beginning of result buffer (CAPTURE node ID for control flow)
        let! memcpy1 = memcpy resultPtr lhsId lhsLen Types.uint8Type

        // Compute offset pointer (resultPtr + lhsLen)
        let! offsetPtr = ptrAdd resultPtr lhsLen Types.uint8Type

        // Copy rhs memref after lhs (CAPTURE node ID for control flow)
        let! memcpy2 = memcpy offsetPtr rhsId rhsLen Types.uint8Type

        // MEMREF RESULT: Use NativeStr.fromPointer to create string from buffer.
        // This establishes control-flow dependency: memcpy ops execute before result.
        // NativeStr.fromPointer is witnessed in Alex as identity (buffer IS the string).
        // Include memcpy1 and memcpy2 as children to ensure they execute first.
        let! finalState = getUserState
        let fromPtrFuncType = NativeType.TFun(Types.nintType, NativeType.TFun(Types.intType, stringType))
        let fromPtrInfo = { Module = IntrinsicModule.NativeStr; Operation = "fromPointer"; Category = IntrinsicCategory.Pure; FullName = "NativeStr.fromPointer" }
        let fromPtrFunc = mkNode finalState (SemanticKind.Intrinsic fromPtrInfo) fromPtrFuncType []
        do! emit fromPtrFunc
        let! finalState' = getUserState
        // Children: prerequisites first (memcpy1, memcpy2), then function and args
        let fromPtrApp = mkNode finalState' (SemanticKind.Application (fromPtrFunc.Id, [resultPtr; combinedLen])) stringType [memcpy1; memcpy2; fromPtrFunc.Id; resultPtr; combinedLen]
        do! emit fromPtrApp
        return fromPtrApp.Id
    }

//=============================================================================
// STRING.LENGTH & STRING.ISEMPTY: Atomic intrinsics (not decomposed)
//=============================================================================
//
// In memref semantics, String.length and String.isEmpty are ATOMIC operations
// witnessed directly by Alex (generate memref.dim + optional comparison).
//
// These operations do NOT decompose - they remain as Application nodes in PSG
// and are handled by ApplicationWitness in Alex/Witnesses/ApplicationWitness.fs.
//
// This is architecturally correct: memref operations are primitives, not compositions.

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// Try to decompose a String operation
let tryDecompose
    (ctx: Context)
    (operation: string)
    (args: NodeId list)
    (_inputType: NativeType)
    (_outputType: NativeType option)
    : Result option =

    match operation, args with
    // String.concat2: lhs + rhs
    | "concat2", [lhs; rhs] ->
        Some (runSaturation ctx (stringConcat2Recipe lhs rhs Types.stringType))

    | "concat2", _ ->
        None  // Wrong arg count

    // String.length: ATOMIC INTRINSIC (not decomposed)
    // In memref semantics, String.length generates memref.dim directly in Alex.
    // No decomposition needed - strings ARE memrefs, length is intrinsic to descriptor.
    | "length", _ ->
        None  // Not decomposed - witnessed as atomic intrinsic by Alex

    // String.isEmpty: ATOMIC INTRINSIC (not decomposed)
    // In memref semantics, String.isEmpty uses memref.dim + comparison in Alex.
    // No decomposition needed - composite atomic operation.
    | "isEmpty", _ ->
        None  // Not decomposed - witnessed as atomic intrinsic by Alex

    // Other string operations - not handled by intrinsic elaboration (handled by Alex)
    | "contains", _
    | "startsWith", _
    | "endsWith", _
    | "substring", _
    | "trim", _
    | "trimStart", _
    | "trimEnd", _
    | "toUpper", _
    | "toLower", _
    | "charAt", _
    | "indexOf", _
    | "replace", _
    | "concat", _
    | "toBytes", _
    | "fromBytes", _ ->
        None  // Alex handles these

    | _, _ ->
        None  // Unknown operation

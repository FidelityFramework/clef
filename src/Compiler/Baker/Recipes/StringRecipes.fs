// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
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
module Clef.Compiler.Baker.Recipes.StringRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

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
// STRING OPERATIONS: Atomic intrinsics (not decomposed)
//=============================================================================
//
// In memref semantics, String operations (length, isEmpty, concat2) are ATOMIC
// operations witnessed directly by Alex using pure memref operations.
//
// - String.length: memref.dim (returns index, cast to i64 at F# boundary)
// - String.isEmpty: memref.dim + comparison
// - String.concat2: memref.dim + arith.addi (index) + memref.alloc + memcpy
//
// These operations do NOT decompose - they remain as Application nodes in PSG
// and are handled by ApplicationWitness in Alex/Witnesses/ApplicationWitness.fs.
//
// This is architecturally correct: memref operations are primitives, not compositions.
// NO i64 arithmetic for internal operations - pure index throughout.

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// Try to decompose a String operation
let tryDecompose
    (_ctx: Context)
    (operation: string)
    (args: NodeId list)
    (_inputType: NativeType)
    (_outputType: NativeType option)
    : Result option =

    match operation, args with
    // String.concat2: ATOMIC INTRINSIC (not decomposed)
    // In memref semantics, String.concat2 is witnessed directly by Alex.
    // Generates: memref.dim + arith.addi (index) + memref.alloc + memcpy
    // NO i64 arithmetic - pure index operations throughout
    | "concat2", _ ->
        None  // Alex handles this with pure memref operations

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

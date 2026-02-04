// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker String Recipes - Decomposition of String operations to primitives.
///
/// String operations decompose to memory operations since strings are fat pointers
/// with {ptr: nativeptr<byte>, len: int} representation.
///
/// COMBINATOR MODEL:
/// Each recipe composes patterns from Ingredients/ primitives.
/// String.concat2 expands to: field extraction, stackalloc, memcpy, pointer arithmetic,
/// and record construction.
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
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
        // Extract pointers and lengths from fat pointer strings
        let! lhsPtr = fieldGet lhsId "ptr" Types.nintType   // nativeptr<byte>
        let! lhsLen = fieldGet lhsId "len" Types.intType
        let! rhsPtr = fieldGet rhsId "ptr" Types.nintType
        let! rhsLen = fieldGet rhsId "len" Types.intType

        // Compute combined length
        let! combinedLen = add lhsLen rhsLen Types.intType

        // Allocate result buffer on stack (returns nativeptr<byte>)
        let! resultPtr = stackAlloc combinedLen Types.uint8Type

        // Copy lhs string to beginning of buffer (CAPTURE node ID)
        let! memcpy1 = memcpy resultPtr lhsPtr lhsLen Types.uint8Type

        // Compute offset pointer (resultPtr + lhsLen)
        let! offsetPtr = ptrAdd resultPtr lhsLen Types.uint8Type

        // Copy rhs string after lhs (CAPTURE node ID)
        let! memcpy2 = memcpy offsetPtr rhsPtr rhsLen Types.uint8Type

        // Build result string fat pointer with side-effect prerequisites
        // The memcpy operations must be witnessed before the RecordExpr
        return! buildRecordWithPrereqs
            [("ptr", resultPtr); ("len", combinedLen)]
            [memcpy1; memcpy2]  // Control-flow prerequisites
            stringType
    }

//=============================================================================
// STRING.LENGTH: Extract .len field from fat pointer
//=============================================================================

let private stringLengthRecipe (strId: NodeId) : SaturationParser<NodeId> =
    saturation {
        // Extract len field from fat pointer string
        let! len = fieldGet strId "len" Types.intType
        return len
    }

//=============================================================================
// STRING.ISEMPTY: Check if len == 0
//=============================================================================

let private stringIsEmptyRecipe (strId: NodeId) : SaturationParser<NodeId> =
    saturation {
        // Extract len field
        let! len = fieldGet strId "len" Types.intType

        // Create literal 0
        let! state = getUserState
        let zeroNode = mkNode state (SemanticKind.Literal (NativeLiteral.Int (0L, NTUKind.NTUint32))) Types.intType []
        do! emit zeroNode

        // Compare len == 0
        let! isZero = eq len zeroNode.Id Types.boolType
        return isZero
    }

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

    // String.length: extract .len field
    | "length", [str] ->
        Some (runSaturation ctx (stringLengthRecipe str))

    | "length", _ ->
        None  // Wrong arg count

    // String.isEmpty: check len == 0
    | "isEmpty", [str] ->
        Some (runSaturation ctx (stringIsEmptyRecipe str))

    | "isEmpty", _ ->
        None  // Wrong arg count

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

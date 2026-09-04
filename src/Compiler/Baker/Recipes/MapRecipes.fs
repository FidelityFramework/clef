// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Baker Map Recipes - Decomposition of Map HOFs to AVL tree primitives.
///
/// Map is represented as an AVL tree with nodes: {key, value, left, right, height}
/// Empty map = null pointer
///
/// PRIMITIVE OPERATIONS (Alex witnesses directly):
/// - empty: returns null pointer
/// - isEmpty: null check
/// - node: create AVL node (arena alloc + struct construct)
/// - key, value, left, right, height: field access (GEP + load)
///
/// HOF OPERATIONS (Baker decomposes via combinators):
/// - toList, tryFind, add, containsKey, keys, values, forall
///
/// COMBINATOR MODEL:
/// Each recipe composes patterns from Ingredients/ (AVL tree patterns).
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "collection_machinery_architecture"
module Clef.Compiler.Baker.Recipes.MapRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Patterns

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
// MAP.TOLIST: toList m → in-order traversal to list of (key, value) pairs
//=============================================================================

let private mapToListParser
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    // Use the AVL in-order traversal pattern
    inOrderTraversalMap mapNodeId keyType valueType

//=============================================================================
// MAP.TOSEQ: toSeq m → lazy in-order traversal yielding (key, value) pairs
// PRD-16: Returns seq<'K * 'V> for lazy enumeration
//=============================================================================

let private mapToSeqParser
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    // Use the lazy in-order seq traversal pattern for pairs
    inOrderPairsSeq mapNodeId keyType valueType

//=============================================================================
// MAP.TRYFIND: tryFind k m → binary search returning Option<value>
//=============================================================================

let private mapTryFindParser
    (keyNodeId: NodeId)
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =
    
    // Use the AVL binary search pattern
    binarySearchMap keyNodeId mapNodeId keyType valueType

//=============================================================================
// MAP.ADD: add k v m → AVL insertion with (simplified) rebalancing
//=============================================================================

let private mapAddParser
    (keyNodeId: NodeId)
    (valueNodeId: NodeId)
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =
    
    // Use the AVL insert pattern
    avlInsertMap keyNodeId valueNodeId mapNodeId keyType valueType

//=============================================================================
// MAP.CONTAINSKEY: containsKey k m → binary search returning bool
//=============================================================================

let private mapContainsKeyParser
    (keyNodeId: NodeId)
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =
    
    // Implement as isSome (tryFind k m)
    saturation {
        let! optionResult = binarySearchMap keyNodeId mapNodeId keyType valueType
        return! isSome optionResult valueType
    }

//=============================================================================
// MAP.KEYS: keys m → lazy seq of keys via in-order traversal
// PRD-16: Returns seq<'K> for lazy enumeration
//=============================================================================

let private mapKeysParser
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    // Use the in-order seq traversal pattern
    inOrderKeysSeq mapNodeId keyType valueType

//=============================================================================
// MAP.VALUES: values m → lazy seq of values via in-order traversal
// PRD-16: Returns seq<'V> for lazy enumeration
//=============================================================================

let private mapValuesParser
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    // Use the in-order seq traversal pattern
    inOrderValuesSeq mapNodeId keyType valueType

//=============================================================================
// MAP.FORALL: forall p m → check predicate on all (key, value) pairs
//=============================================================================

let private mapForallParser
    (predicateNodeId: NodeId)
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =
    
    // Use the AVL forall pattern
    treeForallMap predicateNodeId mapNodeId keyType valueType

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// Try to decompose a Map HOF operation
let tryDecompose
    (ctx: Context)
    (operation: string)
    (args: NodeId list)
    (keyType: NativeType)
    (valueType: NativeType)
    : Result option =
    
    match operation, args with
    | "toList", [m] ->
        Some (runSaturation ctx (mapToListParser m keyType valueType))

    | "toSeq", [m] ->
        Some (runSaturation ctx (mapToSeqParser m keyType valueType))

    | "tryFind", [k; m] ->
        Some (runSaturation ctx (mapTryFindParser k m keyType valueType))
    
    | "add", [k; v; m] ->
        Some (runSaturation ctx (mapAddParser k v m keyType valueType))
    
    | "containsKey", [k; m] ->
        Some (runSaturation ctx (mapContainsKeyParser k m keyType valueType))
    
    | "keys", [m] ->
        Some (runSaturation ctx (mapKeysParser m keyType valueType))
    
    | "values", [m] ->
        Some (runSaturation ctx (mapValuesParser m keyType valueType))
    
    | "forall", [p; m] ->
        Some (runSaturation ctx (mapForallParser p m keyType valueType))
    
    // Primitive operations - Alex witnesses directly
    | "empty", _
    | "isEmpty", _ -> None
    
    | _ -> None

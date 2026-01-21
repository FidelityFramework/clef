// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
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
module FSharp.Native.Compiler.Baker.Recipes.MapRecipes

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Baker.Recipes.Decomposition
open FSharp.Native.Compiler.Baker.ShadowAST
open FSharp.Native.Compiler.Baker.Ingredients.RecipeBuilder
open FSharp.Native.Compiler.Baker.Ingredients.Primitives
open FSharp.Native.Compiler.Baker.Ingredients.Patterns

//=============================================================================
// BRIDGE: Convert Recipe results to Decomposition.Result
//=============================================================================

/// Convert a Decomposition.Context to a RecipeBuilder.RecipeContext
let private toRecipeContext (ctx: Context) : RecipeContext =
    { SourceRange = ctx.SourceRange
      OriginalHOF = ctx.OriginalHOF
      ExpansionId = ctx.ExpansionId
      InspiringNode = ctx.InspiringNode
      Platform = ctx.Platform }

/// Run a recipe and convert to Decomposition.Result
let private runRecipe (ctx: Context) (recipe: Recipe<NodeId>) : Result =
    let recipeCtx = toRecipeContext ctx
    let resultNodeId, nodes = run recipeCtx recipe
    mkResultNoShadow nodes resultNodeId []

//=============================================================================
// MAP.TOLIST: toList m → in-order traversal to list of (key, value) pairs
//=============================================================================

let private mapToListRecipe
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =

    // Use the AVL in-order traversal pattern
    inOrderTraversalMap mapNodeId keyType valueType

//=============================================================================
// MAP.TOSEQ: toSeq m → lazy in-order traversal yielding (key, value) pairs
// PRD-16: Returns seq<'K * 'V> for lazy enumeration
//=============================================================================

let private mapToSeqRecipe
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =

    // Use the lazy in-order seq traversal pattern for pairs
    inOrderPairsSeq mapNodeId keyType valueType

//=============================================================================
// MAP.TRYFIND: tryFind k m → binary search returning Option<value>
//=============================================================================

let private mapTryFindRecipe
    (keyNodeId: NodeId)
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =
    
    // Use the AVL binary search pattern
    binarySearchMap keyNodeId mapNodeId keyType valueType

//=============================================================================
// MAP.ADD: add k v m → AVL insertion with (simplified) rebalancing
//=============================================================================

let private mapAddRecipe
    (keyNodeId: NodeId)
    (valueNodeId: NodeId)
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =
    
    // Use the AVL insert pattern
    avlInsertMap keyNodeId valueNodeId mapNodeId keyType valueType

//=============================================================================
// MAP.CONTAINSKEY: containsKey k m → binary search returning bool
//=============================================================================

let private mapContainsKeyRecipe
    (keyNodeId: NodeId)
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =
    
    // Implement as isSome (tryFind k m)
    recipe {
        let! optionResult = binarySearchMap keyNodeId mapNodeId keyType valueType
        return! isSome optionResult valueType
    }

//=============================================================================
// MAP.KEYS: keys m → lazy seq of keys via in-order traversal
// PRD-16: Returns seq<'K> for lazy enumeration
//=============================================================================

let private mapKeysRecipe
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =

    // Use the in-order seq traversal pattern
    inOrderKeysSeq mapNodeId keyType valueType

//=============================================================================
// MAP.VALUES: values m → lazy seq of values via in-order traversal
// PRD-16: Returns seq<'V> for lazy enumeration
//=============================================================================

let private mapValuesRecipe
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =

    // Use the in-order seq traversal pattern
    inOrderValuesSeq mapNodeId keyType valueType

//=============================================================================
// MAP.FORALL: forall p m → check predicate on all (key, value) pairs
//=============================================================================

let private mapForallRecipe
    (predicateNodeId: NodeId)
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =
    
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
        Some (runRecipe ctx (mapToListRecipe m keyType valueType))

    | "toSeq", [m] ->
        Some (runRecipe ctx (mapToSeqRecipe m keyType valueType))

    | "tryFind", [k; m] ->
        Some (runRecipe ctx (mapTryFindRecipe k m keyType valueType))
    
    | "add", [k; v; m] ->
        Some (runRecipe ctx (mapAddRecipe k v m keyType valueType))
    
    | "containsKey", [k; m] ->
        Some (runRecipe ctx (mapContainsKeyRecipe k m keyType valueType))
    
    | "keys", [m] ->
        Some (runRecipe ctx (mapKeysRecipe m keyType valueType))
    
    | "values", [m] ->
        Some (runRecipe ctx (mapValuesRecipe m keyType valueType))
    
    | "forall", [p; m] ->
        Some (runRecipe ctx (mapForallRecipe p m keyType valueType))
    
    // Primitive operations - Alex witnesses directly
    | "empty", _
    | "isEmpty", _ -> None
    
    | _ -> None

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
// MAP.KEYS: keys m → list of keys via in-order traversal
//=============================================================================

let private mapKeysRecipe
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =
    
    let mapType = NativeType.TMap (keyType, valueType)
    let keyListType = NativeType.TList keyType
    let loopFuncType = NativeType.TFun (mapType, keyListType)
    
    recipe {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! bindVariable "tree" treeParamId mapType
        
        // Base case: []
        let! emptyListId = emptyList keyType
        
        // Guard: isEmpty tree
        let! isEmptyId = mapIsEmpty treeParamId keyType valueType
        
        // Get key, left, right
        let! nodeKeyId = mapKey treeParamId keyType valueType
        let! leftId = mapLeft treeParamId keyType valueType
        let! rightId = mapRight treeParamId keyType valueType
        
        // Recursive calls
        let! loopRefLeft = varRef "keys" None loopFuncType
        let! leftKeysId = app1 loopRefLeft leftId keyListType
        
        let! loopRefRight = varRef "keys" None loopFuncType
        let! rightKeysId = app1 loopRefRight rightId keyListType
        
        // Create singleton list: [key]
        let! singletonId = cons nodeKeyId emptyListId keyType
        
        // Concatenate: leftKeys @ [key] @ rightKeys
        let appendInfo = {
            Module = IntrinsicModule.List
            Operation = "append"
            Category = IntrinsicCategory.Pure
            FullName = "List.append"
        }
        let appendFuncType = NativeType.TFun (keyListType, NativeType.TFun (keyListType, keyListType))
        let! appendFunc1 = createAndEmit (SemanticKind.Intrinsic appendInfo) appendFuncType
        let! midResultId = app2 appendFunc1 leftKeysId singletonId keyListType
        
        let! appendFunc2 = createAndEmit (SemanticKind.Intrinsic appendInfo) appendFuncType
        let! fullResultId = app2 appendFunc2 midResultId rightKeysId keyListType
        
        // If-then-else
        let! ifNodeId = ifThenElse isEmptyId emptyListId fullResultId keyListType
        
        // Lambda
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            ifNodeId,
            [],
            Some "keys",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]
        
        // Binding
        let! bindingId = letRecBind "keys" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "keys" (Some bindingId) loopFuncType
        return! app1 loopCallRefId mapNodeId keyListType
    }

//=============================================================================
// MAP.VALUES: values m → list of values via in-order traversal
//=============================================================================

let private mapValuesRecipe
    (mapNodeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : Recipe<NodeId> =
    
    let mapType = NativeType.TMap (keyType, valueType)
    let valueListType = NativeType.TList valueType
    let loopFuncType = NativeType.TFun (mapType, valueListType)
    
    recipe {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! bindVariable "tree" treeParamId mapType
        
        // Base case: []
        let! emptyListId = emptyList valueType
        
        // Guard: isEmpty tree
        let! isEmptyId = mapIsEmpty treeParamId keyType valueType
        
        // Get value, left, right
        let! nodeValueId = mapValue treeParamId keyType valueType
        let! leftId = mapLeft treeParamId keyType valueType
        let! rightId = mapRight treeParamId keyType valueType
        
        // Recursive calls
        let! loopRefLeft = varRef "values" None loopFuncType
        let! leftValsId = app1 loopRefLeft leftId valueListType
        
        let! loopRefRight = varRef "values" None loopFuncType
        let! rightValsId = app1 loopRefRight rightId valueListType
        
        // Create singleton list: [value]
        let! singletonId = cons nodeValueId emptyListId valueType
        
        // Concatenate: leftVals @ [value] @ rightVals
        let appendInfo = {
            Module = IntrinsicModule.List
            Operation = "append"
            Category = IntrinsicCategory.Pure
            FullName = "List.append"
        }
        let appendFuncType = NativeType.TFun (valueListType, NativeType.TFun (valueListType, valueListType))
        let! appendFunc1 = createAndEmit (SemanticKind.Intrinsic appendInfo) appendFuncType
        let! midResultId = app2 appendFunc1 leftValsId singletonId valueListType
        
        let! appendFunc2 = createAndEmit (SemanticKind.Intrinsic appendInfo) appendFuncType
        let! fullResultId = app2 appendFunc2 midResultId rightValsId valueListType
        
        // If-then-else
        let! ifNodeId = ifThenElse isEmptyId emptyListId fullResultId valueListType
        
        // Lambda
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            ifNodeId,
            [],
            Some "values",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]
        
        // Binding
        let! bindingId = letRecBind "values" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "values" (Some bindingId) loopFuncType
        return! app1 loopCallRefId mapNodeId valueListType
    }

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

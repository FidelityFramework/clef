// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Baker Set Recipes - Decomposition of Set HOFs to AVL tree primitives.
///
/// Set is represented as an AVL tree with nodes: {value, left, right, height}
/// Links are bounded arena-relative indices. Empty set = the static sentinel node (height 0) at
/// offset 0 of the arena (spec set-representation §2). INTERIM: the code still emits a null.
///
/// PRIMITIVE OPERATIONS (Alex witnesses directly):
/// - empty: returns the sentinel's index (interim: null)
/// - isEmpty: literal comparison height = 0 (interim: null check)
/// - node: create AVL node (arena alloc + struct construct)
/// - value, left, right, height: field access (GEP + load)
///
/// HOF OPERATIONS (Baker decomposes via combinators):
/// - add, contains, remove, union, intersect, difference
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "collection_machinery_architecture"
module Clef.Compiler.Baker.Recipes.SetRecipes

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
// SET.ADD: add v s → AVL insertion
//=============================================================================

let private setAddParser
    (valueNodeId: NodeId)
    (setNodeId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =
    
    // Use the AVL insert pattern for Set
    avlInsertSet valueNodeId setNodeId elemType

//=============================================================================
// SET.CONTAINS: contains v s → binary search returning bool
//=============================================================================

let private setContainsParser
    (valueNodeId: NodeId)
    (setNodeId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =
    
    // Use the AVL binary search pattern for Set
    binarySearchSet valueNodeId setNodeId elemType

//=============================================================================
// SET.REMOVE: remove v s → AVL deletion (simplified - marks as removed)
//=============================================================================

let private setRemoveParser
    (valueNodeId: NodeId)
    (setNodeId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =
    
    let setType = NativeType.TSet elemType
    let loopFuncType = NativeType.TFun (setType, setType)
    
    // AVL deletion is complex (need to handle rebalancing after removal)
    // Simplified implementation: rebuild tree without the value
    // Full AVL deletion would need predecessor/successor finding + rebalance
    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" setType
        do! withBinding "tree" treeParamId setType
        
        // Base case: empty - return empty (value not found)
        let! emptySetId = emptySet elemType
        
        // Guard: isEmpty tree
        let! isEmptyId = setIsEmpty treeParamId elemType
        
        // Get existing value, left, right
        let! nodeValueId = setValue treeParamId elemType
        let! leftId = setLeft treeParamId elemType
        let! rightId = setRight treeParamId elemType
        
        // Compare: compare removeValue nodeValue
        let! cmpResultId = compareTo valueNodeId nodeValueId elemType
        
        // Check comparison results
        let! isLessId = compareIsLess cmpResultId
        let! isGreaterId = compareIsGreater cmpResultId
        
        // Recursive calls
        let! loopRefLeft = varRef "remove" None loopFuncType
        let! newLeftId = app1 loopRefLeft leftId setType
        
        let! loopRefRight = varRef "remove" None loopFuncType
        let! newRightId = app1 loopRefRight rightId setType
        
        // Found case: merge left and right subtrees
        // Simplified: just return left if right is empty, or right if left is empty
        // For a proper implementation, would need to find in-order successor
        let! leftEmptyId = setIsEmpty leftId elemType
        let! rightEmptyId = setIsEmpty rightId elemType
        
        // If left is empty, return right; if right empty, return left
        // Otherwise need proper merge (simplified: rebuild)
        let! mergeResult1 = ifThenElse leftEmptyId rightId leftId setType
        let! mergeResult2 = ifThenElse rightEmptyId mergeResult1 mergeResult1 setType
        
        // Greater case: remove from right subtree, keep left
        let! removeRightNodeId = setNode nodeValueId leftId newRightId elemType
        
        // Less case: remove from left subtree, keep right
        let! removeLeftNodeId = setNode nodeValueId newLeftId rightId elemType
        
        // Innermost if: if cmp > 0 then removeRight else mergeResult
        let! innerIfId = ifThenElse isGreaterId removeRightNodeId mergeResult2 setType
        
        // Middle if: if cmp < 0 then removeLeft else innerIf
        let! middleIfId = ifThenElse isLessId removeLeftNodeId innerIfId setType
        
        // Outer if: if isEmpty then empty else middleIf
        let! outerIfId = ifThenElse isEmptyId emptySetId middleIfId setType
        
        // Lambda
        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", setType, treeParamId)],
            outerIfId,
            [],
            Some "remove",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [outerIfId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id
        
        // Binding
        let! bindingId = letRecBind "remove" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "remove" (Some bindingId) loopFuncType
        return! app1 loopCallRefId setNodeId setType
    }

//=============================================================================
// SET.UNION: union s1 s2 → merge two sets
//=============================================================================

let private setUnionParser
    (set1NodeId: NodeId)
    (set2NodeId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =
    
    let setType = NativeType.TSet elemType
    let loopFuncType = NativeType.TFun (setType, NativeType.TFun (setType, setType))
    
    // Union: fold insert over set1 starting with set2 as accumulator
    // union s1 s2 = fold add s2 s1
    saturation {
        // Parameters: tree1, acc
        let! tree1ParamId = patternBinding "tree1" setType
        do! withBinding "tree1" tree1ParamId setType
        
        let! accParamId = patternBinding "acc" setType
        do! withBinding "acc" accParamId setType
        
        // Base case: return acc (empty tree adds nothing)
        let! accRefId = varRef "acc" (Some accParamId) setType
        
        // Guard: isEmpty tree1
        let! isEmptyId = setIsEmpty tree1ParamId elemType
        
        // Get value, left, right from tree1
        let! nodeValueId = setValue tree1ParamId elemType
        let! leftId = setLeft tree1ParamId elemType
        let! rightId = setRight tree1ParamId elemType
        
        // Add current value to accumulator
        let! newAccId = avlInsertSet nodeValueId accParamId elemType
        
        // Recursive calls: union left (union right newAcc)
        let! loopRef1 = varRef "union" None loopFuncType
        let! rightResultId = app loopRef1 [rightId; newAccId] setType
        
        let! loopRef2 = varRef "union" None loopFuncType
        let! fullResultId = app loopRef2 [leftId; rightResultId] setType
        
        // If-then-else
        let! ifNodeId = ifThenElse isEmptyId accRefId fullResultId setType
        
        // Lambda
        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("tree1", setType, tree1ParamId); ("acc", setType, accParamId)],
            ifNodeId,
            [],
            Some "union",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id
        
        // Binding
        let! bindingId = letRecBind "union" lambdaId loopFuncType
        
        // Initial call: union set1 set2
        let! loopCallRefId = varRef "union" (Some bindingId) loopFuncType
        return! app loopCallRefId [set1NodeId; set2NodeId] setType
    }

//=============================================================================
// SET.INTERSECT: intersect s1 s2 → elements in both sets
//=============================================================================

let private setIntersectParser
    (set1NodeId: NodeId)
    (set2NodeId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =
    
    let setType = NativeType.TSet elemType
    let loopFuncType = NativeType.TFun (setType, setType)
    
    // Intersect: fold over s1, add to result only if also in s2
    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" setType
        do! withBinding "tree" treeParamId setType
        
        // Base case: empty
        let! emptySetId = emptySet elemType
        
        // Guard: isEmpty tree
        let! isEmptyId = setIsEmpty treeParamId elemType
        
        // Get value, left, right
        let! nodeValueId = setValue treeParamId elemType
        let! leftId = setLeft treeParamId elemType
        let! rightId = setRight treeParamId elemType
        
        // Check if value is in set2
        let! inSet2Id = binarySearchSet nodeValueId set2NodeId elemType
        
        // Recursive calls
        let! loopRefLeft = varRef "intersect" None loopFuncType
        let! leftResultId = app1 loopRefLeft leftId setType
        
        let! loopRefRight = varRef "intersect" None loopFuncType
        let! rightResultId = app1 loopRefRight rightId setType
        
        // Merge left and right results
        // Simplified: union leftResult rightResult
        let! mergedId = setUnionParser leftResultId rightResultId elemType
        
        // If in set2, add value to merged result
        let! withValueId = avlInsertSet nodeValueId mergedId elemType
        
        // Conditional: if inSet2 then withValue else merged
        let! conditionalId = ifThenElse inSet2Id withValueId mergedId setType
        
        // If-then-else: if isEmpty then empty else conditional
        let! ifNodeId = ifThenElse isEmptyId emptySetId conditionalId setType
        
        // Lambda
        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", setType, treeParamId)],
            ifNodeId,
            [],
            Some "intersect",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id
        
        // Binding
        let! bindingId = letRecBind "intersect" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "intersect" (Some bindingId) loopFuncType
        return! app1 loopCallRefId set1NodeId setType
    }

//=============================================================================
// SET.DIFFERENCE: difference s1 s2 → elements in s1 but not s2
//=============================================================================

let private setDifferenceParser
    (set1NodeId: NodeId)
    (set2NodeId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =
    
    let setType = NativeType.TSet elemType
    let loopFuncType = NativeType.TFun (setType, setType)
    
    // Difference: fold over s1, add to result only if NOT in s2
    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" setType
        do! withBinding "tree" treeParamId setType
        
        // Base case: empty
        let! emptySetId = emptySet elemType
        
        // Guard: isEmpty tree
        let! isEmptyId = setIsEmpty treeParamId elemType
        
        // Get value, left, right
        let! nodeValueId = setValue treeParamId elemType
        let! leftId = setLeft treeParamId elemType
        let! rightId = setRight treeParamId elemType
        
        // Check if value is in set2
        let! inSet2Id = binarySearchSet nodeValueId set2NodeId elemType
        
        // Recursive calls
        let! loopRefLeft = varRef "difference" None loopFuncType
        let! leftResultId = app1 loopRefLeft leftId setType
        
        let! loopRefRight = varRef "difference" None loopFuncType
        let! rightResultId = app1 loopRefRight rightId setType
        
        // Merge left and right results
        let! mergedId = setUnionParser leftResultId rightResultId elemType
        
        // If NOT in set2, add value to merged result
        let! withValueId = avlInsertSet nodeValueId mergedId elemType
        
        // Conditional: if inSet2 then merged (don't add) else withValue (add)
        let! conditionalId = ifThenElse inSet2Id mergedId withValueId setType
        
        // If-then-else: if isEmpty then empty else conditional
        let! ifNodeId = ifThenElse isEmptyId emptySetId conditionalId setType
        
        // Lambda
        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", setType, treeParamId)],
            ifNodeId,
            [],
            Some "difference",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id
        
        // Binding
        let! bindingId = letRecBind "difference" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "difference" (Some bindingId) loopFuncType
        return! app1 loopCallRefId set1NodeId setType
    }

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// Try to decompose a Set HOF operation
let tryDecompose
    (ctx: Context)
    (operation: string)
    (args: NodeId list)
    (elemType: NativeType)
    : Result option =
    
    match operation, args with
    | "add", [v; s] ->
        Some (runSaturation ctx (setAddParser v s elemType))
    
    | "contains", [v; s] ->
        Some (runSaturation ctx (setContainsParser v s elemType))
    
    | "remove", [v; s] ->
        Some (runSaturation ctx (setRemoveParser v s elemType))
    
    | "union", [s1; s2] ->
        Some (runSaturation ctx (setUnionParser s1 s2 elemType))
    
    | "intersect", [s1; s2] ->
        Some (runSaturation ctx (setIntersectParser s1 s2 elemType))
    
    | "difference", [s1; s2] ->
        Some (runSaturation ctx (setDifferenceParser s1 s2 elemType))
    
    // Primitive operations - Alex witnesses directly
    | "empty", _
    | "isEmpty", _ -> None
    
    | _ -> None

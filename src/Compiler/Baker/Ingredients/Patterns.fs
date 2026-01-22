// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker Patterns - Recursive structure generators using XParsec-style combinators.
///
/// LAYER 2: "Cooking Techniques"
///
/// Patterns generate the full recursive PSG structure for list operations.
/// They capture the boilerplate that was being repeated across all recipes:
/// - isEmpty guard
/// - head/tail extraction
/// - let rec binding
/// - recursive call structure
///
/// Recipes (Layer 3) just specify WHAT:
/// - Base case value
/// - How to combine head with recursive result (foldRight)
/// - How to combine accumulator with head (foldLeft)
///
/// Patterns generate HOW (the recursive structure).
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
module FSharp.Native.Compiler.Baker.Ingredients.Patterns

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Baker.Ingredients.SaturationCombinators
open FSharp.Native.Compiler.Baker.Ingredients.Primitives

//=============================================================================
// FOLD RIGHT PATTERN
//=============================================================================

/// Generate a right-fold recursive structure over a list.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let rec loop xs =
///     if List.isEmpty xs then baseCase
///     else combine (List.head xs) (loop (List.tail xs))
/// in loop inputList
/// ```
let foldRight
    (baseCase: SaturationParser<NodeId>)
    (combine: NodeId -> NodeId -> SaturationParser<NodeId>)
    (inputListId: NodeId)
    (elemType: NativeType)
    (resultType: NativeType)
    : SaturationParser<NodeId> =
    
    let listType = NativeType.TList elemType
    let loopFuncType = NativeType.TFun (listType, resultType)
    
    saturation {
        // Create parameter for the lambda: xs
        let! xsParamId = patternBinding "xs" listType
        do! withBinding "xs" xsParamId listType
        
        // Create the base case
        let! baseCaseId = baseCase
        
        // Create the guard: List.isEmpty xs
        let! isEmptyId = isEmpty xsParamId elemType
        
        // Create head and tail
        let! headId = head xsParamId elemType
        let! tailId = tail xsParamId elemType
        
        // Create recursive call reference (will be resolved by name)
        let! loopRefId = varRef "loop" None loopFuncType
        
        // Apply loop to tail: loop (tail xs)
        let! recurseCallId = app1 loopRefId tailId resultType
        
        // Combine: combine (head xs) (loop (tail xs))
        let! combineResultId = combine headId recurseCallId
        
        // If-then-else: if isEmpty then base else combine
        let! ifNodeId = ifThenElse isEmptyId baseCaseId combineResultId resultType
        
        // Create the lambda: fun xs -> if...
        let! state = getState
        let lambdaKind = SemanticKind.Lambda ([("xs", listType, xsParamId)], ifNodeId, [], Some "loop", LambdaContext.RegularClosure)
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id
        
        // Create the recursive binding: let rec loop = fun xs -> ...
        let! bindingId = letRecBind "loop" lambdaId loopFuncType
        
        // Create the initial call: loop inputList
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId inputListId resultType
    }

//=============================================================================
// FOLD LEFT PATTERN
//=============================================================================

/// Generate a left-fold recursive structure over a list.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let rec loop acc xs =
///     if List.isEmpty xs then acc
///     else loop (combine acc (List.head xs)) (List.tail xs)
/// in loop initialAcc inputList
/// ```
///
/// Parameters:
/// - initialAcc: Recipe that produces the initial accumulator value
/// - combine: Function taking (accId, headId) -> Recipe<NodeId>
/// - inputListId: The list to fold over
/// - elemType: Element type of the input list
/// - accType: Type of the accumulator (and result)
let foldLeft
    (initialAcc: SaturationParser<NodeId>)
    (combine: NodeId -> NodeId -> SaturationParser<NodeId>)
    (inputListId: NodeId)
    (elemType: NativeType)
    (accType: NativeType)
    : SaturationParser<NodeId> =

    let listType = NativeType.TList elemType
    let loopFuncType = NativeType.TFun (accType, NativeType.TFun (listType, accType))

    saturation {
        // Create parameters: acc, xs
        let! accParamId = patternBinding "acc" accType
        do! withBinding "acc" accParamId accType

        let! xsParamId = patternBinding "xs" listType
        do! withBinding "xs" xsParamId listType

        // Base case: return acc
        let! accRefId = varRef "acc" (Some accParamId) accType

        // Guard: List.isEmpty xs
        let! isEmptyId = isEmpty xsParamId elemType

        // Get head and tail
        let! headId = head xsParamId elemType
        let! tailId = tail xsParamId elemType

        // Combine: combine acc (head xs)
        let! accRefForCombine = varRef "acc" (Some accParamId) accType
        let! newAccId = combine accRefForCombine headId

        // Recursive call: loop newAcc (tail xs)
        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app loopRefId [newAccId; tailId] accType

        // If-then-else: if isEmpty then acc else loop(combine, tail)
        let! ifNodeId = ifThenElse isEmptyId accRefId recurseCallId accType

        // Lambda: fun acc xs -> if...
        let! state = getState
        let lambdaKind = SemanticKind.Lambda (
            [("acc", accType, accParamId); ("xs", listType, xsParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Recursive binding
        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        // Initial accumulator
        let! initAccId = initialAcc

        // Initial call: loop initAcc inputList
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app loopCallRefId [initAccId; inputListId] accType
    }

//=============================================================================
// FOLD LEFT 2 PATTERN (for two lists)
//=============================================================================

/// Generate a left-fold recursive structure over two lists in parallel.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let rec loop xs ys =
///     if List.isEmpty xs then
///         List.isEmpty ys  // Both must be empty for success
///     else if List.isEmpty ys then
///         false  // Length mismatch
///     else if combine (head xs) (head ys) then
///         loop (tail xs) (tail ys)
///     else
///         false
/// in loop list1 list2
/// ```
///
/// Used for forall2, exists2, map2, etc.
let foldLeft2
    (combine: NodeId -> NodeId -> SaturationParser<NodeId>)
    (list1Id: NodeId)
    (list2Id: NodeId)
    (elemType1: NativeType)
    (elemType2: NativeType)
    : SaturationParser<NodeId> =

    let listType1 = NativeType.TList elemType1
    let listType2 = NativeType.TList elemType2
    let loopFuncType = NativeType.TFun (listType1, NativeType.TFun (listType2, Types.boolType))

    saturation {
        // Parameters: xs, ys
        let! xsParamId = patternBinding "xs" listType1
        do! withBinding "xs" xsParamId listType1

        let! ysParamId = patternBinding "ys" listType2
        do! withBinding "ys" ysParamId listType2

        // Guards
        let! isEmptyXsId = isEmpty xsParamId elemType1
        let! isEmptyYsId = isEmpty ysParamId elemType2

        // Base case when xs is empty: return isEmpty ys (both must be empty)
        let! isEmptyYsForBase = isEmpty ysParamId elemType2

        // Get heads and tails
        let! headXsId = head xsParamId elemType1
        let! headYsId = head ysParamId elemType2
        let! tailXsId = tail xsParamId elemType1
        let! tailYsId = tail ysParamId elemType2

        // Combine: predicate (head xs) (head ys)
        let! combineResultId = combine headXsId headYsId

        // Recursive call: loop (tail xs) (tail ys)
        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app loopRefId [tailXsId; tailYsId] Types.boolType

        // Innermost if: if combine then recurse else false
        let! falseForInner = boolLit false
        let! innerIfId = ifThenElse combineResultId recurseCallId falseForInner Types.boolType

        // Middle if: if isEmpty ys then false else innerIf
        let! falseForMiddle = boolLit false
        let! middleIfId = ifThenElse isEmptyYsId falseForMiddle innerIfId Types.boolType

        // Outer if: if isEmpty xs then (isEmpty ys) else middleIf
        let! outerIfId = ifThenElse isEmptyXsId isEmptyYsForBase middleIfId Types.boolType

        // Lambda
        let! state = getState
        let lambdaKind = SemanticKind.Lambda (
            [("xs", listType1, xsParamId); ("ys", listType2, ysParamId)],
            outerIfId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [outerIfId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding
        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        // Initial call
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app loopCallRefId [list1Id; list2Id] Types.boolType
    }

//=============================================================================
// SPECIALIZED PATTERNS
//=============================================================================

/// Generate a simple recursive traversal that returns a boolean.
/// Used for exists, forall operations.
///
/// ```fsharp
/// let rec loop xs =
///     if List.isEmpty xs then baseValue
///     else if predicate (List.head xs) then shortCircuitValue
///     else loop (List.tail xs)
/// in loop inputList
/// ```
let boolFold
    (baseValue: bool)
    (shortCircuitValue: bool)
    (predicate: NodeId -> SaturationParser<NodeId>)
    (inputListId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let listType = NativeType.TList elemType
    let loopFuncType = NativeType.TFun (listType, Types.boolType)

    saturation {
        // Parameter: xs
        let! xsParamId = patternBinding "xs" listType
        do! withBinding "xs" xsParamId listType

        // Base case
        let! baseId = boolLit baseValue

        // Guard: isEmpty
        let! isEmptyId = isEmpty xsParamId elemType

        // Head and tail
        let! headId = head xsParamId elemType
        let! tailId = tail xsParamId elemType

        // Apply predicate
        let! predResultId = predicate headId

        // Short circuit value
        let! shortCircuitId = boolLit shortCircuitValue

        // Recursive call
        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app1 loopRefId tailId Types.boolType

        // Inner if: if pred then shortCircuit else recurse
        let! innerIfId = ifThenElse predResultId shortCircuitId recurseCallId Types.boolType

        // Outer if: if isEmpty then base else innerIf
        let! outerIfId = ifThenElse isEmptyId baseId innerIfId Types.boolType

        // Lambda
        let! state = getState
        let lambdaKind = SemanticKind.Lambda (
            [("xs", listType, xsParamId)],
            outerIfId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [outerIfId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding
        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        // Initial call
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId inputListId Types.boolType
    }


//=============================================================================
// AVL TREE PATTERNS (for Map and Set)
//=============================================================================

/// Generate an in-order tree traversal that collects elements into a list.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let rec inOrder tree =
///     if isEmpty tree then []
///     else inOrder (left tree) @ [(key, value)] @ inOrder (right tree)
/// in inOrder inputTree
/// ```
///
/// For Map, produces list of (key, value) pairs.
/// For Set, produces list of values.
let inOrderTraversalMap
    (inputTreeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    let mapType = NativeType.TMap (keyType, valueType)
    let pairType = NativeType.TTuple ([keyType; valueType], false)
    let listType = NativeType.TList pairType
    let loopFuncType = NativeType.TFun (mapType, listType)

    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! withBinding "tree" treeParamId mapType

        // Base case: []
        let! emptyListId = emptyList pairType

        // Guard: isEmpty tree
        let! isEmptyId = mapIsEmpty treeParamId keyType valueType

        // Get key, value, left, right
        let! keyId = mapKey treeParamId keyType valueType
        let! valueId = mapValue treeParamId keyType valueType
        let! leftId = mapLeft treeParamId keyType valueType
        let! rightId = mapRight treeParamId keyType valueType

        // Create (key, value) tuple
        let! state = getState
        let tupleKind = SemanticKind.TupleExpr [keyId; valueId]
        let tupleNode = mkNode state tupleKind pairType []
        do! emit tupleNode
        let tupleId = tupleNode.Id

        // Recursive calls
        let! loopRefLeft = varRef "inOrder" None loopFuncType
        let! leftResultId = app1 loopRefLeft leftId listType

        let! loopRefRight = varRef "inOrder" None loopFuncType
        let! rightResultId = app1 loopRefRight rightId listType

        // Create singleton list: [(key, value)]
        let! singletonId = cons tupleId emptyListId pairType

        // Use concatenation intrinsic for append operations
        let appendInfo = {
            Module = IntrinsicModule.List
            Operation = "append"
            Category = IntrinsicCategory.Pure
            FullName = "List.append"
        }
        let appendFuncType = NativeType.TFun (listType, NativeType.TFun (listType, listType))

        // First append intrinsic node
        let! state1 = getState
        let appendNode1 = mkNode state1 (SemanticKind.Intrinsic appendInfo) appendFuncType []
        do! emit appendNode1
        let appendFunc1 = appendNode1.Id

        // leftResult @ singleton
        let! midResultId = app2 appendFunc1 leftResultId singletonId listType

        // Second append intrinsic node
        let! state2 = getState
        let appendNode2 = mkNode state2 (SemanticKind.Intrinsic appendInfo) appendFuncType []
        do! emit appendNode2
        let appendFunc2 = appendNode2.Id

        // midResult @ rightResult
        let! fullResultId = app2 appendFunc2 midResultId rightResultId listType

        // If-then-else
        let! ifNodeId = ifThenElse isEmptyId emptyListId fullResultId listType

        // Lambda
        let! state3 = getState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            ifNodeId,
            [],
            Some "inOrder",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state3 lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding
        let! bindingId = letRecBind "inOrder" lambdaId loopFuncType

        // Initial call
        let! loopCallRefId = varRef "inOrder" (Some bindingId) loopFuncType
        return! app1 loopCallRefId inputTreeId listType
    }

/// Generate a binary search on an AVL tree.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let rec search tree =
///     if isEmpty tree then None
///     else
///         let cmp = compare searchKey (key tree)
///         if cmp < 0 then search (left tree)
///         elif cmp > 0 then search (right tree)
///         else Some (value tree)
/// in search inputTree
/// ```
let binarySearchMap
    (searchKeyId: NodeId)
    (inputTreeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    let mapType = NativeType.TMap (keyType, valueType)
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [valueType])
    let loopFuncType = NativeType.TFun (mapType, optionType)

    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! withBinding "tree" treeParamId mapType

        // Base case: None
        let! noneId = none valueType

        // Guard: isEmpty tree
        let! isEmptyId = mapIsEmpty treeParamId keyType valueType

        // Get key, value, left, right
        let! nodeKeyId = mapKey treeParamId keyType valueType
        let! nodeValueId = mapValue treeParamId keyType valueType
        let! leftId = mapLeft treeParamId keyType valueType
        let! rightId = mapRight treeParamId keyType valueType

        // Compare: compare searchKey nodeKey
        let! cmpResultId = compareTo searchKeyId nodeKeyId keyType

        // Check comparison results
        let! isLessId = compareIsLess cmpResultId
        let! isGreaterId = compareIsGreater cmpResultId

        // Found case: Some (value tree)
        let! foundId = some nodeValueId valueType

        // Recursive calls
        let! loopRefLeft = varRef "search" None loopFuncType
        let! leftSearchId = app1 loopRefLeft leftId optionType

        let! loopRefRight = varRef "search" None loopFuncType
        let! rightSearchId = app1 loopRefRight rightId optionType

        // Innermost if: if cmp > 0 then search right else found
        let! innerIfId = ifThenElse isGreaterId rightSearchId foundId optionType

        // Middle if: if cmp < 0 then search left else innerIf
        let! middleIfId = ifThenElse isLessId leftSearchId innerIfId optionType

        // Outer if: if isEmpty then None else middleIf
        let! outerIfId = ifThenElse isEmptyId noneId middleIfId optionType

        // Lambda
        let! state = getState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            outerIfId,
            [],
            Some "search",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [outerIfId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding
        let! bindingId = letRecBind "search" lambdaId loopFuncType

        // Initial call
        let! loopCallRefId = varRef "search" (Some bindingId) loopFuncType
        return! app1 loopCallRefId inputTreeId optionType
    }

/// Generate AVL tree insertion with balancing.
///
/// Produces the PSG equivalent of (simplified - full AVL has rotations):
/// ```fsharp
/// let rec insert tree =
///     if isEmpty tree then node newKey newValue empty empty
///     else
///         let cmp = compare newKey (key tree)
///         if cmp < 0 then balance (key tree) (value tree) (insert (left tree)) (right tree)
///         elif cmp > 0 then balance (key tree) (value tree) (left tree) (insert (right tree))
///         else node newKey newValue (left tree) (right tree)  // Replace value
/// in insert inputTree
/// ```
let avlInsertMap
    (newKeyId: NodeId)
    (newValueId: NodeId)
    (inputTreeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    let mapType = NativeType.TMap (keyType, valueType)
    let loopFuncType = NativeType.TFun (mapType, mapType)

    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! withBinding "tree" treeParamId mapType

        // Empty maps for leaf construction
        let! emptyMapId = emptyMap keyType valueType

        // Base case: create new leaf node
        let! leafNodeId = mapNode newKeyId newValueId emptyMapId emptyMapId keyType valueType

        // Guard: isEmpty tree
        let! isEmptyId = mapIsEmpty treeParamId keyType valueType

        // Get existing key, value, left, right
        let! nodeKeyId = mapKey treeParamId keyType valueType
        let! nodeValueId = mapValue treeParamId keyType valueType
        let! leftId = mapLeft treeParamId keyType valueType
        let! rightId = mapRight treeParamId keyType valueType

        // Compare: compare newKey nodeKey
        let! cmpResultId = compareTo newKeyId nodeKeyId keyType

        // Check comparison results
        let! isLessId = compareIsLess cmpResultId
        let! isGreaterId = compareIsGreater cmpResultId

        // Recursive calls
        let! loopRefLeft = varRef "insert" None loopFuncType
        let! newLeftId = app1 loopRefLeft leftId mapType

        let! loopRefRight = varRef "insert" None loopFuncType
        let! newRightId = app1 loopRefRight rightId mapType

        // Equal case: replace value at this node (same key)
        let! replaceNodeId = mapNode nodeKeyId newValueId leftId rightId keyType valueType

        // Greater case: insert into right subtree, keep left
        // Note: For proper AVL we'd balance here, but this is simplified
        let! insertRightNodeId = mapNode nodeKeyId nodeValueId leftId newRightId keyType valueType

        // Less case: insert into left subtree, keep right
        let! insertLeftNodeId = mapNode nodeKeyId nodeValueId newLeftId rightId keyType valueType

        // Innermost if: if cmp > 0 then insertRight else replaceNode
        let! innerIfId = ifThenElse isGreaterId insertRightNodeId replaceNodeId mapType

        // Middle if: if cmp < 0 then insertLeft else innerIf
        let! middleIfId = ifThenElse isLessId insertLeftNodeId innerIfId mapType

        // Outer if: if isEmpty then leafNode else middleIf
        let! outerIfId = ifThenElse isEmptyId leafNodeId middleIfId mapType

        // Lambda
        let! state = getState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            outerIfId,
            [],
            Some "insert",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [outerIfId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding
        let! bindingId = letRecBind "insert" lambdaId loopFuncType

        // Initial call
        let! loopCallRefId = varRef "insert" (Some bindingId) loopFuncType
        return! app1 loopCallRefId inputTreeId mapType
    }

/// Generate a tree forall traversal.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let rec forall tree =
///     if isEmpty tree then true
///     else predicate (key tree) (value tree) && forall (left tree) && forall (right tree)
/// in forall inputTree
/// ```
let treeForallMap
    (predicateId: NodeId)
    (inputTreeId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    let mapType = NativeType.TMap (keyType, valueType)
    let loopFuncType = NativeType.TFun (mapType, Types.boolType)

    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! withBinding "tree" treeParamId mapType

        // Base case: true
        let! trueId = boolLit true

        // Guard: isEmpty tree
        let! isEmptyId = mapIsEmpty treeParamId keyType valueType

        // Get key, value, left, right
        let! nodeKeyId = mapKey treeParamId keyType valueType
        let! nodeValueId = mapValue treeParamId keyType valueType
        let! leftId = mapLeft treeParamId keyType valueType
        let! rightId = mapRight treeParamId keyType valueType

        // Apply predicate to (key, value)
        let! predResultId = app2 predicateId nodeKeyId nodeValueId Types.boolType

        // Recursive calls
        let! loopRefLeft = varRef "forall" None loopFuncType
        let! leftResultId = app1 loopRefLeft leftId Types.boolType

        let! loopRefRight = varRef "forall" None loopFuncType
        let! rightResultId = app1 loopRefRight rightId Types.boolType

        // Combine: predResult && leftResult && rightResult
        let! andLeftId = andAlso predResultId leftResultId
        let! andAllId = andAlso andLeftId rightResultId

        // If-then-else
        let! ifNodeId = ifThenElse isEmptyId trueId andAllId Types.boolType

        // Lambda
        let! state = getState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            ifNodeId,
            [],
            Some "forall",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding
        let! bindingId = letRecBind "forall" lambdaId loopFuncType

        // Initial call
        let! loopCallRefId = varRef "forall" (Some bindingId) loopFuncType
        return! app1 loopCallRefId inputTreeId Types.boolType
    }

//=============================================================================
// SET AVL PATTERNS
//=============================================================================

/// Generate a binary search on an AVL Set.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let rec contains tree =
///     if isEmpty tree then false
///     else
///         let cmp = compare searchValue (value tree)
///         if cmp < 0 then contains (left tree)
///         elif cmp > 0 then contains (right tree)
///         else true
/// in contains inputTree
/// ```
let binarySearchSet
    (searchValueId: NodeId)
    (inputTreeId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let setType = NativeType.TSet elemType
    let loopFuncType = NativeType.TFun (setType, Types.boolType)

    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" setType
        do! withBinding "tree" treeParamId setType

        // Base case: false
        let! falseId = boolLit false

        // Guard: isEmpty tree
        let! isEmptyId = setIsEmpty treeParamId elemType

        // Get value, left, right
        let! nodeValueId = setValue treeParamId elemType
        let! leftId = setLeft treeParamId elemType
        let! rightId = setRight treeParamId elemType

        // Compare: compare searchValue nodeValue
        let! cmpResultId = compareTo searchValueId nodeValueId elemType

        // Check comparison results
        let! isLessId = compareIsLess cmpResultId
        let! isGreaterId = compareIsGreater cmpResultId

        // Found case: true
        let! foundId = boolLit true

        // Recursive calls
        let! loopRefLeft = varRef "contains" None loopFuncType
        let! leftSearchId = app1 loopRefLeft leftId Types.boolType

        let! loopRefRight = varRef "contains" None loopFuncType
        let! rightSearchId = app1 loopRefRight rightId Types.boolType

        // Innermost if: if cmp > 0 then search right else true
        let! innerIfId = ifThenElse isGreaterId rightSearchId foundId Types.boolType

        // Middle if: if cmp < 0 then search left else innerIf
        let! middleIfId = ifThenElse isLessId leftSearchId innerIfId Types.boolType

        // Outer if: if isEmpty then false else middleIf
        let! outerIfId = ifThenElse isEmptyId falseId middleIfId Types.boolType

        // Lambda
        let! state = getState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", setType, treeParamId)],
            outerIfId,
            [],
            Some "contains",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [outerIfId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding
        let! bindingId = letRecBind "contains" lambdaId loopFuncType

        // Initial call
        let! loopCallRefId = varRef "contains" (Some bindingId) loopFuncType
        return! app1 loopCallRefId inputTreeId Types.boolType
    }

/// Generate AVL Set insertion.
let avlInsertSet
    (newValueId: NodeId)
    (inputTreeId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let setType = NativeType.TSet elemType
    let loopFuncType = NativeType.TFun (setType, setType)

    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" setType
        do! withBinding "tree" treeParamId setType

        // Empty sets for leaf construction
        let! emptySetId = emptySet elemType

        // Base case: create new leaf node
        let! leafNodeId = setNode newValueId emptySetId emptySetId elemType

        // Guard: isEmpty tree
        let! isEmptyId = setIsEmpty treeParamId elemType

        // Get existing value, left, right
        let! nodeValueId = setValue treeParamId elemType
        let! leftId = setLeft treeParamId elemType
        let! rightId = setRight treeParamId elemType

        // Compare: compare newValue nodeValue
        let! cmpResultId = compareTo newValueId nodeValueId elemType

        // Check comparison results
        let! isLessId = compareIsLess cmpResultId
        let! isGreaterId = compareIsGreater cmpResultId

        // Recursive calls
        let! loopRefLeft = varRef "insert" None loopFuncType
        let! newLeftId = app1 loopRefLeft leftId setType

        let! loopRefRight = varRef "insert" None loopFuncType
        let! newRightId = app1 loopRefRight rightId setType

        // Equal case: value already exists, return unchanged tree
        let! treeRefId = varRef "tree" (Some treeParamId) setType

        // Greater case: insert into right subtree, keep left
        let! insertRightNodeId = setNode nodeValueId leftId newRightId elemType

        // Less case: insert into left subtree, keep right
        let! insertLeftNodeId = setNode nodeValueId newLeftId rightId elemType

        // Innermost if: if cmp > 0 then insertRight else treeRef (unchanged)
        let! innerIfId = ifThenElse isGreaterId insertRightNodeId treeRefId setType

        // Middle if: if cmp < 0 then insertLeft else innerIf
        let! middleIfId = ifThenElse isLessId insertLeftNodeId innerIfId setType

        // Outer if: if isEmpty then leafNode else middleIf
        let! outerIfId = ifThenElse isEmptyId leafNodeId middleIfId setType

        // Lambda
        let! state = getState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", setType, treeParamId)],
            outerIfId,
            [],
            Some "insert",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [outerIfId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding
        let! bindingId = letRecBind "insert" lambdaId loopFuncType

        // Initial call
        let! loopCallRefId = varRef "insert" (Some bindingId) loopFuncType
        return! app1 loopCallRefId inputTreeId setType
    }

//=============================================================================
// IN-ORDER SEQ TRAVERSAL PATTERNS (PRD-16 - Lazy Map/Set Enumeration)
//=============================================================================

/// Generate an in-order seq traversal of a Map's keys.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let keys map =
///     let rec traverse tree =
///         seq {
///             if not (Map.isEmpty tree) then
///                 yield! traverse (Map.left tree)
///                 yield (Map.key tree)
///                 yield! traverse (Map.right tree)
///         }
///     in traverse map
/// ```
///
/// This creates a lazy seq that yields keys in sorted order during traversal.
let inOrderKeysSeq
    (inputMapId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    let mapType = NativeType.TMap (keyType, valueType)
    let seqKeyType = NativeType.TSeq keyType
    let traverseFuncType = NativeType.TFun (mapType, seqKeyType)

    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! withBinding "tree" treeParamId mapType

        // Guard: isEmpty tree
        let! isEmptyId = mapIsEmpty treeParamId keyType valueType

        // Get key, left, right
        let! nodeKeyId = mapKey treeParamId keyType valueType
        let! leftId = mapLeft treeParamId keyType valueType
        let! rightId = mapRight treeParamId keyType valueType

        // Recursive calls to traverse
        let! traverseRefLeft = varRef "traverse" None traverseFuncType
        let! leftSeqId = app1 traverseRefLeft leftId seqKeyType

        let! traverseRefRight = varRef "traverse" None traverseFuncType
        let! rightSeqId = app1 traverseRefRight rightId seqKeyType

        // Build seq body: yield! left; yield key; yield! right
        let! yieldLeftId = yieldBang leftSeqId keyType
        let! yieldKeyId = yield' nodeKeyId keyType
        let! yieldRightId = yieldBang rightSeqId keyType

        // Sequential body: yieldLeft; yieldKey; yieldRight
        let! state1 = getState
        let seqKind = SemanticKind.Sequential [yieldLeftId; yieldKeyId; yieldRightId]
        let seqChildren = [yieldLeftId; yieldKeyId; yieldRightId]
        let seqBodyNode = mkNode state1 seqKind Types.unitType seqChildren
        do! emit seqBodyNode
        let seqBodyId = seqBodyNode.Id

        // If isEmpty then empty seq else seq body
        let! emptySeqId = emptySeq keyType
        let! condBodyId = ifThenElse isEmptyId emptySeqId seqBodyId seqKeyType

        // Wrap in SeqExpr (captures the tree parameter)
        let capture: CaptureInfo = { Name = "tree"; Type = mapType; IsMutable = false; SourceNodeId = Some treeParamId }
        let! seqExprId = seqExpr condBodyId [capture] keyType

        // Lambda: fun tree -> seq { ... }
        let! state2 = getState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            seqExprId,
            [],
            Some "traverse",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state2 lambdaKind traverseFuncType [seqExprId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding: let rec traverse = ...
        let! bindingId = letRecBind "traverse" lambdaId traverseFuncType

        // Initial call: traverse inputMap
        let! traverseCallRefId = varRef "traverse" (Some bindingId) traverseFuncType
        return! app1 traverseCallRefId inputMapId seqKeyType
    }

/// Generate an in-order seq traversal of a Map's values.
///
/// Same structure as inOrderKeysSeq but yields values instead of keys.
let inOrderValuesSeq
    (inputMapId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    let mapType = NativeType.TMap (keyType, valueType)
    let seqValueType = NativeType.TSeq valueType
    let traverseFuncType = NativeType.TFun (mapType, seqValueType)

    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! withBinding "tree" treeParamId mapType

        // Guard: isEmpty tree
        let! isEmptyId = mapIsEmpty treeParamId keyType valueType

        // Get value, left, right
        let! nodeValueId = mapValue treeParamId keyType valueType
        let! leftId = mapLeft treeParamId keyType valueType
        let! rightId = mapRight treeParamId keyType valueType

        // Recursive calls to traverse
        let! traverseRefLeft = varRef "traverse" None traverseFuncType
        let! leftSeqId = app1 traverseRefLeft leftId seqValueType

        let! traverseRefRight = varRef "traverse" None traverseFuncType
        let! rightSeqId = app1 traverseRefRight rightId seqValueType

        // Build seq body: yield! left; yield value; yield! right
        let! yieldLeftId = yieldBang leftSeqId valueType
        let! yieldValueId = yield' nodeValueId valueType
        let! yieldRightId = yieldBang rightSeqId valueType

        // Sequential body: yieldLeft; yieldValue; yieldRight
        let! state1 = getState
        let seqKind = SemanticKind.Sequential [yieldLeftId; yieldValueId; yieldRightId]
        let seqChildren = [yieldLeftId; yieldValueId; yieldRightId]
        let seqBodyNode = mkNode state1 seqKind Types.unitType seqChildren
        do! emit seqBodyNode
        let seqBodyId = seqBodyNode.Id

        // If isEmpty then empty seq else seq body
        let! emptySeqId = emptySeq valueType
        let! condBodyId = ifThenElse isEmptyId emptySeqId seqBodyId seqValueType

        // Wrap in SeqExpr (captures the tree parameter)
        let capture: CaptureInfo = { Name = "tree"; Type = mapType; IsMutable = false; SourceNodeId = Some treeParamId }
        let! seqExprId = seqExpr condBodyId [capture] valueType

        // Lambda: fun tree -> seq { ... }
        let! state2 = getState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            seqExprId,
            [],
            Some "traverse",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state2 lambdaKind traverseFuncType [seqExprId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding: let rec traverse = ...
        let! bindingId = letRecBind "traverse" lambdaId traverseFuncType

        // Initial call: traverse inputMap
        let! traverseCallRefId = varRef "traverse" (Some bindingId) traverseFuncType
        return! app1 traverseCallRefId inputMapId seqValueType
    }

/// Generate an in-order seq traversal of a Map's key-value pairs.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let toSeq map =
///     let rec traverse tree =
///         seq {
///             if not (Map.isEmpty tree) then
///                 yield! traverse (Map.left tree)
///                 yield (Map.key tree, Map.value tree)
///                 yield! traverse (Map.right tree)
///         }
///     in traverse map
/// ```
///
/// This creates a lazy seq that yields (key, value) pairs in sorted order.
/// Used by Map.toSeq for BAREWire and other consumers requiring lazy enumeration.
let inOrderPairsSeq
    (inputMapId: NodeId)
    (keyType: NativeType)
    (valueType: NativeType)
    : SaturationParser<NodeId> =

    let mapType = NativeType.TMap (keyType, valueType)
    let pairType = NativeType.TTuple ([keyType; valueType], false)
    let seqPairType = NativeType.TSeq pairType
    let traverseFuncType = NativeType.TFun (mapType, seqPairType)

    saturation {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! withBinding "tree" treeParamId mapType

        // Guard: isEmpty tree
        let! isEmptyId = mapIsEmpty treeParamId keyType valueType

        // Get key, value, left, right
        let! nodeKeyId = mapKey treeParamId keyType valueType
        let! nodeValueId = mapValue treeParamId keyType valueType
        let! leftId = mapLeft treeParamId keyType valueType
        let! rightId = mapRight treeParamId keyType valueType

        // Create (key, value) tuple
        let! state0 = getState
        let tupleKind = SemanticKind.TupleExpr [nodeKeyId; nodeValueId]
        let tupleNode = mkNode state0 tupleKind pairType []
        do! emit tupleNode
        let tupleId = tupleNode.Id

        // Recursive calls to traverse
        let! traverseRefLeft = varRef "traverse" None traverseFuncType
        let! leftSeqId = app1 traverseRefLeft leftId seqPairType

        let! traverseRefRight = varRef "traverse" None traverseFuncType
        let! rightSeqId = app1 traverseRefRight rightId seqPairType

        // Build seq body: yield! left; yield (key, value); yield! right
        let! yieldLeftId = yieldBang leftSeqId pairType
        let! yieldPairId = yield' tupleId pairType
        let! yieldRightId = yieldBang rightSeqId pairType

        // Sequential body: yieldLeft; yieldPair; yieldRight
        let! state1 = getState
        let seqKind = SemanticKind.Sequential [yieldLeftId; yieldPairId; yieldRightId]
        let seqChildren = [yieldLeftId; yieldPairId; yieldRightId]
        let seqBodyNode = mkNode state1 seqKind Types.unitType seqChildren
        do! emit seqBodyNode
        let seqBodyId = seqBodyNode.Id

        // If isEmpty then empty seq else seq body
        let! emptySeqId = emptySeq pairType
        let! condBodyId = ifThenElse isEmptyId emptySeqId seqBodyId seqPairType

        // Wrap in SeqExpr (captures the tree parameter)
        let capture: CaptureInfo = { Name = "tree"; Type = mapType; IsMutable = false; SourceNodeId = Some treeParamId }
        let! seqExprId = seqExpr condBodyId [capture] pairType

        // Lambda: fun tree -> seq { ... }
        let! state2 = getState
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            seqExprId,
            [],
            Some "traverse",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state2 lambdaKind traverseFuncType [seqExprId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding: let rec traverse = ...
        let! bindingId = letRecBind "traverse" lambdaId traverseFuncType

        // Initial call: traverse inputMap
        let! traverseCallRefId = varRef "traverse" (Some bindingId) traverseFuncType
        return! app1 traverseCallRefId inputMapId seqPairType
    }

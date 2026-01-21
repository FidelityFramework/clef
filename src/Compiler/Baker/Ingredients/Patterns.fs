// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker Patterns - Recursive structure generators.
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
module FSharp.Native.Compiler.Baker.Ingredients.Patterns

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Baker.Ingredients.RecipeBuilder
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
///
/// Parameters:
/// - baseCase: Recipe that produces the value for empty list
/// - combine: Function taking (headId, recurseResultId) -> Recipe<NodeId>
/// - inputListId: The list to fold over
/// - elemType: Element type of the input list
/// - resultType: Type of the result
let foldRight
    (baseCase: Recipe<NodeId>)
    (combine: NodeId -> NodeId -> Recipe<NodeId>)
    (inputListId: NodeId)
    (elemType: NativeType)
    (resultType: NativeType)
    : Recipe<NodeId> =
    
    let listType = NativeType.TList elemType
    let loopFuncType = NativeType.TFun (listType, resultType)
    
    recipe {
        // We need to build:
        // let rec loop xs = if isEmpty xs then base else combine (head xs) (loop (tail xs))
        // in loop inputList
        
        // First, create the recursive function
        // The body references 'loop' for the recursive call, but we don't have its ID yet.
        // We'll use a placeholder approach: create the binding first, then the body.
        
        // Create parameter for the lambda: xs
        let! xsParamId = patternBinding "xs" listType
        do! bindVariable "xs" xsParamId listType
        
        // Create the base case
        let! baseCaseId = baseCase
        
        // Create the guard: List.isEmpty xs
        let! isEmptyId = isEmpty xsParamId elemType
        
        // Create head and tail: List.head xs, List.tail xs
        let! headId = head xsParamId elemType
        let! tailId = tail xsParamId elemType
        
        // Create recursive call reference (placeholder - will be updated)
        // For now, we create a varRef with None, then update it after binding
        let! loopRefId = varRef "loop" None loopFuncType
        
        // Apply loop to tail: loop (tail xs)
        let! recurseCallId = app1 loopRefId tailId resultType
        
        // Combine: combine (head xs) (loop (tail xs))
        let! combineResultId = combine headId recurseCallId
        
        // If-then-else: if isEmpty then base else combine
        let! ifNodeId = ifThenElse isEmptyId baseCaseId combineResultId resultType
        
        // Create the lambda: fun xs -> if...
        let lambdaKind = SemanticKind.Lambda (
            [("xs", listType, xsParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]
        
        // Create the recursive binding: let rec loop = fun xs -> ...
        let! bindingId = letRecBind "loop" lambdaId loopFuncType
        
        // Update the recursive reference to point to the binding
        // (In a full implementation, we'd need to patch the node. For now,
        // the varRef with name "loop" will be resolved by the graph structure)
        
        // Create the initial call: loop inputList
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        let! initialCallId = app1 loopCallRefId inputListId resultType
        
        return initialCallId
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
    (initialAcc: Recipe<NodeId>)
    (combine: NodeId -> NodeId -> Recipe<NodeId>)
    (inputListId: NodeId)
    (elemType: NativeType)
    (accType: NativeType)
    : Recipe<NodeId> =
    
    let listType = NativeType.TList elemType
    let loopFuncType = NativeType.TFun (accType, NativeType.TFun (listType, accType))
    
    recipe {
        // Create parameters: acc, xs
        let! accParamId = patternBinding "acc" accType
        do! bindVariable "acc" accParamId accType
        
        let! xsParamId = patternBinding "xs" listType
        do! bindVariable "xs" xsParamId listType
        
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
        let lambdaKind = SemanticKind.Lambda (
            [("acc", accType, accParamId); ("xs", listType, xsParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]
        
        // Recursive binding
        let! bindingId = letRecBind "loop" lambdaId loopFuncType
        
        // Initial accumulator
        let! initAccId = initialAcc
        
        // Initial call: loop initAcc inputList
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        let! initialCallId = app loopCallRefId [initAccId; inputListId] accType
        
        return initialCallId
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
    (combine: NodeId -> NodeId -> Recipe<NodeId>)
    (list1Id: NodeId)
    (list2Id: NodeId)
    (elemType1: NativeType)
    (elemType2: NativeType)
    : Recipe<NodeId> =
    
    let listType1 = NativeType.TList elemType1
    let listType2 = NativeType.TList elemType2
    let loopFuncType = NativeType.TFun (listType1, NativeType.TFun (listType2, Types.boolType))
    
    recipe {
        // Parameters: xs, ys
        let! xsParamId = patternBinding "xs" listType1
        do! bindVariable "xs" xsParamId listType1
        
        let! ysParamId = patternBinding "ys" listType2
        do! bindVariable "ys" ysParamId listType2
        
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
        let lambdaKind = SemanticKind.Lambda (
            [("xs", listType1, xsParamId); ("ys", listType2, ysParamId)],
            outerIfId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [outerIfId]
        
        // Binding
        let! bindingId = letRecBind "loop" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        let! initialCallId = app loopCallRefId [list1Id; list2Id] Types.boolType
        
        return initialCallId
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
    (predicate: NodeId -> Recipe<NodeId>)
    (inputListId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    let listType = NativeType.TList elemType
    let loopFuncType = NativeType.TFun (listType, Types.boolType)
    
    recipe {
        // Parameter: xs
        let! xsParamId = patternBinding "xs" listType
        do! bindVariable "xs" xsParamId listType
        
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
        let lambdaKind = SemanticKind.Lambda (
            [("xs", listType, xsParamId)],
            outerIfId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [outerIfId]
        
        // Binding
        let! bindingId = letRecBind "loop" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        let! initialCallId = app1 loopCallRefId inputListId Types.boolType
        
        return initialCallId
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
    : Recipe<NodeId> =
    
    let mapType = NativeType.TMap (keyType, valueType)
    let pairType = NativeType.TTuple ([keyType; valueType], false)
    let listType = NativeType.TList pairType
    let loopFuncType = NativeType.TFun (mapType, listType)
    
    recipe {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! bindVariable "tree" treeParamId mapType
        
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
        let tupleKind = SemanticKind.TupleExpr [keyId; valueId]
        let! ctx = getContext
        let tupleNode = mkNode ctx tupleKind pairType
        do! emitNode tupleNode
        let tupleId = tupleNode.Id
        
        // Recursive calls
        let! loopRefLeft = varRef "inOrder" None loopFuncType
        let! leftResultId = app1 loopRefLeft leftId listType
        
        let! loopRefRight = varRef "inOrder" None loopFuncType
        let! rightResultId = app1 loopRefRight rightId listType
        
        // Create singleton list: [(key, value)]
        let! singletonId = cons tupleId emptyListId pairType
        
        // Append: left @ singleton
        // We need to implement append inline since we're building PSG
        // Actually, let's use the simpler approach: fold over left, then cons singleton, then append right
        // For simplicity, just cons each element: left @ [tuple] @ right
        // This produces: inOrder(left) @ [(k,v)] @ inOrder(right)
        
        // For now, use nested cons pattern: result = cons tuple (right result appended to left result)
        // Actually the cleanest is: fold_right cons leftResult (singleton @ rightResult)
        // Let's simplify: build the structure directly
        
        // Simpler approach: use fold-based append pattern
        // result = fold_right cons (cons tuple rightResult) leftResult
        // But this requires another nested fold...
        
        // Even simpler: just return cons tuple (append left right) - not quite right for in-order
        
        // Correct approach: fold cons from right: 
        // append leftResult (cons tuple rightResult)
        // where append xs ys = fold_right cons ys xs
        
        // For MVP: concat in the inefficient way using another recursive structure
        // Actually let's use: result = leftResult @ [tuple] @ rightResult
        // where @ is implemented via fold
        
        // Temporary simplification: use concatenation intrinsic
        // This defers the problem but gets the structure correct
        let appendInfo = {
            Module = IntrinsicModule.List
            Operation = "append"
            Category = IntrinsicCategory.Pure
            FullName = "List.append"
        }
        let appendFuncType = NativeType.TFun (listType, NativeType.TFun (listType, listType))
        let! appendFunc1 = createAndEmit (SemanticKind.Intrinsic appendInfo) appendFuncType
        
        // leftResult @ singleton
        let! midResultId = app2 appendFunc1 leftResultId singletonId listType
        
        // midResult @ rightResult
        let! appendFunc2 = createAndEmit (SemanticKind.Intrinsic appendInfo) appendFuncType
        let! fullResultId = app2 appendFunc2 midResultId rightResultId listType
        
        // If-then-else
        let! ifNodeId = ifThenElse isEmptyId emptyListId fullResultId listType
        
        // Lambda
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            ifNodeId,
            [],
            Some "inOrder",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]
        
        // Binding
        let! bindingId = letRecBind "inOrder" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "inOrder" (Some bindingId) loopFuncType
        let! initialCallId = app1 loopCallRefId inputTreeId listType
        
        return initialCallId
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
    : Recipe<NodeId> =
    
    let mapType = NativeType.TMap (keyType, valueType)
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [valueType])
    let loopFuncType = NativeType.TFun (mapType, optionType)
    
    recipe {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! bindVariable "tree" treeParamId mapType
        
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
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            outerIfId,
            [],
            Some "search",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [outerIfId]
        
        // Binding
        let! bindingId = letRecBind "search" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "search" (Some bindingId) loopFuncType
        let! initialCallId = app1 loopCallRefId inputTreeId optionType
        
        return initialCallId
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
    : Recipe<NodeId> =
    
    let mapType = NativeType.TMap (keyType, valueType)
    let loopFuncType = NativeType.TFun (mapType, mapType)
    
    recipe {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! bindVariable "tree" treeParamId mapType
        
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
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            outerIfId,
            [],
            Some "insert",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [outerIfId]
        
        // Binding
        let! bindingId = letRecBind "insert" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "insert" (Some bindingId) loopFuncType
        let! initialCallId = app1 loopCallRefId inputTreeId mapType
        
        return initialCallId
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
    : Recipe<NodeId> =
    
    let mapType = NativeType.TMap (keyType, valueType)
    let loopFuncType = NativeType.TFun (mapType, Types.boolType)
    
    recipe {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" mapType
        do! bindVariable "tree" treeParamId mapType
        
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
        let lambdaKind = SemanticKind.Lambda (
            [("tree", mapType, treeParamId)],
            ifNodeId,
            [],
            Some "forall",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]
        
        // Binding
        let! bindingId = letRecBind "forall" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "forall" (Some bindingId) loopFuncType
        let! initialCallId = app1 loopCallRefId inputTreeId Types.boolType
        
        return initialCallId
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
    : Recipe<NodeId> =
    
    let setType = NativeType.TSet elemType
    let loopFuncType = NativeType.TFun (setType, Types.boolType)
    
    recipe {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" setType
        do! bindVariable "tree" treeParamId setType
        
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
        let lambdaKind = SemanticKind.Lambda (
            [("tree", setType, treeParamId)],
            outerIfId,
            [],
            Some "contains",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [outerIfId]
        
        // Binding
        let! bindingId = letRecBind "contains" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "contains" (Some bindingId) loopFuncType
        let! initialCallId = app1 loopCallRefId inputTreeId Types.boolType
        
        return initialCallId
    }

/// Generate AVL Set insertion.
let avlInsertSet
    (newValueId: NodeId)
    (inputTreeId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    let setType = NativeType.TSet elemType
    let loopFuncType = NativeType.TFun (setType, setType)
    
    recipe {
        // Parameter: tree
        let! treeParamId = patternBinding "tree" setType
        do! bindVariable "tree" treeParamId setType
        
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
        let lambdaKind = SemanticKind.Lambda (
            [("tree", setType, treeParamId)],
            outerIfId,
            [],
            Some "insert",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [outerIfId]
        
        // Binding
        let! bindingId = letRecBind "insert" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "insert" (Some bindingId) loopFuncType
        let! initialCallId = app1 loopCallRefId inputTreeId setType
        
        return initialCallId
    }

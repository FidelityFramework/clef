// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker List Recipes - Decomposition of List HOFs to primitives.
///
/// List is a singly-linked cons cell: {head: T, tail: ptr<List<T>>}
/// Empty list = null pointer
///
/// PRIMITIVE OPERATIONS (Alex witnesses directly):
/// - empty: returns null pointer
/// - isEmpty: null check  
/// - head: GEP to field 0, load
/// - tail: GEP to field 1, load
/// - cons: arena alloc + store head + store tail
///
/// HOF OPERATIONS (Baker decomposes via combinators):
/// - map, filter, fold, length, rev, append, exists, forall, collect, etc.
///
/// COMBINATOR MODEL:
/// Each recipe is 5-10 lines composing patterns from Ingredients/.
/// The verbose 100+ line manual node construction is eliminated.
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
module FSharp.Native.Compiler.Baker.Recipes.ListRecipes

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
    // For now, skip shadow tree construction - focus on PSG structure
    mkResultNoShadow nodes resultNodeId []

//=============================================================================
// LIST.MAP: map f xs → cons (f h) (map f t) | [] → []
//=============================================================================

let private listMapRecipe
    (mapperNodeId: NodeId)
    (inputListId: NodeId)
    (inputElemType: NativeType)
    (outputElemType: NativeType)
    : Recipe<NodeId> =
    
    let outputListType = NativeType.TList outputElemType
    
    foldRight
        (emptyList outputElemType)
        (fun headId recurseId ->
            recipe {
                let! mappedHead = app1 mapperNodeId headId outputElemType
                return! cons mappedHead recurseId outputElemType
            })
        inputListId
        inputElemType
        outputListType

//=============================================================================
// LIST.FILTER: filter p xs → if p h then h :: filter p t else filter p t | [] → []
//=============================================================================

let private listFilterRecipe
    (predicateNodeId: NodeId)
    (inputListId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    let listType = NativeType.TList elemType
    
    foldRight
        (emptyList elemType)
        (fun headId recurseId ->
            recipe {
                let! shouldInclude = app1 predicateNodeId headId Types.boolType
                return! guardCons shouldInclude headId recurseId elemType
            })
        inputListId
        elemType
        listType

//=============================================================================
// LIST.FOLD: fold f s xs → if isEmpty then s else fold f (f s h) t
//=============================================================================

let private listFoldRecipe
    (folderNodeId: NodeId)
    (stateNodeId: NodeId)
    (inputListId: NodeId)
    (elemType: NativeType)
    (stateType: NativeType)
    : Recipe<NodeId> =
    
    foldLeft
        (ret stateNodeId)  // Initial accumulator is the provided state
        (fun accId headId ->
            recipe {
                // f acc head
                return! app2 folderNodeId accId headId stateType
            })
        inputListId
        elemType
        stateType

//=============================================================================
// LIST.EXISTS: exists p xs → if p h then true else exists p t | [] → false
//=============================================================================

let private listExistsRecipe
    (predicateNodeId: NodeId)
    (inputListId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    boolFold
        false  // Base case: empty list → false
        true   // Short circuit: predicate true → true
        (fun headId -> app1 predicateNodeId headId Types.boolType)
        inputListId
        elemType

//=============================================================================
// LIST.FORALL: forall p xs → if not (p h) then false else forall p t | [] → true
//=============================================================================

let private listForallRecipe
    (predicateNodeId: NodeId)
    (inputListId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    // forall is "all elements satisfy predicate"
    // Short-circuit on first failure (predicate returns false)
    // boolFold with baseValue=true, shortCircuitValue=false, but we need
    // to short-circuit when predicate is FALSE, not TRUE.
    // So we use a negated test.
    boolFold
        true   // Base case: empty list → true (vacuously true)
        false  // Short circuit: predicate false → false
        (fun headId ->
            recipe {
                // Check if predicate returns false
                let! predResult = app1 predicateNodeId headId Types.boolType
                // If predResult is false, we want to return true (to trigger short-circuit)
                // Actually, boolFold short-circuits when the predicate returns shortCircuitValue.
                // For forall, we want: if NOT(pred(h)) then false else continue
                // So the inner predicate should return true when pred(h) is false.
                // We need a "not" primitive or just flip the logic.
                // For now, let's return predResult directly and the boolFold will
                // short-circuit when it's false (which is what we want for forall).
                return predResult
            })
        inputListId
        elemType

//=============================================================================
// LIST.LENGTH: length xs → count elements recursively
//=============================================================================

let private listLengthRecipe
    (inputListId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    foldLeft
        (intLit 0)  // Initial count is 0
        (fun accId _headId ->
            recipe {
                let! one = intLit 1
                return! add accId one Types.intType
            })
        inputListId
        elemType
        Types.intType

//=============================================================================
// LIST.REV: rev xs → fold (fun acc h → h :: acc) [] xs
//=============================================================================

let private listRevRecipe
    (inputListId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    let listType = NativeType.TList elemType
    
    foldLeft
        (emptyList elemType)  // Start with empty accumulator
        (fun accId headId ->
            recipe {
                // Prepend head to accumulator: h :: acc
                return! cons headId accId elemType
            })
        inputListId
        elemType
        listType

//=============================================================================
// LIST.APPEND: append xs ys → foldRight cons ys xs
//=============================================================================

let private listAppendRecipe
    (list1Id: NodeId)
    (list2Id: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    let listType = NativeType.TList elemType
    
    // append xs ys = fold_right cons ys xs
    // Going right-to-left through xs, cons each element onto ys
    foldRight
        (ret list2Id)  // Base case: return ys
        (fun headId recurseId ->
            recipe {
                return! cons headId recurseId elemType
            })
        list1Id
        elemType
        listType

//=============================================================================
// LIST.COLLECT: collect f xs → concat (map f xs)
// = foldRight (fun h acc → append (f h) acc) [] xs
//=============================================================================

let private listCollectRecipe
    (mapperNodeId: NodeId)
    (inputListId: NodeId)
    (inputElemType: NativeType)
    (outputElemType: NativeType)
    : Recipe<NodeId> =
    
    let outputListType = NativeType.TList outputElemType
    
    // collect f xs = fold_right (\h acc -> append (f h) acc) [] xs
    foldRight
        (emptyList outputElemType)
        (fun headId recurseId ->
            recipe {
                // Apply f to get a list
                let! mappedList = app1 mapperNodeId headId outputListType
                // Append that list to the accumulated result
                // We need to inline the append logic here since we don't have
                // a recursive append available. Actually, we can use foldRight
                // to implement append inline:
                return! foldRight
                    (ret recurseId)  // Base: return accumulated result
                    (fun h acc ->
                        recipe {
                            return! cons h acc outputElemType
                        })
                    mappedList
                    outputElemType
                    outputListType
            })
        inputListId
        inputElemType
        outputListType

//=============================================================================
// LIST.CONTAINS: contains x xs → exists (fun e → e = x) xs
//=============================================================================

let private listContainsRecipe
    (valueNodeId: NodeId)
    (inputListId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    boolFold
        false  // Empty list doesn't contain anything
        true   // Found! Short-circuit with true
        (fun headId ->
            recipe {
                return! eq headId valueNodeId elemType
            })
        inputListId
        elemType

//=============================================================================
// LIST.TRYPICK: tryPick f xs → find first Some result
//=============================================================================

let private listTryPickRecipe
    (chooserNodeId: NodeId)
    (inputListId: NodeId)
    (inputElemType: NativeType)
    (outputElemType: NativeType)
    : Recipe<NodeId> =
    
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [outputElemType])
    let listType = NativeType.TList inputElemType
    let loopFuncType = NativeType.TFun (listType, optionType)
    
    // tryPick is like exists but returns the first Some result
    // let rec loop xs =
    //     if isEmpty xs then None
    //     else
    //         let result = f (head xs)
    //         if isSome result then result
    //         else loop (tail xs)
    recipe {
        // Create parameter for xs
        let! xsParamId = patternBinding "xs" listType
        do! bindVariable "xs" xsParamId listType
        
        // Base case: None
        let! noneId = none outputElemType
        
        // Guard: isEmpty xs
        let! isEmptyId = isEmpty xsParamId inputElemType
        
        // Get head and tail
        let! headId = head xsParamId inputElemType
        let! tailId = tail xsParamId inputElemType
        
        // Apply chooser: f (head xs)
        let! resultId = app1 chooserNodeId headId optionType
        
        // Check if result isSome
        let! isSomeId = isSome resultId outputElemType
        
        // Recursive call
        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseId = app1 loopRefId tailId optionType
        
        // Inner if: if isSome result then result else recurse
        let! innerIfId = ifThenElse isSomeId resultId recurseId optionType
        
        // Outer if: if isEmpty then None else innerIf
        let! outerIfId = ifThenElse isEmptyId noneId innerIfId optionType
        
        // Create the recursive lambda and binding
        let! lambdaId = lambda [("xs", listType)] (fun _ -> ret outerIfId) optionType
        let! bindingId = letRecBind "loop" lambdaId loopFuncType
        
        // Initial call
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId inputListId optionType
    }

//=============================================================================
// LIST.MINBY: minBy f xs → element with minimum f value
//=============================================================================

let private listMinByRecipe
    (projectionNodeId: NodeId)
    (inputListId: NodeId)
    (elemType: NativeType)
    (keyType: NativeType)
    : Recipe<NodeId> =
    
    // We need a tuple type for (minElem, minKey) but let's simplify:
    // Actually, minBy needs to track both the element and its projected key.
    // For now, use a simpler approach: two accumulators via nested state.
    // This is getting complex - let's use the foldLeft pattern with element only,
    // recomputing the projection each time (less efficient but correct).
    
    // let rec loop minElem xs =
    //     if isEmpty xs then minElem
    //     else
    //         let h = head xs
    //         let newMin = if f h < f minElem then h else minElem
    //         loop newMin (tail xs)
    // in loop (head inputList) (tail inputList)
    
    recipe {
        // Get first element as initial min
        let! firstElem = head inputListId elemType
        let! restList = tail inputListId elemType
        
        // Fold through the rest
        let combiner = fun currentMinId headId ->
            recipe {
                // Project both elements
                let! currentMinKey = app1 projectionNodeId currentMinId keyType
                let! headKey = app1 projectionNodeId headId keyType
                // Compare: if headKey < currentMinKey then head else currentMin
                let! isLess = lt headKey currentMinKey keyType
                return! ifThenElse isLess headId currentMinId elemType
            }
        let! result = foldLeft (ret firstElem) combiner restList elemType elemType
        
        return result
    }

//=============================================================================
// LIST.MAX: max xs → maximum element
//=============================================================================

let private listMaxRecipe
    (inputListId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =
    
    recipe {
        // Get first element as initial max
        let! firstElem = head inputListId elemType
        let! restList = tail inputListId elemType
        
        // Fold through the rest
        let combiner = fun currentMaxId headId ->
            recipe {
                // if head > currentMax then head else currentMax
                let! isGreater = gt headId currentMaxId elemType
                return! ifThenElse isGreater headId currentMaxId elemType
            }
        let! result = foldLeft (ret firstElem) combiner restList elemType elemType
        
        return result
    }

//=============================================================================
// LIST.FORALL2: forall2 f xs ys → all pairs satisfy f
//=============================================================================

let private listForall2Recipe
    (predicateNodeId: NodeId)
    (list1Id: NodeId)
    (list2Id: NodeId)
    (elemType1: NativeType)
    (elemType2: NativeType)
    : Recipe<NodeId> =
    
    // Use the foldLeft2 pattern from Patterns.fs
    foldLeft2
        (fun head1Id head2Id ->
            recipe {
                // Apply predicate to both heads
                return! app2 predicateNodeId head1Id head2Id Types.boolType
            })
        list1Id
        list2Id
        elemType1
        elemType2

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// Try to decompose a List operation.
/// Returns Some Result if the operation can be decomposed, None for primitives.
let tryDecompose
    (ctx: Context)
    (operation: string)
    (args: NodeId list)
    (elemType: NativeType)
    (outputElemType: NativeType option)
    (stateType: NativeType option)
    : Result option =
    
    match operation, args with
    | "map", [mapper; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runRecipe ctx (listMapRecipe mapper xs elemType outElem))
    
    | "fold", [folder; state; xs] ->
        let stTy = stateType |> Option.defaultValue elemType
        Some (runRecipe ctx (listFoldRecipe folder state xs elemType stTy))
    
    | "filter", [predicate; xs] ->
        Some (runRecipe ctx (listFilterRecipe predicate xs elemType))
    
    | "exists", [predicate; xs] ->
        Some (runRecipe ctx (listExistsRecipe predicate xs elemType))
    
    | "forall", [predicate; xs] ->
        Some (runRecipe ctx (listForallRecipe predicate xs elemType))
    
    | "length", [xs] ->
        Some (runRecipe ctx (listLengthRecipe xs elemType))
    
    | "rev", [xs] ->
        Some (runRecipe ctx (listRevRecipe xs elemType))
    
    | "append", [xs; ys] ->
        Some (runRecipe ctx (listAppendRecipe xs ys elemType))
    
    | "collect", [mapper; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runRecipe ctx (listCollectRecipe mapper xs elemType outElem))
    
    | "contains", [value; xs] ->
        Some (runRecipe ctx (listContainsRecipe value xs elemType))
    
    | "tryPick", [chooser; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runRecipe ctx (listTryPickRecipe chooser xs elemType outElem))
    
    | "minBy", [projection; xs] ->
        // For minBy, we need the key type. For now, assume same as elem type.
        // This should be extracted from the projection function's return type.
        let keyType = stateType |> Option.defaultValue elemType
        Some (runRecipe ctx (listMinByRecipe projection xs elemType keyType))
    
    | "max", [xs] ->
        Some (runRecipe ctx (listMaxRecipe xs elemType))
    
    | "forall2", [predicate; xs; ys] ->
        // For forall2, both lists have same element type for now
        Some (runRecipe ctx (listForall2Recipe predicate xs ys elemType elemType))
    
    // Primitive operations - Alex witnesses directly
    | "empty", _
    | "isEmpty", _
    | "head", _
    | "tail", _
    | "cons", _ -> None
    
    | _ -> None

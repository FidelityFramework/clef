// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker Seq Recipes - Decomposition of Seq HOFs to primitives.
///
/// Seq<'T> is a lazy sequence: evaluated only when iterated.
/// PRD-15/16: State machine compilation for lazy evaluation.
///
/// PRIMITIVE OPERATIONS (Alex witnesses directly):
/// - Seq.empty: returns empty seq
/// - Seq.getEnumerator: creates enumerator state machine
/// - SeqEnumerator.moveNext: advances enumerator, returns bool
/// - SeqEnumerator.current: gets current element
///
/// HOF OPERATIONS (Baker decomposes via combinators):
///
/// PRODUCERS (return lazy seq):
/// - map, filter, collect, append
/// These create new seq expressions that transform during iteration.
///
/// CONSUMERS (iterate seq, return non-seq):
/// - toList, toArray, fold, exists, forall, length, isEmpty, head, tryHead,
///   max, min, minBy, maxBy, tryPick
/// These iterate the seq and accumulate/find results.
///
/// ARCHITECTURAL NOTES:
/// 1. Producers wrap transformations in SeqExpr nodes
/// 2. Consumers iterate using the enumerator pattern
/// 3. Fusion/SIMD optimizations are preserved by this decomposed model
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
module FSharp.Native.Compiler.Baker.Recipes.SeqRecipes

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
// CONSUMER PATTERN: Iterate seq with enumerator
//=============================================================================

/// Generate an enumerator-based iteration over a seq.
///
/// Produces the PSG equivalent of:
/// ```fsharp
/// let enum = Seq.getEnumerator xs
/// let rec loop acc =
///     if SeqEnumerator.moveNext enum then
///         let elem = SeqEnumerator.current enum
///         loop (combine acc elem)
///     else
///         acc
/// in loop initialAcc
/// ```
///
/// Parameters:
/// - initialAcc: Recipe that produces the initial accumulator value
/// - combine: Function taking (accId, elemId) -> Recipe<NodeId>
/// - inputSeqId: The seq to iterate over
/// - elemType: Element type of the seq
/// - accType: Type of the accumulator (and result)
let private seqFoldLeft
    (initialAcc: Recipe<NodeId>)
    (combine: NodeId -> NodeId -> Recipe<NodeId>)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    (accType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let loopFuncType = NativeType.TFun (accType, accType)

    recipe {
        // Get enumerator: let enum = Seq.getEnumerator xs
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // Create parameter for accumulator
        let! accParamId = patternBinding "acc" accType
        do! bindVariable "acc" accParamId accType

        // MoveNext check: SeqEnumerator.moveNext enum
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory  // mutates enumerator state
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! hasNextId = app1 moveNextFuncId enumId Types.boolType

        // Get current element: SeqEnumerator.current enum
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! elemId = app1 currentFuncId enumId elemType

        // Combine: combine acc elem
        let! accRefForCombine = varRef "acc" (Some accParamId) accType
        let! newAccId = combine accRefForCombine elemId

        // Recursive call: loop newAcc
        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app1 loopRefId newAccId accType

        // Base case: return acc
        let! accRefId = varRef "acc" (Some accParamId) accType

        // If-then-else: if moveNext then loop(combine) else acc
        let! ifNodeId = ifThenElse hasNextId recurseCallId accRefId accType

        // Lambda: fun acc -> if...
        let lambdaKind = SemanticKind.Lambda (
            [("acc", accType, accParamId)],
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

        // Initial call: loop initAcc
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        let! initialCallId = app1 loopCallRefId initAccId accType

        return initialCallId
    }

/// Generate a boolean short-circuit iteration over a seq.
///
/// Used for exists and forall operations.
let private seqBoolFold
    (baseValue: bool)
    (shortCircuitValue: bool)
    (predicate: NodeId -> Recipe<NodeId>)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let loopFuncType = NativeType.TFun (Types.unitType, Types.boolType)

    recipe {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! hasNextId = app1 moveNextFuncId enumId Types.boolType

        // Get current
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! elemId = app1 currentFuncId enumId elemType

        // Apply predicate
        let! predResultId = predicate elemId

        // Short circuit value
        let! shortCircuitId = boolLit shortCircuitValue

        // Recursive call
        let! loopRefId = varRef "loop" None loopFuncType
        let! unitId = createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        let! recurseCallId = app1 loopRefId unitId Types.boolType

        // Inner if: if pred then shortCircuit else recurse
        let! innerIfId = ifThenElse predResultId shortCircuitId recurseCallId Types.boolType

        // Base case
        let! baseId = boolLit baseValue

        // Outer if: if hasNext then innerIf else base
        let! outerIfId = ifThenElse hasNextId innerIfId baseId Types.boolType

        // Lambda (takes unit, returns bool)
        let! unitParamId = patternBinding "_" Types.unitType
        let lambdaKind = SemanticKind.Lambda (
            [("_", Types.unitType, unitParamId)],
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
        let! unitForCall = createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        let! initialCallId = app1 loopCallRefId unitForCall Types.boolType

        return initialCallId
    }

//=============================================================================
// PRODUCER: SEQ.MAP
//=============================================================================

/// Seq.map f xs → seq { for x in xs -> f x }
///
/// Creates a new seq that lazily applies f to each element.
let private seqMapRecipe
    (mapperNodeId: NodeId)
    (inputSeqId: NodeId)
    (inputElemType: NativeType)
    (outputElemType: NativeType)
    : Recipe<NodeId> =

    let inputSeqType = NativeType.TSeq inputElemType
    let _outputSeqType = NativeType.TSeq outputElemType  // for clarity, not used
    let enumType = NativeType.TSeqEnumerator inputElemType

    recipe {
        // The seq expression body iterates the input and yields transformed elements
        // seq {
        //     let enum = getEnumerator xs
        //     while moveNext enum do
        //         yield f (current enum)
        // }

        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (inputSeqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! conditionId = app1 moveNextFuncId enumId Types.boolType

        // Get current element
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, inputElemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! elemId = app1 currentFuncId enumId inputElemType

        // Apply mapper: f elem
        let! mappedId = app1 mapperNodeId elemId outputElemType

        // Yield the mapped element
        let! yieldId = yield' mappedId outputElemType

        // While loop: while moveNext do yield f(current)
        let! whileBodyId = createWithChildren (SemanticKind.WhileLoop (conditionId, yieldId)) Types.unitType [conditionId; yieldId]

        // Seq expression wrapping the iteration
        let capture: CaptureInfo = { Name = "xs"; Type = inputSeqType; IsMutable = false; SourceNodeId = Some inputSeqId }
        let mapperCapture: CaptureInfo = { Name = "f"; Type = NativeType.TFun(inputElemType, outputElemType); IsMutable = false; SourceNodeId = Some mapperNodeId }
        let! seqExprId = seqExpr whileBodyId [capture; mapperCapture] outputElemType

        return seqExprId
    }

//=============================================================================
// PRODUCER: SEQ.FILTER
//=============================================================================

/// Seq.filter p xs → seq { for x in xs do if p x then yield x }
let private seqFilterRecipe
    (predicateNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    recipe {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! conditionId = app1 moveNextFuncId enumId Types.boolType

        // Get current
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! elemId = app1 currentFuncId enumId elemType

        // Apply predicate
        let! predResultId = app1 predicateNodeId elemId Types.boolType

        // Yield element (conditional)
        let! yieldId = yield' elemId elemType

        // Unit for else branch
        let! unitId = createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType

        // If predicate then yield else skip
        let! conditionalYieldId = ifThenElse predResultId yieldId unitId Types.unitType

        // While loop
        let! whileBodyId = createWithChildren (SemanticKind.WhileLoop (conditionId, conditionalYieldId)) Types.unitType [conditionId; conditionalYieldId]

        // Seq expression
        let capture: CaptureInfo = { Name = "xs"; Type = seqType; IsMutable = false; SourceNodeId = Some inputSeqId }
        let predCapture: CaptureInfo = { Name = "p"; Type = NativeType.TFun(elemType, Types.boolType); IsMutable = false; SourceNodeId = Some predicateNodeId }
        let! seqExprId = seqExpr whileBodyId [capture; predCapture] elemType

        return seqExprId
    }

//=============================================================================
// PRODUCER: SEQ.COLLECT (flatMap/bind)
//=============================================================================

/// Seq.collect f xs → seq { for x in xs do yield! f x }
let private seqCollectRecipe
    (mapperNodeId: NodeId)
    (inputSeqId: NodeId)
    (inputElemType: NativeType)
    (outputElemType: NativeType)
    : Recipe<NodeId> =

    let inputSeqType = NativeType.TSeq inputElemType
    let outputSeqType = NativeType.TSeq outputElemType
    let enumType = NativeType.TSeqEnumerator inputElemType

    recipe {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (inputSeqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! conditionId = app1 moveNextFuncId enumId Types.boolType

        // Get current
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, inputElemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! elemId = app1 currentFuncId enumId inputElemType

        // Apply mapper to get inner seq: f elem
        let! innerSeqId = app1 mapperNodeId elemId outputSeqType

        // Yield! the inner seq (flattens)
        let! yieldBangId = yieldBang innerSeqId outputElemType

        // While loop
        let! whileBodyId = createWithChildren (SemanticKind.WhileLoop (conditionId, yieldBangId)) Types.unitType [conditionId; yieldBangId]

        // Seq expression
        let capture: CaptureInfo = { Name = "xs"; Type = inputSeqType; IsMutable = false; SourceNodeId = Some inputSeqId }
        let mapperCapture: CaptureInfo = { Name = "f"; Type = NativeType.TFun(inputElemType, outputSeqType); IsMutable = false; SourceNodeId = Some mapperNodeId }
        let! seqExprId = seqExpr whileBodyId [capture; mapperCapture] outputElemType

        return seqExprId
    }

//=============================================================================
// PRODUCER: SEQ.APPEND
//=============================================================================

/// Seq.append xs ys → seq { yield! xs; yield! ys }
let private seqAppendRecipe
    (seq1Id: NodeId)
    (seq2Id: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType

    recipe {
        // yield! xs
        let! yieldBang1Id = yieldBang seq1Id elemType

        // yield! ys
        let! yieldBang2Id = yieldBang seq2Id elemType

        // Sequential: yield! xs; yield! ys
        let seqKind = SemanticKind.Sequential [yieldBang1Id; yieldBang2Id]
        let! seqBodyId = createWithChildren seqKind Types.unitType [yieldBang1Id; yieldBang2Id]

        // Seq expression
        let capture1: CaptureInfo = { Name = "xs"; Type = seqType; IsMutable = false; SourceNodeId = Some seq1Id }
        let capture2: CaptureInfo = { Name = "ys"; Type = seqType; IsMutable = false; SourceNodeId = Some seq2Id }
        let! seqExprId = seqExpr seqBodyId [capture1; capture2] elemType

        return seqExprId
    }

//=============================================================================
// CONSUMER: SEQ.TOLIST
//=============================================================================

/// Seq.toList xs → iterate and cons each element
let private seqToListRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let listType = NativeType.TList elemType

    // Fold over seq, accumulating reversed list, then reverse at end
    // This is O(n) instead of O(n²) for naive append approach
    let consToAcc accId elemId =
        recipe {
            // Prepend: elem :: acc (builds reversed list)
            return! cons elemId accId elemType
        }

    recipe {
        let! reversedList =
            seqFoldLeft (emptyList elemType) consToAcc inputSeqId elemType listType

        // Reverse the accumulated list
        // Use List.rev intrinsic (Baker will decompose this if needed)
        let revInfo = {
            Module = IntrinsicModule.List
            Operation = "rev"
            Category = IntrinsicCategory.Pure
            FullName = "List.rev"
        }
        let revFuncType = NativeType.TFun (listType, listType)
        let! revFuncId = createAndEmit (SemanticKind.Intrinsic revInfo) revFuncType
        return! app1 revFuncId reversedList listType
    }

//=============================================================================
// CONSUMER: SEQ.TOARRAY
//=============================================================================

/// Seq.toArray xs → collect to list then convert to array
let private seqToArrayRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let listType = NativeType.TList elemType
    let arrayType = mkArrayType elemType

    let consToAcc accId elemId =
        recipe {
            return! cons elemId accId elemType
        }

    recipe {
        // First convert to list
        let! listId =
            seqFoldLeft (emptyList elemType) consToAcc inputSeqId elemType listType

        // Reverse the list
        let revInfo = {
            Module = IntrinsicModule.List
            Operation = "rev"
            Category = IntrinsicCategory.Pure
            FullName = "List.rev"
        }
        let revFuncType = NativeType.TFun (listType, listType)
        let! revFuncId = createAndEmit (SemanticKind.Intrinsic revInfo) revFuncType
        let! reversedListId = app1 revFuncId listId listType

        // Convert list to array using List.toArray intrinsic
        let toArrayInfo = {
            Module = IntrinsicModule.List
            Operation = "toArray"
            Category = IntrinsicCategory.Pure
            FullName = "List.toArray"
        }
        let toArrayFuncType = NativeType.TFun (listType, arrayType)
        let! toArrayFuncId = createAndEmit (SemanticKind.Intrinsic toArrayInfo) toArrayFuncType
        return! app1 toArrayFuncId reversedListId arrayType
    }

//=============================================================================
// CONSUMER: SEQ.FOLD
//=============================================================================

/// Seq.fold f s xs → iterate applying f to accumulator
let private seqFoldRecipe
    (folderNodeId: NodeId)
    (stateNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    (stateType: NativeType)
    : Recipe<NodeId> =

    let applyFolder accId elemId =
        recipe {
            // f acc elem
            return! app2 folderNodeId accId elemId stateType
        }

    seqFoldLeft (ret stateNodeId) applyFolder inputSeqId elemType stateType

//=============================================================================
// CONSUMER: SEQ.EXISTS
//=============================================================================

/// Seq.exists p xs → short-circuit on first true
let private seqExistsRecipe
    (predicateNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    seqBoolFold
        false   // base: empty seq → false
        true    // short-circuit: predicate true → true
        (fun elemId -> app1 predicateNodeId elemId Types.boolType)
        inputSeqId
        elemType

//=============================================================================
// CONSUMER: SEQ.FORALL
//=============================================================================

/// Seq.forall p xs → short-circuit on first false
let private seqForallRecipe
    (predicateNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    // forall: short-circuit when predicate returns false
    // We invert the logic: check "not pred" and short-circuit on true
    seqBoolFold
        true    // base: empty seq → true (vacuously true)
        false   // short-circuit: predicate false → false
        (fun elemId ->
            recipe {
                // We want to short-circuit when pred is FALSE
                // boolFold short-circuits when result = shortCircuitValue
                // So we return the predicate result directly
                // and set shortCircuitValue = false
                return! app1 predicateNodeId elemId Types.boolType
            })
        inputSeqId
        elemType

//=============================================================================
// CONSUMER: SEQ.LENGTH
//=============================================================================

/// Seq.length xs → count elements
let private seqLengthRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    seqFoldLeft
        (intLit 0)
        (fun accId _elemId ->
            recipe {
                let! one = intLit 1
                return! add accId one Types.intType
            })
        inputSeqId
        elemType
        Types.intType

//=============================================================================
// CONSUMER: SEQ.ISEMPTY
//=============================================================================

/// Seq.isEmpty xs → check if first moveNext fails
let private seqIsEmptyRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    recipe {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // Check if first moveNext fails
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! hasElementId = app1 moveNextFuncId enumId Types.boolType

        // isEmpty = not hasElement
        return! not' hasElementId
    }

//=============================================================================
// CONSUMER: SEQ.HEAD
//=============================================================================

/// Seq.head xs → get first element (throws if empty)
let private seqHeadRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    recipe {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // Move to first element
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! _hasElementId = app1 moveNextFuncId enumId Types.boolType
        // Note: In a full implementation, we'd check hasElement and throw if false
        // For now, assume non-empty (Alex can add runtime check)

        // Get current element
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        return! app1 currentFuncId enumId elemType
    }

//=============================================================================
// CONSUMER: SEQ.TRYHEAD
//=============================================================================

/// Seq.tryHead xs → Some first element or None
let private seqTryHeadRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [elemType])

    recipe {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // Check if has element
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! hasElementId = app1 moveNextFuncId enumId Types.boolType

        // Get current if exists
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! elemId = app1 currentFuncId enumId elemType

        // Some elem
        let! someId = some elemId elemType

        // None
        let! noneId = none elemType

        // if hasElement then Some elem else None
        return! ifThenElse hasElementId someId noneId optionType
    }

//=============================================================================
// CONSUMER: SEQ.TRYPICK
//=============================================================================

/// Seq.tryPick f xs → first Some result from f
let private seqTryPickRecipe
    (chooserNodeId: NodeId)
    (inputSeqId: NodeId)
    (inputElemType: NativeType)
    (outputElemType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq inputElemType
    let enumType = NativeType.TSeqEnumerator inputElemType
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [outputElemType])
    let loopFuncType = NativeType.TFun (Types.unitType, optionType)

    recipe {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! hasNextId = app1 moveNextFuncId enumId Types.boolType

        // Get current
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, inputElemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! elemId = app1 currentFuncId enumId inputElemType

        // Apply chooser
        let! resultId = app1 chooserNodeId elemId optionType

        // Check if result is Some
        let! isSomeId = isSome resultId outputElemType

        // Recursive call
        let! loopRefId = varRef "loop" None loopFuncType
        let! unitId = createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        let! recurseCallId = app1 loopRefId unitId optionType

        // Inner if: if isSome result then result else recurse
        let! innerIfId = ifThenElse isSomeId resultId recurseCallId optionType

        // Base case: None
        let! noneId = none outputElemType

        // Outer if: if hasNext then innerIf else None
        let! outerIfId = ifThenElse hasNextId innerIfId noneId optionType

        // Lambda
        let! unitParamId = patternBinding "_" Types.unitType
        let lambdaKind = SemanticKind.Lambda (
            [("_", Types.unitType, unitParamId)],
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
        let! unitForCall = createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        return! app1 loopCallRefId unitForCall optionType
    }

//=============================================================================
// CONSUMER: SEQ.MAX
//=============================================================================

/// Seq.max xs → maximum element
let private seqMaxRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    recipe {
        // Get first element as initial max
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! _ = app1 moveNextFuncId enumId Types.boolType

        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! firstElemId = app1 currentFuncId enumId elemType

        // Now fold over remaining elements
        let loopFuncType = NativeType.TFun (elemType, elemType)

        let! maxParamId = patternBinding "currentMax" elemType
        do! bindVariable "currentMax" maxParamId elemType

        // Check if more elements
        let! hasNextId = app1 moveNextFuncId enumId Types.boolType

        // Get next element
        let! nextElemId = app1 currentFuncId enumId elemType

        // Compare: if next > currentMax then next else currentMax
        let! currentMaxRefId = varRef "currentMax" (Some maxParamId) elemType
        let! isGreaterId = gt nextElemId currentMaxRefId elemType
        let! newMaxId = ifThenElse isGreaterId nextElemId currentMaxRefId elemType

        // Recursive call
        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app1 loopRefId newMaxId elemType

        // Base case: return currentMax
        let! currentMaxReturnId = varRef "currentMax" (Some maxParamId) elemType

        // If hasNext then recurse else return currentMax
        let! ifNodeId = ifThenElse hasNextId recurseCallId currentMaxReturnId elemType

        // Lambda
        let lambdaKind = SemanticKind.Lambda (
            [("currentMax", elemType, maxParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]

        // Binding
        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        // Initial call with first element
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId firstElemId elemType
    }

//=============================================================================
// CONSUMER: SEQ.MIN
//=============================================================================

/// Seq.min xs → minimum element
let private seqMinRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    recipe {
        // Get first element as initial min
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! _ = app1 moveNextFuncId enumId Types.boolType

        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! firstElemId = app1 currentFuncId enumId elemType

        // Fold over remaining elements
        let loopFuncType = NativeType.TFun (elemType, elemType)

        let! minParamId = patternBinding "currentMin" elemType
        do! bindVariable "currentMin" minParamId elemType

        let! hasNextId = app1 moveNextFuncId enumId Types.boolType
        let! nextElemId = app1 currentFuncId enumId elemType

        let! currentMinRefId = varRef "currentMin" (Some minParamId) elemType
        let! isLessId = lt nextElemId currentMinRefId elemType
        let! newMinId = ifThenElse isLessId nextElemId currentMinRefId elemType

        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app1 loopRefId newMinId elemType

        let! currentMinReturnId = varRef "currentMin" (Some minParamId) elemType
        let! ifNodeId = ifThenElse hasNextId recurseCallId currentMinReturnId elemType

        let lambdaKind = SemanticKind.Lambda (
            [("currentMin", elemType, minParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]

        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId firstElemId elemType
    }

//=============================================================================
// CONSUMER: SEQ.MINBY
//=============================================================================

/// Seq.minBy f xs → element with minimum f value
let private seqMinByRecipe
    (projectionNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    (keyType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    recipe {
        // Get first element
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! _ = app1 moveNextFuncId enumId Types.boolType

        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! firstElemId = app1 currentFuncId enumId elemType

        // Fold with projection comparison
        let loopFuncType = NativeType.TFun (elemType, elemType)

        let! minParamId = patternBinding "currentMin" elemType
        do! bindVariable "currentMin" minParamId elemType

        let! hasNextId = app1 moveNextFuncId enumId Types.boolType
        let! nextElemId = app1 currentFuncId enumId elemType

        // Project both elements
        let! currentMinRefId = varRef "currentMin" (Some minParamId) elemType
        let! currentMinKeyId = app1 projectionNodeId currentMinRefId keyType
        let! nextKeyId = app1 projectionNodeId nextElemId keyType

        // Compare keys
        let! isLessId = lt nextKeyId currentMinKeyId keyType
        let! newMinId = ifThenElse isLessId nextElemId currentMinRefId elemType

        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app1 loopRefId newMinId elemType

        let! currentMinReturnId = varRef "currentMin" (Some minParamId) elemType
        let! ifNodeId = ifThenElse hasNextId recurseCallId currentMinReturnId elemType

        let lambdaKind = SemanticKind.Lambda (
            [("currentMin", elemType, minParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]

        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId firstElemId elemType
    }

//=============================================================================
// CONSUMER: SEQ.MAXBY
//=============================================================================

/// Seq.maxBy f xs → element with maximum f value
let private seqMaxByRecipe
    (projectionNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    (keyType: NativeType)
    : Recipe<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    recipe {
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = createAndEmit (SemanticKind.Intrinsic getEnumInfo) getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = createAndEmit (SemanticKind.Intrinsic moveNextInfo) moveNextFuncType
        let! _ = app1 moveNextFuncId enumId Types.boolType

        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = createAndEmit (SemanticKind.Intrinsic currentInfo) currentFuncType
        let! firstElemId = app1 currentFuncId enumId elemType

        let loopFuncType = NativeType.TFun (elemType, elemType)

        let! maxParamId = patternBinding "currentMax" elemType
        do! bindVariable "currentMax" maxParamId elemType

        let! hasNextId = app1 moveNextFuncId enumId Types.boolType
        let! nextElemId = app1 currentFuncId enumId elemType

        let! currentMaxRefId = varRef "currentMax" (Some maxParamId) elemType
        let! currentMaxKeyId = app1 projectionNodeId currentMaxRefId keyType
        let! nextKeyId = app1 projectionNodeId nextElemId keyType

        let! isGreaterId = gt nextKeyId currentMaxKeyId keyType
        let! newMaxId = ifThenElse isGreaterId nextElemId currentMaxRefId elemType

        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app1 loopRefId newMaxId elemType

        let! currentMaxReturnId = varRef "currentMax" (Some maxParamId) elemType
        let! ifNodeId = ifThenElse hasNextId recurseCallId currentMaxReturnId elemType

        let lambdaKind = SemanticKind.Lambda (
            [("currentMax", elemType, maxParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let! lambdaId = createWithChildren lambdaKind loopFuncType [ifNodeId]

        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId firstElemId elemType
    }

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// Try to decompose a Seq operation.
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
    // Producers
    | "map", [mapper; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runRecipe ctx (seqMapRecipe mapper xs elemType outElem))

    | "filter", [predicate; xs] ->
        Some (runRecipe ctx (seqFilterRecipe predicate xs elemType))

    | "collect", [mapper; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runRecipe ctx (seqCollectRecipe mapper xs elemType outElem))

    | "append", [xs; ys] ->
        Some (runRecipe ctx (seqAppendRecipe xs ys elemType))

    // Consumers
    | "toList", [xs] ->
        Some (runRecipe ctx (seqToListRecipe xs elemType))

    | "toArray", [xs] ->
        Some (runRecipe ctx (seqToArrayRecipe xs elemType))

    | "fold", [folder; state; xs] ->
        let stTy = stateType |> Option.defaultValue elemType
        Some (runRecipe ctx (seqFoldRecipe folder state xs elemType stTy))

    | "exists", [predicate; xs] ->
        Some (runRecipe ctx (seqExistsRecipe predicate xs elemType))

    | "forall", [predicate; xs] ->
        Some (runRecipe ctx (seqForallRecipe predicate xs elemType))

    | "length", [xs] ->
        Some (runRecipe ctx (seqLengthRecipe xs elemType))

    | "isEmpty", [xs] ->
        Some (runRecipe ctx (seqIsEmptyRecipe xs elemType))

    | "head", [xs] ->
        Some (runRecipe ctx (seqHeadRecipe xs elemType))

    | "tryHead", [xs] ->
        Some (runRecipe ctx (seqTryHeadRecipe xs elemType))

    | "tryPick", [chooser; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runRecipe ctx (seqTryPickRecipe chooser xs elemType outElem))

    | "max", [xs] ->
        Some (runRecipe ctx (seqMaxRecipe xs elemType))

    | "min", [xs] ->
        Some (runRecipe ctx (seqMinRecipe xs elemType))

    | "minBy", [projection; xs] ->
        let keyType = stateType |> Option.defaultValue elemType
        Some (runRecipe ctx (seqMinByRecipe projection xs elemType keyType))

    | "maxBy", [projection; xs] ->
        let keyType = stateType |> Option.defaultValue elemType
        Some (runRecipe ctx (seqMaxByRecipe projection xs elemType keyType))

    // Primitives - Alex witnesses directly
    | "empty", _
    | "getEnumerator", _ -> None

    | _ -> None

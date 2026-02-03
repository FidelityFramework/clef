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
// HELPER: Create intrinsic node
//=============================================================================

let private intrinsicNode (info: IntrinsicInfo) (ty: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Intrinsic info) ty []
        do! emit node
        return node.Id
    }

let private unitLit : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Literal NativeLiteral.Unit) Types.unitType []
        do! emit node
        return node.Id
    }

let private whileLoop (conditionId: NodeId) (bodyId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.WhileLoop (conditionId, bodyId)) Types.unitType [conditionId; bodyId]
        do! emit node
        return node.Id
    }

//=============================================================================
// CONSUMER PATTERN: Iterate seq with enumerator
//=============================================================================

/// Generate an enumerator-based iteration over a seq.
let private seqFoldLeft
    (initialAcc: SaturationParser<NodeId>)
    (combine: NodeId -> NodeId -> SaturationParser<NodeId>)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    (accType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let loopFuncType = NativeType.TFun (accType, accType)

    saturation {
        // Get enumerator: let enum = Seq.getEnumerator xs
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // Create parameter for accumulator
        let! accParamId = patternBinding "acc" accType
        do! withBinding "acc" accParamId accType

        // MoveNext check: SeqEnumerator.moveNext enum
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory  // mutates enumerator state
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! hasNextId = app1 moveNextFuncId enumId Types.boolType

        // Get current element: SeqEnumerator.current enum
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
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
        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("acc", accType, accParamId)],
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

        // Initial call: loop initAcc
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId initAccId accType
    }

/// Generate a boolean short-circuit iteration over a seq.
let private seqBoolFold
    (baseValue: bool)
    (shortCircuitValue: bool)
    (predicate: NodeId -> SaturationParser<NodeId>)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let loopFuncType = NativeType.TFun (Types.unitType, Types.boolType)

    saturation {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! hasNextId = app1 moveNextFuncId enumId Types.boolType

        // Get current
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        let! elemId = app1 currentFuncId enumId elemType

        // Apply predicate
        let! predResultId = predicate elemId

        // Short circuit value
        let! shortCircuitId = boolLit shortCircuitValue

        // Recursive call
        let! loopRefId = varRef "loop" None loopFuncType
        let! unitId = unitLit
        let! recurseCallId = app1 loopRefId unitId Types.boolType

        // Inner if: if pred then shortCircuit else recurse
        let! innerIfId = ifThenElse predResultId shortCircuitId recurseCallId Types.boolType

        // Base case
        let! baseId = boolLit baseValue

        // Outer if: if hasNext then innerIf else base
        let! outerIfId = ifThenElse hasNextId innerIfId baseId Types.boolType

        // Lambda (takes unit, returns bool)
        let! unitParamId = patternBinding "_" Types.unitType
        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("_", Types.unitType, unitParamId)],
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
        let! unitForCall = unitLit
        return! app1 loopCallRefId unitForCall Types.boolType
    }

//=============================================================================
// PRODUCER: SEQ.MAP
//=============================================================================

let private seqMapRecipe
    (mapperNodeId: NodeId)
    (inputSeqId: NodeId)
    (inputElemType: NativeType)
    (outputElemType: NativeType)
    : SaturationParser<NodeId> =

    let inputSeqType = NativeType.TSeq inputElemType
    let enumType = NativeType.TSeqEnumerator inputElemType

    saturation {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (inputSeqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! conditionId = app1 moveNextFuncId enumId Types.boolType

        // Get current element
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, inputElemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        let! elemId = app1 currentFuncId enumId inputElemType

        // Apply mapper: f elem
        let! mappedId = app1 mapperNodeId elemId outputElemType

        // Yield the mapped element
        let! yieldId = yield' mappedId outputElemType

        // While loop: while moveNext do yield f(current)
        let! whileBodyId = whileLoop conditionId yieldId

        // Seq expression wrapping the iteration
        let capture: CaptureInfo = { Name = "xs"; Type = inputSeqType; IsMutable = false; SourceNodeId = Some inputSeqId }
        let mapperCapture: CaptureInfo = { Name = "f"; Type = NativeType.TFun(inputElemType, outputElemType); IsMutable = false; SourceNodeId = Some mapperNodeId }
        return! seqExpr whileBodyId [capture; mapperCapture] outputElemType
    }

//=============================================================================
// PRODUCER: SEQ.FILTER
//=============================================================================

let private seqFilterRecipe
    (predicateNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    saturation {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! conditionId = app1 moveNextFuncId enumId Types.boolType

        // Get current
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        let! elemId = app1 currentFuncId enumId elemType

        // Apply predicate
        let! predResultId = app1 predicateNodeId elemId Types.boolType

        // Yield element (conditional)
        let! yieldId = yield' elemId elemType

        // Unit for else branch
        let! unitId = unitLit

        // If predicate then yield else skip
        let! conditionalYieldId = ifThenElse predResultId yieldId unitId Types.unitType

        // While loop
        let! whileBodyId = whileLoop conditionId conditionalYieldId

        // Seq expression
        let capture: CaptureInfo = { Name = "xs"; Type = seqType; IsMutable = false; SourceNodeId = Some inputSeqId }
        let predCapture: CaptureInfo = { Name = "p"; Type = NativeType.TFun(elemType, Types.boolType); IsMutable = false; SourceNodeId = Some predicateNodeId }
        return! seqExpr whileBodyId [capture; predCapture] elemType
    }

//=============================================================================
// PRODUCER: SEQ.COLLECT (flatMap/bind)
//=============================================================================

let private seqCollectRecipe
    (mapperNodeId: NodeId)
    (inputSeqId: NodeId)
    (inputElemType: NativeType)
    (outputElemType: NativeType)
    : SaturationParser<NodeId> =

    let inputSeqType = NativeType.TSeq inputElemType
    let outputSeqType = NativeType.TSeq outputElemType
    let enumType = NativeType.TSeqEnumerator inputElemType

    saturation {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (inputSeqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! conditionId = app1 moveNextFuncId enumId Types.boolType

        // Get current
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, inputElemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        let! elemId = app1 currentFuncId enumId inputElemType

        // Apply mapper to get inner seq: f elem
        let! innerSeqId = app1 mapperNodeId elemId outputSeqType

        // Yield! the inner seq (flattens)
        let! yieldBangId = yieldBang innerSeqId outputElemType

        // While loop
        let! whileBodyId = whileLoop conditionId yieldBangId

        // Seq expression
        let capture: CaptureInfo = { Name = "xs"; Type = inputSeqType; IsMutable = false; SourceNodeId = Some inputSeqId }
        let mapperCapture: CaptureInfo = { Name = "f"; Type = NativeType.TFun(inputElemType, outputSeqType); IsMutable = false; SourceNodeId = Some mapperNodeId }
        return! seqExpr whileBodyId [capture; mapperCapture] outputElemType
    }

//=============================================================================
// PRODUCER: SEQ.APPEND
//=============================================================================

let private seqAppendRecipe
    (seq1Id: NodeId)
    (seq2Id: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType

    saturation {
        // yield! xs
        let! yieldBang1Id = yieldBang seq1Id elemType

        // yield! ys
        let! yieldBang2Id = yieldBang seq2Id elemType

        // Sequential: yield! xs; yield! ys
        let! state = getUserState
        let seqKind = SemanticKind.Sequential [yieldBang1Id; yieldBang2Id]
        let seqBodyNode = mkNode state seqKind Types.unitType [yieldBang1Id; yieldBang2Id]
        do! emit seqBodyNode
        let seqBodyId = seqBodyNode.Id

        // Seq expression
        let capture1: CaptureInfo = { Name = "xs"; Type = seqType; IsMutable = false; SourceNodeId = Some seq1Id }
        let capture2: CaptureInfo = { Name = "ys"; Type = seqType; IsMutable = false; SourceNodeId = Some seq2Id }
        return! seqExpr seqBodyId [capture1; capture2] elemType
    }

//=============================================================================
// CONSUMER: SEQ.TOLIST
//=============================================================================

/// Seq.toList xs → iterate and cons each element
/// Also aliased as List.ofSeq
let seqToListRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let listType = NativeType.TList elemType

    // Fold over seq, accumulating reversed list, then reverse at end
    let consToAcc accId elemId =
        saturation {
            // Prepend: elem :: acc (builds reversed list)
            return! cons elemId accId elemType
        }

    saturation {
        let! reversedList =
            seqFoldLeft (emptyList elemType) consToAcc inputSeqId elemType listType

        // Reverse the accumulated list
        let revInfo = {
            Module = IntrinsicModule.List
            Operation = "rev"
            Category = IntrinsicCategory.Pure
            FullName = "List.rev"
        }
        let revFuncType = NativeType.TFun (listType, listType)
        let! revFuncId = intrinsicNode revInfo revFuncType
        return! app1 revFuncId reversedList listType
    }

//=============================================================================
// CONSUMER: SEQ.TOARRAY
//=============================================================================

let private seqToArrayRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let listType = NativeType.TList elemType
    let arrayType = NativeType.TApp(Types.arrayTyCon, [elemType])

    let consToAcc accId elemId =
        saturation {
            return! cons elemId accId elemType
        }

    saturation {
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
        let! revFuncId = intrinsicNode revInfo revFuncType
        let! reversedListId = app1 revFuncId listId listType

        // Convert list to array using List.toArray intrinsic
        let toArrayInfo = {
            Module = IntrinsicModule.List
            Operation = "toArray"
            Category = IntrinsicCategory.Pure
            FullName = "List.toArray"
        }
        let toArrayFuncType = NativeType.TFun (listType, arrayType)
        let! toArrayFuncId = intrinsicNode toArrayInfo toArrayFuncType
        return! app1 toArrayFuncId reversedListId arrayType
    }

//=============================================================================
// CONSUMER: SEQ.FOLD
//=============================================================================

let private seqFoldRecipe
    (folderNodeId: NodeId)
    (stateNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    (stateType: NativeType)
    : SaturationParser<NodeId> =

    let applyFolder accId elemId =
        saturation {
            // f acc elem
            return! app2 folderNodeId accId elemId stateType
        }

    seqFoldLeft (preturn stateNodeId) applyFolder inputSeqId elemType stateType

//=============================================================================
// CONSUMER: SEQ.EXISTS
//=============================================================================

let private seqExistsRecipe
    (predicateNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    seqBoolFold
        false   // base: empty seq → false
        true    // short-circuit: predicate true → true
        (fun elemId -> app1 predicateNodeId elemId Types.boolType)
        inputSeqId
        elemType

//=============================================================================
// CONSUMER: SEQ.FORALL
//=============================================================================

let private seqForallRecipe
    (predicateNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    seqBoolFold
        true    // base: empty seq → true (vacuously true)
        false   // short-circuit: predicate false → false
        (fun elemId ->
            saturation {
                return! app1 predicateNodeId elemId Types.boolType
            })
        inputSeqId
        elemType

//=============================================================================
// CONSUMER: SEQ.LENGTH
//=============================================================================

let private seqLengthRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    seqFoldLeft
        (intLit 0)
        (fun accId _elemId ->
            saturation {
                let! one = intLit 1
                return! add accId one Types.intType
            })
        inputSeqId
        elemType
        Types.intType

//=============================================================================
// CONSUMER: SEQ.ISEMPTY
//=============================================================================

let private seqIsEmptyRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    saturation {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // Check if first moveNext fails
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! hasElementId = app1 moveNextFuncId enumId Types.boolType

        // isEmpty = not hasElement
        return! not' hasElementId
    }

//=============================================================================
// CONSUMER: SEQ.HEAD
//=============================================================================

let private seqHeadRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType

    saturation {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // Move to first element
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! _hasElementId = app1 moveNextFuncId enumId Types.boolType

        // Get current element
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        return! app1 currentFuncId enumId elemType
    }

//=============================================================================
// CONSUMER: SEQ.TRYHEAD
//=============================================================================

let private seqTryHeadRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let optionType = NativeType.TApp (Types.optionTyCon, [elemType])

    saturation {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // Check if has element
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! hasElementId = app1 moveNextFuncId enumId Types.boolType

        // Get current if exists
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
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

let private seqTryPickRecipe
    (chooserNodeId: NodeId)
    (inputSeqId: NodeId)
    (inputElemType: NativeType)
    (outputElemType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq inputElemType
    let enumType = NativeType.TSeqEnumerator inputElemType
    let optionType = NativeType.TApp (Types.optionTyCon, [outputElemType])
    let loopFuncType = NativeType.TFun (Types.unitType, optionType)

    saturation {
        // Get enumerator
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        // MoveNext
        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! hasNextId = app1 moveNextFuncId enumId Types.boolType

        // Get current
        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, inputElemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        let! elemId = app1 currentFuncId enumId inputElemType

        // Apply chooser
        let! resultId = app1 chooserNodeId elemId optionType

        // Check if result is Some
        let! isSomeId = isSome resultId outputElemType

        // Recursive call
        let! loopRefId = varRef "loop" None loopFuncType
        let! unitId = unitLit
        let! recurseCallId = app1 loopRefId unitId optionType

        // Inner if: if isSome result then result else recurse
        let! innerIfId = ifThenElse isSomeId resultId recurseCallId optionType

        // Base case: None
        let! noneId = none outputElemType

        // Outer if: if hasNext then innerIf else None
        let! outerIfId = ifThenElse hasNextId innerIfId noneId optionType

        // Lambda
        let! unitParamId = patternBinding "_" Types.unitType
        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("_", Types.unitType, unitParamId)],
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
        let! unitForCall = unitLit
        return! app1 loopCallRefId unitForCall optionType
    }

//=============================================================================
// CONSUMER: SEQ.MAX
//=============================================================================

let private seqMaxRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let loopFuncType = NativeType.TFun (elemType, elemType)

    saturation {
        // Get enumerator and first element
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! _ = app1 moveNextFuncId enumId Types.boolType

        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        let! firstElemId = app1 currentFuncId enumId elemType

        // Create loop parameter
        let! maxParamId = patternBinding "currentMax" elemType
        do! withBinding "currentMax" maxParamId elemType

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
        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("currentMax", elemType, maxParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        // Binding
        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        // Initial call with first element
        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId firstElemId elemType
    }

//=============================================================================
// CONSUMER: SEQ.MIN
//=============================================================================

let private seqMinRecipe
    (inputSeqId: NodeId)
    (elemType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let loopFuncType = NativeType.TFun (elemType, elemType)

    saturation {
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! _ = app1 moveNextFuncId enumId Types.boolType

        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        let! firstElemId = app1 currentFuncId enumId elemType

        let! minParamId = patternBinding "currentMin" elemType
        do! withBinding "currentMin" minParamId elemType

        let! hasNextId = app1 moveNextFuncId enumId Types.boolType
        let! nextElemId = app1 currentFuncId enumId elemType

        let! currentMinRefId = varRef "currentMin" (Some minParamId) elemType
        let! isLessId = lt nextElemId currentMinRefId elemType
        let! newMinId = ifThenElse isLessId nextElemId currentMinRefId elemType

        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app1 loopRefId newMinId elemType

        let! currentMinReturnId = varRef "currentMin" (Some minParamId) elemType
        let! ifNodeId = ifThenElse hasNextId recurseCallId currentMinReturnId elemType

        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("currentMin", elemType, minParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId firstElemId elemType
    }

//=============================================================================
// CONSUMER: SEQ.MINBY
//=============================================================================

let private seqMinByRecipe
    (projectionNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    (keyType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let loopFuncType = NativeType.TFun (elemType, elemType)

    saturation {
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! _ = app1 moveNextFuncId enumId Types.boolType

        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        let! firstElemId = app1 currentFuncId enumId elemType

        let! minParamId = patternBinding "currentMin" elemType
        do! withBinding "currentMin" minParamId elemType

        let! hasNextId = app1 moveNextFuncId enumId Types.boolType
        let! nextElemId = app1 currentFuncId enumId elemType

        let! currentMinRefId = varRef "currentMin" (Some minParamId) elemType
        let! currentMinKeyId = app1 projectionNodeId currentMinRefId keyType
        let! nextKeyId = app1 projectionNodeId nextElemId keyType

        let! isLessId = lt nextKeyId currentMinKeyId keyType
        let! newMinId = ifThenElse isLessId nextElemId currentMinRefId elemType

        let! loopRefId = varRef "loop" None loopFuncType
        let! recurseCallId = app1 loopRefId newMinId elemType

        let! currentMinReturnId = varRef "currentMin" (Some minParamId) elemType
        let! ifNodeId = ifThenElse hasNextId recurseCallId currentMinReturnId elemType

        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("currentMin", elemType, minParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

        let! bindingId = letRecBind "loop" lambdaId loopFuncType

        let! loopCallRefId = varRef "loop" (Some bindingId) loopFuncType
        return! app1 loopCallRefId firstElemId elemType
    }

//=============================================================================
// CONSUMER: SEQ.MAXBY
//=============================================================================

let private seqMaxByRecipe
    (projectionNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    (keyType: NativeType)
    : SaturationParser<NodeId> =

    let seqType = NativeType.TSeq elemType
    let enumType = NativeType.TSeqEnumerator elemType
    let loopFuncType = NativeType.TFun (elemType, elemType)

    saturation {
        let getEnumInfo = {
            Module = IntrinsicModule.Seq
            Operation = "getEnumerator"
            Category = IntrinsicCategory.Pure
            FullName = "Seq.getEnumerator"
        }
        let getEnumFuncType = NativeType.TFun (seqType, enumType)
        let! getEnumFuncId = intrinsicNode getEnumInfo getEnumFuncType
        let! enumId = app1 getEnumFuncId inputSeqId enumType

        let moveNextInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "moveNext"
            Category = IntrinsicCategory.Memory
            FullName = "SeqEnumerator.moveNext"
        }
        let moveNextFuncType = NativeType.TFun (enumType, Types.boolType)
        let! moveNextFuncId = intrinsicNode moveNextInfo moveNextFuncType
        let! _ = app1 moveNextFuncId enumId Types.boolType

        let currentInfo = {
            Module = IntrinsicModule.SeqEnumerator
            Operation = "current"
            Category = IntrinsicCategory.Pure
            FullName = "SeqEnumerator.current"
        }
        let currentFuncType = NativeType.TFun (enumType, elemType)
        let! currentFuncId = intrinsicNode currentInfo currentFuncType
        let! firstElemId = app1 currentFuncId enumId elemType

        let! maxParamId = patternBinding "currentMax" elemType
        do! withBinding "currentMax" maxParamId elemType

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

        let! state = getUserState
        let lambdaKind = SemanticKind.Lambda (
            [("currentMax", elemType, maxParamId)],
            ifNodeId,
            [],
            Some "loop",
            LambdaContext.RegularClosure
        )
        let lambdaNode = mkNode state lambdaKind loopFuncType [ifNodeId]
        do! emit lambdaNode
        let lambdaId = lambdaNode.Id

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
        Some (runSaturation ctx (seqMapRecipe mapper xs elemType outElem))

    | "filter", [predicate; xs] ->
        Some (runSaturation ctx (seqFilterRecipe predicate xs elemType))

    | "collect", [mapper; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runSaturation ctx (seqCollectRecipe mapper xs elemType outElem))

    | "append", [xs; ys] ->
        Some (runSaturation ctx (seqAppendRecipe xs ys elemType))

    // Consumers
    | "toList", [xs] ->
        Some (runSaturation ctx (seqToListRecipe xs elemType))

    | "toArray", [xs] ->
        Some (runSaturation ctx (seqToArrayRecipe xs elemType))

    | "fold", [folder; state; xs] ->
        let stTy = stateType |> Option.defaultValue elemType
        Some (runSaturation ctx (seqFoldRecipe folder state xs elemType stTy))

    | "exists", [predicate; xs] ->
        Some (runSaturation ctx (seqExistsRecipe predicate xs elemType))

    | "forall", [predicate; xs] ->
        Some (runSaturation ctx (seqForallRecipe predicate xs elemType))

    | "length", [xs] ->
        Some (runSaturation ctx (seqLengthRecipe xs elemType))

    | "isEmpty", [xs] ->
        Some (runSaturation ctx (seqIsEmptyRecipe xs elemType))

    | "head", [xs] ->
        Some (runSaturation ctx (seqHeadRecipe xs elemType))

    | "tryHead", [xs] ->
        Some (runSaturation ctx (seqTryHeadRecipe xs elemType))

    | "tryPick", [chooser; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runSaturation ctx (seqTryPickRecipe chooser xs elemType outElem))

    | "max", [xs] ->
        Some (runSaturation ctx (seqMaxRecipe xs elemType))

    | "min", [xs] ->
        Some (runSaturation ctx (seqMinRecipe xs elemType))

    | "minBy", [projection; xs] ->
        let keyType = stateType |> Option.defaultValue elemType
        Some (runSaturation ctx (seqMinByRecipe projection xs elemType keyType))

    | "maxBy", [projection; xs] ->
        let keyType = stateType |> Option.defaultValue elemType
        Some (runSaturation ctx (seqMaxByRecipe projection xs elemType keyType))

    // Primitives - Alex witnesses directly
    | "empty", _
    | "getEnumerator", _ -> None

    | _ -> None

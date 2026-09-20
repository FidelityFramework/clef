// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Baker sequence recipes compose typed saturation ingredients.
/// Producer arguments are evaluated when the sequence is formed; generator
/// bodies execute on demand during enumeration. Explicit iterator operations,
/// callback applications and accumulator updates feed the later ownership,
/// evaluation, range, residence and continuation construction passes.
///
/// HOF OPERATIONS (Baker decomposes via combinators):
///
/// PRODUCERS (return lazy seq):
/// - map, filter, collect, append, take
/// These create new seq expressions that transform during iteration.
///
/// CONSUMERS (iterate seq, return non-seq):
/// - toList, toArray, fold, iter, exists, forall, length, isEmpty, head, tryHead,
///   max, min, minBy, maxBy, tryPick
/// These iterate the seq and accumulate/find results.
///
/// This catalog describes recipe composition. Public admission and native
/// coverage are recorded by the C-07 operation gates.
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
module Clef.Compiler.Baker.Recipes.SeqRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
module Options = Clef.Compiler.Baker.Ingredients.Options
module Sequences = Clef.Compiler.Baker.Ingredients.Sequences
module Continuations = Clef.Compiler.Baker.Ingredients.Continuations

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

    saturation {
        let! expansion = getExpansionId
        let name = sprintf "__seq_accumulator_%d" expansion
        let! initial = initialAcc
        let! accumulator = Continuations.mutableBinding name initial accType
        let! loop = Sequences.iterate inputSeqId elemType (fun current -> saturation {
            let! previous = varRef name (Some accumulator) accType
            let! updated = combine previous current
            return! Continuations.assign accumulator name accType updated
        })
        let! result = varRef name (Some accumulator) accType
        return! evaluateBefore [accumulator; loop] result accType
    }

/// A consumer evaluates every supplied value once before it starts pulling.
/// Callback references inside its loop refer to these explicit snapshots.
let private consumer arguments resultType bodyBuilder =
    saturation {
        let! origin = getUserState
        do! updateUserState (fun (state: SaturationState) -> { state with SourceRange = { origin.SourceRange with End = origin.SourceRange.Start } })
        let! snapshots =
            arguments
            |> List.mapi (fun index (value, valueType) -> saturation {
                let name = sprintf "__seq_operand_%d_%d" origin.ExpansionId index
                let! binding = letBind name value valueType
                let! reference = varRef name (Some binding) valueType
                return binding, reference
            })
            |> sequence
        let! body = bodyBuilder (List.map snd snapshots)
        do! updateUserState (fun state -> { state with SourceRange = origin.SourceRange })
        return! evaluateBefore (List.map fst snapshots) body resultType
    }

/// Preserve the last predicate result and stop before the next pull once it
/// differs from the empty result. Thus exists stops on true, forall on false.
let private seqBoolFold baseValue predicate inputSeqId elemType =
    saturation {
        let! expansion = getExpansionId
        let name = sprintf "__seq_boolean_%d" expansion
        let! initial = boolLit baseValue
        let! result = Continuations.mutableBinding name initial Types.boolType
        let guard pull = saturation {
            let! previous = varRef name (Some result) Types.boolType
            let! continuing = if baseValue then preturn previous else not' previous
            let! exhausted = boolLit false
            return! ifThenElse continuing pull exhausted Types.boolType
        }
        let! loop = Sequences.iterateWhile guard inputSeqId elemType (fun current -> saturation {
            let! tested = predicate current
            return! Continuations.assign result name Types.boolType tested
        })
        let! answer = varRef name (Some result) Types.boolType
        return! evaluateBefore [result; loop] answer Types.boolType
    }

//=============================================================================
// PRODUCERS: eager value capture, deferred generator work
//=============================================================================

/// Supplied expressions are evaluated in argument order in the forming scope.
/// The generator refers to those immutable snapshots; their captured storage
/// identities remain shared according to the ordinary closure contract.
let private producer (arguments: (NodeId * NativeType) list) (elementType: NativeType)
                     (enclosingFunction: string option)
                     (bodyBuilder: NodeId list -> SaturationParser<NodeId>) : SaturationParser<NodeId> =
    saturation {
        let! origin = getUserState
        // These nodes are synthesized at the call, not declarations of source
        // variables. Only the replacement expression claims the full call span.
        do! updateUserState (fun (state: SaturationState) -> { state with SourceRange = { origin.SourceRange with End = origin.SourceRange.Start } })
        let! captures =
            arguments |> List.mapi (fun index (value, valueType) -> saturation {
                let name = sprintf "__seq_capture_%d_%d" origin.ExpansionId index
                let! snapshot = letBind name value valueType
                return { Name = name; Type = valueType; IsMutable = false; SourceNodeId = Some snapshot }
            }) |> sequence
        let! localRefs = captures |> List.map (fun capture -> varRef capture.Name capture.SourceNodeId capture.Type) |> sequence
        let! body = bodyBuilder localRefs
        let! value = seqExpr body captures elementType enclosingFunction
        do! updateUserState (fun state -> { state with SourceRange = origin.SourceRange })
        return! evaluateBefore (captures |> List.choose (fun capture -> capture.SourceNodeId)) value (NativeType.TSeq elementType)
    }

let private transformRecipe operation callback input inputElement outputElement enclosingFunction =
    let callbackResult =
        match operation with
        | "filter" -> Types.boolType
        | "collect" -> NativeType.TSeq outputElement
        | _ -> outputElement
    let callbackType = NativeType.TFun (inputElement, callbackResult)
    producer [callback, callbackType; input, NativeType.TSeq inputElement] outputElement enclosingFunction (fun locals ->
        match locals with
        | [callbackRef; inputRef] ->
            Sequences.iterate inputRef inputElement (fun current -> saturation {
                let! transformed = app1 callbackRef current callbackResult
                match operation with
                | "filter" ->
                    let! yielded = yield' current
                    let! skipped = unitLit
                    return! ifThenElse transformed yielded skipped Types.unitType
                | "collect" -> return! yieldBang transformed
                | _ -> return! yield' transformed
            })
        | _ -> failwith "A sequence transformer requires its callback and input captures")

let private seqAppendRecipe first second elementType enclosingFunction =
    let sequenceType = NativeType.TSeq elementType
    producer [first, sequenceType; second, sequenceType] elementType enclosingFunction (fun locals ->
        match locals with
        | [firstRef; secondRef] -> saturation {
            let! firstYield = yieldBang firstRef
            let! secondYield = yieldBang secondRef
            return! evaluateBefore [firstYield] secondYield Types.unitType
          }
        | _ -> failwith "Sequence append requires both input captures")

/// Take checks its own remaining demand before asking the input to advance.
/// The counter is per enumeration; operands were captured at producer creation.
let private seqTakeRecipe count input elementType enclosingFunction =
    producer [count, Types.intType; input, NativeType.TSeq elementType] elementType enclosingFunction (fun locals ->
        match locals with
        | [countRef; inputRef] -> saturation {
            let! expansion = getExpansionId
            let name = sprintf "__seq_remaining_%d" expansion
            let! remaining = Continuations.mutableBinding name countRef Types.intType
            let guard pull = saturation {
                let! currentCount = varRef name (Some remaining) Types.intType
                let! zero = intLit 0
                let! positive = gt currentCount zero Types.intType
                let! exhausted = boolLit false
                return! ifThenElse positive pull exhausted Types.boolType
            }
            let! loop = Sequences.iterateWhile guard inputRef elementType (fun current -> saturation {
                let! currentCount = varRef name (Some remaining) Types.intType
                let! one = intLit 1
                let! next = sub currentCount one Types.intType
                let! decrement = Continuations.assign remaining name Types.intType next
                let! yielded = yield' current
                return! evaluateBefore [decrement] yielded Types.unitType
            })
            return! evaluateBefore [remaining] loop Types.unitType
          }
        | _ -> failwith "Sequence take requires its count and input captures")

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
        let! revFuncId = createAndEmit (SemanticKind.Intrinsic revInfo) revFuncType
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

let private seqFoldRecipe
    (folderNodeId: NodeId)
    (stateNodeId: NodeId)
    (inputSeqId: NodeId)
    (elemType: NativeType)
    (stateType: NativeType)
    : SaturationParser<NodeId> =

    let folderType = NativeType.TFun(stateType, NativeType.TFun(elemType, stateType))
    consumer [folderNodeId, folderType; stateNodeId, stateType; inputSeqId, NativeType.TSeq elemType] stateType (fun operands ->
        match operands with
        | [folder; initial; input] ->
            seqFoldLeft (preturn initial) (fun accumulator current -> app2 folder accumulator current stateType) input elemType stateType
        | _ -> failwith "Sequence fold requires its folder, initial state and input")

let private seqIterRecipe action input elementType =
    consumer [action, NativeType.TFun(elementType, Types.unitType); input, NativeType.TSeq elementType] Types.unitType (fun operands ->
        match operands with
        | [actionRef; inputRef] -> Sequences.iterate inputRef elementType (fun current -> app1 actionRef current Types.unitType)
        | _ -> failwith "Sequence iter requires its action and input")

//=============================================================================
// CONSUMER: SEQ.EXISTS
//=============================================================================

let private seqPredicateRecipe baseValue predicate input elementType =
    consumer [predicate, NativeType.TFun(elementType, Types.boolType); input, NativeType.TSeq elementType] Types.boolType (fun operands ->
        match operands with
        | [predicateRef; inputRef] ->
            seqBoolFold baseValue (fun current -> app1 predicateRef current Types.boolType) inputRef elementType
        | _ -> failwith "Sequence predicate requires its callback and input")

let private seqExistsRecipe predicate input elementType =
    seqPredicateRecipe false predicate input elementType

let private seqForallRecipe predicate input elementType =
    seqPredicateRecipe true predicate input elementType

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

/// Optional selection retains the chooser result once and stops before a
/// further pull after Some. Empty or entirely unselected inputs retain None.
/// The option payload type is independent of the sequence element type.
let private seqOptionalSelection input elementType resultType choose =
    saturation {
        let! expansion = getExpansionId
        let optionType = NativeType.TApp(Types.optionTyCon, [resultType])
        let resultName = sprintf "__seq_selection_%d" expansion
        let foundName = sprintf "__seq_selected_%d" expansion
        let! empty = Options.none resultType
        let! result = Continuations.mutableBinding resultName empty optionType
        let! no = boolLit false
        let! found = Continuations.mutableBinding foundName no Types.boolType
        let guard pull = saturation {
            let! selected = varRef foundName (Some found) Types.boolType
            let! searching = not' selected
            let! exhausted = boolLit false
            return! ifThenElse searching pull exhausted Types.boolType
        }
        let! loop = Sequences.iterateWhile guard input elementType (fun current -> saturation {
            let! chosen = choose current
            let name = sprintf "__seq_candidate_%d" expansion
            let! snapshot = letBind name chosen optionType
            let! candidate = varRef name (Some snapshot) optionType
            let! selected = Options.hasValue candidate resultType
            let! save = Continuations.assign result resultName optionType candidate
            let! stop = Continuations.assign found foundName Types.boolType selected
            return! evaluateBefore [snapshot; save] stop Types.unitType
        })
        let! answer = varRef resultName (Some result) optionType
        return! evaluateBefore [result; found; loop] answer optionType
    }

let private seqTryHeadRecipe input elementType =
    let optionType = NativeType.TApp(Types.optionTyCon, [elementType])
    consumer [input, NativeType.TSeq elementType] optionType (function
        | [inputRef] -> seqOptionalSelection inputRef elementType elementType (fun current -> Options.some current elementType)
        | _ -> failwith "Sequence tryHead requires its evaluated input")

//=============================================================================
// CONSUMER: SEQ.TRYPICK
//=============================================================================

let private seqTryPickRecipe chooser input elementType resultType =
    let optionType = NativeType.TApp(Types.optionTyCon, [resultType])
    let chooserType = NativeType.TFun(elementType, optionType)
    consumer [chooser, chooserType; input, NativeType.TSeq elementType] optionType (function
        | [chooserRef; inputRef] ->
            seqOptionalSelection inputRef elementType resultType (fun current -> app1 chooserRef current optionType)
        | _ -> failwith "Sequence tryPick requires its evaluated chooser and input")

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
    (enclosingFunction: string option)
    : Result option =

    match operation, args with
    // Producers
    | "map", [mapper; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runSaturation ctx (transformRecipe "map" mapper xs elemType outElem enclosingFunction))

    | "filter", [predicate; xs] ->
        Some (runSaturation ctx (transformRecipe "filter" predicate xs elemType elemType enclosingFunction))

    | "collect", [mapper; xs] ->
        let outElem = outputElemType |> Option.defaultValue elemType
        Some (runSaturation ctx (transformRecipe "collect" mapper xs elemType outElem enclosingFunction))

    | "append", [xs; ys] ->
        Some (runSaturation ctx (seqAppendRecipe xs ys elemType enclosingFunction))

    | "take", [count; xs] ->
        Some (runSaturation ctx (seqTakeRecipe count xs elemType enclosingFunction))

    // Consumers
    | "iter", [action; xs] ->
        Some (runSaturation ctx (seqIterRecipe action xs elemType))

    | "toList", [xs] ->
        Some (runSaturation ctx (seqToListRecipe xs elemType))

    | "toArray", [xs] ->
        Some (runSaturation ctx (seqToArrayRecipe xs elemType))

    | "fold", [folder; state; xs] ->
        stateType |> Option.map (fun stTy -> runSaturation ctx (seqFoldRecipe folder state xs elemType stTy))

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
        outputElemType |> Option.map (fun outElem -> runSaturation ctx (seqTryPickRecipe chooser xs elemType outElem))

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

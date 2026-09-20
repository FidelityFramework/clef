// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Shared sequence iteration structure, before suspension and frame settlement.
module Clef.Compiler.Baker.Ingredients.Sequences

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures

let private sequenceOperation modl operation argument argumentType resultType =
    saturation {
        let info = {
            Module = modl; Operation = operation
            Category = if operation = "moveNext" then IntrinsicCategory.Memory else IntrinsicCategory.Pure
            FullName = sprintf "%A.%s" modl operation
        }
        let! state = getUserState
        let functionNode = mkNode state (SemanticKind.Intrinsic info) (NativeType.TFun (argumentType, resultType)) []
        do! emit functionNode
        return! app1 functionNode.Id argument resultType
    }

let private whileLoop (conditionId: NodeId) (bodyId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.WhileLoop (conditionId, bodyId)) Types.unitType [conditionId; bodyId]
        do! emit node
        return node.Id
    }

/// Initialize enumeration before its loop in the caller's current scope.
/// Each successful pull binds current once before the supplied unit action;
/// exhaustion completes without evaluating that action. Source anchors and
/// expansion provenance remain those of the surrounding saturation state.
let private iterateWithGuard (guard: NodeId -> SaturationParser<NodeId>)
                             (input: NodeId) (elementType: NativeType)
                             (consume: NodeId -> SaturationParser<NodeId>) : SaturationParser<NodeId> =
    saturation {
        let! expansion = getExpansionId
        let enumType = NativeType.TSeqEnumerator elementType
        let enumName = sprintf "__seq_enumerator_%d" expansion
        let! enumerator = sequenceOperation IntrinsicModule.Seq "getEnumerator" input (NativeType.TSeq elementType) enumType
        let! enumBinding = letBind enumName enumerator enumType
        let! conditionRef = varRef enumName (Some enumBinding) enumType
        let! pull = sequenceOperation IntrinsicModule.SeqEnumerator "moveNext" conditionRef enumType Types.boolType
        let! condition = guard pull
        let! bodyRef = varRef enumName (Some enumBinding) enumType
        let! current = sequenceOperation IntrinsicModule.SeqEnumerator "current" bodyRef enumType elementType
        let currentName = sprintf "__seq_current_%d" expansion
        let! currentBinding = letBind currentName current elementType
        let! currentRef = varRef currentName (Some currentBinding) elementType
        let! action = consume currentRef
        // The same current value dominates every use in the supplied action.
        let! loopBody = evaluateBefore [currentBinding; currentRef] action Types.unitType
        let! loop = whileLoop condition loopBody
        return! evaluateBefore [enumBinding] loop Types.unitType
    }

/// Iterate every successful pull with the canonical current prefix.
let iterate input elementType consume = iterateWithGuard preturn input elementType consume

/// A bounded producer may guard demand with `if condition then pull else false`.
/// The supplied builder receives the exact pull identity; the resulting graph,
/// not recipe construction order, determines whether that pull is demanded.
let iterateWhile guard input elementType consume = iterateWithGuard guard input elementType consume

/// Keep the source site's identity and context as a unit expression. The
/// protocol lives beneath it, so enclosing branches/loops and proof incidence
/// still refer to the same source operation after fold-in.
let delegateAt (source: SemanticNode) input elementType : SaturationParser<NodeId> =
    saturation {
        let! body = iterate input elementType yield'
        do! enrich source (SemanticKind.Sequential [body]) Types.unitType [body] source.EmissionStrategy false
        return source.Id
    }

let delegationOrigin source input yielded : Hyperedge =
    { Sources = [source; input]; Target = yielded
      Class = EdgeClass.Provenance; Role = EdgeRole.DelegationOrigin; Ordinal = 0 }

/// Exact iterator-instance evidence, independent of local evaluation facts.
let currentAdmitted enumerator guard loop current : Hyperedge =
    { Sources = [enumerator; guard; loop]; Target = current
      Class = EdgeClass.Suspension; Role = EdgeRole.IteratorCurrentAdmitted; Ordinal = 0 }

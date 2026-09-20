// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Certify the exact shared iterate protocol. A current read outside this
/// proven true-guard prefix remains unadmitted; no general dominance is guessed.
module Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Sequences
open Clef.Compiler.Baker.Ingredients.Closures

/// Keep occurrences, including repeated slots in one container. A good guarded
/// occurrence cannot authorize another structural demand for the same read.
let structuralConsumers (graph: SemanticGraph) =
    graph.Nodes.Values
    |> Seq.filter _.IsReachable
    |> Seq.collect structuralIncidence
    |> Seq.filter Hyperedge.isStructural
    |> Seq.collect (fun edge -> edge.Sources |> Seq.map (fun source -> source, edge.Target))
    |> Seq.groupBy fst
    |> Seq.map (fun (source, incidence) -> source, incidence |> Seq.map snd |> Seq.toList)
    |> Map.ofSeq

let forLoop (graph: SemanticGraph) (consumers: Map<NodeId, NodeId list>) (loop: SemanticNode) : Hyperedge option =
    let resident id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
    let solelyWithin source container = consumers.TryFind source = Some [container]
    let reference id =
        resident id |> Option.bind (fun node ->
            match node.Kind with SemanticKind.VarRef(_, Some declaration) -> Some(declaration, node.Type) | _ -> None)
    let application modl operation id =
        resident id |> Option.bind (fun node ->
            match node.Kind with
            | SemanticKind.Application(callee, [argument]) ->
                resident callee |> Option.bind (fun functionNode ->
                    match functionNode.Kind with
                    | SemanticKind.Intrinsic info when info.Module = modl && info.Operation = operation -> Some(argument, node.Type)
                    | _ -> None)
            | _ -> None)
    let successfulPull guard =
        match application IntrinsicModule.SeqEnumerator "moveNext" guard with
        | Some pull -> Some pull
        | None ->
            // True for this exact conditional implies that its selected pull
            // succeeded. A true fallback, duplicated pull occurrence or body
            // action before current cannot supply this premise.
            match resident guard with
            | Some { Kind = SemanticKind.IfThenElse(demand, pull, Some exhausted); Type = guardType }
                when guardType = Types.boolType && solelyWithin pull guard ->
                match resident demand, resident exhausted with
                | Some { Type = demandType }, Some { Kind = SemanticKind.Literal(NativeLiteral.Bool false); Type = exhaustedType }
                    when demandType = Types.boolType && exhaustedType = Types.boolType ->
                    application IntrinsicModule.SeqEnumerator "moveNext" pull
                | _ -> None
            | _ -> None
    match loop.Kind with
    | SemanticKind.WhileLoop(guard, body) when loop.IsReachable && solelyWithin guard loop.Id ->
        match successfulPull guard, resident body with
        | Some(guardArgument, guardType), Some { Kind = SemanticKind.Sequential [currentBindingId; currentRefId; action] }
            when guardType = Types.boolType && (resident action).IsSome ->
            match reference guardArgument, resident currentBindingId, reference currentRefId with
            | Some(enumeratorId, enumRefType),
              Some { Kind = SemanticKind.Binding(_, false, false, _); Children = [currentCall]; Type = currentType },
              Some(actualCurrentBinding, currentRefType)
                when actualCurrentBinding = currentBindingId && currentType = currentRefType
                     && solelyWithin currentCall currentBindingId
                     && solelyWithin currentBindingId body
                     && solelyWithin body loop.Id ->
                match resident enumeratorId, application IntrinsicModule.SeqEnumerator "current" currentCall with
                | Some { Kind = SemanticKind.Binding(_, false, false, _); Children = [initialization]; Type = NativeType.TSeqEnumerator element },
                  Some(currentArgument, resultType)
                    when resultType = element && currentType = element && enumRefType = NativeType.TSeqEnumerator element ->
                    match reference currentArgument, application IntrinsicModule.Seq "getEnumerator" initialization with
                    | Some(actualEnumerator, currentEnumType), Some(input, initializerType)
                        when actualEnumerator = enumeratorId && currentEnumType = enumRefType && initializerType = enumRefType ->
                        match resident input with
                        | Some { Type = NativeType.TSeq inputElement } when inputElement = element ->
                            Some(currentAdmitted enumeratorId guard loop.Id currentCall)
                        | _ -> None
                    | _ -> None
                | _ -> None
            | _ -> None
        | _ -> None
    | _ -> None

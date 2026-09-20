// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Finite source-origin propagation for sequence values. A singleton known
/// origin is evidence for eliding the function half of (moveNext, environment).
/// Unknown alternatives remain in the set and prevent that elision.
module Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

[<RequireQualifiedAccess>]
type Origin = Known of NodeId | Unknown of NodeId

let private sequenceType ty =
    match applySubst ty with NativeType.TSeq _ | NativeType.TSeqEnumerator _ -> true | _ -> false

let settle (graph: SemanticGraph) (curry: CurryInfo) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    // Read the same declaration-currying boundary as Curry.normalize, before
    // that later pass has physically flattened its lambdas/applications.
    let isFunctionValue (node: SemanticNode) =
        [ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
        |> List.exists (fun key -> node.Metadata.TryFind key = Some (MetadataValue.Bool true))
    let rec declarationChain seen parameters body =
        if Set.contains body seen then parameters, body else
        match nodes.TryFind body with
        | Some ({ Kind = SemanticKind.Lambda (more, next, _, _, _) } as node) when not (isFunctionValue node) ->
            declarationChain (Set.add body seen) (parameters @ more) next
        | _ -> parameters, body
    let rec callable seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } -> Some (declarationChain seen parameters body)
        | Some { Kind = SemanticKind.VarRef (_, Some definition) } -> callable seen definition
        | Some { Kind = SemanticKind.Binding _; Children = [value] } -> callable seen value
        | Some { Kind = SemanticKind.TypeAnnotation (value, _) } -> callable seen value
        | _ -> None
    let rec applicationChain seen callee arguments =
        if Set.contains callee seen then callee, arguments else
        let seen = Set.add callee seen
        match nodes.TryFind callee with
        | Some { Kind = SemanticKind.Application (inner, earlier) } -> applicationChain seen inner (earlier @ arguments)
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> applicationChain seen inner arguments
        | _ -> callee, arguments
    let calls = nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Application (callee, arguments) ->
            let callee, arguments =
                match curry.SaturatedCalls.TryFind id with
                | Some call -> call.TargetBindingId, call.AllArgNodes
                | None -> applicationChain Set.empty callee arguments
            callable Set.empty callee |> Option.bind (fun (parameters, body) ->
                if parameters.Length = arguments.Length then Some (id, parameters, arguments, body) else None)
        | _ -> None)
    let parameterInputs =
        calls |> List.collect (fun (_, parameters, arguments, _) ->
            List.zip parameters arguments |> List.map (fun ((_, _, parameter), argument) -> parameter, argument))
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ pairs -> List.map snd pairs)
    let callResults = calls |> List.map (fun (id, _, _, body) -> id, body) |> Map.ofList
    let mutations =
        nodes |> Map.toList |> List.choose (fun (_, node) ->
            match node.Kind with
            | SemanticKind.Set (target, value) ->
                match nodes.TryFind target with
                | Some { Kind = SemanticKind.VarRef (_, Some declaration) } -> Some (declaration, value)
                | _ -> None
            | _ -> None)
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ pairs -> List.map snd pairs)
    let yielded =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources, nodes.TryFind edge.Target with
            | EdgeClass.Suspension, EdgeRole.Delimiter, [owner; _], Some { Kind = SemanticKind.Yield payload } -> Some (owner, payload)
            | _ -> None)
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ pairs -> List.map snd pairs)
    let tracked = nodes |> Map.filter (fun _ node -> sequenceType node.Type)
    let rec fixedPoint (facts: Map<NodeId, Set<Origin>>) =
        let read id = facts.TryFind id |> Option.defaultValue Set.empty
        let union ids = ids |> List.fold (fun values id -> Set.union values (read id)) Set.empty
        let next = tracked |> Map.map (fun id node ->
            let unknown () = Set.singleton (Origin.Unknown id)
            let produced =
                match node.Kind with
                | SemanticKind.SeqExpr _ -> Set.singleton (Origin.Known id)
                | SemanticKind.ContinuationAllocate owner -> Set.singleton (Origin.Known owner)
                | SemanticKind.Binding _ -> union node.Children
                | SemanticKind.VarRef (_, Some declaration) -> read declaration
                | SemanticKind.PatternBinding _ ->
                    match parameterInputs.TryFind id with Some arguments -> union arguments | None -> unknown ()
                | SemanticKind.TypeAnnotation (value, _) -> read value
                | SemanticKind.Sequential values -> values |> List.tryLast |> Option.map read |> Option.defaultWith unknown
                | SemanticKind.IfThenElse (_, yes, Some no) -> union [yes; no]
                | SemanticKind.Application (callee, [argument]) ->
                    match nodes.TryFind callee with
                    | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Seq; Operation = "getEnumerator" } } -> read argument
                    | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.SeqEnumerator; Operation = "current" } } ->
                        read argument |> Set.fold (fun values origin ->
                            let current =
                                match origin with
                                | Origin.Known owner -> yielded.TryFind owner |> Option.map union |> Option.defaultWith unknown
                                | Origin.Unknown site -> Set.singleton (Origin.Unknown site)
                            Set.union values current) Set.empty
                    | _ -> callResults.TryFind id |> Option.map read |> Option.defaultWith unknown
                | SemanticKind.Application _ -> callResults.TryFind id |> Option.map read |> Option.defaultWith unknown
                | _ -> unknown ()
            let assigned = mutations.TryFind id |> Option.map union |> Option.defaultValue Set.empty
            Set.union (read id) (Set.union produced assigned))
        if next = facts then facts else fixedPoint next
    let facts = fixedPoint (tracked |> Map.map (fun _ _ -> Set.empty))
    let unique = facts |> Map.toList |> List.choose (fun (id, origins) ->
        match Set.toList origins with [Origin.Known owner] -> Some (id, owner) | _ -> None) |> Map.ofList
    unique, facts

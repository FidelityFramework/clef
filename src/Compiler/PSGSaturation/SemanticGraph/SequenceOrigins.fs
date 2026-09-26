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

let settle (graph: SemanticGraph) (_curry: CurryInfo) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    // Actual callable boundaries own formal/actual and returned-value flow.
    // Earlier supplies in declaration partials remain inputs, while a returned
    // callable is a separate invocation; its arguments are not flattened into
    // the first call. Opaque alternatives remain visible beside known targets.
    let calls = CallableOrigins.resolve graph
    let parameterInputs =
        calls.ParameterInputs |> Map.map (fun _ inputs -> inputs |> List.map snd |> List.distinct)
    let environmentInputs =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources, nodes.TryFind edge.Target with
            | EdgeClass.Provenance, EdgeRole.EnvironmentCapture false, [owner; slot; value],
              Some { Kind = SemanticKind.EnvironmentCreate(actual, initializers) }
                when owner = actual && List.contains (slot, value) initializers -> Some((owner, slot), value)
            | _ -> None)
        |> List.groupBy fst |> Map.ofList
        |> Map.map (fun _ rows -> rows |> List.map snd |> List.distinct)
    let environmentInput environment slot =
        ClosureEnvironments.tryEnvironmentOwner graph environment
        |> Option.bind (fun owner ->
            match environmentInputs.TryFind (owner, slot) with Some [value] -> Some value | _ -> None)
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
        let callResult id =
            match calls.Calls.TryFind id with
            | Some call ->
                let known = call.Targets |> List.map _.Body |> union
                if call.Unknown then Set.add (Origin.Unknown id) known else known
            | None -> Set.singleton (Origin.Unknown id)
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
                | SemanticKind.EnvironmentRead(environment, slot) ->
                    environmentInput environment slot |> Option.map read |> Option.defaultWith unknown
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
                    | _ -> callResult id
                | SemanticKind.Application _ -> callResult id
                | _ -> unknown ()
            let assigned = mutations.TryFind id |> Option.map union |> Option.defaultValue Set.empty
            Set.union (read id) (Set.union produced assigned))
        if next = facts then facts else fixedPoint next
    let facts = fixedPoint (tracked |> Map.map (fun _ _ -> Set.empty))
    let unique = facts |> Map.toList |> List.choose (fun (id, origins) ->
        match Set.toList origins with [Origin.Known owner] -> Some (id, owner) | _ -> None) |> Map.ofList
    unique, facts

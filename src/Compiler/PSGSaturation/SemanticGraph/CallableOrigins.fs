// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Read actual callable boundaries from resident value flow. A function's type
/// supplies the types at a proved boundary; it never supplies the native arity.
module Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins

open System.Collections.Generic
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

/// One stage of an application whose complete argument list crosses a returned
/// function boundary. The arity is established from every possible callee.
type Stage = { Arguments: NodeId list; ResultType: NativeType }

type private Origin = NodeId * int

let private isFunctionValue (node: SemanticNode) =
    [ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
    |> List.exists (fun key -> node.Metadata.TryFind key = Some (MetadataValue.Bool true))

/// Synthetic parameter tails belong to one declaration; a new function expression
/// in its body is a returned value, including a unit-parameter function.
let rec private shape (nodes: Map<NodeId, SemanticNode>) id =
    match nodes.TryFind id with
    | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } ->
        match nodes.TryFind body with
        | Some ({ Kind = SemanticKind.Lambda _ } as inner) when not (isFunctionValue inner) ->
            shape nodes body |> Option.map (fun (rest, result) -> parameters @ rest, result)
        | _ -> Some (parameters, body)
    | _ -> None

let private afterArguments count ty =
    let rec drop remaining ty =
        if remaining = 0 then Some ty
        else
            match applySubst ty with
            | NativeType.TFun (_, result) -> drop (remaining - 1) result
            | _ -> None
    drop count ty

/// A finite origin analysis over declaration, parameter, result and aggregate
/// edges. Unknown callable leaves remain explicit origins, preventing a known
/// candidate from silently standing in for an opaque alternative.
let applicationStages (graph: SemanticGraph) : Map<NodeId, Stage list> =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let facts = Dictionary<NodeId, Set<Origin>>()
    let fields = Dictionary<NodeId * string, Set<Origin>>()
    let read id = match facts.TryGetValue id with true, values -> values | _ -> Set.empty
    let mutable changed = false
    let add id values =
        let old = read id
        let combined = Set.union old values
        if old <> combined then
            facts[id] <- combined
            changed <- true
    let union ids = ids |> Seq.map read |> Seq.fold Set.union Set.empty
    let shapes =
        nodes |> Map.toSeq |> Seq.choose (fun (id, _) -> shape nodes id |> Option.map (fun value -> id, value)) |> Map.ofSeq

    for KeyValue(id, node) in nodes do
        match node.Kind with
        | SemanticKind.Lambda _ | SemanticKind.RecordExpr _ | SemanticKind.TupleExpr _
        | SemanticKind.DUConstruct _ | SemanticKind.UnionCase _ -> add id (Set.singleton (id, 0))
        | SemanticKind.Intrinsic _ | SemanticKind.PlatformBinding _ ->
            match applySubst node.Type with
            | NativeType.TFun _ -> add id (Set.singleton (id, 0))
            | _ -> ()
        | _ -> ()

    let rec invoke seen (origins: Set<Origin>) (arguments: NodeId list) =
        origins |> Set.fold (fun results (id, offset) ->
            let key = id, offset, arguments.Length
            if Set.contains key seen then results
            else
                match shapes.TryFind id with
                | Some (parameters, body) ->
                    let total = max 1 parameters.Length
                    let available = total - offset
                    let supplied = min available arguments.Length
                    parameters |> List.skip (min offset parameters.Length) |> List.truncate supplied
                    |> List.iteri (fun index (_, _, parameter) -> add parameter (read arguments[index]))
                    let produced =
                        if supplied < available then Set.singleton (id, offset + supplied)
                        elif arguments.Length = supplied then read body
                        else invoke (Set.add key seen) (read body) (List.skip supplied arguments)
                    Set.union results produced
                | None -> Set.add (id, -1) results) Set.empty

    changed <- true
    let mutable seedUnknown = true
    while changed || seedUnknown do
        if not changed then
            // A callable or aggregate with no resident producing edge is
            // opaque. Its projections must remain in later joins beside any
            // known candidate; an absent origin is not an absent alternative.
            seedUnknown <- false
            for KeyValue(id, node) in nodes do
                match applySubst node.Type with
                | NativeType.TFun _ | NativeType.TApp _ | NativeType.TTuple _
                | NativeType.TAnon _ | NativeType.TUnion _ when Set.isEmpty (read id) ->
                    add id (Set.singleton (id, -1))
                | _ -> ()
        changed <- false
        for KeyValue(id, node) in nodes do
            let values =
                match node.Kind with
                | SemanticKind.Binding _ -> union node.Children
                | SemanticKind.VarRef (_, Some definition) -> read definition
                | SemanticKind.TypeAnnotation (value, _) -> read value
                | SemanticKind.Sequential expressions -> expressions |> List.tryLast |> Option.map read |> Option.defaultValue Set.empty
                | SemanticKind.IfThenElse (_, yes, no) -> union (yes :: Option.toList no)
                | SemanticKind.Match (_, cases) -> union (cases |> List.map (fun arm -> arm.Body))
                | SemanticKind.CaseElimination (_, arms) -> union (arms |> List.map (fun arm -> arm.Body))
                | SemanticKind.Application (callee, arguments) -> invoke Set.empty (read callee) arguments
                | SemanticKind.Set (target, value) ->
                    match nodes.TryFind target with
                    | Some { Kind = SemanticKind.VarRef (_, Some definition) } -> add definition (read value)
                    | Some { Kind = SemanticKind.Binding _ } -> add target (read value)
                    | _ -> ()
                    Set.empty
                | SemanticKind.DUEliminate (value, tag, _, _) ->
                    read value |> Set.fold (fun values (origin, _) ->
                        let payload =
                            match nodes.TryFind origin with
                            | Some { Kind = SemanticKind.DUConstruct (_, actual, payload, _) }
                            | Some { Kind = SemanticKind.UnionCase (_, actual, payload) } ->
                                if actual = tag then payload |> Option.map read |> Option.defaultValue Set.empty
                                else Set.empty
                            | _ -> Set.singleton (origin, -1)
                        Set.union values payload) Set.empty
                | SemanticKind.TupleGet (value, index) ->
                    read value |> Set.fold (fun values (origin, _) ->
                        let element =
                            match nodes.TryFind origin with
                            | Some { Kind = SemanticKind.TupleExpr elements } ->
                                elements |> List.tryItem index |> Option.map read |> Option.defaultValue Set.empty
                            | _ -> Set.singleton (origin, -1)
                        Set.union values element) Set.empty
                | SemanticKind.FieldGet (value, name) ->
                    read value |> Set.fold (fun values (origin, _) ->
                        let initial =
                            match nodes.TryFind origin with
                            | Some { Kind = SemanticKind.RecordExpr (members, _) } -> members |> List.tryPick (fun (field, value) -> if field = name then Some (read value) else None) |> Option.defaultValue (Set.singleton (origin, -1))
                            | _ -> Set.singleton (origin, -1)
                        let assigned = match fields.TryGetValue ((origin, name)) with true, values -> values | _ -> Set.empty
                        Set.union values (Set.union initial assigned)) Set.empty
                | SemanticKind.FieldSet (value, name, assigned) ->
                    for origin, _ in read value do
                        let old = match fields.TryGetValue ((origin, name)) with true, values -> values | _ -> Set.empty
                        let combined = Set.union old (read assigned)
                        if old <> combined then
                            fields[(origin, name)] <- combined
                            changed <- true
                    Set.empty
                | _ -> Set.empty
            add id values

    let boundary origins =
        if Set.isEmpty origins then None
        else
            let counts = origins |> Set.toList |> List.map (fun (id, offset) ->
                shapes.TryFind id |> Option.map (fun (parameters, _) -> max 1 parameters.Length - offset))
            match List.distinct counts with
            | [Some count] when count > 0 -> Some count
            | _ -> None
    let returned origins =
        origins |> Set.fold (fun values (id, _) ->
            match shapes.TryFind id with
            | Some (_, body) -> Set.union values (read body)
            | None -> values) Set.empty
    let rec stages origins ty (arguments: NodeId list) =
        match boundary origins with
        | Some count when arguments.Length >= count ->
            afterArguments count ty |> Option.bind (fun resultType ->
                let stage = { Arguments = List.take count arguments; ResultType = resultType }
                if arguments.Length = count then Some [stage]
                else stages (returned origins) resultType (List.skip count arguments) |> Option.map (fun rest -> stage :: rest))
        | _ -> None
    nodes |> Map.toSeq |> Seq.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Application (callee, arguments) ->
            stages (read callee) nodes[callee].Type arguments
            |> Option.bind (fun plan -> if plan.Length > 1 then Some (id, plan) else None)
        | _ -> None) |> Map.ofSeq

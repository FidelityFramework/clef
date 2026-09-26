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

/// A complete invocation at an actual callable boundary. Parameters already
/// supplied by an earlier partial application are represented by ParameterInputs.
type CallTarget = {
    Lambda: NodeId
    Parameters: (string * NativeType * NodeId) list
    Arguments: NodeId list
    Body: NodeId
}
type ResolvedCall = { Targets: CallTarget list; Unknown: bool }
type Resolution = {
    Calls: Map<NodeId, ResolvedCall>
    ParameterInputs: Map<NodeId, (NodeId * NodeId) list>
    Lambdas: Map<NodeId, NodeId>
}

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
let private analyze (graph: SemanticGraph) =
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
    let captures =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources, nodes.TryFind edge.Target with
            | EdgeClass.Provenance, EdgeRole.EnvironmentCapture false, [owner; slot; value],
              Some { Kind = SemanticKind.EnvironmentCreate(actual, initializers) }
                when owner = actual && List.contains (slot, value) initializers -> Some((owner, slot), value)
            | _ -> None)
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ rows -> List.map snd rows)
    let environments =
      graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Sources with
        | EdgeClass.Provenance, EdgeRole.EnvironmentFormal, [owner; implementation] ->
            match nodes.TryFind owner, nodes.TryFind implementation with
            | Some { Kind = SemanticKind.ClosureValue(actual, environment) }, Some { Kind = SemanticKind.Lambda(parameters, _, _, _, _) }
                when actual = implementation && (parameters |> List.exists (fun (_, _, formal) -> formal = edge.Target)) ->
                match nodes.TryFind environment with
                | Some { Kind = SemanticKind.EnvironmentCreate(expected, _) } when expected = owner -> Some(edge.Target, (owner, implementation))
                | _ -> None
            | _ -> None
        | _ -> None) |> Map.ofList
    let rec environmentOwner seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match environments.TryFind id with
        | Some(owner, _) -> Some owner
        | None ->
            match nodes.TryFind id with
            | Some { Kind = SemanticKind.EnvironmentCreate(owner, _) } -> Some owner
            | Some { Kind = SemanticKind.ClosureValue _ } -> Some id
            | Some { Kind = SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _)
                           | SemanticKind.EnvironmentReference value } -> environmentOwner seen value
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> environmentOwner seen value
            | Some { Kind = SemanticKind.Sequential values } -> List.tryLast values |> Option.bind (environmentOwner seen)
            | _ -> None
    let inputs = Dictionary<NodeId, Set<NodeId * NodeId>>()
    let supply call parameter argument =
        let old = match inputs.TryGetValue parameter with true, values -> values | _ -> Set.empty
        inputs[parameter] <- Set.add (call, argument) old

    for KeyValue(id, node) in nodes do
        match node.Kind with
        | SemanticKind.Lambda _ | SemanticKind.RecordExpr _ | SemanticKind.TupleExpr _
        | SemanticKind.DUConstruct _ | SemanticKind.UnionCase _ -> add id (Set.singleton (id, 0))
        | SemanticKind.Intrinsic _ | SemanticKind.PlatformBinding _ ->
            match applySubst node.Type with
            | NativeType.TFun _ -> add id (Set.singleton (id, 0))
            | _ -> ()
        | _ -> ()

    let rec invoke call seen (origins: Set<Origin>) (arguments: NodeId list) =
        origins |> Set.fold (fun results (id, offset) ->
            let key = id, offset, arguments.Length
            if Set.contains key seen then results
            else
                match shapes.TryFind id with
                | Some (parameters, body) when offset >= 0 ->
                    let total = max 1 parameters.Length
                    let available = total - offset
                    let supplied = min available arguments.Length
                    parameters |> List.skip (min offset parameters.Length) |> List.truncate supplied
                    |> List.iteri (fun index (_, _, parameter) ->
                        supply call parameter arguments[index]
                        add parameter (read arguments[index]))
                    let produced =
                        if supplied < available then Set.singleton (id, offset + supplied)
                        elif arguments.Length = supplied then read body
                        else invoke call (Set.add key seen) (read body) (List.skip supplied arguments)
                    Set.union results produced
                | _ -> Set.add (id, -1) results) Set.empty

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
                | SemanticKind.Application (callee, arguments) -> invoke id Set.empty (read callee) arguments
                | SemanticKind.EnvironmentRead(environment, slot) ->
                    environmentOwner Set.empty environment
                    |> Option.bind (fun owner -> captures.TryFind (owner, slot))
                    |> Option.map union |> Option.defaultValue Set.empty
                | SemanticKind.ClosureValue(implementation, _) ->
                    // The pair closes over its explicitly declared environment
                    // formal. Rewritten direct calls still supply that formal.
                    let formal = graph.Edges |> List.tryPick (fun edge ->
                        if edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.EnvironmentFormal
                           && edge.Sources = [id; implementation] then Some edge.Target else None)
                    match shapes.TryFind implementation, formal with
                    | Some ((_, _, first) :: _, _), Some actual when first = actual -> Set.singleton(implementation, 1)
                    | _ -> Set.empty
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

    nodes, shapes, (facts |> Seq.map (fun pair -> pair.Key, pair.Value) |> Map.ofSeq),
        (inputs |> Seq.map (fun pair -> pair.Key, Set.toList pair.Value) |> Map.ofSeq)

/// Share actual value-flow evidence with range and sequence analyses. Opaque
/// alternatives remain visible even when a known implementation also reaches
/// the call. This does not establish environment residence or native admission.
let resolve (graph: SemanticGraph) : Resolution =
    let nodes, shapes, facts, inputs = analyze graph
    let read id = facts.TryFind id |> Option.defaultValue Set.empty
    let calls = nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Application(callee, arguments) ->
            let origins = read callee
            let targets = origins |> Set.toList |> List.choose (fun (lambda, offset) ->
                match shapes.TryFind lambda with
                | Some (parameters, body) when offset >= 0 && max 1 parameters.Length - offset = arguments.Length ->
                    Some { Lambda = lambda; Parameters = parameters |> List.skip (min offset parameters.Length)
                           Arguments = arguments; Body = body }
                | _ -> None)
            let unknown = origins.IsEmpty || (origins |> Set.exists (fun (lambda, offset) ->
                match shapes.TryFind lambda with
                | Some (parameters, _) when offset >= 0 -> arguments.Length > max 1 parameters.Length - offset
                | _ -> true))
            Some(id, { Targets = targets; Unknown = unknown })
        | _ -> None) |> Map.ofList
    let lambdas = facts |> Map.toList |> List.choose (fun (id, origins) ->
        match Set.toList origins with
        | [lambda, 0] when shapes.ContainsKey lambda -> Some(id, lambda)
        | _ -> None) |> Map.ofList
    { Calls = calls; ParameterInputs = inputs; Lambdas = lambdas }

let resolveCalls graph = (resolve graph).Calls
let knownLambdas graph = (resolve graph).Lambdas

let applicationStages (graph: SemanticGraph) : Map<NodeId, Stage list> =
    let nodes, shapes, facts, _ = analyze graph
    let read id = facts.TryFind id |> Option.defaultValue Set.empty

    let boundary origins =
        if Set.isEmpty origins then None
        else
            let counts = origins |> Set.toList |> List.map (fun (id, offset) ->
                if offset < 0 then None
                else shapes.TryFind id |> Option.map (fun (parameters, _) -> max 1 parameters.Length - offset))
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

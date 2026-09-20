// SPDX-License-Identifier: MIT
/// Exact logical callable/environment identities. These readings never select
/// physical layout or recover an environment from a function's code identity.
module Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let environmentType = Types.mkArrayType Types.uint8Type

/// Source names and mutable aliases are not callable identity evidence.
let rec private follow (graph: SemanticGraph) terminal seen id =
    if Set.contains id seen then None else
    let seen = Set.add id seen
    match graph.Nodes.TryFind id with
    | Some node ->
        match terminal node with
        | Some value -> Some value
        | None ->
            match node.Kind with
            | SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _)
            | SemanticKind.EnvironmentReference source -> follow graph terminal seen source
            | SemanticKind.Binding(_, false, _, _) ->
                match node.Children with [value] -> follow graph terminal seen value | _ -> None
            | SemanticKind.Sequential values -> List.tryLast values |> Option.bind (follow graph terminal seen)
            | SemanticKind.FrameRead(_, source) -> follow graph terminal seen source
            | SemanticKind.IfThenElse(_, yes, Some no) ->
                match follow graph terminal seen yes, follow graph terminal seen no with
                | Some first, Some second when first = second -> Some first
                | _ -> None
            | _ -> None
    | None -> None

let tryKnown graph id =
    follow graph (fun node ->
        match node.Kind with
        | SemanticKind.ClosureValue(implementation, _) ->
            Some { Implementation = implementation; EnvironmentOwner = node.Id }
        | _ -> None) Set.empty id

/// Code identity through the same immutable value flow. This alone does not
/// authorize invoking a closure: complete calls must also satisfy its actual
/// environment convention, as checked by callEnvironments.
let tryImplementation graph id =
    follow graph (fun node ->
        match node.Kind with
        | SemanticKind.Lambda _ -> Some node.Id
        | SemanticKind.ClosureValue(implementation, _) -> Some implementation
        | _ -> None) Set.empty id

type private Convention = {
    Owner: NodeId
    Implementation: NodeId
    Formal: NodeId
    Ordinal: int
    Arity: int
}

/// Other recipes may prepend real parameters (for example a caller-owned
/// sequence result destination). The resident formal identity, rather than its
/// historical position, selects the environment in the final signature.
let private conventions (graph: SemanticGraph) =
    graph.Nodes.Values |> Seq.choose (fun owner ->
        match owner.Kind with
        | SemanticKind.ClosureValue(implementation, environment) when owner.IsReachable ->
            match graph.Nodes.TryFind implementation, graph.Nodes.TryFind environment with
            | Some { Kind = SemanticKind.Lambda(parameters, _, [], _, _); IsReachable = true },
              Some { Kind = SemanticKind.EnvironmentCreate(actual, _) } when actual = owner.Id ->
                let relations = graph.Edges |> List.filter (fun edge ->
                    edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.EnvironmentFormal
                    && edge.Sources = [owner.Id; implementation])
                match relations with
                | [relation] ->
                    let matching = parameters |> List.indexed |> List.filter (fun (_, (_, ty, formal)) ->
                        formal = relation.Target && applySubst ty = environmentType)
                    match matching, graph.Nodes.TryFind relation.Target with
                    | [(ordinal, _)], Some { Kind = SemanticKind.PatternBinding _; Type = ty }
                        when applySubst ty = environmentType ->
                        Some { Owner = owner.Id; Implementation = implementation; Formal = relation.Target
                               Ordinal = ordinal; Arity = parameters.Length }
                    | _ -> None
                | _ -> None
            | _ -> None
        | _ -> None) |> Seq.toList

let private environmentReader (graph: SemanticGraph) =
    let formals =
        conventions graph |> List.groupBy _.Formal
        |> List.choose (function formal, [convention] -> Some(formal, convention.Owner) | _ -> None)
        |> Map.ofList
    follow graph (fun node ->
        match node.Kind with
        | SemanticKind.EnvironmentCreate(owner, _) -> Some owner
        | SemanticKind.ClosureValue _ -> Some node.Id
        | _ -> formals.TryFind node.Id) Set.empty

let tryEnvironmentOwner graph id = environmentReader graph id

let origins graph =
    let read = environmentReader graph
    graph.Nodes |> Map.toList |> List.choose (fun (id, _) ->
        read id |> Option.map (fun owner -> id, owner)) |> Map.ofList

let knownCallables graph =
    graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match applySubst node.Type with
        | NativeType.TFun _ -> tryKnown graph id |> Option.map (fun known -> id, known)
        | _ -> None) |> Map.ofList

/// Lifted implementations are code declarations, not activation values that
/// need an initializer in a generator. Actual environment identities are never
/// admitted as code, and arbitrary Lambdas have no such convention relation.
let implementationBindings (graph: SemanticGraph) =
    let implementations = conventions graph |> List.map _.Implementation |> Set.ofList
    graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind, node.Children with
        | SemanticKind.Binding(_, false, _, _), [implementation]
            when node.IsReachable && implementations.Contains implementation && node.Type = graph.Nodes[implementation].Type -> Some id
        | _ -> None) |> Set.ofList

/// Each complete ordinary call's actual environment position and value. The
/// explicit formal relation survives hidden destination insertion. Arity and
/// exact environment owner are checked before a use is admitted as consumption.
let callEnvironments (graph: SemanticGraph) =
    let byImplementation =
        conventions graph |> List.groupBy _.Implementation
        |> List.choose (function implementation, [convention] -> Some(implementation, convention) | _ -> None)
        |> Map.ofList
    let environment = environmentReader graph
    let implementation id = follow graph (fun node -> byImplementation.TryFind node.Id) Set.empty id
    graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Application(callee, arguments) ->
            match implementation callee with
            | Some convention when arguments.Length = convention.Arity ->
                let actual = arguments[convention.Ordinal]
                if environment actual = Some convention.Owner then Some(id, (convention.Ordinal, actual)) else None
            | _ -> None
        | _ -> None) |> Map.ofList

/// Capture mode is a resident typed relation emitted by the closure recipe.
/// It does not depend on a binding still being on the emission spine.
let captures (graph: SemanticGraph) owner =
    graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Sources, graph.Nodes.TryFind edge.Target with
        | EdgeClass.Provenance, EdgeRole.EnvironmentCapture mutableCell, [actual; source; value],
          Some { Kind = SemanticKind.EnvironmentCreate(expected, initializers) }
            when actual = owner && expected = owner && List.contains (source, value) initializers ->
            graph.Nodes.TryFind source |> Option.map (fun declaration ->
                edge.Ordinal, { Name = sprintf "__capture_%d" (NodeId.value source)
                                Type = declaration.Type; IsMutable = mutableCell; SourceNodeId = Some source })
        | _ -> None)
    |> List.sortBy fst |> List.map snd

type Plan = { Source: SemanticNode; Captures: CaptureInfo list; Calls: NodeId list }

/// A child constructor's explicit formation relation is complete or residual.
/// Its source slot remains the declaration captured by the deferred generator.
let sequenceInitializers (graph: SemanticGraph) (owner: SemanticNode) =
    match owner.Kind with
    | SemanticKind.SeqExpr(_, captured) ->
        let formation = graph.Edges |> List.filter (fun edge -> edge.Target = owner.Id && edge.Role = EdgeRole.SequenceCaptureFormation)
        let rows = graph.Edges |> List.filter (fun edge -> edge.Target = owner.Id && match edge.Role with EdgeRole.SequenceCaptureInitializer _ -> true | _ -> false)
        match formation with
        | [] when rows.IsEmpty -> Some(captured |> List.choose (fun capture -> capture.SourceNodeId |> Option.map (fun id -> id, id)))
        | [{ Class = EdgeClass.Provenance; Sources = [closure; implementation; formal] }]
            when rows.Length = captured.Length &&
                 (conventions graph |> List.exists (fun convention -> convention.Owner = closure && convention.Implementation = implementation && convention.Formal = formal)) ->
            let values = captured |> List.mapi (fun ordinal capture ->
                let row = rows |> List.filter (fun edge -> edge.Ordinal = ordinal)
                match capture.SourceNodeId, row with
                | Some source, [{ Class = EdgeClass.Provenance; Role = EdgeRole.SequenceCaptureInitializer mutableCell; Sources = [slot; value] }]
                    when source = slot && mutableCell = capture.IsMutable && graph.Nodes.ContainsKey value ->
                    if slot = value then Some(slot, value) else
                    let access =
                        match graph.Nodes[value].Kind with
                        | SemanticKind.EnvironmentRead(environment, actual) when not mutableCell && actual = slot -> Some environment
                        | SemanticKind.EnvironmentBorrow(environment, actual) when mutableCell && actual = slot -> Some environment
                        | _ -> None
                    access |> Option.bind (fun environment ->
                        match graph.Nodes.TryFind environment with
                        | Some { Kind = SemanticKind.VarRef(_, Some actual) } when actual = formal &&
                            (captures graph closure |> List.exists (fun held -> held.SourceNodeId = Some slot && held.IsMutable = mutableCell)) -> Some(slot, value)
                        | _ -> None)
                | _ -> None)
            if List.forall Option.isSome values then Some(List.choose id values) else None
        | _ -> None
    | _ -> None

/// The first materialized form has a concrete source lambda and only complete
/// direct calls or immutable sequence captures. Returned/opaque/aggregate
/// callables retain their residual; no environment is guessed for them.
let plans (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let lambda id = follow graph (fun node -> match node.Kind with SemanticKind.Lambda _ -> Some node.Id | _ -> None) Set.empty id
    let candidates =
        nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.SeqExpr(_, captures) ->
                captures |> List.choose (fun capture ->
                    match applySubst capture.Type, capture.SourceNodeId with
                    | NativeType.TFun _, Some source when not capture.IsMutable -> lambda source
                    | _ -> None)
            | _ -> []) |> Set.ofSeq
    candidates |> Set.toList |> List.choose (fun id ->
        let source = nodes[id]
        match source.Kind with
        | SemanticKind.Lambda(parameters, body, captures, _, LambdaContext.RegularClosure) when not parameters.IsEmpty ->
            let aliases = nodes |> Map.toList |> List.choose (fun (value, _) -> if lambda value = Some id then Some value else None) |> Set.ofList
            let bodyNodes =
                let rec visit seen id =
                    if Set.contains id seen then seen else
                    match nodes.TryFind id with
                    | Some node ->
                        let seen = Set.add id seen
                        match node.Kind with
                        | SemanticKind.SeqExpr _ | SemanticKind.Lambda _ | SemanticKind.LazyExpr _ -> seen
                        | _ -> List.fold visit seen node.Children
                    | None -> seen
                visit Set.empty body
            let sources = captures |> List.choose _.SourceNodeId |> Set.ofList
            let scalarCapture (capture: CaptureInfo) =
                match Types.tryGetNTUKind (applySubst capture.Type) with
                | Some (NTUKind.NTUint _ | NTUKind.NTUuint _ | NTUKind.NTUfloat _ | NTUKind.NTUposit _
                      | NTUKind.NTUbool | NTUKind.NTUchar | NTUKind.NTUunit) -> true
                | _ -> false
            let unsupportedNested = bodyNodes |> Set.exists (fun child ->
                match nodes[child].Kind with
                | SemanticKind.Lambda(_, _, nested, _, _) | SemanticKind.LazyExpr(_, nested) ->
                    nested |> List.exists (fun capture -> capture.SourceNodeId |> Option.exists sources.Contains)
                | _ -> false)
            let mutable rejected = unsupportedNested || (captures |> List.exists (fun capture -> capture.SourceNodeId.IsNone || not (scalarCapture capture)))
            let mutable calls = []
            for node in nodes.Values do
                let inputs = kindEdges node.Id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                             |> List.append node.Children |> List.distinct |> List.filter aliases.Contains
                for input in inputs do
                    match node.Kind with
                    | SemanticKind.Binding(_, false, _, _) | SemanticKind.TypeAnnotation _ -> ()
                    | SemanticKind.Sequential _ -> ()
                    | SemanticKind.Application(callee, arguments) when callee = input && arguments.Length = parameters.Length -> calls <- node.Id :: calls
                    | _ -> rejected <- true
                match node.Kind with
                | SemanticKind.Lambda(_, _, nested, _, context) ->
                    if context <> LambdaContext.SeqGenerator && (nested |> List.exists (fun capture -> capture.SourceNodeId |> Option.exists aliases.Contains)) then rejected <- true
                | SemanticKind.LazyExpr(_, nested) ->
                    if nested |> List.exists (fun capture -> capture.SourceNodeId |> Option.exists aliases.Contains) then rejected <- true
                | _ -> ()
            if rejected || calls.IsEmpty then None
            else Some { Source = source; Captures = captures; Calls = List.distinct calls }
        | _ -> None)

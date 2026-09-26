// SPDX-License-Identifier: MIT
/// Exact logical callable/environment identities. These readings never select
/// physical layout or recover an environment from a function's code identity.
module Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let environmentType = Types.mkArrayType Types.uint8Type

/// Capture incidence must agree with the actual initializer, slot and mode.
/// A slot declaration alone is not evidence for the value held by an instance.
let capturedInitializers (graph: SemanticGraph) owner =
    match graph.Nodes.TryFind owner with
    | Some { Kind = SemanticKind.ClosureValue(_, environment) } ->
        match graph.Nodes.TryFind environment with
        | Some { Kind = SemanticKind.EnvironmentCreate(actual, initializers) } when actual = owner ->
            let rows = graph.Edges |> List.filter (fun edge ->
                edge.Target = environment &&
                (match edge.Role with EdgeRole.EnvironmentCapture _ -> true | _ -> false))
            let values = initializers |> List.mapi (fun ordinal (slot, value) ->
                match rows |> List.filter (fun edge -> edge.Ordinal = ordinal) with
                | [{ Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentCapture mutableCell; Sources = [actual; source; initial] }]
                    when actual = owner && source = slot && initial = value &&
                         graph.Nodes.ContainsKey slot && graph.Nodes.ContainsKey value -> Some(slot, value, mutableCell)
                | _ -> None)
            if rows.Length = initializers.Length && List.forall Option.isSome values then Some(List.choose id values) else None
        | _ -> None
    | _ -> None

let private formalOwner (graph: SemanticGraph) formal =
    graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Sources with
        | EdgeClass.Provenance, EdgeRole.EnvironmentFormal, [owner; implementation] when edge.Target = formal ->
            match graph.Nodes.TryFind owner, graph.Nodes.TryFind implementation, graph.Nodes.TryFind formal with
            | Some { Kind = SemanticKind.ClosureValue(actual, _) },
              Some { Kind = SemanticKind.Lambda(parameters, _, [], _, _) },
              Some { Kind = SemanticKind.PatternBinding _; Type = ty } when actual = implementation && applySubst ty = environmentType &&
                    (parameters |> List.exists (fun (_, ty, parameter) -> parameter = formal && applySubst ty = environmentType)) -> Some owner
            | _ -> None
        | _ -> None)
    |> function [owner] -> Some owner | _ -> None

let private resultOwner (graph: SemanticGraph) formal =
    graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Sources with
        | EdgeClass.Provenance, EdgeRole.EnvironmentResultDestination, [implementation; owner; destination]
            when destination = formal ->
            match graph.Nodes.TryFind implementation, graph.Nodes.TryFind edge.Target, graph.Nodes.TryFind formal with
            | Some { Kind = SemanticKind.Lambda(parameters, _, [], _, _) },
              Some { Kind = SemanticKind.EnvironmentCreate(actual, _) },
              Some { Kind = SemanticKind.PatternBinding _; Type = ty }
                when actual = owner && applySubst ty = environmentType &&
                     (parameters |> List.exists (fun (_, ty, id) -> id = formal && applySubst ty = environmentType)) -> Some owner
            | _ -> None
        | _ -> None)
    |> function [owner] -> Some owner | _ -> None

/// Source names and mutable aliases are not callable identity evidence.
/// Complete call/result and formal/actual relations retain unknown alternatives.
let rec private followUsing<'T when 'T: equality>
    (graph: SemanticGraph) (resolution: Lazy<CallableOrigins.Resolution>)
    (terminal: SemanticNode -> 'T option) (seen: Set<NodeId>) (id: NodeId) : 'T option =
    if Set.contains id seen then None else
    let seen = Set.add id seen
    let follow = followUsing<'T> graph resolution
    let same values =
        match values |> List.map (follow terminal seen) |> List.distinct with
        | [Some value] -> Some value
        | _ -> None
    match graph.Nodes.TryFind id with
    | Some node ->
        match terminal node with
        | Some value -> Some value
        | None ->
            match node.Kind with
            | SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _)
            | SemanticKind.EnvironmentReference source -> follow terminal seen source
            | SemanticKind.Binding(_, false, _, _) ->
                match node.Children with [value] -> follow terminal seen value | _ -> None
            | SemanticKind.Sequential values -> List.tryLast values |> Option.bind (follow terminal seen)
            | SemanticKind.FrameRead(_, source) -> follow terminal seen source
            | SemanticKind.IfThenElse(_, yes, Some no) ->
                same [yes; no]
            | SemanticKind.Application _ ->
                resolution.Value.Calls.TryFind id |> Option.bind (fun call ->
                    if call.Unknown then None else same (call.Targets |> List.map _.Body))
            | SemanticKind.PatternBinding _ ->
                resolution.Value.ParameterInputs.TryFind id |> Option.bind (List.map snd >> same)
            | SemanticKind.EnvironmentRead(environment, slot) ->
                let owner = followUsing<NodeId> graph resolution (fun candidate ->
                    match candidate.Kind with
                    | SemanticKind.EnvironmentCreate(owner, _) | SemanticKind.EnvironmentAllocate owner -> Some owner
                    | SemanticKind.ClosureValue _ -> Some candidate.Id
                    | _ -> formalOwner graph candidate.Id |> Option.orElseWith (fun () -> resultOwner graph candidate.Id)) seen environment
                owner |> Option.bind (capturedInitializers graph) |> Option.bind (fun initializers ->
                    initializers |> List.tryPick (fun (source, value, mutableCell) ->
                        if source = slot && not mutableCell then follow terminal seen value else None))
            | _ -> None
    | None -> None

let private follow graph terminal = followUsing graph (lazy (CallableOrigins.resolve graph)) terminal

let tryKnown graph =
    follow graph (fun node ->
        match node.Kind with
        | SemanticKind.ClosureValue(implementation, _) ->
            Some { Implementation = implementation; EnvironmentOwner = node.Id }
        | _ -> None) Set.empty

/// Code identity through the same immutable value flow. This alone does not
/// authorize invoking a closure: complete calls must also satisfy its actual
/// environment convention, as checked by callEnvironments.
let tryImplementation graph =
    follow graph (fun node ->
        match node.Kind with
        | SemanticKind.Lambda _ -> Some node.Id
        | SemanticKind.ClosureValue(implementation, _) -> Some implementation
        | _ -> None) Set.empty

/// Source navigation follows an occurrence's explicit promotion relation,
/// never a generated name or a code binding shared by several source aliases.
/// Build this reader once per graph so all lookups share callable resolution.
let trySourceDeclaration (graph: SemanticGraph) =
    let implementation = lazy (tryImplementation graph)
    let origins = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.CallableReferenceOrigin)
                  |> List.groupBy _.Target |> Map.ofList
    fun occurrence ->
        match graph.Nodes.TryFind occurrence, origins.TryFind occurrence with
        | Some { Kind = SemanticKind.VarRef(_, Some code) },
          Some [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [declaration; binding] }] when code = binding ->
            match graph.Nodes.TryFind declaration, graph.Nodes.TryFind binding with
            | Some { Kind = SemanticKind.Binding(_, false, _, _) | SemanticKind.PatternBinding _ },
              Some { Kind = SemanticKind.Binding(_, false, false, None); Children = [lambda] } ->
                match graph.Nodes.TryFind lambda with
                | Some { Kind = SemanticKind.Lambda(_, _, [], _, _); Parent = Some parent; Metadata = metadata }
                    when parent = binding && metadata.ContainsKey ClosureMetadata.SourceSignature &&
                         implementation.Value declaration = Some lambda -> Some declaration
                | _ -> None
            | _ -> None
        | _ -> None

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
        | SemanticKind.EnvironmentCreate(owner, _) | SemanticKind.EnvironmentAllocate owner -> Some owner
        | SemanticKind.ClosureValue _ -> Some node.Id
        | _ -> formals.TryFind node.Id |> Option.orElseWith (fun () -> resultOwner graph node.Id)) Set.empty

let tryEnvironmentOwner graph id = environmentReader graph id

let origins graph =
    let read = environmentReader graph
    graph.Nodes |> Map.toList |> List.choose (fun (id, _) ->
        read id |> Option.map (fun owner -> id, owner)) |> Map.ofList

let knownCallables graph =
    let known = follow graph (fun node ->
        match node.Kind with
        | SemanticKind.ClosureValue(implementation, _) -> Some { Implementation = implementation; EnvironmentOwner = node.Id }
        | _ -> None) Set.empty
    graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match applySubst node.Type with
        | NativeType.TFun _ -> known id |> Option.map (fun value -> id, value)
        | _ -> None) |> Map.ofList

/// Lifted implementations are code declarations, not activation values that
/// need an initializer in a generator. Actual environment identities are never
/// admitted as code. Stateless promotion supplies a typed source signature and
/// a capture-free named declaration; capturing implementations still require
/// their exact environment convention, even if that convention is malformed.
let implementationBindings (graph: SemanticGraph) =
    let implementations = conventions graph |> List.map _.Implementation |> Set.ofList
    let environmental = graph.Nodes.Values |> Seq.choose (fun node ->
        match node.Kind with SemanticKind.ClosureValue(implementation, _) -> Some implementation | _ -> None) |> Set.ofSeq
    let stateless binding implementation =
        match graph.Nodes.TryFind implementation with
        | Some { Kind = SemanticKind.Lambda(_, _, [], _, LambdaContext.RegularClosure); Parent = Some parent; Metadata = metadata }
            when parent = binding && not (environmental.Contains implementation) ->
                (match metadata.TryFind ClosureMetadata.SourceSignature with Some (MetadataValue.Type _) -> true | _ -> false)
                && ([ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
                    |> List.forall (fun key -> metadata.TryFind key <> Some (MetadataValue.Bool true)))
        | _ -> false
    graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind, node.Children with
        | SemanticKind.Binding(_, false, _, _), [implementation]
            when node.IsReachable && (implementations.Contains implementation || stateless id implementation)
                 && node.Type = graph.Nodes[implementation].Type -> Some id
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
    capturedInitializers graph owner |> Option.defaultValue [] |> List.map (fun (source, _, mutableCell) ->
        { Name = sprintf "__capture_%d" (NodeId.value source)
          Type = graph.Nodes[source].Type; IsMutable = mutableCell; SourceNodeId = Some source })

/// Read one immutable held value through its exact environment occurrence.
/// Mutable cells deliberately have no immutable-value alias here.
let tryCapturedValue graph =
    let environmentOwner = environmentReader graph
    fun environment slot ->
        environmentOwner environment |> Option.bind (capturedInitializers graph) |> Option.bind (fun values ->
            values |> List.tryPick (fun (source, value, mutableCell) -> if source = slot && not mutableCell then Some value else None))

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

/// Sequence callables include their retained higher-order formation frontiers.
/// Every invocation must have an exact complete callable boundary. Materializing
/// its value does not prove the environment's residence or a returned lifetime.
let plans (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let resolution = CallableOrigins.resolve graph
    let known = knownCallables graph
    let lambda id =
        resolution.Lambdas.TryFind id
        |> Option.orElseWith (fun () -> known.TryFind id |> Option.map _.Implementation)
    let isSequence ty = match applySubst ty with NativeType.TSeq _ -> true | _ -> false
    let seeds =
        nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.SeqExpr(_, captures) ->
                captures |> List.choose (fun capture ->
                    match applySubst capture.Type, capture.SourceNodeId with
                    | NativeType.TFun _, Some source when not capture.IsMutable -> lambda source
                    | _ -> None)
            | SemanticKind.Lambda(parameters, body, _, _, LambdaContext.RegularClosure)
                when (parameters |> List.exists (fun (_, ty, _) -> isSequence ty)) ||
                     (nodes.TryFind body |> Option.exists (fun body -> isSequence body.Type)) -> [node.Id]
            | _ -> []) |> Set.ofSeq
    // The closure family follows typed value flow, not operation names. A
    // retained front may return another front and capture a callable argument.
    let rec family (selected: Set<NodeId>) =
        let next = nodes.Values |> Seq.fold (fun (selected: Set<NodeId>) node ->
            match node.Kind with
            | SemanticKind.Lambda(_, body, captures, _, LambdaContext.RegularClosure) ->
                let selected =
                    if lambda body |> Option.exists selected.Contains then Set.add node.Id selected else selected
                if selected.Contains node.Id then
                    captures |> List.fold (fun selected capture ->
                        match capture.SourceNodeId |> Option.bind lambda with
                        | Some dependency when not capture.IsMutable -> Set.add dependency selected
                        | _ -> selected) selected
                else selected
            | _ -> selected) selected
        if next = selected then selected else family next
    let candidates = family seeds
    candidates |> Set.toList |> List.choose (fun id ->
        let source = nodes[id]
        match source.Kind with
        | SemanticKind.Lambda(parameters, body, captures, _, LambdaContext.RegularClosure)
            when not parameters.IsEmpty && not (source.Metadata.ContainsKey ClosureMetadata.SourceSignature) &&
                 (not captures.IsEmpty ||
                  ([ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
                   |> List.exists (fun key -> source.Metadata.TryFind key = Some (MetadataValue.Bool true)))) ->
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
            let supportedCapture (capture: CaptureInfo) =
                match applySubst capture.Type with
                | NativeType.TFun _ when not capture.IsMutable ->
                    capture.SourceNodeId |> Option.exists (fun source ->
                        known.ContainsKey source || (lambda source |> Option.exists candidates.Contains))
                | NativeType.TSeq _ when not capture.IsMutable -> true
                | ty ->
                    match Types.tryGetNTUKind ty with
                    | Some (NTUKind.NTUint _ | NTUKind.NTUuint _ | NTUKind.NTUfloat _ | NTUKind.NTUposit _
                          | NTUKind.NTUbool | NTUKind.NTUchar | NTUKind.NTUunit) -> true
                    | _ -> false
            let unsupportedNested = bodyNodes |> Set.exists (fun child ->
                match nodes[child].Kind with
                | SemanticKind.Lambda(_, _, nested, _, _) | SemanticKind.LazyExpr(_, nested) ->
                    nested |> List.exists (fun capture -> capture.SourceNodeId |> Option.exists sources.Contains)
                | _ -> false)
            let mutable rejected = unsupportedNested || (captures |> List.exists (fun capture -> capture.SourceNodeId.IsNone || not (supportedCapture capture)))
            let calls = resolution.Calls |> Map.toList |> List.choose (fun (call, resolved) ->
                match resolved.Targets with
                | [target] when not resolved.Unknown && target.Lambda = id &&
                               (captures.IsEmpty || target.Parameters = parameters) -> Some call
                | _ -> None)
            for node in nodes.Values do
                let inputs = kindEdges node.Id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                             |> List.append node.Children |> List.distinct |> List.filter aliases.Contains
                for input in inputs do
                    match node.Kind with
                    | SemanticKind.Binding(_, false, _, _) | SemanticKind.TypeAnnotation _ -> ()
                    | SemanticKind.Sequential _ -> ()
                    | SemanticKind.Application(callee, _) when callee = input && List.contains node.Id calls -> ()
                    | SemanticKind.Application(_, arguments) when List.contains input arguments ->
                        // An actual callable argument must feed an exact known
                        // formal; opaque higher-order consumers remain residual.
                        match resolution.Calls.TryFind node.Id with
                        | Some { Targets = [target]; Unknown = false } when candidates.Contains target.Lambda -> ()
                        | _ -> rejected <- true
                    | SemanticKind.Lambda(formals, body, _, _, _) when
                        (formals |> List.exists (fun (_, _, formal) -> formal = input)) ||
                        (body = input && candidates.Contains node.Id) -> ()
                    | SemanticKind.EnvironmentCreate(owner, _) when
                        capturedInitializers graph owner |> Option.exists (List.exists (fun (_, value, mutableCell) -> value = input && not mutableCell)) -> ()
                    | _ -> rejected <- true
                match node.Kind with
                | SemanticKind.Lambda(_, _, nested, _, context) ->
                    for capture in nested do
                        if capture.SourceNodeId |> Option.exists aliases.Contains then
                            if capture.IsMutable || (context <> LambdaContext.SeqGenerator && not (candidates.Contains node.Id)) then rejected <- true
                | SemanticKind.LazyExpr(_, nested) ->
                    if nested |> List.exists (fun capture -> capture.SourceNodeId |> Option.exists aliases.Contains) then rejected <- true
                | _ -> ()
            if rejected || calls.IsEmpty then None
            else Some { Source = source; Captures = captures; Calls = calls }
        | _ -> None)
    // Plain code has no runtime environment. Settle these declarations before
    // a capturing front chooses slots for its retained values.
    |> List.sortBy (fun plan -> not plan.Captures.IsEmpty, plan.Source.Id)

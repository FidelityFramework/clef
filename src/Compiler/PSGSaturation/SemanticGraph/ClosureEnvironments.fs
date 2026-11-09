// SPDX-License-Identifier: MIT
/// Exact logical callable/environment identities. These readings never select
/// physical layout or recover an environment from a function's code identity.
module Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let environmentType = Types.internalStorageType

type private EnvEdgeIndex = {
    CaptureEdgesByTarget: Map<NodeId, Hyperedge list>
    FormalEdgesByTarget: Map<NodeId, Hyperedge list>
    FormalEdgesByOwnerImpl: Map<NodeId * NodeId, Hyperedge list>
    ResultEdgesByDest: Map<NodeId, Hyperedge list>
}

let private envEdgeIndices = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, EnvEdgeIndex>()
let private getEnvEdgeIndex (graph: SemanticGraph) =
    envEdgeIndices.GetValue(graph, fun g ->
        let mutable captures = []
        let mutable formalsByTarget = []
        let mutable formalsByOwnerImpl = []
        let mutable resultsByDest = []
        for edge in g.Edges do
            match edge.Class, edge.Role, edge.Sources with
            | _, EdgeRole.EnvironmentCapture _, _ ->
                captures <- (edge.Target, edge) :: captures
            | EdgeClass.Provenance, EdgeRole.EnvironmentFormal, [owner; implementation] ->
                formalsByTarget <- (edge.Target, edge) :: formalsByTarget
                formalsByOwnerImpl <- ((owner, implementation), edge) :: formalsByOwnerImpl
            | EdgeClass.Provenance, EdgeRole.EnvironmentResultDestination, [_; _; destination] ->
                resultsByDest <- (destination, edge) :: resultsByDest
            | _ -> ()
        let groupPairs pairs =
            pairs
            |> List.rev
            |> List.groupBy fst
            |> List.map (fun (k, xs) -> k, xs |> List.map snd)
            |> Map.ofList
        { CaptureEdgesByTarget = groupPairs captures
          FormalEdgesByTarget = groupPairs formalsByTarget
          FormalEdgesByOwnerImpl = groupPairs formalsByOwnerImpl
          ResultEdgesByDest = groupPairs resultsByDest })

/// Capture incidence must agree with the actual initializer, slot and mode.
/// A slot declaration alone is not evidence for the value held by an instance.
let capturedInitializers (graph: SemanticGraph) owner =
    match graph.Nodes.TryFind owner with
    | Some { Kind = SemanticKind.ClosureValue(_, environment) } ->
        match graph.Nodes.TryFind environment with
        | Some { Kind = SemanticKind.EnvironmentCreate(actual, initializers) } when actual = owner ->
            let rows = (getEnvEdgeIndex graph).CaptureEdgesByTarget.TryFind environment |> Option.defaultValue []
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
    (getEnvEdgeIndex graph).FormalEdgesByTarget.TryFind formal
    |> Option.defaultValue []
    |> List.choose (fun edge ->
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
    (getEnvEdgeIndex graph).ResultEdgesByDest.TryFind formal
    |> Option.defaultValue []
    |> List.choose (fun edge ->
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
let private followUsing<'T when 'T: equality>
    (graph: SemanticGraph) (resolution: Lazy<CallableOrigins.Resolution>)
    (terminal: SemanticNode -> 'T option) : Set<NodeId> -> NodeId -> 'T option =
    let gate = obj()
    let memo = System.Collections.Generic.Dictionary<NodeId, 'T option>()
    let ownerMemo = System.Collections.Generic.Dictionary<NodeId, NodeId option>()
    let ownerTerminal (candidate: SemanticNode) =
        match candidate.Kind with
        | SemanticKind.EnvironmentCreate(owner, _) | SemanticKind.EnvironmentAllocate owner -> Some owner
        | SemanticKind.ClosureValue _ -> Some candidate.Id
        | _ -> formalOwner graph candidate.Id |> Option.orElseWith (fun () -> resultOwner graph candidate.Id)
    let rec goOwner (seen: Set<NodeId>) (id: NodeId) : bool * NodeId option =
        if Set.contains id seen then true, None else
        match ownerMemo.TryGetValue id with
        | true, cached -> false, cached
        | false, _ ->
            let seen = Set.add id seen
            let sameOwner (values: NodeId list) =
                match values with
                | [] -> false, None
                | _ ->
                    let rec loop hadCycleAcc (expectedOpt: NodeId option) remaining =
                        match remaining with
                        | [] -> hadCycleAcc, expectedOpt
                        | nextId :: rest ->
                            let c, res = goOwner seen nextId
                            let hadCycleAcc = hadCycleAcc || c
                            match res with
                            | None -> hadCycleAcc, None
                            | Some actual ->
                                match expectedOpt with
                                | None -> loop hadCycleAcc (Some actual) rest
                                | Some prev when prev = actual -> loop hadCycleAcc expectedOpt rest
                                | _ -> hadCycleAcc, None
                    loop false None values
            let hadCycle, result =
                match graph.Nodes.TryFind id with
                | Some node ->
                    match ownerTerminal node with
                    | Some value -> false, Some value
                    | None ->
                        match node.Kind with
                        | SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _)
                        | SemanticKind.EnvironmentReference source -> goOwner seen source
                        | SemanticKind.EagerExpr source when ExplicitDemand.operand graph id = Some source -> goOwner seen source
                        | SemanticKind.Binding(_, false, _, _) ->
                            match node.Children with [value] -> goOwner seen value | _ -> false, None
                        | SemanticKind.Sequential values ->
                            match List.tryLast values with Some v -> goOwner seen v | None -> false, None
                        | SemanticKind.FrameRead(_, source) -> goOwner seen source
                        | SemanticKind.IfThenElse(_, yes, Some no) -> sameOwner [yes; no]
                        | SemanticKind.Application _ ->
                            match resolution.Value.Calls.TryFind id with
                            | Some call when not call.Unknown && call.Complete -> sameOwner (call.Targets |> List.map _.Body)
                            | _ -> false, None
                        | SemanticKind.PatternBinding _ ->
                            match resolution.Value.ParameterInputs.TryFind id with
                            | Some inputs -> sameOwner (inputs |> List.map snd)
                            | None -> false, None
                        | SemanticKind.EnvironmentRead(environment, slot) ->
                            let cEnv, owner = goOwner seen environment
                            match owner |> Option.bind (capturedInitializers graph) with
                            | Some initializers ->
                                match initializers |> List.tryPick (fun (source, value, mutableCell) ->
                                    if source = slot && not mutableCell then Some value else None) with
                                | Some value ->
                                    let cVal, res = goOwner seen value
                                    cEnv || cVal, res
                                | None -> cEnv, None
                            | None -> cEnv, None
                        | _ -> false, None
                | None -> false, None
            if not hadCycle then ownerMemo[id] <- result
            hadCycle, result
    let rec go (seen: Set<NodeId>) (id: NodeId) : bool * 'T option =
        if Set.contains id seen then true, None else
        match memo.TryGetValue id with
        | true, cached -> false, cached
        | false, _ ->
            let seen = Set.add id seen
            let same (values: NodeId list) =
                match values with
                | [] -> false, None
                | _ ->
                    let rec loop hadCycleAcc (expectedOpt: 'T option) remaining =
                        match remaining with
                        | [] -> hadCycleAcc, expectedOpt
                        | nextId :: rest ->
                            let c, res = go seen nextId
                            let hadCycleAcc = hadCycleAcc || c
                            match res with
                            | None -> hadCycleAcc, None
                            | Some actual ->
                                match expectedOpt with
                                | None -> loop hadCycleAcc (Some actual) rest
                                | Some prev when prev = actual -> loop hadCycleAcc expectedOpt rest
                                | _ -> hadCycleAcc, None
                    loop false None values
            let hadCycle, result =
                match graph.Nodes.TryFind id with
                | Some node ->
                    match terminal node with
                    | Some value -> false, Some value
                    | None ->
                        match node.Kind with
                        | SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _)
                        | SemanticKind.EnvironmentReference source -> go seen source
                        | SemanticKind.EagerExpr source when ExplicitDemand.operand graph id = Some source -> go seen source
                        | SemanticKind.Binding(_, false, _, _) ->
                            match node.Children with [value] -> go seen value | _ -> false, None
                        | SemanticKind.Sequential values ->
                            match List.tryLast values with Some v -> go seen v | None -> false, None
                        | SemanticKind.FrameRead(_, source) -> go seen source
                        | SemanticKind.IfThenElse(_, yes, Some no) -> same [yes; no]
                        | SemanticKind.Application _ ->
                            match resolution.Value.Calls.TryFind id with
                            | Some call when not call.Unknown && call.Complete -> same (call.Targets |> List.map _.Body)
                            | _ -> false, None
                        | SemanticKind.PatternBinding _ ->
                            match resolution.Value.ParameterInputs.TryFind id with
                            | Some inputs -> same (inputs |> List.map snd)
                            | None -> false, None
                        | SemanticKind.EnvironmentRead(environment, slot) ->
                            let cEnv, owner = goOwner seen environment
                            match owner |> Option.bind (capturedInitializers graph) with
                            | Some initializers ->
                                match initializers |> List.tryPick (fun (source, value, mutableCell) ->
                                    if source = slot && not mutableCell then Some value else None) with
                                | Some value ->
                                    let cVal, res = go seen value
                                    cEnv || cVal, res
                                | None -> cEnv, None
                            | None -> cEnv, None
                        | _ -> false, None
                | None -> false, None
            if not hadCycle then memo[id] <- result
            hadCycle, result
    fun seen id ->
        lock gate (fun () ->
            let _, res = go seen id
            res)

let private follow graph terminal = followUsing graph (lazy (CallableOrigins.resolve graph)) terminal

type private CachedKnownReader = { Reader: NodeId -> KnownCallable option }
let private knownReaders = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, CachedKnownReader>()

let tryKnown (graph: SemanticGraph) =
    (knownReaders.GetValue(graph, fun g ->
        let reader =
            follow g (fun node ->
                match node.Kind with
                | SemanticKind.ClosureValue(implementation, _) ->
                    Some { Implementation = implementation; EnvironmentOwner = node.Id }
                | _ -> None) Set.empty
        { Reader = reader })).Reader

/// Code identity through the same immutable value flow. This alone does not
/// authorize invoking a closure: complete calls must also satisfy its actual
/// environment convention, as checked by callEnvironments.
type private CachedImplementationReader = { Reader: NodeId -> NodeId option }
let private implementationReaders = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, CachedImplementationReader>()

let tryImplementation (graph: SemanticGraph) =
    (implementationReaders.GetValue(graph, fun g ->
        let reader =
            follow g (fun node ->
                match node.Kind with
                | SemanticKind.Lambda _ -> Some node.Id
                | SemanticKind.ClosureValue(implementation, _) -> Some implementation
                | _ -> None) Set.empty
        { Reader = reader })).Reader

/// Source navigation follows an occurrence's explicit promotion relation,
/// never a generated name or a code binding shared by several source aliases.
/// Build this reader once per graph so all lookups share callable resolution.
let trySourceDeclaration (graph: SemanticGraph) =
    let implementation = lazy (tryImplementation graph)
    let origins =
        lazy (
            graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.CallableReferenceOrigin)
            |> List.groupBy _.Target |> Map.ofList)
    fun occurrence ->
        match graph.Nodes.TryFind occurrence with
        | Some { Kind = SemanticKind.VarRef(_, Some code) } ->
            match origins.Value.TryFind occurrence with
            | Some [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [declaration; binding] }] when code = binding ->
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
    let index = getEnvEdgeIndex graph
    graph.Nodes.Values |> Seq.choose (fun owner ->
        match owner.Kind with
        | SemanticKind.ClosureValue(implementation, environment) when owner.IsReachable ->
            match graph.Nodes.TryFind implementation, graph.Nodes.TryFind environment with
            | Some { Kind = SemanticKind.Lambda(parameters, _, [], _, _); IsReachable = true },
              Some { Kind = SemanticKind.EnvironmentCreate(actual, _) } when actual = owner.Id ->
                let relations = index.FormalEdgesByOwnerImpl.TryFind (owner.Id, implementation) |> Option.defaultValue []
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

type private CachedEnvironmentReader = { Reader: NodeId -> NodeId option }
let private environmentReaders = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, CachedEnvironmentReader>()

let private environmentReader (graph: SemanticGraph) =
    (environmentReaders.GetValue(graph, fun g ->
        let formals =
            conventions g |> List.groupBy _.Formal
            |> List.choose (function formal, [convention] -> Some(formal, convention.Owner) | _ -> None)
            |> Map.ofList
        let reader =
            follow g (fun node ->
                match node.Kind with
                | SemanticKind.EnvironmentCreate(owner, _) | SemanticKind.EnvironmentAllocate owner -> Some owner
                | SemanticKind.ClosureValue _ -> Some node.Id
                | _ -> formals.TryFind node.Id |> Option.orElseWith (fun () -> resultOwner g node.Id)) Set.empty
        { Reader = reader })).Reader

let tryEnvironmentOwner graph id = environmentReader graph id

let origins graph =
    let read = environmentReader graph
    graph.Nodes |> Map.toList |> List.choose (fun (id, _) ->
        read id |> Option.map (fun owner -> id, owner)) |> Map.ofList

type private CachedKnownCallables = { Callables: Map<NodeId, KnownCallable> }
let private knownCallablesCache = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, CachedKnownCallables>()

let knownCallables (graph: SemanticGraph) =
    (knownCallablesCache.GetValue(graph, fun g ->
        let hasClosureValues =
            g.Nodes.Values |> Seq.exists (fun node ->
                match node.Kind with SemanticKind.ClosureValue _ -> true | _ -> false)
        let callables =
            if not hasClosureValues then
                Map.empty
            else
                let known = tryKnown g
                g.Nodes |> Map.toList |> List.choose (fun (id, node) ->
                    match applySubst node.Type with
                    | NativeType.TFun _ -> known id |> Option.map (fun value -> id, value)
                    | _ -> None) |> Map.ofList
        { Callables = callables })).Callables

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

/// Project only an actual source reference preserved by environment
/// materialization. A generated capture initializer can read the same slot,
/// but does not thereby become a source VarRef or a navigation anchor.
let tryCapturedSourceReference (graph: SemanticGraph) =
    let environmentOwner = environmentReader graph
    let origins = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.CaptureReferenceOrigin)
                  |> List.groupBy _.Target |> Map.ofList
    fun occurrence ->
        match graph.Nodes.TryFind occurrence, origins.TryFind occurrence with
        | Some ({ Kind = SemanticKind.EnvironmentRead(environment, slot); Children = [actual] } as value),
          Some [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [owner; declaration] }]
            when actual = environment && slot = declaration && environmentOwner environment = Some owner ->
            match graph.Nodes.TryFind declaration, capturedInitializers graph owner with
            | Some ({ Kind = SemanticKind.Binding _ | SemanticKind.PatternBinding _ } as source), Some captures
                when applySubst value.Type = applySubst source.Type &&
                     (captures |> List.exists (fun (captured, _, _) -> captured = declaration)) -> Some declaration
            | _ -> None
        | _ -> None

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

/// Ordinary callables include their retained higher-order formation frontiers.
/// Every invocation must have an exact complete callable boundary. Materializing
/// its value does not prove the environment's residence or a returned lifetime.
let plans (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let regularClosures =
        nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Lambda(_, body, captures, _, LambdaContext.RegularClosure) ->
                Some (node.Id, body, captures)
            | _ -> None) |> Seq.toList
    let isEligibleSource (source: SemanticNode) =
        match source.Kind with
        | SemanticKind.Lambda(parameters, _, captures, _, LambdaContext.RegularClosure) ->
            not parameters.IsEmpty && not (source.Metadata.ContainsKey ClosureMetadata.SourceSignature) &&
            (not captures.IsEmpty ||
             ([ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
              |> List.exists (fun key -> source.Metadata.TryFind key = Some (MetadataValue.Bool true))))
        | _ -> false
    if not (regularClosures |> List.exists (fun (id, _, _) -> isEligibleSource nodes[id])) then [] else
    let resolution = CallableOrigins.resolve graph
    let known = knownCallables graph
    let lambda id =
        resolution.Lambdas.TryFind id
        |> Option.orElseWith (fun () -> known.TryFind id |> Option.map _.Implementation)
    let seeds = regularClosures |> List.map (fun (id, _, _) -> id) |> Set.ofList
    let rec family (selected: Set<NodeId>) =
        let next = regularClosures |> List.fold (fun (selected: Set<NodeId>) (nodeId, body, captures) ->
            let selected =
                if lambda body |> Option.exists selected.Contains then Set.add nodeId selected else selected
            if selected.Contains nodeId then
                captures |> List.fold (fun selected capture ->
                    match capture.SourceNodeId |> Option.bind lambda with
                    | Some dependency when not capture.IsMutable -> Set.add dependency selected
                    | _ -> selected) selected
            else selected) selected
        if next = selected then selected else family next
    let candidates = family seeds
    if candidates.IsEmpty then [] else
    let aliasesByLambda =
        let fromLambdas =
            resolution.Lambdas
            |> Map.toSeq
            |> Seq.choose (fun (value, target) ->
                if candidates.Contains target && nodes.ContainsKey value then Some (target, value) else None)
        let fromKnown =
            known
            |> Map.toSeq
            |> Seq.choose (fun (value, kc) ->
                if not (resolution.Lambdas.ContainsKey value) && candidates.Contains kc.Implementation && nodes.ContainsKey value then
                    Some (kc.Implementation, value)
                else None)
        Seq.append fromLambdas fromKnown
        |> Seq.groupBy fst
        |> Seq.map (fun (target, pairs) -> target, pairs |> Seq.map snd |> Set.ofSeq)
        |> Map.ofSeq
    let completeCallsByLambda =
        resolution.Calls
        |> Map.toSeq
        |> Seq.choose (fun (call, resolved) ->
            match resolved.Targets with
            | [target] when resolved.Complete && not resolved.Unknown && candidates.Contains target.Lambda ->
                Some (target.Lambda, (call, target.Parameters))
            | _ -> None)
        |> Seq.groupBy fst
        |> Seq.map (fun (targetLambda, pairs) -> targetLambda, pairs |> Seq.map snd |> Seq.toList)
        |> Map.ofSeq
    let structuralUsersByInput = System.Collections.Generic.Dictionary<NodeId, ResizeArray<SemanticNode>>()
    let captureUsersBySource = System.Collections.Generic.Dictionary<NodeId, ResizeArray<SemanticNode * CaptureInfo>>()
    for node in nodes.Values do
        let inputs =
            kindEdges node.Id node.Kind
            |> List.filter Hyperedge.isStructural
            |> List.collect _.Sources
            |> List.append node.Children
            |> List.distinct
        for input in inputs do
            match structuralUsersByInput.TryGetValue input with
            | true, bucket -> bucket.Add node
            | false, _ ->
                let bucket = ResizeArray<SemanticNode>()
                bucket.Add node
                structuralUsersByInput[input] <- bucket
        match node.Kind with
        | SemanticKind.Lambda(_, _, nested, _, _)
        | SemanticKind.LazyExpr(_, nested) ->
            for capture in nested do
                match capture.SourceNodeId with
                | Some sourceId ->
                    match captureUsersBySource.TryGetValue sourceId with
                    | true, bucket -> bucket.Add(node, capture)
                    | false, _ ->
                        let bucket = ResizeArray<SemanticNode * CaptureInfo>()
                        bucket.Add(node, capture)
                        captureUsersBySource[sourceId] <- bucket
                | None -> ()
        | _ -> ()
    candidates |> Set.toList |> List.choose (fun id ->
        let source = nodes[id]
        match source.Kind with
        | SemanticKind.Lambda(parameters, body, captures, _, LambdaContext.RegularClosure)
            when not parameters.IsEmpty && not (source.Metadata.ContainsKey ClosureMetadata.SourceSignature) &&
                 (not captures.IsEmpty ||
                  ([ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
                   |> List.exists (fun key -> source.Metadata.TryFind key = Some (MetadataValue.Bool true)))) ->
            let aliases = aliasesByLambda |> Map.tryFind id |> Option.defaultValue Set.empty
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
                | ty when not capture.IsMutable && Types.tryGetNTUKind ty = Some NTUKind.NTUstring -> true
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
            let calls =
                completeCallsByLambda
                |> Map.tryFind id
                |> Option.defaultValue []
                |> List.choose (fun (call, targetParameters) ->
                    if captures.IsEmpty || targetParameters = parameters then Some call else None)
            let callSet = Set.ofList calls
            for input in aliases do
                match structuralUsersByInput.TryGetValue input with
                | true, users ->
                    for node in users do
                        match node.Kind with
                        | SemanticKind.Binding(_, false, _, _) | SemanticKind.TypeAnnotation _ | SemanticKind.EagerExpr _ -> ()
                        | SemanticKind.Sequential _ -> ()
                        | SemanticKind.Application(callee, _) when callee = input && callSet.Contains node.Id -> ()
                        | SemanticKind.Application(_, arguments) when List.contains input arguments ->
                            // An actual callable argument must feed an exact known
                            // formal; opaque higher-order consumers remain residual.
                            match resolution.Calls.TryFind node.Id with
                            | Some { Targets = [target]; Unknown = false; Complete = true } when candidates.Contains target.Lambda -> ()
                            | _ -> rejected <- true
                        | SemanticKind.Lambda(formals, body, _, _, _) when
                            (formals |> List.exists (fun (_, _, formal) -> formal = input)) ||
                            (body = input && candidates.Contains node.Id) -> ()
                        | SemanticKind.EnvironmentCreate(owner, _) when
                            capturedInitializers graph owner |> Option.exists (List.exists (fun (_, value, mutableCell) -> value = input && not mutableCell)) -> ()
                        | _ -> rejected <- true
                | false, _ -> ()
                match captureUsersBySource.TryGetValue input with
                | true, capUsers ->
                    for (node, capture) in capUsers do
                        match node.Kind with
                        | SemanticKind.Lambda(_, _, _, _, context) ->
                            if capture.IsMutable || (context <> LambdaContext.SeqGenerator && not (candidates.Contains node.Id)) then rejected <- true
                        | SemanticKind.LazyExpr _ ->
                            rejected <- true
                        | _ -> ()
                | false, _ -> ()
            // Stateless promotion supplies a named declaration; it rewrites no
            // invocation and needs no singleton direct call. A higher-order
            // formal can legitimately receive several such code alternatives.
            if rejected || (not captures.IsEmpty && calls.IsEmpty) then None
            else Some { Source = source; Captures = captures; Calls = calls }
        | _ -> None)
    // Plain code has no runtime environment. Settle these declarations before
    // a capturing front chooses slots for its retained values.
    |> List.sortBy (fun plan -> not plan.Captures.IsEmpty, plan.Source.Id)

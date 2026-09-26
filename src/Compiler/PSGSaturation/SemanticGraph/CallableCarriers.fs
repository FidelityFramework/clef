// SPDX-License-Identifier: MIT
/// Project a settled callable boundary from its resident participants. This
/// does not choose a layout, infer native arity from arrows, or identify an
/// environment instance from code identity. Inputs avoid forcing final Codata
/// while NativeService is constructing that same immutable reading.
module Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Inputs = {
    Layouts: Map<NodeId, EnvironmentLayout>
    Origins: Map<NodeId, NodeId>
    Known: Map<NodeId, KnownCallable>
}

type Residual = { Occurrence: NodeId; Reason: string }

let sourceType (node: SemanticNode) =
    match node.Metadata.TryFind ClosureMetadata.SourceSignature with
    | Some (MetadataValue.Type ty) -> ty
    | _ -> node.Type

let private finalPath (graph: SemanticGraph) terminal body =
    let rec walk seen id =
        if Set.contains id seen then None else
        match graph.Nodes.TryFind id with
        | Some node when terminal node -> Some [id]
        | Some { Kind = SemanticKind.Sequential values } ->
            List.tryLast values |> Option.bind (walk (Set.add id seen)) |> Option.map (fun path -> id :: path)
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } ->
            walk (Set.add id seen) inner |> Option.map (fun path -> id :: path)
        | Some { Kind = SemanticKind.EagerExpr inner } when ExplicitDemand.operand graph id = Some inner ->
            walk (Set.add id seen) inner |> Option.map (fun path -> id :: path)
        | _ -> None
    walk Set.empty body

/// Hidden result formals are recognized only by the producer's actual final
/// constructor and its exact resident destination relation, never by a name.
let resultDestinations (graph: SemanticGraph) implementation body =
    let sequencePath = finalPath graph (fun node -> match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) body
    let closurePath = finalPath graph (fun node -> match node.Kind with SemanticKind.ClosureValue _ -> true | _ -> false) body
    let lazyPath = finalPath graph (fun node -> match node.Kind with SemanticKind.LazyValue _ -> true | _ -> false) body
    graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Sources with
        | EdgeClass.Provenance, EdgeRole.EnrichedWith, path ->
            sequencePath |> Option.bind (fun resultPath ->
                if path = implementation :: resultPath then
                    let owner = graph.Nodes[List.last resultPath]
                    match graph.Nodes.TryFind edge.Target with
                    | Some { Kind = SemanticKind.PatternBinding _; Type = ty } when applySubst ty = applySubst owner.Type -> Some edge.Target
                    | _ -> None
                else None)
        | EdgeClass.Provenance, EdgeRole.EnvironmentResultDestination, [actual; owner; formal] when actual = implementation ->
            closurePath |> Option.bind (fun path ->
                if List.last path <> owner then None else
                match graph.Nodes[owner].Kind, graph.Nodes.TryFind edge.Target, graph.Nodes.TryFind formal with
                | SemanticKind.ClosureValue(_, constructor), Some { Kind = SemanticKind.EnvironmentCreate(expected, _) },
                  Some { Kind = SemanticKind.PatternBinding _; Type = ty }
                    when constructor = edge.Target && expected = owner && applySubst ty = ClosureEnvironments.environmentType -> Some formal
                | _ -> None)
        | EdgeClass.Provenance, EdgeRole.LazyResultDestination, [actual; owner; formal] when actual = implementation ->
            lazyPath |> Option.bind (fun path ->
                if List.last path <> owner then None else
                match graph.Nodes[owner].Kind, graph.Nodes.TryFind edge.Target, graph.Nodes.TryFind formal with
                | SemanticKind.LazyValue(_, constructor), Some { Kind = SemanticKind.LazyEnvironment(expected, _) },
                  Some { Kind = SemanticKind.PatternBinding _; Type = ty }
                    when constructor = edge.Target && expected = owner && applySubst ty = ClosureEnvironments.environmentType -> Some formal
                | _ -> None)
        | _ -> None) |> Set.ofList

/// A source sequence value transports its protocol and actual environment.
/// The generator's frame formal and a producer's proved destination instead
/// name storage, even though their source type carries the sequence element.
/// Follow only immutable aliases and the resident continuation value relation;
/// equal source types or generated names never establish this distinction.
let private rawSequenceStorage (graph: SemanticGraph) =
    let roots =
        graph.Nodes.Values
        |> Seq.collect (fun candidate ->
            match candidate.Kind with
            | SemanticKind.Lambda(parameters, _, _, _, LambdaContext.SeqGenerator) ->
                parameters |> Seq.map (fun (_, _, formal) -> formal)
            | SemanticKind.Lambda(_, body, _, _, _) -> resultDestinations graph candidate.Id body |> Set.toSeq
            | SemanticKind.ContinuationAllocate _ -> Seq.singleton candidate.Id
            | _ -> Seq.empty)
        |> Set.ofSeq
    let provenance =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources with
            | EdgeClass.Provenance, EdgeRole.ContinuationValue, [source] when edge.Ordinal = 0 -> Some(edge.Target, source)
            | _ -> None)
        |> List.groupBy fst
        |> List.choose (fun (target, rows) ->
            match rows |> List.map snd |> List.distinct with [source] -> Some(target, source) | _ -> None)
        |> Map.ofList
    let aliases =
        graph.Nodes.Values |> Seq.choose (fun node ->
            let source =
                match node.Kind, node.Children with
                | SemanticKind.VarRef(_, Some declaration), _ -> Some declaration
                | SemanticKind.Binding(_, false, _, _), [value] -> Some value
                | SemanticKind.TypeAnnotation(value, _), _ -> Some value
                | SemanticKind.EagerExpr value, _ when ExplicitDemand.operand graph node.Id = Some value -> Some value
                | _ -> provenance.TryFind node.Id
            source |> Option.map (fun source -> source, node.Id))
        |> Seq.toList
        |> List.groupBy fst
        |> List.map (fun (source, values) -> source, values |> List.map snd)
        |> Map.ofList
    let pending = System.Collections.Generic.Queue<NodeId>(roots)
    let mutable found = roots
    while pending.Count > 0 do
        let source = pending.Dequeue()
        for target in aliases.TryFind source |> Option.defaultValue [] do
            if not (found.Contains target) then
                found <- found.Add target
                pending.Enqueue target
    found

// A graph is an immutable snapshot. Only reference identity keys this pure
// incidence cache, so changed Nodes/Edges retract every derived role, and weak
// keys do not retain abandoned editor snapshots. No Codata is forced here.
let private rawStorageCache = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, Set<NodeId>>()

let valueShape (graph: SemanticGraph) (node: SemanticNode) =
    match applySubst node.Type with
    | NativeType.TFun _ -> CallableValueShape.Callable node.Id
    | NativeType.TLazy _ -> CallableValueShape.Lazy node.Id
    | NativeType.TSeq _ | NativeType.TSeqEnumerator _ ->
        let raw = rawStorageCache.GetValue(graph, fun graph -> rawSequenceStorage graph)
        if raw.Contains node.Id then CallableValueShape.Data node.Id else CallableValueShape.Sequence node.Id
    | _ -> CallableValueShape.Data node.Id

let private signatureResult parameters ty =
    let rec loop remaining ty =
        match remaining, applySubst ty with
        | _, NativeType.TForall(_, body) -> loop remaining body
        | [], result -> Some result
        | (_, argument, _) :: rest, NativeType.TFun(actual, result)
            when applySubst argument = applySubst actual -> loop rest result
        | _ -> None
    loop parameters ty

/// Only actual source callable values with a uniquely established boundary are
/// seeded here. Opaque functions and intrinsics do not acquire an invented form;
/// a consumer requiring their carrier must request owning-stage settlement.
let settle (inputs: Inputs) (graph: SemanticGraph) : Map<NodeId, CallableCarrier> * Residual list =
    let resolution = CallableOrigins.resolve graph
    let lambdas = resolution.Lambdas
    let ingress = CallableIngress.analyzeWith graph resolution
    let instance = CallableInstantiations.readerWith graph resolution ingress
    let lazyThunks = LazyContracts.instances graph |> Map.toSeq |> Seq.map (fun (_, instance) -> instance.Thunk) |> Set.ofSeq
    let mutable residuals = []
    let refuse occurrence reason =
        residuals <- { Occurrence = occurrence; Reason = reason } :: residuals
        None
    let project (node: SemanticNode) implementation environment =
        match graph.Nodes.TryFind implementation with
        | Some ({ Kind = SemanticKind.Lambda(parameters, body, [], _, context)
                  Type = physicalType; IsReachable = true } as implementationNode)
            when context = LambdaContext.RegularClosure ||
                 (context = LambdaContext.LazyThunk && lazyThunks.Contains implementation) ->
            let formalsAgree =
                (parameters |> List.map (fun (_, _, id) -> id) |> Set.ofList).Count = parameters.Length &&
                (parameters |> List.forall (fun (_, ty, id) ->
                    match graph.Nodes.TryFind id with
                    | Some { Kind = SemanticKind.PatternBinding _; Type = actual } -> applySubst actual = applySubst ty
                    | _ -> false))
            let resultAgrees =
                match signatureResult parameters physicalType, graph.Nodes.TryFind body with
                | Some expected, Some result -> applySubst expected = applySubst result.Type
                | _ -> false
            let environmentRows = graph.Edges |> List.filter (fun edge ->
                edge.Role = EdgeRole.EnvironmentFormal && List.tryLast edge.Sources = Some implementation)
            let environmentAgrees =
                match environment with
                | None -> environmentRows.IsEmpty
                | Some (known: KnownCallable) ->
                    match inputs.Layouts.TryFind known.EnvironmentOwner, environmentRows, parameters with
                    | Some layout, [row], (_, ty, formal) :: _ ->
                        let capturesAgree =
                            match ClosureEnvironments.capturedInitializers graph layout.Owner with
                            | Some initializers when initializers.Length = layout.Slots.Length ->
                                (layout.Slots |> List.map _.Source |> Set.ofList).Count = layout.Slots.Length &&
                                (layout.Slots |> List.forall (fun slot ->
                                    initializers |> List.exists (fun (source, _, mutableCell) ->
                                        source = slot.Source && slot.IsCapture &&
                                        applySubst graph.Nodes[source].Type = applySubst slot.ValueType &&
                                        (match slot.Holds with CaptureSlotKind.CellView _ -> mutableCell | _ -> not mutableCell))))
                            | _ -> false
                        layout.Owner = known.EnvironmentOwner && layout.Implementation = implementation &&
                        layout.Formal = formal && not layout.Slots.IsEmpty && layout.Bytes > 0 && layout.Alignment > 0 &&
                        row.Class = EdgeClass.Provenance && row.Sources = [layout.Owner; implementation] && row.Target = formal &&
                        applySubst ty = ClosureEnvironments.environmentType &&
                        inputs.Origins.TryFind node.Id = Some layout.Owner &&
                        capturesAgree &&
                        (match graph.Nodes.TryFind layout.Owner with
                         | Some { Kind = SemanticKind.ClosureValue(code, _) } -> code = implementation
                         | _ -> false)
                    | _ -> false
            let hidden =
                let destinations = resultDestinations graph implementation body
                match environment with
                | Some known ->
                    inputs.Layouts.TryFind known.EnvironmentOwner
                    |> Option.map (fun layout -> Set.add layout.Formal destinations)
                    |> Option.defaultValue destinations
                | None -> destinations
            let directCaptures =
                if context = LambdaContext.RegularClosure then DirectCaptures.tryCaptureFormals graph implementation hidden
                else Some Set.empty
            let publicTypeAgrees =
                match graph.Nodes.TryFind body, directCaptures with
                | Some result, Some captures ->
                    let hidden = Set.union hidden captures
                    let visible = parameters |> List.filter (fun (_, _, id) -> not (hidden.Contains id))
                    let logical = List.foldBack (fun (_, ty, _) result -> NativeType.TFun(ty, result)) visible result.Type
                    let declared =
                        match implementationNode.Metadata.TryFind ClosureMetadata.SourceSignature with
                        | Some (MetadataValue.Type ty) -> ty
                        | _ -> logical
                    applySubst logical = applySubst declared &&
                    (applySubst (sourceType node) = applySubst declared ||
                     instance implementation declared node.Id |> Option.isSome)
                | _ -> false
            if not formalsAgree then refuse node.Id "Callable formals do not match their unique typed graph declarations."
            elif not resultAgrees then refuse node.Id "Callable physical signature does not agree with its declared parameters and actual body result."
            elif not environmentAgrees then refuse node.Id "Callable environment is not the settled nonempty environment at this occurrence and its first formal."
            elif directCaptures.IsNone then refuse node.Id "Callable direct-capture formals lack valid immutable source and typed parameter provenance."
            elif not publicTypeAgrees then refuse node.Id "Callable public signature disagrees after removing only its proved hidden formals."
            else
                Some(node.Id,
                    { Occurrence = node.Id; SourceType = sourceType node; Implementation = implementation
                      Parameters = parameters
                      ParameterShapes = parameters |> List.map (fun (_, _, id) -> valueShape graph graph.Nodes[id])
                      Result = body; ResultShape = valueShape graph graph.Nodes[body]
                      Environment = environment |> Option.map (fun known ->
                          { Owner = known.EnvironmentOwner; Formal = inputs.Layouts[known.EnvironmentOwner].Formal }) })
        | _ -> refuse node.Id "Callable implementation lacks a reachable capture-free physical lambda boundary."
    let carriers = graph.Nodes |> Map.toList |> List.choose (fun (_, node) ->
        match applySubst node.Type with
        | NativeType.TFun _ when node.IsReachable && CallableIngress.allowsOccurrence ingress node.Id ->
            match inputs.Known.TryFind node.Id with
            | Some known -> project node known.Implementation (Some known)
            | None ->
                match lambdas.TryFind node.Id with
                | Some implementation ->
                    match graph.Nodes.TryFind implementation with
                    | Some ({ Kind = SemanticKind.Lambda(_, _, [], _, context) } as code)
                        when context = LambdaContext.RegularClosure ||
                             (context = LambdaContext.LazyThunk && lazyThunks.Contains implementation) ->
                        // Materialized implementations themselves are code
                        // declarations with an explicit environment parameter;
                        // they are not captureless source callable values.
                        let materialized = graph.Edges |> List.exists (fun edge ->
                            edge.Role = EdgeRole.EnvironmentFormal && List.tryLast edge.Sources = Some implementation)
                        let unsettledExpression =
                            [ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
                            |> List.exists (fun key -> code.Metadata.TryFind key = Some (MetadataValue.Bool true))
                        if materialized || (unsettledExpression && not (lazyThunks.Contains implementation)) then None
                        else project node implementation None
                    | _ -> None
                | None -> None
        | _ -> None) |> Map.ofList
    carriers, List.rev residuals

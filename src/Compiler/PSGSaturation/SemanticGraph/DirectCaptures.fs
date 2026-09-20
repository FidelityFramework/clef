// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Conservative admission of the direct named-function form (closure spec §8).
/// This first slice passes immutable captures only. A binding parent is a
/// candidate shape; every reachable use must independently establish a direct call.
module Clef.Compiler.PSGSaturation.SemanticGraph.DirectCaptures

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Plan = {
    Binding: SemanticNode
    Lambda: SemanticNode
    Captures: CaptureInfo list
    BodyNodes: Set<NodeId>
    CalleeNodes: Set<NodeId>
    Calls: Set<NodeId>
}

/// Recover the declaration a source reference named before direct-capture
/// elaboration. Only the typed CaptureOrigin relation authorizes a step;
/// unrelated enrichment edges and source names are not definition evidence.
/// Malformed, ambiguous or cyclic chains leave the semantic definition intact.
let sourceDefinition (graph: SemanticGraph) (definition: NodeId) : NodeId =
    let rec follow seen current =
        if Set.contains current seen then None else
        match graph.Nodes.TryFind current with
        | Some { Kind = SemanticKind.PatternBinding _ } ->
            let origins = graph.Edges |> List.filter (fun edge ->
                edge.Target = current && edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.CaptureOrigin)
            match origins with
            | [] -> Some current
            | [{ Sources = [lambda; declaration] }] ->
                match graph.Nodes.TryFind lambda, graph.Nodes.TryFind declaration with
                | Some { Kind = SemanticKind.Lambda _ }, Some { Kind = SemanticKind.Binding _ | SemanticKind.PatternBinding _ } ->
                    follow (Set.add current seen) declaration
                | _ -> None
            | _ -> None
        | Some _ -> Some current
        | None -> None
    follow Set.empty definition |> Option.defaultValue definition

let private functionValue (node: SemanticNode) =
    [ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
    |> List.exists (fun key -> node.Metadata.TryFind key = Some (MetadataValue.Bool true))

let private frontier = function
    | SemanticKind.Lambda (_, _, captures, _, _) | SemanticKind.LazyExpr (_, captures)
    | SemanticKind.SeqExpr (_, captures) -> captures
    | _ -> []

let private subtree (nodes: Map<NodeId, SemanticNode>) root =
    let rec visit seen id =
        if Set.contains id seen then seen else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some node -> List.fold visit seen node.Children
        | None -> seen
    visit Set.empty root

/// Every supplied capture already denotes an ordinary value. In particular,
/// a direct named declaration is not yet a materialized function argument.
let private valueCapture (nodes: Map<NodeId, SemanticNode>) (capture: CaptureInfo) =
    if capture.IsMutable then false else
    match capture.SourceNodeId |> Option.bind nodes.TryFind with
    | Some { Kind = SemanticKind.PatternBinding _ } -> true
    | Some { Kind = SemanticKind.Binding (_, false, _, _); Children = [value] } ->
        let rec ordinary seen id =
            if Set.contains id seen then false else
            match nodes.TryFind id with
            | Some ({ Kind = SemanticKind.Lambda _ } as lambda) -> functionValue lambda
            | Some { Kind = SemanticKind.TypeAnnotation (inner, _) }
            | Some { Kind = SemanticKind.VarRef (_, Some inner) } -> ordinary (Set.add id seen) inner
            | Some { Kind = SemanticKind.Binding (_, false, _, _); Children = [inner] } -> ordinary (Set.add id seen) inner
            | Some _ -> true
            | None -> false
        match applySubst capture.Type with
        | NativeType.TFun _ -> ordinary Set.empty value
        | _ -> true
    | _ -> false

let plans (graph: SemanticGraph) : Plan list =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let uses =
        nodes |> Map.fold (fun acc id node ->
            let inputs =
                kindEdges id node.Kind
                |> List.filter (fun edge -> edge.Class = EdgeClass.Structural)
                |> List.collect (fun edge -> edge.Sources)
                |> List.append node.Children |> List.distinct
            inputs |> List.fold (fun acc input ->
                let previous = Map.tryFind input acc |> Option.defaultValue []
                Map.add input (id :: previous) acc) acc) Map.empty
    let rec arity id =
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } ->
            match nodes.TryFind body with
            | Some ({ Kind = SemanticKind.Lambda _ } as inner) when not (functionValue inner) -> parameters.Length + arity body
            | _ -> parameters.Length
        | _ -> 0
    let admit binding lambda captures body =
        let count = arity lambda.Id
        let refs = nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.VarRef (_, Some target) -> target = binding.Id | _ -> false) |> Seq.toList
        let capturedAsValue = nodes.Values |> Seq.exists (fun node ->
            frontier node.Kind |> List.exists (fun capture -> capture.SourceNodeId = Some binding.Id))
        let opaqueReference = graph.Edges |> List.exists (fun edge ->
            edge.Class = EdgeClass.Reference && List.contains binding.Id edge.Sources &&
            (match nodes.TryFind edge.Target with
             | Some { Kind = SemanticKind.VarRef (_, Some target) } when target = binding.Id -> false
             | Some _ -> true
             | None -> false))
        let rec directUses seen id =
            if Set.contains id seen then None else
            let seen = Set.add id seen
            let users = uses.TryFind id |> Option.defaultValue []
            if users.IsEmpty then None else
            users |> List.fold (fun state user ->
                state |> Option.bind (fun (callees, calls) ->
                    match nodes[user].Kind with
                    | SemanticKind.TypeAnnotation (inner, _) when inner = id ->
                        directUses seen user |> Option.map (fun (more, sites) -> Set.union callees more, Set.union calls sites)
                    | SemanticKind.Application (callee, args) when callee = id && args.Length = count ->
                        Some (Set.add id callees, Set.add user calls)
                    | SemanticKind.Sequential expressions when List.tryLast expressions <> Some id ->
                        // CallableApplications retains eager callee evaluation before
                        // staged calls. A discarded named reference does not escape.
                        Some (Set.add id callees, calls)
                    | _ -> None)) (Some (Set.singleton id, Set.empty))
        if count = 0 || refs.IsEmpty || capturedAsValue || opaqueReference || not (List.forall (valueCapture nodes) captures) then None else
        refs |> List.fold (fun state reference ->
            state |> Option.bind (fun (callees, calls) ->
                directUses Set.empty reference.Id |> Option.map (fun (more, sites) -> Set.union callees more, Set.union calls sites)))
            (Some (Set.empty, Set.empty))
        |> Option.filter (fun (_, calls) -> not calls.IsEmpty)
        |> Option.map (fun (callees, calls) ->
            { Binding = binding; Lambda = lambda; Captures = captures
              BodyNodes = subtree nodes body; CalleeNodes = callees; Calls = calls })
    nodes.Values |> Seq.choose (fun binding ->
        match binding.Kind, binding.Children with
        | SemanticKind.Binding (_, false, _, None), [lambdaId] ->
            match nodes.TryFind lambdaId with
            | Some ({ Kind = SemanticKind.Lambda (_, body, captures, Some _, LambdaContext.RegularClosure) } as lambda)
                when not captures.IsEmpty && not (functionValue lambda) -> admit binding lambda captures body
            | _ -> None
        | _ -> None)
    // Settle nested candidates first; each firing removes one nonempty frontier.
    |> Seq.sortBy (fun plan -> plan.BodyNodes.Count, plan.Lambda.Id) |> Seq.toList

// SPDX-License-Identifier: MIT
/// Source selection for immutable finite dispatch environments. A tag names a
/// proved code alternative, never a code address. Selection cannot close an
/// exported or opaque input from the callers that happen to be observed.
module Clef.Compiler.PSGSaturation.SemanticGraph.CallableDispatch

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Member = { Implementation: SemanticNode; Declaration: SemanticNode }
type Actual = { Call: SemanticNode; Position: int; Value: NodeId; Member: int }
type Plan = { Formal: SemanticNode; Members: Member list; Actuals: Actual list }

/// This first source construction admits immutable stateless references. An
/// effectful factory or captured leaf needs its actual retained environment;
/// neither may be replaced by a tag alone.
let plans (graph: SemanticGraph) =
    let resolution = lazy (CallableOrigins.resolve graph)
    let ingress = lazy (CallableIngress.analyzeWith graph resolution.Value)
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let captured =
        nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.Lambda(_, _, captures, _, LambdaContext.RegularClosure) ->
                captures |> List.choose (fun capture ->
                    match applySubst capture.Type, capture.IsMutable, capture.SourceNodeId with
                    | NativeType.TFun _, false, Some source -> Some source
                    | _ -> None)
            | _ -> []) |> Set.ofSeq
    let rec plain seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _) } -> plain seen value
        | Some { Kind = SemanticKind.Binding(_, false, _, None); Children = [value] } -> plain seen value
        | Some ({ Kind = SemanticKind.Lambda(_, _, [], _, LambdaContext.RegularClosure); Parent = Some parent } as implementation)
            when implementation.Metadata.TryFind ClosureMetadata.LambdaExpression <> Some(MetadataValue.Bool true) &&
                 implementation.Metadata.TryFind ClosureMetadata.RequiresClosurePair <> Some(MetadataValue.Bool true) ->
            match nodes.TryFind parent with
            | Some ({ Kind = SemanticKind.Binding(_, false, _, None); Children = [child] } as declaration)
                when child = id -> Some { Implementation = implementation; Declaration = declaration }
            | _ -> None
        | _ -> None
    captured |> Set.toList |> List.choose (fun formal ->
        match nodes.TryFind formal with
        | Some ({ Kind = SemanticKind.PatternBinding _ } as node) ->
            let inputs = resolution.Value.ParameterInputs.TryFind formal |> Option.defaultValue []
            let actuals = inputs |> List.map (fun (callId, actual) ->
                match nodes.TryFind callId, resolution.Value.Calls.TryFind callId, plain Set.empty actual with
                | Some ({ Kind = SemanticKind.Application(_, arguments) } as call), Some resolved, Some memberValue
                    when resolved.Complete && not resolved.Unknown && not resolved.Targets.IsEmpty ->
                    let positions = resolved.Targets |> List.map (fun target ->
                        target.Parameters |> List.tryFindIndex (fun (_, _, id) -> id = formal)) |> List.distinct
                    match positions with
                    | [Some position] when List.tryItem position arguments = Some actual &&
                                           applySubst node.Type = applySubst memberValue.Implementation.Type ->
                        Some(call, position, actual, memberValue)
                    | _ -> None
                | _ -> None)
            if inputs.IsEmpty || List.exists Option.isNone actuals then None else
            let actuals = List.choose id actuals
            let members = actuals |> List.map (fun (_, _, _, memberValue) -> memberValue)
                          |> List.distinctBy _.Implementation.Id |> List.sortBy _.Implementation.Id
            let shapes = members |> List.map (fun memberValue ->
                match memberValue.Implementation.Kind with
                | SemanticKind.Lambda(parameters, body, _, _, _) ->
                    parameters |> List.map (fun (_, ty, _) -> applySubst ty), applySubst nodes[body].Type
                | _ -> [], applySubst node.Type) |> List.distinct
            if members.Length < 2 || shapes.Length <> 1 || not (CallableIngress.allowsOccurrence ingress.Value formal) then None else
            Some { Formal = node; Members = members
                   Actuals = actuals |> List.map (fun (call, position, actual, memberValue) ->
                       { Call = call; Position = position; Value = actual
                         Member = members |> List.findIndex (fun selected -> selected.Implementation.Id = memberValue.Implementation.Id) }) }
        | _ -> None)

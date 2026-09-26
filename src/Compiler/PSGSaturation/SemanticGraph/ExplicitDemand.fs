// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// A direct explicit demand marker is transparent only through source grouping
/// and annotations. This reader does not follow aliases or search deferred work.
module Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Direct = { Marker: NodeId; Operand: NodeId; Wrappers: NodeId list }

let direct (graph: SemanticGraph) id : Result<Direct option, NodeId list> =
    let resident id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
    let rec read seen path id =
        if Set.contains id seen then Error (List.rev (id :: path)) else
        match graph.Nodes.TryFind id with
        | Some value when not value.IsReachable -> Error (List.rev (id :: path))
        | Some ({ Kind = SemanticKind.TypeAnnotation(inner, declared) } as wrapper) ->
            match resident inner with
            | Some operand when wrapper.Children = [inner]
                                && applySubst wrapper.Type = applySubst declared
                                && applySubst declared = applySubst operand.Type ->
                read (Set.add id seen) (id :: path) inner
            | _ -> Error (List.rev (inner :: id :: path))
        | Some ({ Kind = SemanticKind.EagerExpr operand } as marker) ->
            match resident operand with
            | Some value when marker.Children = [operand] && applySubst marker.Type = applySubst value.Type ->
                Ok (Some { Marker = id; Operand = operand; Wrappers = List.rev path })
            | _ -> Error (List.rev (operand :: id :: path))
        | Some _ -> Ok None
        | None -> Error (List.rev path)
    read Set.empty [] id

/// Value-origin readers may cross this marker while retaining its identity in
/// their evidence. This establishes no activation, hoisting or demand of a body.
let operand (graph: SemanticGraph) id =
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.EagerExpr _ } ->
        match direct graph id with
        | Ok (Some marker) -> Some marker.Operand
        | _ -> None
    | _ -> None

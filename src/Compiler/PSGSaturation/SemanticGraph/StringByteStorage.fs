// SPDX-License-Identifier: MIT
/// Exact storage projection of Baker's byte-unit encoding evidence.
module Clef.Compiler.PSGSaturation.SemanticGraph.StringByteStorage

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let element (graph: SemanticGraph) (arrayId: NodeId) : SettledSlot option =
    graph.Edges
    |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Sources with
        | EdgeClass.Range, EdgeRole.StringByteStorage(lo, hi, representation), _ :: _ :: _ :: _
            when edge.Target = arrayId && lo >= 0I && hi <= 255I && lo <= hi
                 && (edge.Sources |> List.forall graph.Nodes.ContainsKey) ->
            Some(SettledSlot.Integer(8, Some representation))
        | _ -> None)
    |> List.distinct
    |> function [slot] -> Some slot | _ -> None

/// A scalar read fact remains resident across the range pass that settles
/// newly composed copy operations. Its dependencies travel with the graph.
let readRange (graph: SemanticGraph) (readId: NodeId) : ValueRange option =
    graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role with
        | EdgeClass.Range, EdgeRole.StringByteRange(lo, hi)
            when edge.Target = readId && lo <= hi && not edge.Sources.IsEmpty
                 && (edge.Sources |> List.forall graph.Nodes.ContainsKey) -> Some(ValueRange.bounded lo hi)
        | _ -> None)
    |> function [] -> None | ranges -> Some(List.reduce ValueRange.meet ranges)

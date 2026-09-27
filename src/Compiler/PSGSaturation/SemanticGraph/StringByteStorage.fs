// SPDX-License-Identifier: MIT
/// Exact storage projection of Baker's byte-unit encoding evidence.
module Clef.Compiler.PSGSaturation.SemanticGraph.StringByteStorage

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let evidence (graph: SemanticGraph) arrayId =
    let rec follow seen id =
        if Set.contains id seen then None else
        let seen=Set.add id seen
        let rows=graph.Edges |> List.choose(fun edge ->
            match edge.Class,edge.Role,edge.Sources with
            | EdgeClass.Range,EdgeRole.StringByteStorage(lo,hi,representation),_::_::_::_
                when edge.Target=id && 0I<=lo && lo<=hi && hi<=255I && List.forall graph.Nodes.ContainsKey edge.Sources ->
                Some(SettledSlot.Integer(8,Some representation),lo,hi,Set.ofList(id::edge.Sources))
            | _ -> None) |> List.distinct
        match rows with
        | [slot,lo,hi,participants] -> Some(slot,lo,hi,Set.union seen participants)
        | _::_ -> None
        | [] ->
            match graph.Nodes.TryFind id with
            | Some {Kind=SemanticKind.VarRef(_,Some binding)} ->
                match graph.Nodes.TryFind binding with
                | Some {Kind=SemanticKind.Binding(_,false,_,_)} -> follow seen binding
                | _ -> None
            | Some {Kind=SemanticKind.Binding(_,false,_,_);Children=[value]}
            | Some {Kind=SemanticKind.TypeAnnotation(value,_)} -> follow seen value
            | Some {Kind=SemanticKind.Sequential values} when not values.IsEmpty -> follow seen (List.last values)
            | _ -> None
    follow Set.empty arrayId

let element (graph: SemanticGraph) (arrayId: NodeId) : SettledSlot option =
    evidence graph arrayId |> Option.map(fun (slot,_,_,_) -> slot)

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

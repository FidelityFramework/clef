// SPDX-License-Identifier: MIT
/// Exact storage projection of Baker's byte-unit encoding evidence.
module Clef.Compiler.PSGSaturation.SemanticGraph.StringByteStorage

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type private GraphByteIndex = {
    StorageByTarget: Lazy<Map<NodeId, (SettledSlot * bigint * bigint * Set<NodeId>) list>>
    ReadRangesByTarget: Lazy<Map<NodeId, ValueRange>>
}

let private byteIndexes = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, GraphByteIndex>()
let private buildByteIndex =
    System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, GraphByteIndex>.CreateValueCallback(fun graph ->
        let storage = lazy (
            let mutable rows = []
            for edge in graph.Edges do
                match edge.Class, edge.Role, edge.Sources with
                | EdgeClass.Range, EdgeRole.StringByteStorage(lo, hi, representation), _ :: _ :: _ :: _
                    when 0I <= lo && lo <= hi && hi <= 255I && List.forall graph.Nodes.ContainsKey edge.Sources ->
                    rows <- (edge.Target, (SettledSlot.Integer(8, Some representation), lo, hi, Set.ofList(edge.Target :: edge.Sources))) :: rows
                | _ -> ()
            if rows.IsEmpty then Map.empty
            else
                rows
                |> List.rev
                |> List.groupBy fst
                |> List.map (fun (target, items) -> target, items |> List.map snd |> List.distinct)
                |> Map.ofList)
        let readRanges = lazy (
            let mutable rows = []
            for edge in graph.Edges do
                match edge.Class, edge.Role with
                | EdgeClass.Range, EdgeRole.StringByteRange(lo, hi)
                    when lo <= hi && not edge.Sources.IsEmpty && (edge.Sources |> List.forall graph.Nodes.ContainsKey) ->
                    rows <- (edge.Target, ValueRange.bounded lo hi) :: rows
                | _ -> ()
            if rows.IsEmpty then Map.empty
            else
                rows
                |> List.rev
                |> List.groupBy fst
                |> List.map (fun (target, items) -> target, items |> List.map snd |> List.reduce ValueRange.meet)
                |> Map.ofList)
        { StorageByTarget = storage; ReadRangesByTarget = readRanges })

let private getByteIndex (graph: SemanticGraph) =
    byteIndexes.GetValue(graph, buildByteIndex)

let evidence (graph: SemanticGraph) arrayId =
    let storage = (getByteIndex graph).StorageByTarget.Value
    if storage.IsEmpty then None
    else
        let rec follow seen id =
            if Set.contains id seen then None else
            let seen=Set.add id seen
            let rows = storage.TryFind id |> Option.defaultValue []
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
    (getByteIndex graph).ReadRangesByTarget.Value.TryFind readId

// SPDX-License-Identifier: MIT
/// Read typed field/payload transport from the shared source origin census.
/// This grants neither storage nor lifetime authority; those belong to the
/// aggregate recipe. Opaque suppliers cannot disappear beside known values.
module Clef.Compiler.Baker.Ingredients.CallableAggregateProjections

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins

type Reading = {
    Aggregate: NodeId
    Path: CallableAggregatePathStep list
    Inputs: NodeId list
    Participants: Set<NodeId>
    Dependencies: Map<NodeId, NodeId list>
}

let private candidates (resolution: Origins.Resolution) occurrence =
    resolution.Aggregates |> Map.toList |> List.collect (fun (aggregate, row) ->
        row.Projections |> List.choose (fun (projection, path) ->
            if projection = occurrence then Some(aggregate, path, row) else None))

let private participants aggregate occurrence inputs (row: Origins.AggregateResolution) =
    [ yield aggregate; yield occurrence
      yield! inputs
      yield! row.Alternatives |> List.map _.Construction
      for KeyValue(node, sources) in row.Dependencies do
          yield node; yield! sources ] |> Set.ofList

let read (resolution: Origins.Resolution) occurrence =
    match candidates resolution occurrence with
    | [aggregate, path, row] when row.UnknownOrigins.IsEmpty && not row.Alternatives.IsEmpty ->
        let slots = row.Alternatives |> List.map (fun alternative ->
            match alternative.Slots |> List.filter (fun slot -> slot.Path = path) with
            | [slot] when slot.UnknownOrigins.IsEmpty && (not slot.Values.IsEmpty || slot.Absent) -> Some slot
            | _ -> None)
        if slots |> List.exists Option.isNone then None else
        let inputs = slots |> List.choose id |> List.collect _.Values |> List.distinct
        if inputs.IsEmpty then None else
        let participants = participants aggregate occurrence inputs row
        Some { Aggregate = aggregate; Path = path; Inputs = inputs
               Participants = participants; Dependencies = row.Dependencies }
    | _ -> None

/// A typed projection of another component does not transport the callable.
/// Both the projection path and the complete callable slot inventory come
/// from the existing source census. Operand evaluation remains demanded.
let tryTerminal (resolution: Origins.Resolution) occurrence =
    let prefix left right =
        List.length left <= List.length right && List.take (List.length left) right = left
    match candidates resolution occurrence with
    | [aggregate, path, row] when row.UnknownOrigins.IsEmpty && not row.Alternatives.IsEmpty &&
                                  (row.Alternatives |> List.forall (fun alternative ->
                                      alternative.Slots |> List.forall (fun slot ->
                                          slot.UnknownOrigins.IsEmpty &&
                                          not (prefix path slot.Path || prefix slot.Path path)))) ->
        Some(aggregate, participants aggregate occurrence [] row)
    | _ -> None

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

let read (resolution: Origins.Resolution) occurrence =
    let candidates =
        resolution.Aggregates |> Map.toList |> List.collect (fun (aggregate, row) ->
            row.Projections |> List.choose (fun (projection, path) ->
                if projection = occurrence then Some(aggregate, path, row) else None))
    match candidates with
    | [aggregate, path, row] when row.UnknownOrigins.IsEmpty && not row.Alternatives.IsEmpty ->
        let slots = row.Alternatives |> List.map (fun alternative ->
            match alternative.Slots |> List.filter (fun slot -> slot.Path = path) with
            | [slot] when slot.UnknownOrigins.IsEmpty && (not slot.Values.IsEmpty || slot.Absent) -> Some slot
            | _ -> None)
        if slots |> List.exists Option.isNone then None else
        let inputs = slots |> List.choose id |> List.collect _.Values |> List.distinct
        if inputs.IsEmpty then None else
        let participants =
            [ yield aggregate; yield occurrence
              yield! inputs
              yield! row.Alternatives |> List.map _.Construction
              for KeyValue(node, sources) in row.Dependencies do
                  yield node; yield! sources ] |> Set.ofList
        Some { Aggregate = aggregate; Path = path; Inputs = inputs
               Participants = participants; Dependencies = row.Dependencies }
    | _ -> None

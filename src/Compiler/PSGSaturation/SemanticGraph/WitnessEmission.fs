// SPDX-License-Identifier: MIT
/// The source publication seam. Builders run while CCS owns the graph; consumers
/// receive already materialized domain projections through exact-object lookup.
/// This snapshot seal is not a cross-edit revision or an incremental worklist.
module Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

open System.Runtime.CompilerServices
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Projection = {
    Ordinary: OrdinaryDemandProjection
    Callable: CallableEmissionProjection
    Storage: StorageWitnessProjection
}

let private published = ConditionalWeakTable<SemanticGraph, Projection>()

let private project graph =
    let ordinary = OrdinaryDemand.projectValidated graph
    let callable = CallableEmission.project graph
    let storage = StorageWitness.project graph
    match ordinary, callable, storage with
    | Ok ordinary, Ok callable, Ok storage ->
        Ok { Ordinary = ordinary; Callable = callable; Storage = storage }
    | _ ->
        let failures = function Ok _ -> [] | Error failures -> failures
        Error (failures ordinary @ failures callable @ failures storage)

let private revoke graph failures =
    published.Remove graph |> ignore
    Error failures

let private register graph projection =
    lock published (fun () ->
        published.Remove graph |> ignore
        published.Add(graph, projection))

let private materialized value =
    let held = lazy value
    held.Force() |> ignore
    held

/// Complete source publication once. The graph returned here owns all current
/// projected facts and eager indices; it is the graph handed to witnessing.
let prepare (graph: SemanticGraph) : Result<SemanticGraph, WitnessProjectionFailure list> =
    match project graph with
    | Error failures -> revoke graph failures
    | Ok projection ->
        let facts = {
            graph.Codata.Value with OrdinaryDemand = projection.Ordinary
                                    CallableEmission = projection.Callable
                                    StorageWitness = projection.Storage }
        // Force semantic lazy computations under their source owner. A consumer
        // must not execute a deferred layout/index/classification computation.
        let settled = {
            graph with
                Types = materialized graph.Types.Value
                ModuleClassifications = materialized graph.ModuleClassifications.Value
                FieldRanges = materialized graph.FieldRanges.Value
                ElementRanges = materialized graph.ElementRanges.Value
                Layouts = materialized graph.Layouts.Value
                Escaping = materialized graph.Escaping.Value
                Codata = materialized facts }
        register settled projection
        Ok settled

/// Validate an already prepared graph without altering its facts. Component
/// source fixtures and retained-input owners may use this source operation;
/// witness consumers never call it to repair a missing admission.
let admit (graph: SemanticGraph) : Result<unit, WitnessProjectionFailure list> =
    match project graph with
    | Error failures -> revoke graph failures
    | Ok projection ->
        let facts = graph.Codata.Value
        if facts.OrdinaryDemand <> projection.Ordinary ||
           facts.CallableEmission <> projection.Callable ||
           facts.StorageWitness <> projection.Storage then
            revoke graph [{ Occurrence = None; Participants = Set.empty
                            Reason = "Witness projection differs from the current source snapshot." }]
        elif not (graph.Types.IsValueCreated && graph.ModuleClassifications.IsValueCreated &&
                  graph.FieldRanges.IsValueCreated && graph.ElementRanges.IsValueCreated &&
                  graph.Layouts.IsValueCreated && graph.Escaping.IsValueCreated) then
            revoke graph [{ Occurrence = None; Participants = Set.empty
                            Reason = "Witness input contains deferred source computations." }]
        else
            register graph projection
            Ok ()

/// Passive reads only: no graph scans, solver calls, semantic lazy forcing or
/// fallback. A copy requires source admission even when its IDs look identical.
let tryRead graph =
    match published.TryGetValue graph with
    | true, projection -> Ok projection
    | _ -> Error "The current graph has no complete source witness projection."

let tryOrdinary graph = tryRead graph |> Result.map _.Ordinary
let tryCallable graph = tryRead graph |> Result.map _.Callable
let tryStorage graph = tryRead graph |> Result.map _.Storage

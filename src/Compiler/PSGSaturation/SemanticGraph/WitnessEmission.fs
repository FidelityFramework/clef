// SPDX-License-Identifier: MIT
/// The source publication seam. Builders run while CCS owns the graph; Alex
/// witnesses the materialized domain projections carried by graph codata.
module Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Projection = WitnessEmissionProjection

let private project graph =
    let ordinary = OrdinaryDemand.projectValidated graph
    // Callable component positions depend on this exact validated omission
    // proof. Reading an older held mask would publish inconsistent domains.
    let callable =
        match ordinary with
        | Ok demand -> CallableEmission.projectWithDemand graph demand
        | Error failures -> Error failures
    let storage = StorageWitness.project graph
    let boundary = BoundaryEmission.project graph
    match ordinary, callable, storage, boundary with
    | Ok ordinary, Ok callable, Ok storage, Ok boundary ->
        Ok { Ordinary = ordinary; Callable = callable; Storage = storage; Boundary = boundary }
    | _ ->
        let failures = function Ok _ -> [] | Error failures -> failures
        // Failed demand validation already owns its diagnostic; the dependent
        // callable domain cannot contribute an independent result in that case.
        let callableFailures = match ordinary with Ok _ -> failures callable | Error _ -> []
        Error (failures ordinary @ callableFailures @ failures storage @ failures boundary)

/// A source edit retains premises for validation but cannot carry publication
/// into witnessing. The original graph retains its own published facts.
let invalidate (graph: SemanticGraph) =
    Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.invalidateWitness graph

let private materialized value =
    let held = lazy value
    held.Force() |> ignore
    held

/// Complete source publication once. The graph returned here owns all current
/// projected facts and eager indices; it is the graph handed to witnessing.
let prepare (graph: SemanticGraph) : Result<SemanticGraph, WitnessProjectionFailure list> =
    match project graph with
    | Error failures -> Error failures
    | Ok projection ->
        let facts = {
            graph.Codata.Value with OrdinaryDemand = projection.Ordinary
                                    WitnessEmission = Some projection }
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
                Codata = materialized facts
                WitnessProvenance = None }
        Ok { settled with WitnessProvenance = Some { PreparedRoots = settled } }

/// Compare only the retained input roots. This neither forces lazy source
/// computations nor reconstructs their premises. Every root participates,
/// including relation and declaration membership. Shared checker cells remain
/// a separate immutable-input requirement; this evidence does not freeze them
/// or identify the accepted source revision.
let private samePreparedRoots (prepared: SemanticGraph) (graph: SemanticGraph) =
    obj.ReferenceEquals(prepared.Nodes, graph.Nodes) &&
    obj.ReferenceEquals(prepared.DeclarationRoots, graph.DeclarationRoots) &&
    obj.ReferenceEquals(prepared.Modules, graph.Modules) &&
    obj.ReferenceEquals(prepared.Types, graph.Types) &&
    obj.ReferenceEquals(prepared.Platform, graph.Platform) &&
    obj.ReferenceEquals(prepared.ModuleClassifications, graph.ModuleClassifications) &&
    obj.ReferenceEquals(prepared.FieldRanges, graph.FieldRanges) &&
    obj.ReferenceEquals(prepared.ElementRanges, graph.ElementRanges) &&
    obj.ReferenceEquals(prepared.Layouts, graph.Layouts) &&
    obj.ReferenceEquals(prepared.StaticStringPool, graph.StaticStringPool) &&
    obj.ReferenceEquals(prepared.Escaping, graph.Escaping) &&
    obj.ReferenceEquals(prepared.Codata, graph.Codata) &&
    obj.ReferenceEquals(prepared.Edges, graph.Edges)

let private isMaterialized (graph: SemanticGraph) =
    graph.Codata.IsValueCreated && graph.Types.IsValueCreated &&
    graph.ModuleClassifications.IsValueCreated && graph.FieldRanges.IsValueCreated &&
    graph.ElementRanges.IsValueCreated && graph.Layouts.IsValueCreated && graph.Escaping.IsValueCreated

/// Passive projection only. Do not force a deferred source computation, scan
/// source relations, infer a missing fact or consult process-global identity.
let tryRead (graph: SemanticGraph) =
    match graph.WitnessProvenance with
    | None -> Error "The current graph has no complete source witness projection."
    | Some provenance when not (samePreparedRoots provenance.PreparedRoots graph) ->
        Error "The current graph differs from its source witness projection input; source republication is required."
    | Some _ when not (isMaterialized graph) ->
        Error "The current graph has no materialized source witness projection."
    | Some _ ->
        match graph.Codata.Value.WitnessEmission with
        | Some projection -> Ok projection
        | None -> Error "The current graph has no complete source witness projection."

/// Validate an already prepared graph without altering its facts. Component
/// source fixtures and retained-input owners may use this source operation;
/// witness consumers never call it to repair a missing admission.
let admit (graph: SemanticGraph) : Result<unit, WitnessProjectionFailure list> =
    match project graph with
    | Error failures -> Error failures
    | Ok projection ->
        let facts = graph.Codata.Value
        if facts.OrdinaryDemand <> projection.Ordinary || facts.WitnessEmission <> Some projection then
            Error [{ Occurrence = None; Participants = Set.empty
                     Reason = "Witness projection differs from the current source snapshot." }]
        elif not (isMaterialized graph) then
            Error [{ Occurrence = None; Participants = Set.empty
                     Reason = "Witness input contains deferred source computations." }]
        else
            Ok ()

let tryOrdinary graph = tryRead graph |> Result.map _.Ordinary
let tryCallable graph = tryRead graph |> Result.map _.Callable
let tryStorage graph = tryRead graph |> Result.map _.Storage
let tryBoundary graph = tryRead graph |> Result.map _.Boundary

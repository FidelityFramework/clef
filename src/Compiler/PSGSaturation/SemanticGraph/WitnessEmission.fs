// SPDX-License-Identifier: MIT
/// The source publication seam. Builders run while CCS owns the graph; Alex
/// witnesses the materialized domain projections carried by graph codata.
module Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module ProofDispatch = Clef.Compiler.Baker.Recipes.ProofDispatchRecipes
module LiveScopes = Clef.Compiler.Baker.Recipes.WitnessScopeRecipes
module PreparedRows = Clef.Compiler.Baker.Recipes.WitnessForeignDemandRecipes
module LiveRows = Clef.Compiler.Baker.Recipes.WitnessLiveRowsRecipes
module PublishedRows = Clef.Compiler.Baker.Recipes.WitnessPublishedRowsRecipes

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
    let numeric = NumericPublication.project graph
    let memory = MemoryPublication.project graph
    let spatial = SpatialPublication.project graph
    match ordinary, callable, storage, boundary, numeric, memory, spatial with
    | Ok ordinary, Ok callable, Ok storage, Ok boundary, Ok numeric, Ok memory, Ok spatial ->
        Ok { Ordinary = ordinary; Callable = callable; Storage = storage; Boundary = boundary; Numeric = numeric; Memory = memory; Spatial = spatial }
    | _ ->
        let failures = function Ok _ -> [] | Error failures -> failures
        // Failed demand validation already owns its diagnostic; the dependent
        // callable domain cannot contribute an independent result in that case.
        let callableFailures = match ordinary with Ok _ -> failures callable | Error _ -> []
        Error (failures ordinary @ callableFailures @ failures storage @ failures boundary @ failures numeric @ failures memory @ failures spatial)

/// The failures of `prepare` as CCS8403 diagnostics, each at the range of its occurrence.
let diagnostics (graph: SemanticGraph) (failures: WitnessProjectionFailure list) : Diagnostics.Diagnostic list =
    failures |> List.map (fun failure ->
        ({ Severity = Diagnostics.NativeDiagnosticSeverity.Error; Code = "CCS8403"
           Message = "Source settlement is required before witnessing: " + failure.Reason
           Range = failure.Occurrence |> Option.bind graph.Nodes.TryFind |> Option.map _.Range |> Option.defaultValue Clef.Compiler.NativeTypedTree.NativeTypes.dummyRange
           RelatedNodes = Set.toList failure.Participants; Reachability = Diagnostics.ReachabilityContext.Reachable } : Diagnostics.Diagnostic))

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
        match ProofDispatch.materialize graph with
        | Error failures -> Error failures
        | Ok dispatch ->
          match LiveScopes.projectWithEmission projection graph with
          | Error failures -> Error failures
          | Ok liveScope ->
            let preparedRows = PreparedRows.project graph
            let segmentation = WitnessSegmentation.project graph projection liveScope
            let liveRows = LiveRows.project graph projection liveScope preparedRows segmentation
            match PublishedRows.project graph liveScope liveRows dispatch with
            | Error failures -> Error failures
            | Ok publishedRows ->
              let facts = {
                  graph.Codata.Value with OrdinaryDemand = projection.Ordinary
                                          WitnessEmission = Some projection
                                          WitnessSegmentation = Some segmentation
                                          WitnessLiveScope = Some liveScope
                                          WitnessPreparedRows = Some preparedRows
                                          WitnessLiveRows = Some liveRows
                                          WitnessPublishedRows = Some publishedRows
                                          ProofDispatch = Some dispatch }
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

/// The complete identity policy for prepared input roots. Keeping names next
/// to typed accessors lets the maintenance test check this policy against the
/// SemanticGraph record without adding reflection to passive publication.
let internal preparedRootIdentities : (string * (SemanticGraph -> obj | null)) list =
    [ "Nodes", (fun graph -> box graph.Nodes)
      "DeclarationRoots", (fun graph -> box graph.DeclarationRoots)
      "Modules", (fun graph -> box graph.Modules)
      "Types", (fun graph -> box graph.Types)
      "Platform", (fun graph -> box graph.Platform)
      "ModuleClassifications", (fun graph -> box graph.ModuleClassifications)
      "FieldRanges", (fun graph -> box graph.FieldRanges)
      "ElementRanges", (fun graph -> box graph.ElementRanges)
      "Layouts", (fun graph -> box graph.Layouts)
      "StaticStringPool", (fun graph -> box graph.StaticStringPool)
      "LiteralStorage", (fun graph -> box graph.LiteralStorage)
      "Escaping", (fun graph -> box graph.Escaping)
      "Codata", (fun graph -> box graph.Codata)
      "Edges", (fun graph -> box graph.Edges)
      "SequenceRangeProvenance", (fun graph -> box graph.SequenceRangeProvenance)
      // The prepared projection consumed this exact producer receipt. Equal
      // reissued facts still require source preparation, not passive rebasing.
      "RangeContextFacts", (fun graph -> box graph.RangeContextFacts) ]

/// This root supplies the retained inputs being compared. tryRead explicitly
/// requires it; prepare's retained graph intentionally has no self-reference.
let internal preparedRootExceptions =
    [ ("WitnessProvenance", "Required and opened by tryRead; its PreparedRoots are the identity comparison baseline.") ]

/// Compare only the retained input roots. This neither forces lazy source
/// computations nor reconstructs their premises. Every root participates,
/// including relation and declaration membership. Shared checker cells remain
/// a separate immutable-input requirement; this evidence does not freeze them
/// or identify the accepted source revision.
let private samePreparedRoots (prepared: SemanticGraph) (graph: SemanticGraph) =
    preparedRootIdentities |> List.forall (fun (_, read) ->
        obj.ReferenceEquals(read prepared, read graph))

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
        | Some _ when graph.Codata.Value.WitnessPreparedRows.IsNone ->
            Error "The current graph has no Baker-prepared foreign, demand and incidence rows."
        | Some _ when graph.Codata.Value.WitnessLiveRows.IsNone ->
            Error "The current graph has no Baker-selected live fact rows."
        | Some _ when graph.Codata.Value.WitnessPublishedRows.IsNone ->
            Error "The current graph has no Baker-frozen publication rows."
        | Some projection when graph.Codata.Value.WitnessLiveScope.IsSome -> Ok projection
        | Some _ -> Error "The current graph has no source-owned live occurrence scope."
        | None -> Error "The current graph has no complete source witness projection."

/// Validate an already prepared graph without altering its facts. Component
/// source fixtures and retained-input owners may use this source operation;
/// witness consumers never call it to repair a missing admission.
let admit (graph: SemanticGraph) : Result<unit, WitnessProjectionFailure list> =
    let facts = graph.Codata.Value
    // Dispatch retains incidence independently of the domain projections. Its
    // precise refusal must survive a broader domain freshness failure.
    match ProofDispatch.materialize graph with
    | Error failures -> Error failures
    | Ok current when facts.ProofDispatch |> Option.exists (fun held -> ProofDispatch.matches held current) |> not ->
        Error [{ Occurrence = None; Participants = Set.empty
                 Reason = "Proof dispatch differs from the current source snapshot." }]
    | Ok dispatch ->
      match project graph with
      | Error failures -> Error failures
      | Ok projection ->
        if facts.OrdinaryDemand <> projection.Ordinary || facts.WitnessEmission <> Some projection then
            Error [{ Occurrence = None; Participants = Set.empty
                     Reason = "Witness projection differs from the current source snapshot." }]
        elif
            (match LiveScopes.projectWithEmission projection graph with
             | Ok liveScope -> facts.WitnessSegmentation = Some (WitnessSegmentation.project graph projection liveScope)
             | Error _ -> false) |> not then
            Error [{ Occurrence = None; Participants = Set.empty
                     Reason = "Witness segmentation differs from the current source snapshot." }]
        elif
            (match LiveScopes.projectWithEmission projection graph, facts.WitnessLiveScope with
             | Ok current, Some held -> LiveScopes.matches held current
             | _ -> false) |> not then
            Error [{ Occurrence = None; Participants = Set.empty
                     Reason = "Live occurrence scope differs from the current source snapshot." }]
        elif
            (facts.WitnessPreparedRows |> Option.exists (fun held -> PreparedRows.matches held (PreparedRows.project graph))) |> not then
            Error [{ Occurrence = None; Participants = Set.empty
                     Reason = "Baker-prepared foreign, demand and incidence rows differ from the current source snapshot." }]
        elif
            (match facts.WitnessLiveScope, facts.WitnessPreparedRows, facts.WitnessSegmentation, facts.WitnessLiveRows with
             | Some scope, Some prepared, Some segmentation, Some held ->
                 LiveRows.matches held (LiveRows.project graph projection scope prepared segmentation)
             | _ -> false) |> not then
            Error [{ Occurrence = None; Participants = Set.empty
                     Reason = "Baker-selected live fact rows differ from the current source snapshot." }]
        elif not (isMaterialized graph) then
            Error [{ Occurrence = None; Participants = Set.empty
                     Reason = "Witness input contains deferred source computations." }]
        elif
            (match facts.WitnessLiveScope, facts.WitnessLiveRows, facts.WitnessPublishedRows with
             | Some scope, Some rows, Some held ->
                 match PublishedRows.project graph scope rows dispatch with
                 | Ok current -> PublishedRows.matches held current
                 | Error _ -> false
             | _ -> false) |> not then
            Error [{ Occurrence = None; Participants = Set.empty
                     Reason = "Baker-frozen publication rows differ from the current source snapshot." }]
        else Ok ()

let tryOrdinary graph = tryRead graph |> Result.map _.Ordinary
let tryCallable graph = tryRead graph |> Result.map _.Callable
let tryStorage graph = tryRead graph |> Result.map _.Storage
let tryBoundary graph = tryRead graph |> Result.map _.Boundary
let tryNumeric graph = tryRead graph |> Result.map _.Numeric
let tryMemory graph = tryRead graph |> Result.map _.Memory
let trySpatial graph = tryRead graph |> Result.map _.Spatial

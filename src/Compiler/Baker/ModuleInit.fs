// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Module Initialization - Intermediate output for debugging.
///
/// Classification logic is now in PSG/SemanticGraph.fs (computed lazily).
/// This module provides intermediate output formatting for the -k flag.
module FSharp.Native.Compiler.Baker.ModuleInit

open System
open System.Diagnostics
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.Infrastructure.PhaseTypes

/// Create the Baker ModuleInit phase output for intermediate emission.
let createOutput (graph: SemanticGraph) (elapsedMs: int64) : BakerModuleInitOutput =
    let classifications = graph.ModuleClassifications.Value
    let modules =
        classifications
        |> Map.toList
        |> List.map (fun (nodeId, classification) ->
            {
                ModuleId = NodeId.value nodeId
                Name = classification.Name
                ModuleInit = classification.ModuleInit |> List.map NodeId.value
                Definitions = classification.Definitions |> List.map NodeId.value
                EntryPoint = classification.EntryPoint |> Option.map NodeId.value
            })

    let totalModuleInit = modules |> List.sumBy (fun m -> List.length m.ModuleInit)
    let totalDefinitions = modules |> List.sumBy (fun m -> List.length m.Definitions)
    let entryPointModules =
        modules
        |> List.filter (fun m -> m.EntryPoint.IsSome)
        |> List.map (fun m -> m.Name)

    let summary = {
        Phase = PhaseId.BakerModuleInit
        Timestamp = DateTime.UtcNow
        NodeCount = Map.count graph.Nodes
        ReachableCount = Some (graph.Nodes |> Map.filter (fun _ n -> n.IsReachable) |> Map.count)
        EntryPointCount = List.length graph.EntryPoints
        DiagnosticCount = 0
        ErrorCount = 0
        ElapsedMs = elapsedMs
        Metrics = Map.empty
    }

    {
        Summary = summary
        Modules = modules
        TotalModuleInitCount = totalModuleInit
        TotalDefinitionsCount = totalDefinitions
        EntryPointModules = entryPointModules
    }

/// Run classification (forces lazy) and produce output
let runWithOutput (graph: SemanticGraph) : BakerModuleInitOutput =
    let sw = Stopwatch.StartNew()
    let _ = graph.ModuleClassifications.Value  // Force lazy computation
    sw.Stop()
    createOutput graph sw.ElapsedMilliseconds

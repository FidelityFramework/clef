// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Combinational Depth Analysis — Layer 1 Structural Heuristic
///
/// Walks the PSG via foldWithLambdaPreBind (the same semantic-edge-following
/// traversal used for code generation), counting weighted combinational
/// operation depth between register boundaries. Emits diagnostics when depth
/// exceeds an empirical threshold.
///
/// Layer 2 (Vivado post-route WNS trap) provides ground truth.
///
/// FPGA-only. Gated on PlatformContext.SubstrateKind = FPGA.
///
/// See: docs/AutomaticPipelineInference.md in HelloArty
module Clef.Compiler.PSGSaturation.SemanticGraph.DepthAnalysis

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.Traversal

type PeakInfo = {
    Depth: int
    Chain: string list
    Range: SourceRange
}

type DepthAnalysisState = {
    Depths: Map<NodeId, int>
    Chains: Map<NodeId, string list>
    Peaks: Map<int, PeakInfo>
    Graph: SemanticGraph
    Threshold: int
}

module DepthAnalysisState =
    let create (graph: SemanticGraph) (threshold: int) =
        { Depths = Map.empty; Chains = Map.empty; Peaks = Map.empty
          Graph = graph; Threshold = threshold }

    let setDepth (nodeId: NodeId) (depth: int) (chain: string list) (state: DepthAnalysisState) =
        { state with
            Depths = Map.add nodeId depth state.Depths
            Chains = Map.add nodeId chain state.Chains }

    let getDepth (nodeId: NodeId) (state: DepthAnalysisState) =
        Map.tryFind nodeId state.Depths |> Option.defaultValue 0

    let getChain (nodeId: NodeId) (state: DepthAnalysisState) =
        Map.tryFind nodeId state.Chains |> Option.defaultValue []

    let recordPeak (line: int) (peak: PeakInfo) (state: DepthAnalysisState) =
        match Map.tryFind line state.Peaks with
        | Some existing when existing.Depth >= peak.Depth -> state
        | _ -> { state with Peaks = Map.add line peak state.Peaks }

//=============================================================================
// WEIGHT TABLE — Structural complexity weights (unitless, NOT nanoseconds)
//=============================================================================

/// Calibrated against Layer 2 ground truth over time.
/// HelloArty: weighted depth 12, WNS = -2.635 ns at 100 MHz on Artix-7.
let private arithmeticWeight (operation: string) =
    match operation with
    | "op_Multiply" | "op_Division" | "op_Modulus" -> 2
    | _ -> 1

let private intrinsicWeight (info: IntrinsicInfo) =
    match info.Category with
    | IntrinsicCategory.Arithmetic -> arithmeticWeight info.Operation
    | IntrinsicCategory.Comparison -> 1
    | IntrinsicCategory.Bitwise -> 1
    | _ -> 0

/// PSG structure: Application(Intrinsic, operand1, operand2).
/// The Intrinsic is a leaf naming the operation; the Application is where
/// computation happens. Weight lives on Application, resolved via its func child.
let private operationWeight (graph: SemanticGraph) (kind: SemanticKind) =
    match kind with
    | SemanticKind.Application(funcId, _) ->
        match Map.tryFind funcId graph.Nodes with
        | Some funcNode ->
            match funcNode.Kind with
            | SemanticKind.Intrinsic info -> intrinsicWeight info
            | _ -> 0
        | None -> 0
    | SemanticKind.IfThenElse _ -> 1
    | SemanticKind.Match _ -> 1
    | SemanticKind.CaseElimination _ -> 1
    | _ -> 0

let private nodeLabel (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Application(funcId, _) ->
        match Map.tryFind funcId graph.Nodes with
        | Some funcNode ->
            match funcNode.Kind with
            | SemanticKind.Intrinsic info -> info.Operation
            | _ -> "apply"
        | None -> "apply"
    | SemanticKind.IfThenElse _ -> "mux"
    | SemanticKind.Match _ -> "match"
    | SemanticKind.CaseElimination _ -> "case"
    | _ -> "node"

//=============================================================================
// CATAMORPHISM
//=============================================================================

let [<Literal>] DefaultThreshold = 6

/// Compute combinational depth threshold from clock frequency and fabric delay.
/// threshold = floor(clock_period_ns / ns_per_weight_unit)
/// Falls back to DefaultThreshold when timing data is unavailable.
let computeThreshold (clockMhz: int option) (nsPerUnit: float option) : int =
    match clockMhz, nsPerUnit with
    | Some mhz, Some npu when mhz > 0 && npu > 0.0 ->
        let periodNs = 1000.0 / float mhz
        int (floor (periodNs / npu))
    | _ -> DefaultThreshold

let private analyzeNode (state: DepthAnalysisState) (node: SemanticNode) : DepthAnalysisState =
    let graph = state.Graph
    let weight = operationWeight graph node.Kind

    let maxChildDepth =
        node.Children
        |> List.map (fun childId -> DepthAnalysisState.getDepth childId state)
        |> function
           | [] -> 0
           | depths -> List.max depths

    let nodeDepth = maxChildDepth + weight

    let chain =
        if node.Children.IsEmpty then
            if weight > 0 then [nodeLabel graph node] else []
        else
            let deepestChildChain =
                node.Children
                |> List.maxBy (fun childId -> DepthAnalysisState.getDepth childId state)
                |> fun childId -> DepthAnalysisState.getChain childId state
            if weight > 0 then deepestChildChain @ [nodeLabel graph node] else deepestChildChain

    let state = DepthAnalysisState.setDepth node.Id nodeDepth chain state

    if nodeDepth > state.Threshold && weight > 0 then
        let peak = { Depth = nodeDepth; Chain = chain; Range = node.Range }
        DepthAnalysisState.recordPeak node.Range.Start.Line peak state
    else
        state

//=============================================================================
// REMEDIATION — Derived from chain content, not a lookup dictionary
//=============================================================================

let private isDspOp = function
    | "op_Multiply" | "op_Division" | "op_Modulus" -> true
    | _ -> false

let private isMuxOp = function
    | "mux" | "match" | "case" -> true
    | _ -> false

/// Two-sided remediation: tells the developer both knobs they can turn.
/// When timing data is available, computes the max clock for the current depth
/// and the required depth for the current clock.
let private remediationHint (chain: string list) (depth: int) (threshold: int)
                            (clockMhz: int option) (nsPerUnit: float option) =
    let structuralAdvice =
        let dspCount = chain |> List.filter isDspOp |> List.length
        let muxCount = chain |> List.filter isMuxOp |> List.length
        if dspCount > muxCount then
            "break the arithmetic/DSP chain with register stages"
        elif muxCount > dspCount then
            "restructure branches to reduce mux cascade depth"
        else
            "pipeline this combinational path with register stages"
    match clockMhz, nsPerUnit with
    | Some mhz, Some npu when npu > 0.0 ->
        // What clock would accommodate this depth?
        let maxFreqMhz = int (floor (1000.0 / (float depth * npu)))
        sprintf "either reduce depth to ≤ %d, or relax clock to ≤ %d MHz (currently %d MHz). To reduce: %s"
            threshold maxFreqMhz mhz structuralAdvice
    | _ ->
        sprintf "%s (reduce depth to ≤ %d)" structuralAdvice threshold

//=============================================================================
// RESIDUAL — Group identical chains, format diagnostics with hints
//=============================================================================

let private formatDiagnostics (threshold: int) (clockMhz: int option) (nsPerUnit: float option)
                              (peaks: PeakInfo list) : Diagnostic list =
    let clockNote =
        match clockMhz with
        | Some mhz -> sprintf " (%d MHz)" mhz
        | None -> ""
    peaks
    |> List.groupBy (fun p -> p.Chain)
    |> List.map (fun (chain, instances) ->
        let maxDepth = instances |> List.map (fun p -> p.Depth) |> List.max
        let lines = instances |> List.map (fun p -> p.Range.Start.Line) |> List.sort
        let firstRange = instances |> List.minBy (fun p -> p.Range.Start.Line) |> fun p -> p.Range
        let chainStr = chain |> String.concat " → "
        let hint = remediationHint chain maxDepth threshold clockMhz nsPerUnit
        let instanceNote =
            if instances.Length > 1 then
                sprintf " (%d instances: lines %s)" instances.Length (lines |> List.map string |> String.concat ", ")
            else ""
        { Severity = NativeDiagnosticSeverity.Warning
          Code = "CCS0100"
          Message = sprintf "Combinational depth %d exceeds threshold %d%s%s\n  Chain: %s\n  Hint: %s"
                      maxDepth threshold clockNote instanceNote chainStr hint
          Range = firstRange
          RelatedNodes = []
          Reachability = ReachabilityContext.Reachable })

/// Run combinational depth analysis on the semantic graph.
/// FPGA-only — returns empty list for non-FPGA substrates.
/// Threshold is calibrated from platform binding timing data when available:
///   threshold = floor(clock_period_ns / ns_per_weight_unit)
let analyze (platformContext: PlatformContext option) (graph: SemanticGraph) : Diagnostic list =
    match platformContext with
    | Some ctx when PlatformContext.substrateKind ctx = SubstrateKind.FPGA ->
        let clockMhz = ctx.ClockFrequencyMhz
        let nsPerUnit = ctx.NsPerWeightUnit
        let threshold = computeThreshold clockMhz nsPerUnit
        let initialState = DepthAnalysisState.create graph threshold
        let finalState = Traversal.foldWithLambdaPreBind (fun s _ -> s) analyzeNode initialState graph
        let peaks = finalState.Peaks |> Map.toList |> List.map snd
        formatDiagnostics threshold clockMhz nsPerUnit peaks
    | _ ->
        []

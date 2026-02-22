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

type DepthAnalysisState = {
    Depths: Map<NodeId, int>
    Chains: Map<NodeId, string list>
    Diagnostics: Diagnostic list
    Graph: SemanticGraph
    Threshold: int
}

module DepthAnalysisState =
    let create (graph: SemanticGraph) (threshold: int) =
        { Depths = Map.empty; Chains = Map.empty; Diagnostics = []
          Graph = graph; Threshold = threshold }

    let setDepth (nodeId: NodeId) (depth: int) (chain: string list) (state: DepthAnalysisState) =
        { state with
            Depths = Map.add nodeId depth state.Depths
            Chains = Map.add nodeId chain state.Chains }

    let getDepth (nodeId: NodeId) (state: DepthAnalysisState) =
        Map.tryFind nodeId state.Depths |> Option.defaultValue 0

    let getChain (nodeId: NodeId) (state: DepthAnalysisState) =
        Map.tryFind nodeId state.Chains |> Option.defaultValue []

    let addDiagnostic (diag: Diagnostic) (state: DepthAnalysisState) =
        { state with Diagnostics = diag :: state.Diagnostics }

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
        let chainStr = chain |> String.concat " → "
        DepthAnalysisState.addDiagnostic {
            Severity = NativeDiagnosticSeverity.Warning
            Code = "CCS0100"
            Message = sprintf "Combinational depth %d exceeds threshold %d. Chain: %s"
                        nodeDepth state.Threshold chainStr
            Range = node.Range
            RelatedNodes = []
            Reachability = ReachabilityContext.Reachable
        } state
    else
        state

/// Run combinational depth analysis on the semantic graph.
/// FPGA-only — returns empty list for non-FPGA substrates.
let analyze (platformContext: PlatformContext option) (graph: SemanticGraph) : Diagnostic list =
    match platformContext with
    | Some ctx when PlatformContext.substrateKind ctx = SubstrateKind.FPGA ->
        let initialState = DepthAnalysisState.create graph DefaultThreshold
        let finalState = Traversal.foldWithLambdaPreBind (fun s _ -> s) analyzeNode initialState graph
        List.rev finalState.Diagnostics
    | _ ->
        []

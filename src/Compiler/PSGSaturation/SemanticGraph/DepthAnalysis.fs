// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Combinational Depth Analysis — Layer 1 Structural Heuristic
///
/// Walks the PSG bottom-up via foldPostOrder, counting weighted combinational
/// operation depth between register boundaries. Emits diagnostics when depth
/// exceeds an empirical threshold.
///
/// This is an opening heuristic — it reports structural complexity, not
/// nanosecond delay. Layer 2 (Vivado post-route WNS trap) provides ground truth.
///
/// FPGA-only. Gated on PlatformContext.SubstrateKind = FPGA.
///
/// Architecture: Four pillars pattern — XParsec combinators drive per-node
/// analysis within a foldPostOrder catamorphism.
///
/// See: Serena memory "depth_analysis_architecture"
/// See: docs/AutomaticPipelineInference.md in HelloArty
module Clef.Compiler.PSGSaturation.SemanticGraph.DepthAnalysis

open XParsec
open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.Traversal

//=============================================================================
// STATE TYPE
//=============================================================================

/// State threaded through the depth analysis catamorphism
type DepthAnalysisState = {
    /// Weighted combinational depth per node
    Depths: Map<NodeId, int>
    /// Chain description per node (for diagnostic messages)
    Chains: Map<NodeId, string list>
    /// Accumulated diagnostics
    Diagnostics: Diagnostic list
    /// The semantic graph (for child lookups)
    Graph: SemanticGraph
    /// Depth threshold — paths exceeding this emit diagnostics
    Threshold: int
}

module DepthAnalysisState =
    /// Create initial state
    let create (graph: SemanticGraph) (threshold: int) =
        { Depths = Map.empty
          Chains = Map.empty
          Diagnostics = []
          Graph = graph
          Threshold = threshold }

    /// Record depth for a node
    let setDepth (nodeId: NodeId) (depth: int) (chain: string list) (state: DepthAnalysisState) =
        { state with
            Depths = Map.add nodeId depth state.Depths
            Chains = Map.add nodeId chain state.Chains }

    /// Look up depth for a node (0 if not yet computed)
    let getDepth (nodeId: NodeId) (state: DepthAnalysisState) =
        Map.tryFind nodeId state.Depths |> Option.defaultValue 0

    /// Look up chain for a node
    let getChain (nodeId: NodeId) (state: DepthAnalysisState) =
        Map.tryFind nodeId state.Chains |> Option.defaultValue []

    /// Add a diagnostic
    let addDiagnostic (diag: Diagnostic) (state: DepthAnalysisState) =
        { state with Diagnostics = diag :: state.Diagnostics }

//=============================================================================
// TYPE ALIAS — XParsec parser with DepthAnalysisState
//=============================================================================

/// Depth analysis parser — XParsec Parser with DepthAnalysisState
/// Uses ReadableString as dummy input (analysis doesn't consume input, just threads state)
type DepthParser<'T> =
    Parser<'T, char, DepthAnalysisState, ReadableString, ReadableStringSlice>

//=============================================================================
// DOMAIN-SPECIFIC COMBINATORS
//=============================================================================

/// Computation expression for depth analysis combinators
let depth = parser

/// Get the full analysis state
let getState : DepthParser<DepthAnalysisState> = getUserState

/// Update the analysis state
let setState (f: DepthAnalysisState -> DepthAnalysisState) : DepthParser<unit> =
    updateUserState f

/// Record depth and chain for a node
let recordDepth (nodeId: NodeId) (d: int) (chain: string list) : DepthParser<unit> =
    setState (DepthAnalysisState.setDepth nodeId d chain)

/// Look up depth for a child node
let childDepth (nodeId: NodeId) : DepthParser<int> =
    getUserState |>> fun s -> DepthAnalysisState.getDepth nodeId s

/// Look up chain for a child node
let childChain (nodeId: NodeId) : DepthParser<string list> =
    getUserState |>> fun s -> DepthAnalysisState.getChain nodeId s

/// Emit a diagnostic
let emitDiagnostic (diag: Diagnostic) : DepthParser<unit> =
    setState (DepthAnalysisState.addDiagnostic diag)

//=============================================================================
// WEIGHT TABLE — Structural complexity weights (unitless, NOT nanoseconds)
//=============================================================================

/// Opening heuristic weights. Calibrated against Layer 2 ground truth over time.
/// HelloArty provides the first calibration data point: weighted depth ~8
/// violates timing by 2.635 ns at 100 MHz on Artix-7.
let private arithmeticWeight (operation: string) =
    match operation with
    | "op_Multiply" | "op_Division" | "op_Modulus" -> 2  // DSP slice or multi-LUT chain
    | _ -> 1  // Add, subtract, negate, etc. — single LUT/carry level

let private operationWeight (kind: SemanticKind) =
    match kind with
    // Intrinsics — weight depends on category and operation
    | SemanticKind.Intrinsic info ->
        match info.Category with
        | IntrinsicCategory.Arithmetic -> arithmeticWeight info.Operation
        | IntrinsicCategory.Comparison -> 1
        | IntrinsicCategory.Bitwise -> 1
        | IntrinsicCategory.Conversion -> 0
        | _ -> 0
    // Mux — selection logic
    | SemanticKind.IfThenElse _ -> 1
    | SemanticKind.Match _ -> 1
    | SemanticKind.CaseElimination _ -> 1
    // Transparent wrappers — no combinational cost
    | SemanticKind.VarRef _
    | SemanticKind.Binding _
    | SemanticKind.FieldGet _
    | SemanticKind.TypeAnnotation _
    | SemanticKind.Upcast _
    | SemanticKind.Downcast _
    | SemanticKind.TupleGet _
    | SemanticKind.Literal _
    | SemanticKind.Lambda _
    | SemanticKind.RecordExpr _ -> 0
    // Application — weight comes from the intrinsic/function being applied
    | SemanticKind.Application _ -> 0
    // Everything else — conservative zero (no false positives)
    | _ -> 0

/// Human-readable label for a node in the chain description
let private nodeLabel (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Intrinsic info -> info.Operation
    | SemanticKind.IfThenElse _ -> "mux"
    | SemanticKind.Match _ -> "match"
    | SemanticKind.CaseElimination _ -> "case"
    | SemanticKind.VarRef(name, _) -> name
    | SemanticKind.Binding(name, _, _, _) -> name
    | SemanticKind.FieldGet(_, fieldName) -> fieldName
    | SemanticKind.Literal _ -> "literal"
    | SemanticKind.Application _ -> "apply"
    | _ -> "node"

//=============================================================================
// PER-NODE PARSER — Computes weighted depth for a single node
//=============================================================================

/// Default depth threshold. HelloArty data: weighted depth ~8 violates at
/// 100 MHz Artix-7. Threshold 6 is conservative (flags before violation).
let [<Literal>] DefaultThreshold = 6

/// Compute depth for a single node. Called within foldPostOrder, so all
/// children have already been processed and their depths are in state.
let computeNodeDepth (node: SemanticNode) : DepthParser<unit> =
    depth {
        let! state = getState
        let weight = operationWeight node.Kind

        // Get max depth across all children (already computed — postorder guarantee)
        let maxChildDepth =
            node.Children
            |> List.map (fun childId -> DepthAnalysisState.getDepth childId state)
            |> function
               | [] -> 0
               | depths -> List.max depths

        let nodeDepth = maxChildDepth + weight

        // Build chain: take the deepest child's chain and append this node
        let deepestChildChain =
            node.Children
            |> List.maxBy (fun childId -> DepthAnalysisState.getDepth childId state)
            |> fun childId -> DepthAnalysisState.getChain childId state
            |> fun chain -> if weight > 0 then chain @ [nodeLabel node] else chain

        let chain =
            if node.Children.IsEmpty && weight > 0 then
                [nodeLabel node]
            elif node.Children.IsEmpty then
                []
            else
                deepestChildChain

        do! recordDepth node.Id nodeDepth chain

        // Emit diagnostic if this node exceeds threshold and has weight
        // (only report at the point where the chain forms, not at every child)
        if nodeDepth > state.Threshold && weight > 0 then
            let chainStr = chain |> String.concat " → "
            let message =
                sprintf "Combinational depth %d exceeds threshold %d. Chain: %s"
                    nodeDepth state.Threshold chainStr
            do! emitDiagnostic {
                Severity = NativeDiagnosticSeverity.Warning
                Code = "CCS0100"
                Message = message
                Range = node.Range
                RelatedNodes = []
                Reachability = ReachabilityContext.Reachable
            }
    }

//=============================================================================
// BRIDGE — Connects XParsec parser to foldPostOrder's fold function
//=============================================================================

/// Bridge function: runs the XParsec parser for a single node, extracting
/// the updated state. Used as the folder in foldPostOrder.
let private analyzeNode (state: DepthAnalysisState) (node: SemanticNode) : DepthAnalysisState =
    // Create dummy reader (no input to consume — real work is in user state)
    let reader = Reader.ofString "" state
    // Run the per-node parser
    let _result = computeNodeDepth node reader
    // Extract and return the updated state
    reader.State

//=============================================================================
// ENTRY POINT
//=============================================================================

/// Run combinational depth analysis on the semantic graph.
/// Returns diagnostics for paths exceeding the depth threshold.
/// FPGA-only — returns empty list for non-FPGA substrates.
let analyze (platformContext: PlatformContext option) (graph: SemanticGraph) : Diagnostic list =
    // Guard: only run for FPGA substrates
    match platformContext with
    | Some ctx when PlatformContext.substrateKind ctx = SubstrateKind.FPGA ->
        let initialState = DepthAnalysisState.create graph DefaultThreshold
        let finalState = Traversal.foldPostOrder analyzeNode initialState graph
        List.rev finalState.Diagnostics
    | _ ->
        []

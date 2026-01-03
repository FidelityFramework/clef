/// PhaseTypes - Phase definitions for FNCS nanopass pipeline
///
/// Defines the formal phases of the FNCS type checking pipeline.
/// Each phase transforms the program representation and can emit intermediates.
///
/// Phase Pipeline:
///   Phase 0: PARSING      - Source text → ParsedInput (SynExpr tree)
///   Phase 1: STRUCTURAL   - SynExpr → SemanticGraph with nodes, edges, types attached
///   Phase 2: CONSTRAINTS  - SemanticGraph + constraints → resolved types
///   Phase 3: SRTP         - SemanticGraph with TraitCall → WitnessResolution attached
///   Phase 4: REACHABILITY - SemanticGraph + EntryPoints → IsReachable marks (soft-delete)
///   Phase 5: FINAL        - Complete CheckResult with diagnostics
module FSharp.Native.Compiler.Checking.Native.Infrastructure.PhaseTypes

open System

/// Identifies a phase in the nanopass pipeline
[<Struct>]
type PhaseId =
    | Parsing
    | Structural
    | Constraints
    | SRTP
    | Reachability
    | Final

    /// Get the numeric phase number
    member this.Number =
        match this with
        | Parsing -> 0
        | Structural -> 1
        | Constraints -> 2
        | SRTP -> 3
        | Reachability -> 4
        | Final -> 5

    /// Get the phase suffix for file naming
    member this.Suffix =
        match this with
        | Parsing -> "parsing"
        | Structural -> "structural"
        | Constraints -> "constraints"
        | SRTP -> "srtp"
        | Reachability -> "reachability"
        | Final -> "final"

    /// Get human-readable phase name
    member this.DisplayName =
        match this with
        | Parsing -> "Parsing"
        | Structural -> "Structural Construction"
        | Constraints -> "Constraint Solving"
        | SRTP -> "SRTP Resolution"
        | Reachability -> "Reachability Analysis"
        | Final -> "Final Result"

/// Summary statistics for a phase
type PhaseSummary = {
    /// Which phase this summary is for
    Phase: PhaseId
    /// When the phase completed
    Timestamp: DateTime
    /// Total node count in the graph
    NodeCount: int
    /// Number of reachable nodes (if applicable)
    ReachableCount: int option
    /// Number of entry points
    EntryPointCount: int
    /// Number of diagnostics (errors + warnings)
    DiagnosticCount: int
    /// Number of errors specifically
    ErrorCount: int
    /// Phase execution time in milliseconds
    ElapsedMs: int64
    /// Additional phase-specific metrics
    Metrics: Map<string, obj>
}

/// Create a summary for a phase
let createSummary
    (phase: PhaseId)
    (nodeCount: int)
    (entryPointCount: int)
    (elapsedMs: int64)
    : PhaseSummary =
    {
        Phase = phase
        Timestamp = DateTime.UtcNow
        NodeCount = nodeCount
        ReachableCount = None
        EntryPointCount = entryPointCount
        DiagnosticCount = 0
        ErrorCount = 0
        ElapsedMs = elapsedMs
        Metrics = Map.empty
    }

/// Create a summary with reachability info (for phase 4+)
let createSummaryWithReachability
    (phase: PhaseId)
    (nodeCount: int)
    (reachableCount: int)
    (entryPointCount: int)
    (elapsedMs: int64)
    : PhaseSummary =
    {
        Phase = phase
        Timestamp = DateTime.UtcNow
        NodeCount = nodeCount
        ReachableCount = Some reachableCount
        EntryPointCount = entryPointCount
        DiagnosticCount = 0
        ErrorCount = 0
        ElapsedMs = elapsedMs
        Metrics = Map.empty
    }

/// Add diagnostics info to a summary
let withDiagnostics (diagnosticCount: int) (errorCount: int) (summary: PhaseSummary) =
    { summary with DiagnosticCount = diagnosticCount; ErrorCount = errorCount }

/// Add custom metrics to a summary
let withMetrics (metrics: Map<string, obj>) (summary: PhaseSummary) =
    { summary with Metrics = metrics }

/// Node representation for phase output
/// This is a simplified view suitable for JSON serialization
type PhaseNodeOutput = {
    /// Node identifier
    Id: int
    /// Node kind as string (e.g., "Application", "Binding", "Lambda")
    Kind: string
    /// Node type as string (e.g., "int", "string -> int", "TVar(42)")
    Type: string
    /// Is this node reachable from entry points?
    IsReachable: bool
    /// Child node IDs
    Children: int list
    /// Parent node ID (if any)
    Parent: int option
    /// Source range as string (file:line:col)
    Range: string option
    /// SRTP resolution info (if applicable)
    SRTPResolution: string option
    /// Optional node body/content (for debugging)
    Body: string option
}

/// Phase output structure for JSON emission
type PhaseOutput = {
    /// Phase summary information
    Summary: PhaseSummary
    /// All nodes in the graph
    Nodes: PhaseNodeOutput list
    /// Entry point node IDs
    EntryPoints: int list
    /// Diagnostics messages
    Diagnostics: string list
}

/// Diff between two phases (for understanding what changed)
type PhaseDiff = {
    /// From which phase
    FromPhase: PhaseId
    /// To which phase
    ToPhase: PhaseId
    /// Nodes added in this phase
    NodesAdded: int list
    /// Nodes removed (should be empty with soft-delete)
    NodesRemoved: int list
    /// Nodes with changed types
    TypeChanges: (int * string * string) list  // (id, oldType, newType)
    /// Nodes with changed reachability
    ReachabilityChanges: (int * bool * bool) list  // (id, wasReachable, isReachable)
    /// New SRTP resolutions
    NewSRTPResolutions: int list
}

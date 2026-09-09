// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Diagnostic types for reporting compiler errors, warnings, and info.
module Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

//-------------------------------------------------------------------------
// Diagnostics
//-------------------------------------------------------------------------

/// Diagnostic severity
type NativeDiagnosticSeverity =
    | Error
    | Warning
    | Info

/// Reachability context for tiered diagnostic presentation.
/// Diagnostics are created during type-checking (before reachability analysis),
/// then tagged after reachability is computed. Consumers use this to tier
/// their response: reachable errors halt compilation, unreachable errors
/// are demoted to informational.
type ReachabilityContext =
    | Reachable
    | Unreachable
    | Unknown

/// A diagnostic message
type Diagnostic = {
    Severity: NativeDiagnosticSeverity
    Code: string
    Message: string
    Range: SourceRange
    RelatedNodes: NodeId list
    /// Reachability context — set after reachability analysis.
    /// Defaults to Unknown at construction time.
    Reachability: ReachabilityContext
}

/// Result of type checking a project
type CheckResult = {
    Graph: SemanticGraph
    Diagnostics: Diagnostic list
    /// Platform context (handed off to Composer for Alex code generation)
    PlatformContext: PlatformContext option
}

module Diagnostic =
    /// Compiler classification projected as the standard LSP unnecessary tag.
    /// Presentation may fade this declaration; proof status is independent.
    let isUnnecessary (d: Diagnostic) = d.Code = "CCS8500"

    /// Effective severity given reachability context.
    /// Reachable diagnostics report at intrinsic severity.
    /// Unreachable diagnostics are demoted to Info.
    /// Unknown diagnostics report at intrinsic severity (conservative).
    let effectiveSeverity (d: Diagnostic) =
        match d.Reachability with
        | Unreachable -> NativeDiagnosticSeverity.Info
        | Reachable | Unknown -> d.Severity

module CheckResult =
    let hasErrors (result: CheckResult) =
        result.Diagnostics |> List.exists (fun d -> Diagnostic.effectiveSeverity d = NativeDiagnosticSeverity.Error)

    let errors (result: CheckResult) =
        result.Diagnostics |> List.filter (fun d -> Diagnostic.effectiveSeverity d = NativeDiagnosticSeverity.Error)

    let warnings (result: CheckResult) =
        result.Diagnostics |> List.filter (fun d -> Diagnostic.effectiveSeverity d = NativeDiagnosticSeverity.Warning)

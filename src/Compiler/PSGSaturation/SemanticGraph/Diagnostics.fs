// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Diagnostic types for reporting compiler errors, warnings, and info.
module FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Diagnostics

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types

//-------------------------------------------------------------------------
// Diagnostics
//-------------------------------------------------------------------------

/// Diagnostic severity
type NativeDiagnosticSeverity =
    | Error
    | Warning
    | Info

/// A diagnostic message
type Diagnostic = {
    Severity: NativeDiagnosticSeverity
    Code: string
    Message: string
    Range: SourceRange
    RelatedNodes: NodeId list
}

/// Result of type checking a project
type CheckResult = {
    Graph: SemanticGraph
    Diagnostics: Diagnostic list
    /// Platform context (handed off to Firefly for Alex code generation)
    PlatformContext: PlatformContext option
}

module CheckResult =
    let hasErrors (result: CheckResult) =
        result.Diagnostics |> List.exists (fun d -> d.Severity = NativeDiagnosticSeverity.Error)

    let errors (result: CheckResult) =
        result.Diagnostics |> List.filter (fun d -> d.Severity = NativeDiagnosticSeverity.Error)

    let warnings (result: CheckResult) =
        result.Diagnostics |> List.filter (fun d -> d.Severity = NativeDiagnosticSeverity.Warning)

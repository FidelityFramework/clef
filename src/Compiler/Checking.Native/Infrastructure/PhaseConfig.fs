/// PhaseConfig - Global configuration for FNCS nanopass intermediate emission
///
/// This module controls whether phase intermediates are emitted during compilation.
/// Each nanopass phase can emit its work product for inspection when enabled.
///
/// Usage:
///   PhaseConfig.enableAllPhases "/path/to/intermediates"
///   // ... run compilation ...
///   // Intermediates written to fncs_phase_*.json files
module FSharp.Native.Compiler.Checking.Native.Infrastructure.PhaseConfig

open System

/// Configuration for a single nanopass phase
type PhaseSettings = {
    /// Whether to emit this phase's intermediate
    Enabled: bool
    /// Custom file suffix (e.g., "parsing" -> fncs_phase_0_parsing.json)
    Suffix: string
}

/// Global configuration for nanopass intermediate emission
type NanopassConfig = {
    /// Master switch for intermediate emission
    EmitIntermediates: bool
    /// Output directory for intermediate files
    OutputDir: string
    /// Use soft-delete for reachability (preserve full graph structure)
    SoftDeleteReachability: bool
    /// Individual phase settings
    PhaseSettings: Map<int, PhaseSettings>
    /// Include node bodies in output (can be verbose)
    IncludeNodeBodies: bool
    /// Include source ranges in output
    IncludeRanges: bool
    /// Pretty-print JSON output
    PrettyPrint: bool
}

/// Default configuration - all emission disabled
/// Note: SoftDeleteReachability = true is required for correct behavior.
/// Hard-delete removes TypeDef nodes needed for record/union field lookups.
let defaultConfig : NanopassConfig = {
    EmitIntermediates = false
    OutputDir = ""
    SoftDeleteReachability = true  // Must be true - hard-delete breaks field lookups
    PhaseSettings = Map.empty
    IncludeNodeBodies = false
    IncludeRanges = true
    PrettyPrint = true
}

/// Default phase suffixes
let private defaultPhaseSuffixes = [
    (0, "parsing")
    (1, "structural")
    (2, "constraints")
    (3, "srtp")
    (4, "reachability")
    (5, "final")
]

/// Global mutable configuration
/// Note: Mutable for easy integration with CLI flags. Thread-safety managed by caller.
let mutable private currentConfig = defaultConfig

/// Get current configuration
let getConfig () = currentConfig

/// Check if intermediates should be emitted
let shouldEmit () = currentConfig.EmitIntermediates

/// Check if a specific phase should be emitted
let shouldEmitPhase (phase: int) =
    currentConfig.EmitIntermediates &&
    match currentConfig.PhaseSettings.TryFind phase with
    | Some settings -> settings.Enabled
    | None -> false  // Unknown phases are not emitted

/// Get output directory
let getOutputDir () = currentConfig.OutputDir

/// Check if soft-delete reachability is enabled
let useSoftDeleteReachability () = currentConfig.SoftDeleteReachability

/// Enable all phases with default settings
let enableAllPhases (outputDir: string) =
    let phaseSettings =
        defaultPhaseSuffixes
        |> List.map (fun (phase, suffix) ->
            phase, { Enabled = true; Suffix = suffix })
        |> Map.ofList

    currentConfig <- {
        EmitIntermediates = true
        OutputDir = outputDir
        SoftDeleteReachability = true  // Enable soft-delete for debugging
        PhaseSettings = phaseSettings
        IncludeNodeBodies = true       // Include bodies for full visibility
        IncludeRanges = true
        PrettyPrint = true
    }

/// Enable specific phases only
let enablePhases (outputDir: string) (phases: int list) =
    let phaseSettings =
        defaultPhaseSuffixes
        |> List.filter (fun (phase, _) -> List.contains phase phases)
        |> List.map (fun (phase, suffix) ->
            phase, { Enabled = true; Suffix = suffix })
        |> Map.ofList

    currentConfig <- {
        EmitIntermediates = true
        OutputDir = outputDir
        SoftDeleteReachability = List.contains 4 phases  // Enable soft-delete if phase 4 requested
        PhaseSettings = phaseSettings
        IncludeNodeBodies = true
        IncludeRanges = true
        PrettyPrint = true
    }

/// Disable all emission (reset to default)
let disableEmission () =
    currentConfig <- defaultConfig

/// Set configuration directly (for testing or custom configurations)
let setConfig (config: NanopassConfig) =
    currentConfig <- config

/// Get the file path for a phase intermediate
let getPhaseFilePath (phase: int) =
    if not (shouldEmitPhase phase) then
        None
    else
        match currentConfig.PhaseSettings.TryFind phase with
        | Some settings ->
            let filename = sprintf "fncs_phase_%d_%s.json" phase settings.Suffix
            Some (System.IO.Path.Combine(currentConfig.OutputDir, filename))
        | None -> None

/// Configuration summary for logging
let getConfigSummary () =
    if not currentConfig.EmitIntermediates then
        "Phase emission: disabled"
    else
        let enabledPhases =
            currentConfig.PhaseSettings
            |> Map.toList
            |> List.filter (fun (_, s) -> s.Enabled)
            |> List.map (fun (p, s) -> sprintf "%d_%s" p s.Suffix)
            |> String.concat ", "
        sprintf "Phase emission: enabled [%s] -> %s (soft-delete: %b)"
            enabledPhases
            currentConfig.OutputDir
            currentConfig.SoftDeleteReachability

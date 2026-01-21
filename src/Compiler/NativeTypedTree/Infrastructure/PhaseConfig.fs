/// PhaseConfig - Configuration for compiler intermediate artifact emission
///
/// Artifacts are numbered ordinally across the entire compilation pipeline.
/// This allows `ls` to show them in pipeline order regardless of which
/// compiler stage produced them.
///
/// FNCS artifacts (01-05):
///   01_psg0.json              - PSG₀: Initial typed tree with reachability
///   02_intrinsic_recipes.json - Intrinsic elaboration recipes
///   03_psg1.json              - PSG₁: After intrinsic fold-in
///   04_saturation_recipes.json- Saturation recipes (Baker)
///   05_psg2.json              - PSG₂: Final saturated PSG to Alex
///
/// Alex artifacts (06-08):
///   06_coeffects.json         - Coeffect analysis (SSA, mutability, etc.)
///   07_output.mlir            - MLIR output
///   08_output.ll              - LLVM IR (future)
module FSharp.Native.Compiler.NativeTypedTree.Infrastructure.PhaseConfig

open System

/// Artifact identifiers - ordinal across entire pipeline
[<RequireQualifiedAccess>]
module ArtifactId =
    // FNCS artifacts
    let [<Literal>] Psg0 = 1               // Initial PSG with reachability
    let [<Literal>] IntrinsicRecipes = 2   // Intrinsic elaboration recipes
    let [<Literal>] Psg1 = 3               // After intrinsic fold-in
    let [<Literal>] SaturationRecipes = 4  // Baker saturation recipes
    let [<Literal>] Psg2 = 5               // Final saturated PSG

    // Alex artifacts (reserved for Firefly side)
    let [<Literal>] Coeffects = 6          // Coeffect analysis
    let [<Literal>] Mlir = 7               // MLIR output
    let [<Literal>] Llvm = 8               // LLVM IR

/// Get the filename for an artifact (without directory)
let artifactFilename (id: int) : string =
    match id with
    | 1 -> "01_psg0.json"
    | 2 -> "02_intrinsic_recipes.json"
    | 3 -> "03_psg1.json"
    | 4 -> "04_saturation_recipes.json"
    | 5 -> "05_psg2.json"
    | 6 -> "06_coeffects.json"
    | 7 -> "07_output.mlir"
    | 8 -> "08_output.ll"
    | n -> sprintf "%02d_unknown.json" n

/// Global configuration for artifact emission
type ArtifactConfig = {
    /// Master switch for intermediate emission
    EmitIntermediates: bool
    /// Output directory for intermediate files
    OutputDir: string
    /// Which artifacts to emit (by ordinal ID)
    EnabledArtifacts: Set<int>
    /// Include node bodies in PSG output (verbose)
    IncludeNodeBodies: bool
    /// Include source ranges in output
    IncludeRanges: bool
    /// Pretty-print JSON output
    PrettyPrint: bool
}

/// Default configuration - all emission disabled
let defaultConfig : ArtifactConfig = {
    EmitIntermediates = false
    OutputDir = ""
    EnabledArtifacts = Set.empty
    IncludeNodeBodies = false
    IncludeRanges = true
    PrettyPrint = true
}

/// Global mutable configuration
let mutable private currentConfig = defaultConfig

/// Get current configuration
let getConfig () = currentConfig

/// Check if intermediates should be emitted
let shouldEmit () = currentConfig.EmitIntermediates

/// Check if a specific artifact should be emitted
let shouldEmitArtifact (id: int) =
    currentConfig.EmitIntermediates && currentConfig.EnabledArtifacts.Contains(id)

// Legacy compatibility - shouldEmitPhase maps to shouldEmitArtifact
let shouldEmitPhase (phase: int) =
    // Map old phase numbers to new artifact IDs
    let artifactId =
        match phase with
        | 1 -> ArtifactId.Psg0  // "structural" -> psg0
        | 4 -> ArtifactId.Psg0  // "reachability" -> psg0 (combined now)
        | 5 -> ArtifactId.Psg1  // "baker_moduleinit" -> psg1
        | 8 -> ArtifactId.Psg2  // "final" -> psg2
        | _ -> phase
    shouldEmitArtifact artifactId

/// Get output directory
let getOutputDir () = currentConfig.OutputDir

/// Get the file path for an artifact
let getArtifactFilePath (id: int) : string option =
    if not (shouldEmitArtifact id) then
        None
    else
        let filename = artifactFilename id
        Some (System.IO.Path.Combine(currentConfig.OutputDir, filename))

// Legacy compatibility
let getPhaseFilePath (phase: int) =
    let artifactId =
        match phase with
        | 1 -> ArtifactId.Psg0
        | 4 -> ArtifactId.Psg0
        | 5 -> ArtifactId.Psg1
        | 8 -> ArtifactId.Psg2
        | _ -> phase
    getArtifactFilePath artifactId

/// Enable all FNCS artifacts (1-5)
let enableAllFncsArtifacts (outputDir: string) =
    currentConfig <- {
        EmitIntermediates = true
        OutputDir = outputDir
        EnabledArtifacts = Set.ofList [1; 2; 3; 4; 5]
        IncludeNodeBodies = true
        IncludeRanges = true
        PrettyPrint = true
    }

/// Enable all artifacts including Alex (1-8)
let enableAllArtifacts (outputDir: string) =
    currentConfig <- {
        EmitIntermediates = true
        OutputDir = outputDir
        EnabledArtifacts = Set.ofList [1; 2; 3; 4; 5; 6; 7; 8]
        IncludeNodeBodies = true
        IncludeRanges = true
        PrettyPrint = true
    }

// Legacy compatibility
let enableAllPhases (outputDir: string) = enableAllArtifacts outputDir

/// Enable specific artifacts only
let enableArtifacts (outputDir: string) (ids: int list) =
    currentConfig <- {
        EmitIntermediates = true
        OutputDir = outputDir
        EnabledArtifacts = Set.ofList ids
        IncludeNodeBodies = true
        IncludeRanges = true
        PrettyPrint = true
    }

// Legacy compatibility
let enablePhases (outputDir: string) (phases: int list) = enableArtifacts outputDir phases

/// Disable all emission (reset to default)
let disableEmission () =
    currentConfig <- defaultConfig

/// Set configuration directly
let setConfig (config: ArtifactConfig) =
    currentConfig <- config

/// Configuration summary for logging
let getConfigSummary () =
    if not currentConfig.EmitIntermediates then
        "Artifact emission: disabled"
    else
        let enabled =
            currentConfig.EnabledArtifacts
            |> Set.toList
            |> List.map artifactFilename
            |> String.concat ", "
        sprintf "Artifact emission: enabled [%s] -> %s" enabled currentConfig.OutputDir

// Legacy - soft delete is always used now
let useSoftDeleteReachability () = true

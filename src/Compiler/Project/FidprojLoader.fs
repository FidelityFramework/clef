/// .fidproj file loading and parsing.
/// Single source of truth for project configuration.
namespace Clef.Compiler.Project

open System.IO
open Fidelity.Data.TOML
open Clef.Compiler.NativeTypedTree.NativeTypes

/// Memory model for native compilation.
[<RequireQualifiedAccess>]
type MemoryModel =
    /// Stack-only allocation, no heap.
    | StackOnly
    /// Static memory pools, pre-allocated.
    | StaticPools
    /// Arena allocation with explicit lifetime.
    | Arena
    /// Standard allocation (malloc/free or GC).
    | Standard

/// Target platform — determines which compilation pipeline (backend) to use.
[<RequireQualifiedAccess>]
type TargetPlatform =
    /// General-purpose processor → LLVM backend.
    | CPU
    /// Field-programmable gate array → CIRCT backend.
    | FPGA
    /// Graphics/compute processor → future.
    | GPU
    /// Microcontroller → LLVM backend (different config).
    | MCU
    /// Neural processing unit → future.
    | NPU
    /// Pure library — substrate-neutral, no hardware affinity.
    | Library

/// Deployment mode — artifact shape only.
/// Determines output format (executable vs library).
/// Does NOT determine runtime model — that comes from the platform binding.
[<RequireQualifiedAccess>]
type DeploymentMode =
    /// Freestanding binary, no libc dependency.
    | Freestanding
    /// Console application with libc.
    | Console
    /// Shared library.
    | Library
    /// Embedded firmware/bare metal.
    | Embedded

/// Parsed [platform] section from a binding's fidproj.
/// The platform binding IS the specification — this is the machine-readable
/// encoding of the platform quotation. See DTS+DMM paper Section 2.6.
type PlatformSection = {
    /// What execution environment services are available.
    RuntimeModel: RuntimeModel
    /// Operating system (e.g., "linux", "none").
    OS: string option
    /// Architecture (e.g., "x86_64", "arm_cortex_m7").
    Arch: string option
    /// Fully qualified immutable binding exported by the selected platform's
    /// source dependency closure. Selects one description independently of paths.
    Description: string option
    /// Keys the section carries that the compiler no longer reads (`word_size`,
    /// retired by CS-7b: width dimensions come from the platform description,
    /// plan L-13). Reported as CCS8205 information, never an error.
    UnusedKeys: string list
    /// Substrate type for FPGA (e.g., "fpga").
    Substrate: string option
    /// Hardware vendor (e.g., "xilinx", "amd").
    Vendor: string option
    /// Hardware family (e.g., "artix7", "rdna3_5").
    Family: string option
    /// Specific device (e.g., "xc7a100t").
    Device: string option
    /// Clock frequency in MHz (FPGA/MCU). Used with NsPerWeightUnit for
    /// combinational depth threshold: threshold = floor(period_ns / ns_per_weight_unit).
    ClockMhz: int option
    /// Fabric-specific delay per weighted combinational depth unit (ns).
    /// Calibrated from Vivado post-route timing (includes routing overhead).
    /// e.g., 1.6 for Artix-7 (from HelloArty WNS=-2.635ns at depth 8, 100 MHz).
    NsPerWeightUnit: float option
}

/// Represents a project dependency.
type FidprojDependency = {
    /// Dependency name.
    Name: string
    /// Version constraint (e.g., "1.0", ">=2.0").
    Version: string option
    /// Local path to dependency (overrides package lookup).
    Path: string option
    /// Features to enable.
    Features: string list
    /// Whether the dependency is optional.
    Optional: bool
}

/// Represents loaded .fidproj options.
/// All paths are ABSOLUTE and NORMALIZED.
type FidprojOptions = {
    /// Absolute path to the .fidproj file.
    ProjectPath: string
    /// Absolute path to the project directory.
    ProjectDirectory: string

    /// Package name.
    Name: string
    /// Package version.
    Version: string

    /// Compilation memory model.
    MemoryModel: MemoryModel
    /// Target platform — determines which backend pipeline to use.
    /// Substrate-neutral libraries use TargetPlatform.Library.
    TargetPlatform: TargetPlatform

    /// Source files (relative paths as declared in fidproj).
    SourceFiles: string list

    /// Output binary name (without extension).
    OutputName: string option
    /// Deployment mode — backend-internal (linker flags, runtime deps).
    DeploymentMode: DeploymentMode

    /// Project dependencies.
    Dependencies: FidprojDependency list
    /// Explicit native library identities from [link] libraries.
    /// Project checking includes the declarations of resolved dependencies.
    LinkedLibraries: string list
    /// Resolved absolute path to Alloy library (if specified).
    AlloyPath: string option
    /// Resolved absolute path to platform binding library (if specified).
    /// E.g., ~/repos/Fidelity.Platform/Linux_x86_64
    PlatformPath: string option
    /// Platform metadata from the binding's [platform] section (if loaded).
    /// The binding IS the specification — this is the authoritative source
    /// for runtime model, architecture, and capabilities.
    PlatformMetadata: PlatformSection option
    /// Project-level clock frequency override (MHz).
    /// When set, overrides the platform binding's clock_mhz for depth analysis.
    /// Use when the design runs at a different frequency than the board oscillator.
    ClockMhzOverride: int option
}

module FidprojLoader =
    /// Normalizes a path to use forward slashes and be absolute.
    let private normalizePath (path: string) =
        Path.GetFullPath(path).Replace('\\', '/')

    let private parseLinkedLibraries (doc: TomlDocument) : Result<string list, string> =
        match Toml.getValue "link.libraries" doc with
        | None -> Ok []
        | Some (TomlValue.Array values) ->
            let names = values |> List.choose (function TomlValue.String name -> Some name | _ -> None)
            if names.Length <> values.Length || (names |> List.exists System.String.IsNullOrWhiteSpace) then
                Error "Expected [link] libraries to be an array of non-empty strings"
            else Ok (List.distinct names)
        | Some _ -> Error "Expected [link] libraries to be an array of non-empty strings"

    /// Parses a memory model string.
    // An unrecognized memory model is refused, never read as Standard.
    let private parseMemoryModel (s: string) : Result<MemoryModel, string> =
        match s.ToLowerInvariant() with
        | "stack_only" | "stackonly" -> Ok MemoryModel.StackOnly
        | "static_pools" | "staticpools" -> Ok MemoryModel.StaticPools
        | "arena" -> Ok MemoryModel.Arena
        | "standard" -> Ok MemoryModel.Standard
        | unknown -> Error $"Unrecognized memory_model '%s{unknown}'. Expected: stack_only, static_pools, arena, standard"

    /// Parses a target platform string from [compilation] target.
    let private parseTargetPlatform (s: string) : Result<TargetPlatform, string> =
        match s.ToLowerInvariant() with
        | "cpu" | "native" -> Ok TargetPlatform.CPU
        | "fpga" -> Ok TargetPlatform.FPGA
        | "gpu" -> Ok TargetPlatform.GPU
        | "mcu" -> Ok TargetPlatform.MCU
        | "npu" -> Ok TargetPlatform.NPU
        | "library" | "lib" -> Ok TargetPlatform.Library
        | unknown -> Error $"Unrecognized target platform '%s{unknown}'. Expected: cpu, fpga, gpu, library, mcu, npu"

    /// Parses a deployment mode string from [build] output_kind.
    /// Parses a deployment mode string from [build] output_kind.
    /// No silent fallbacks — unknown values are hard errors.
    let private parseDeploymentMode (s: string) : Result<DeploymentMode, string> =
        match s.ToLowerInvariant() with
        | "freestanding" -> Ok DeploymentMode.Freestanding
        | "console" | "executable" -> Ok DeploymentMode.Console
        | "library" | "lib" -> Ok DeploymentMode.Library
        | "embedded" | "fpga" -> Ok DeploymentMode.Embedded
        | "kernel" | "npu" -> Ok DeploymentMode.Freestanding
        | unknown -> Error $"Unrecognized output_kind '%s{unknown}'. Expected: console, freestanding, library, embedded, fpga, kernel"

    /// Parses a runtime model string from a binding's [platform] section.
    /// No silent fallbacks — unknown values are hard errors.
    let private parseRuntimeModel (s: string) : Result<RuntimeModel, string> =
        match s.ToLowerInvariant() with
        | "libc" -> Ok RuntimeModel.Libc
        | "freestanding" -> Ok RuntimeModel.Freestanding
        | "bare" -> Ok RuntimeModel.Bare
        | "rocm" -> Ok RuntimeModel.ROCm
        | "xdna" -> Ok RuntimeModel.XDNA
        | unknown -> Error $"Unrecognized runtime_model '%s{unknown}'. Expected: libc, freestanding, bare, rocm, xdna"

    /// Parses a [platform] section from a TOML document.
    let private parsePlatformSection (doc: TomlDocument) : Result<PlatformSection, string> =
        let description =
            match Toml.getValue "platform.description" doc with
            | None -> Ok None
            | Some (TomlValue.String name) when
                not (System.String.IsNullOrWhiteSpace name)
                && name = name.Trim()
                && name.Contains '.'
                && (name.Split('.') |> Array.forall (System.String.IsNullOrWhiteSpace >> not)) -> Ok (Some name)
            | Some _ -> Error "Expected [platform] description to be a fully qualified binding name"
        match description with
        | Error message -> Error message
        | Ok description ->
        match Toml.getString "platform.runtime_model" doc with
        | None -> Error "Missing required field [platform] runtime_model"
        | Some rmStr ->
            match parseRuntimeModel rmStr with
            | Error msg -> Error msg
            | Ok runtimeModel ->
                Ok {
                    RuntimeModel = runtimeModel
                    OS = Toml.getString "platform.os" doc
                    Arch = Toml.getString "platform.arch" doc
                    Description = description
                    UnusedKeys = [ "word_size" ] |> List.filter (fun key -> (Toml.getValue ("platform." + key) doc).IsSome)
                    Substrate = Toml.getString "platform.substrate" doc
                    Vendor = Toml.getString "platform.vendor" doc
                    Family = Toml.getString "platform.family" doc
                    Device = Toml.getString "platform.device" doc
                    ClockMhz = Toml.getInt "platform.clock_mhz" doc |> Option.map int
                    NsPerWeightUnit = Toml.getFloat "platform.ns_per_weight_unit" doc
                }

    /// Loads the [platform] section from a binding's .fidproj file.
    /// The binding IS the specification — this reads what the platform provides.
    let loadBindingPlatformSection (fidprojPath: string) : Result<PlatformSection, string> =
        let path = normalizePath fidprojPath
        if not (File.Exists path) then
            Error $"Platform .fidproj not found: {path}"
        else
            let content = File.ReadAllText(path)
            match Toml.parse content with
            | Error msg -> Error $"Failed to parse binding fidproj {path}: {msg}"
            | Ok doc -> parsePlatformSection doc

    /// Parses a dependency from a TOML value.
    // A dependency entry whose fields are present but malformed is refused; a malformed path,
    // feature list or flag is never read as absent, and an entry of another TOML form is never
    // read as a dependency with no path.
    let private parseDependency (name: string) (value: TomlValue) (projectDir: string): Result<FidprojDependency, string> =
        match value with
        | TomlValue.String version ->
            Ok { Name = name
                 Version = Some version
                 Path = None
                 Features = []
                 Optional = false }
        | TomlValue.InlineTable table ->
            let field key (read: TomlValue -> 'a option) (expected: string) : Result<'a option, string> =
                match Map.tryFind key table with
                | None -> Ok None
                | Some value ->
                    match read value with
                    | Some parsed -> Ok (Some parsed)
                    | None -> Error $"Dependency '%s{name}': '%s{key}' must be %s{expected}"
            let text = function TomlValue.String s -> Some s | _ -> None
            let texts = function
                | TomlValue.Array arr ->
                    let values = arr |> List.choose text
                    if values.Length = arr.Length then Some values else None
                | _ -> None
            let flag = function TomlValue.Boolean b -> Some b | _ -> None
            field "version" text "a string"
            |> Result.bind (fun version ->
                field "path" text "a string"
                |> Result.bind (fun path ->
                    field "features" texts "an array of strings"
                    |> Result.bind (fun features ->
                        field "optional" flag "a boolean"
                        |> Result.map (fun optional ->
                            { Name = name
                              Version = version
                              Path = path |> Option.map (fun p -> normalizePath (Path.Combine(projectDir, p)))
                              Features = features |> Option.defaultValue []
                              Optional = optional |> Option.defaultValue false }))))
        | _ ->
            Error $"Dependency '%s{name}' must be a version string or an inline table"

    /// Loads a .fidproj file.
    let load (fidprojPath: string): Result<FidprojOptions, string> =
        let absPath = normalizePath fidprojPath
        if not (File.Exists absPath) then
            Error $"Project file not found: {absPath}"
        else
            let content = File.ReadAllText(absPath)
            match Toml.parse content with
            | Error msg -> Error $"Failed to parse {absPath}: {msg}"
            | Ok doc ->
                let projectDir =
                    match Path.GetDirectoryName absPath with
                    | null -> failwith $"Cannot get directory for project path: {absPath}"
                    | dir -> normalizePath dir

                // Package section
                let defaultName =
                    match Path.GetFileNameWithoutExtension absPath with
                    | null -> "unnamed"
                    | n -> n
                let name = Toml.getString "package.name" doc |> Option.defaultValue defaultName
                let version = Toml.getString "package.version" doc |> Option.defaultValue "0.1.0"

                // Compilation section
                let memoryModelResult =
                    match Toml.getString "compilation.memory_model" doc with
                    | Some s -> parseMemoryModel s
                    | None -> Ok MemoryModel.StackOnly

                // Build section — parse output_kind first: libraries are substrate-neutral
                // A present but malformed sources list is refused, never read as no sources.
                let sourcesResult =
                    match Toml.getValue "build.sources" doc, Toml.getStringArray "build.sources" doc with
                    | None, _ -> Ok []
                    | Some _, Some sources -> Ok sources
                    | Some _, None -> Error "Expected [build] sources to be an array of strings"
                let outputName = Toml.getString "build.output" doc
                let deploymentModeResult =
                    match Toml.getString "build.output_kind" doc with
                    | None -> Ok DeploymentMode.Console
                    | Some s -> parseDeploymentMode s
                match deploymentModeResult with
                | Error msg -> Error msg
                | Ok deploymentMode ->

                // Target platform — required for all packages.
                // Substrate-neutral packages use target = "library".
                let targetPlatformResult =
                    match Toml.getString "compilation.target" doc with
                    | Some s -> parseTargetPlatform s
                    | None -> Error "Missing required field [compilation] target. Expected: cpu, fpga, gpu, library, mcu, npu"
                match targetPlatformResult with
                | Error msg -> Error msg
                | Ok targetPlatform ->

                match memoryModelResult with
                | Error msg -> Error msg
                | Ok memoryModel ->

                match sourcesResult with
                | Error msg -> Error msg
                | Ok sources ->

                match parseLinkedLibraries doc with
                | Error msg -> Error msg
                | Ok linkedLibraries ->

                // Dependencies section
                let dependenciesResult =
                    match Toml.getTable "dependencies" doc with
                    | Some depTable ->
                        depTable
                        |> Map.toList
                        |> List.fold (fun acc (name, value) ->
                            match acc with
                            | Error message -> Error message
                            | Ok parsed ->
                                parseDependency name value projectDir
                                |> Result.map (fun dependency -> parsed @ [dependency])) (Ok [])
                    | None -> Ok []
                match dependenciesResult with
                | Error msg -> Error msg
                | Ok dependencies ->

                // Extract Alloy path from dependencies
                let alloyPath =
                    dependencies
                    |> List.tryFind (fun d -> d.Name = "alloy" || d.Name = "Alloy")
                    |> Option.bind (fun d -> d.Path)

                // Extract platform binding library path from dependencies
                // E.g., platform = { path = "/home/hhh/repos/Fidelity.Platform/Linux_x86_64" }
                let platformPath =
                    dependencies
                    |> List.tryFind (fun d -> d.Name = "platform" || d.Name = "Platform")
                    |> Option.bind (fun d -> d.Path)

                // Load platform metadata from binding's [platform] section if available.
                // The binding IS the specification — this is the authoritative source.
                // When no platform dependency exists (e.g., standalone kernel fidproj),
                // fall back to the project's own [platform] section as metadata source.
                let platformMetadataResult =
                    match platformPath with
                    | Some path -> loadBindingPlatformSection path |> Result.map Some
                    | None ->
                        // A missing section is allowed; a present malformed section is not.
                        match Toml.getTable "platform" doc with
                        | Some _ -> parsePlatformSection doc |> Result.map Some
                        | None -> Ok None

                match platformMetadataResult with
                | Error message -> Error message
                | Ok platformMetadata ->

                // Project-level clock override from [compilation] section
                let clockMhzOverride =
                    Toml.getInt "compilation.clock_mhz" doc |> Option.map int

                Ok {
                    ProjectPath = absPath
                    ProjectDirectory = projectDir
                    Name = name
                    Version = version
                    MemoryModel = memoryModel
                    TargetPlatform = targetPlatform
                    SourceFiles = sources
                    OutputName = outputName
                    DeploymentMode = deploymentMode
                    Dependencies = dependencies
                    LinkedLibraries = linkedLibraries
                    AlloyPath = alloyPath
                    PlatformPath = platformPath
                    PlatformMetadata = platformMetadata
                    ClockMhzOverride = clockMhzOverride
                }

    /// Finds the .fidproj file containing a source file.
    let findProjectForSourceFile (sourceFile: string) (projects: FidprojOptions list): FidprojOptions option =
        let normalizedSource = normalizePath sourceFile
        projects
        |> List.tryFind (fun p ->
            p.SourceFiles
            |> List.exists (fun sf ->
                let fullPath = normalizePath (Path.Combine(p.ProjectDirectory, sf))
                fullPath = normalizedSource))

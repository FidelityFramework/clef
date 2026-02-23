/// .fidproj file loading and parsing.
/// Single source of truth for project configuration.
namespace Clef.Compiler.Project

open System.IO
open Fidelity.Toml
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
    /// Word size in bits (e.g., 32, 64).
    WordSize: int option
    /// Substrate type for FPGA (e.g., "fpga").
    Substrate: string option
    /// Hardware vendor (e.g., "xilinx", "amd").
    Vendor: string option
    /// Hardware family (e.g., "artix7", "rdna3_5").
    Family: string option
    /// Specific device (e.g., "xc7a100t").
    Device: string option
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
    TargetPlatform: TargetPlatform

    /// Source files (relative paths as declared in fidproj).
    SourceFiles: string list

    /// Output binary name (without extension).
    OutputName: string option
    /// Deployment mode — backend-internal (linker flags, runtime deps).
    DeploymentMode: DeploymentMode

    /// Project dependencies.
    Dependencies: FidprojDependency list
    /// Resolved absolute path to Alloy library (if specified).
    AlloyPath: string option
    /// Resolved absolute path to platform binding library (if specified).
    /// E.g., ~/repos/Fidelity.Platform/Linux_x86_64
    PlatformPath: string option
    /// Platform metadata from the binding's [platform] section (if loaded).
    /// The binding IS the specification — this is the authoritative source
    /// for runtime model, architecture, and capabilities.
    PlatformMetadata: PlatformSection option
}

module FidprojLoader =
    /// Normalizes a path to use forward slashes and be absolute.
    let private normalizePath (path: string) =
        Path.GetFullPath(path).Replace('\\', '/')

    /// Parses a memory model string.
    let private parseMemoryModel (s: string) =
        match s.ToLowerInvariant() with
        | "stack_only" | "stackonly" -> MemoryModel.StackOnly
        | "static_pools" | "staticpools" -> MemoryModel.StaticPools
        | "arena" -> MemoryModel.Arena
        | "standard" | _ -> MemoryModel.Standard

    /// Parses a target platform string from [compilation] target.
    let private parseTargetPlatform (s: string) : Result<TargetPlatform, string> =
        match s.ToLowerInvariant() with
        | "cpu" | "native" -> Ok TargetPlatform.CPU
        | "fpga" -> Ok TargetPlatform.FPGA
        | "gpu" -> Ok TargetPlatform.GPU
        | "mcu" -> Ok TargetPlatform.MCU
        | "npu" -> Ok TargetPlatform.NPU
        | unknown -> Error $"Unrecognized target platform '%s{unknown}'. Expected: cpu, fpga, gpu, mcu, npu"

    /// Parses a deployment mode string from [build] output_kind.
    /// Parses a deployment mode string from [build] output_kind.
    /// No silent fallbacks — unknown values are hard errors.
    let private parseDeploymentMode (s: string) : Result<DeploymentMode, string> =
        match s.ToLowerInvariant() with
        | "freestanding" -> Ok DeploymentMode.Freestanding
        | "console" | "executable" -> Ok DeploymentMode.Console
        | "library" | "lib" -> Ok DeploymentMode.Library
        | "embedded" -> Ok DeploymentMode.Embedded
        | unknown -> Error $"Unrecognized output_kind '%s{unknown}'. Expected: console, freestanding, library, embedded"

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
                    WordSize = Toml.getInt "platform.word_size" doc |> Option.map int
                    Substrate = Toml.getString "platform.substrate" doc
                    Vendor = Toml.getString "platform.vendor" doc
                    Family = Toml.getString "platform.family" doc
                    Device = Toml.getString "platform.device" doc
                }

    /// Tries to find a .fidproj file in the given directory.
    let tryFindInDirectory (directory: string): string option =
        let dir = normalizePath directory
        if Directory.Exists dir then
            Directory.GetFiles(dir, "*.fidproj")
            |> Array.tryHead
            |> Option.map normalizePath
        else
            None

    /// Loads the [platform] section from a binding's .fidproj file.
    /// The binding IS the specification — this reads what the platform provides.
    let loadBindingPlatformSection (platformDir: string) : Result<PlatformSection, string> =
        let dir = normalizePath platformDir
        match tryFindInDirectory dir with
        | None -> Error $"No .fidproj found in platform binding directory: {dir}"
        | Some fidprojPath ->
            let content = File.ReadAllText(fidprojPath)
            match Toml.parse content with
            | Error msg -> Error $"Failed to parse binding fidproj {fidprojPath}: {msg}"
            | Ok doc -> parsePlatformSection doc

    /// Parses a dependency from a TOML value.
    let private parseDependency (name: string) (value: TomlValue) (projectDir: string): FidprojDependency =
        match value with
        | TomlValue.String version ->
            { Name = name
              Version = Some version
              Path = None
              Features = []
              Optional = false }
        | TomlValue.InlineTable table ->
            let version = table |> Map.tryFind "version" |> Option.bind (function TomlValue.String s -> Some s | _ -> None)
            let path =
                table
                |> Map.tryFind "path"
                |> Option.bind (function TomlValue.String s -> Some s | _ -> None)
                |> Option.map (fun p -> normalizePath (Path.Combine(projectDir, p)))
            let features =
                table
                |> Map.tryFind "features"
                |> Option.bind (function
                    | TomlValue.Array arr ->
                        arr |> List.choose (function TomlValue.String s -> Some s | _ -> None) |> Some
                    | _ -> None)
                |> Option.defaultValue []
            let optional =
                table
                |> Map.tryFind "optional"
                |> Option.bind (function TomlValue.Boolean b -> Some b | _ -> None)
                |> Option.defaultValue false
            { Name = name
              Version = version
              Path = path
              Features = features
              Optional = optional }
        | _ ->
            { Name = name
              Version = None
              Path = None
              Features = []
              Optional = false }

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
                let memoryModel =
                    Toml.getString "compilation.memory_model" doc
                    |> Option.map parseMemoryModel
                    |> Option.defaultValue MemoryModel.StackOnly
                let targetPlatformResult =
                    match Toml.getString "compilation.target" doc with
                    | None -> Error "Missing required field [compilation] target. Expected: cpu, fpga, gpu, mcu, npu"
                    | Some s -> parseTargetPlatform s
                match targetPlatformResult with
                | Error msg -> Error msg
                | Ok targetPlatform ->

                // Build section
                let sources =
                    Toml.getStringArray "build.sources" doc
                    |> Option.defaultValue []
                let outputName = Toml.getString "build.output" doc
                let deploymentModeResult =
                    match Toml.getString "build.output_kind" doc with
                    | None -> Ok DeploymentMode.Console
                    | Some s -> parseDeploymentMode s
                match deploymentModeResult with
                | Error msg -> Error msg
                | Ok deploymentMode ->

                // Dependencies section
                let dependencies =
                    match Toml.getTable "dependencies" doc with
                    | Some depTable ->
                        depTable
                        |> Map.toList
                        |> List.map (fun (name, value) -> parseDependency name value projectDir)
                    | None -> []

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
                let platformMetadata =
                    match platformPath with
                    | Some dir ->
                        match loadBindingPlatformSection dir with
                        | Ok section -> Some section
                        | Error _ -> None
                    | None -> None

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
                    AlloyPath = alloyPath
                    PlatformPath = platformPath
                    PlatformMetadata = platformMetadata
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

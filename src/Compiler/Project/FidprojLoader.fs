/// .fidproj file loading and parsing.
/// Single source of truth for project configuration.
namespace Clef.Compiler.Project

open System.IO
open Fidelity.Toml

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

/// Output kind for the compiled binary.
[<RequireQualifiedAccess>]
type OutputKind =
    /// Freestanding binary, no libc dependency.
    | Freestanding
    /// Console application with libc.
    | Console
    /// Shared library.
    | Library
    /// Embedded firmware/bare metal.
    | Embedded

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
    /// Target platform.
    Target: string

    /// Source files (relative paths as declared in fidproj).
    SourceFiles: string list

    /// Output binary name (without extension).
    OutputName: string option
    /// Output kind.
    OutputKind: OutputKind

    /// Project dependencies.
    Dependencies: FidprojDependency list
    /// Resolved absolute path to Alloy library (if specified).
    AlloyPath: string option
    /// Resolved absolute path to platform binding library (if specified).
    /// E.g., ~/repos/Fidelity.Platform/Linux_x86_64
    PlatformPath: string option
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

    /// Parses an output kind string.
    let private parseOutputKind (s: string) =
        match s.ToLowerInvariant() with
        | "freestanding" -> OutputKind.Freestanding
        | "console" -> OutputKind.Console
        | "library" | "lib" -> OutputKind.Library
        | "embedded" -> OutputKind.Embedded
        | _ -> OutputKind.Console

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
                let target =
                    Toml.getString "compilation.target" doc
                    |> Option.defaultValue "native"

                // Build section
                let sources =
                    Toml.getStringArray "build.sources" doc
                    |> Option.defaultValue []
                let outputName = Toml.getString "build.output" doc
                let outputKind =
                    Toml.getString "build.output_kind" doc
                    |> Option.map parseOutputKind
                    |> Option.defaultValue OutputKind.Console

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

                Ok {
                    ProjectPath = absPath
                    ProjectDirectory = projectDir
                    Name = name
                    Version = version
                    MemoryModel = memoryModel
                    Target = target
                    SourceFiles = sources
                    OutputName = outputName
                    OutputKind = outputKind
                    Dependencies = dependencies
                    AlloyPath = alloyPath
                    PlatformPath = platformPath
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

    /// Finds the .fidproj file containing a source file.
    let findProjectForSourceFile (sourceFile: string) (projects: FidprojOptions list): FidprojOptions option =
        let normalizedSource = normalizePath sourceFile
        projects
        |> List.tryFind (fun p ->
            p.SourceFiles
            |> List.exists (fun sf ->
                let fullPath = normalizePath (Path.Combine(p.ProjectDirectory, sf))
                fullPath = normalizedSource))

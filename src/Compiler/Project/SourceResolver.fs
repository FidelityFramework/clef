/// Source file resolution and ordering.
/// Handles Alloy library ordering and project source resolution.
namespace FSharp.Native.Compiler.Project

open System.IO

/// Errors that can occur during source resolution.
/// A production compiler MUST surface these - no silent fallbacks.
type SourceResolutionError =
    /// The Alloy directory specified in dependencies does not exist.
    | AlloyDirectoryNotFound of path: string
    /// The Alloy.fidproj file is missing from the Alloy directory.
    | AlloyFidprojNotFound of path: string
    /// The Alloy.fidproj file exists but failed to parse/load.
    | AlloyFidprojLoadError of path: string * message: string
    /// A source file listed in Alloy.fidproj does not exist.
    | AlloySourceFileNotFound of path: string
    /// A source file listed in the project does not exist.
    | ProjectSourceFileNotFound of path: string

module SourceResolutionError =
    /// Format error for display.
    let format (error: SourceResolutionError): string =
        match error with
        | AlloyDirectoryNotFound path ->
            $"Alloy directory not found: {path}. Check the 'alloy' path in your .fidproj dependencies."
        | AlloyFidprojNotFound path ->
            $"Alloy.fidproj not found at: {path}. The Alloy library must have an Alloy.fidproj file."
        | AlloyFidprojLoadError (path, msg) ->
            $"Failed to load Alloy.fidproj at {path}: {msg}"
        | AlloySourceFileNotFound path ->
            $"Alloy source file not found: {path}. Check your Alloy.fidproj [build] sources."
        | ProjectSourceFileNotFound path ->
            $"Project source file not found: {path}. Check your .fidproj [build] sources."

module SourceResolver =
    /// Normalizes a path to use forward slashes and be absolute.
    let private normalizePath (path: string) =
        Path.GetFullPath(path).Replace('\\', '/')

    /// Gets ordered Alloy source files by reading Alloy.fidproj.
    /// The Alloy.fidproj file is the single source of truth for file ordering.
    /// Returns Error if Alloy cannot be loaded - this is NEVER silently ignored.
    let getAlloySources (alloyPath: string): Result<string list, SourceResolutionError> =
        let normalizedPath = normalizePath alloyPath
        if not (Directory.Exists normalizedPath) then
            Error (AlloyDirectoryNotFound normalizedPath)
        else
            // Look for Alloy.fidproj in the Alloy directory
            let fidprojPath = Path.Combine(normalizedPath, "Alloy.fidproj")
            if not (File.Exists fidprojPath) then
                Error (AlloyFidprojNotFound fidprojPath)
            else
                // Load the Alloy project file to get authoritative source ordering
                match FidprojLoader.load fidprojPath with
                | Error msg ->
                    Error (AlloyFidprojLoadError (fidprojPath, msg))
                | Ok alloyOptions ->
                    // Resolve source paths relative to Alloy directory
                    let resolvedPaths =
                        alloyOptions.SourceFiles
                        |> List.map (fun sf -> normalizePath (Path.Combine(normalizedPath, sf)))

                    // Check that ALL source files exist - missing files are errors
                    let missingFiles =
                        resolvedPaths
                        |> List.filter (fun p -> not (File.Exists p))

                    match missingFiles with
                    | [] -> Ok resolvedPaths
                    | missing :: _ ->
                        // Report the first missing file (could aggregate all)
                        Error (AlloySourceFileNotFound missing)

    /// Resolves project source files to absolute paths.
    /// Preserves the order as declared in the fidproj.
    /// Returns Error if any source file does not exist.
    let resolveProjectSources (projectDir: string) (sourceFiles: string list): Result<string list, SourceResolutionError> =
        let normalizedDir = normalizePath projectDir
        let resolvedPaths =
            sourceFiles
            |> List.map (fun sf -> normalizePath (Path.Combine(normalizedDir, sf)))

        // Check that ALL source files exist - missing files are errors
        let missingFiles =
            resolvedPaths
            |> List.filter (fun p -> not (File.Exists p))

        match missingFiles with
        | [] -> Ok resolvedPaths
        | missing :: _ ->
            Error (ProjectSourceFileNotFound missing)

    /// Gets all sources in compilation order (Alloy first, then project).
    /// Returns absolute, normalized paths for all source files.
    /// Returns Error if Alloy or any source file cannot be resolved.
    let getAllSourcesInOrder (options: FidprojOptions): Result<string list, SourceResolutionError> =
        // First resolve Alloy sources (if Alloy is specified)
        let alloyResult =
            match options.AlloyPath with
            | Some path -> getAlloySources path
            | None -> Ok []

        match alloyResult with
        | Error e -> Error e
        | Ok alloySources ->
            // Then resolve project sources
            match resolveProjectSources options.ProjectDirectory options.SourceFiles with
            | Error e -> Error e
            | Ok projectSources ->
                Ok (alloySources @ projectSources)

    /// Checks if a source file belongs to a project.
    /// Compares normalized absolute paths.
    /// Returns false if source resolution fails (caller should check with getAllSourcesInOrder for details).
    let containsSourceFile (sourceFile: string) (options: FidprojOptions): bool =
        let normalizedSource = normalizePath sourceFile
        match getAllSourcesInOrder options with
        | Error _ -> false  // Can't check membership if sources fail to resolve
        | Ok allSources -> allSources |> List.exists (fun s -> s = normalizedSource)

    /// Finds which project contains a source file.
    /// Returns None if no project contains the file or if source resolution fails.
    let findProjectForSourceFile (sourceFile: string) (projects: FidprojOptions list): FidprojOptions option =
        projects |> List.tryFind (fun p -> containsSourceFile sourceFile p)

    /// Gets the relative path of a source file within its project.
    /// Returns None if the file is not part of the project.
    let getRelativePath (sourceFile: string) (options: FidprojOptions): string option =
        let normalizedSource = normalizePath sourceFile
        let normalizedDir = normalizePath options.ProjectDirectory

        if normalizedSource.StartsWith(normalizedDir + "/") then
            Some (normalizedSource.Substring(normalizedDir.Length + 1))
        else
            // Check if it's in Alloy
            match options.AlloyPath with
            | Some alloyPath ->
                let normalizedAlloy = normalizePath alloyPath
                if normalizedSource.StartsWith(normalizedAlloy + "/") then
                    Some (normalizedSource.Substring(normalizedAlloy.Length + 1))
                else
                    None
            | None -> None

    /// Determines if a source file is part of Alloy (vs project sources).
    let isAlloySource (sourceFile: string) (options: FidprojOptions): bool =
        match options.AlloyPath with
        | Some alloyPath ->
            let normalizedSource = normalizePath sourceFile
            let normalizedAlloy = normalizePath alloyPath
            normalizedSource.StartsWith(normalizedAlloy + "/")
        | None -> false

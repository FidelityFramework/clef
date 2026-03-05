/// Source file resolution and ordering.
/// Handles dependency library ordering and project source resolution.
/// GENERIC DEPENDENCY RESOLUTION - no hardcoded library names.
namespace Clef.Compiler.Project

open System.IO

/// Errors that can occur during source resolution.
/// A production compiler MUST surface these - no silent fallbacks.
type SourceResolutionError =
    /// A dependency's .fidproj file does not exist.
    | DependencyFidprojNotFound of name: string * path: string
    /// A dependency's .fidproj file exists but failed to parse/load.
    | DependencyFidprojLoadError of name: string * path: string * message: string
    /// A source file listed in a dependency's .fidproj does not exist.
    | DependencySourceFileNotFound of name: string * path: string
    /// A source file listed in the project does not exist.
    | ProjectSourceFileNotFound of path: string
    /// Circular dependency detected.
    | CircularDependency of chain: string list

module SourceResolutionError =
    /// Format error for display.
    let format (error: SourceResolutionError): string =
        match error with
        | DependencyFidprojNotFound (name, path) ->
            $"Dependency '{name}' .fidproj not found: {path}. Check the path in your .fidproj dependencies."
        | DependencyFidprojLoadError (name, path, msg) ->
            $"Failed to load dependency '{name}' .fidproj at {path}: {msg}"
        | DependencySourceFileNotFound (name, path) ->
            $"Dependency '{name}' source file not found: {path}. Check the [build] sources in its .fidproj."
        | ProjectSourceFileNotFound path ->
            $"Project source file not found: {path}. Check your .fidproj [build] sources."
        | CircularDependency chain ->
            let chainStr = String.concat " -> " chain
            $"Circular dependency detected: {chainStr}"

module SourceResolver =
    /// Normalizes a path to use forward slashes and be absolute.
    let private normalizePath (path: string) =
        Path.GetFullPath(path).Replace('\\', '/')

    /// Gets ordered source files from a dependency RECURSIVELY by reading its .fidproj.
    /// Transitive dependencies are resolved first (deepest dependencies come first).
    /// The dependency's .fidproj is the single source of truth for file ordering.
    /// Returns Error if dependency cannot be loaded - this is NEVER silently ignored.
    /// Uses visited set to detect circular dependencies.
    ///
    /// depPath is always a fidproj file path — resolution from directory paths happens
    /// in FidprojLoader.parseDependency, not here.
    let rec private getDependencySourcesRec
        (depName: string)
        (depPath: string)
        (visitedPaths: Set<string>)
        (visitChain: string list)
        : Result<string list * Set<string>, SourceResolutionError> =

        let normalizedPath = normalizePath depPath

        // Check for circular dependency
        if Set.contains normalizedPath visitedPaths then
            Error (CircularDependency (List.rev (depName :: visitChain)))
        else
            if not (File.Exists normalizedPath) then
                Error (DependencyFidprojNotFound (depName, normalizedPath))
            else
                // Load the dependency project file to get authoritative source ordering
                match FidprojLoader.load normalizedPath with
                | Error msg ->
                    Error (DependencyFidprojLoadError (depName, normalizedPath, msg))
                | Ok depOptions ->
                    // Mark this path as visited BEFORE recursing
                    let newVisited = Set.add normalizedPath visitedPaths
                    let newChain = depName :: visitChain

                    // FIRST: Recursively get sources from THIS dependency's dependencies
                    // This ensures transitive dependencies are compiled first
                    let transitiveDepsResult =
                        depOptions.Dependencies
                        |> List.filter (fun dep -> dep.Path.IsSome)
                        |> List.fold (fun acc dep ->
                            match acc with
                            | Error e -> Error e
                            | Ok (accSources, accVisited) ->
                                match getDependencySourcesRec dep.Name dep.Path.Value accVisited newChain with
                                | Error e -> Error e
                                | Ok (depSources, depVisited) ->
                                    Ok (accSources @ depSources, depVisited)
                        ) (Ok ([], newVisited))

                    match transitiveDepsResult with
                    | Error e -> Error e
                    | Ok (transitiveSources, finalVisited) ->
                        // THEN: Add this dependency's own sources
                        // depOptions.ProjectDirectory is the fidproj's parent directory,
                        // set by FidprojLoader.load — the authoritative source base.
                        let resolvedPaths =
                            depOptions.SourceFiles
                            |> List.map (fun sf -> normalizePath (Path.Combine(depOptions.ProjectDirectory, sf)))

                        // Check that ALL source files exist - missing files are errors
                        let missingFiles =
                            resolvedPaths
                            |> List.filter (fun p -> not (File.Exists p))

                        match missingFiles with
                        | [] -> Ok (transitiveSources @ resolvedPaths, finalVisited)
                        | missing :: _ ->
                            Error (DependencySourceFileNotFound (depName, missing))

    /// Gets ordered source files from a dependency by reading its .fidproj.
    /// Handles transitive dependencies automatically (deepest first).
    /// Returns Error if dependency cannot be loaded - this is NEVER silently ignored.
    let getDependencySources (depName: string) (depPath: string): Result<string list, SourceResolutionError> =
        match getDependencySourcesRec depName depPath Set.empty [] with
        | Error e -> Error e
        | Ok (sources, _) -> Ok sources

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

    /// Gets all sources in compilation order (dependencies first in order, then project).
    /// Returns absolute, normalized paths for all source files.
    /// Returns Error if any dependency or source file cannot be resolved.
    /// Dependencies with paths are resolved; dependencies without paths are skipped
    /// (they may be package references resolved elsewhere).
    /// Handles transitive dependencies and avoids duplicates from shared dependencies.
    let getAllSourcesInOrder (options: FidprojOptions): Result<string list, SourceResolutionError> =
        // Resolve all dependency sources in order, tracking visited paths across all dependencies
        // This ensures shared transitive dependencies aren't duplicated
        let dependencySourcesResult =
            options.Dependencies
            |> List.filter (fun dep -> dep.Path.IsSome)  // Only process deps with local paths
            |> List.fold (fun acc dep ->
                match acc with
                | Error e -> Error e  // Short-circuit on first error
                | Ok (accSources, visited) ->
                    match getDependencySourcesRec dep.Name dep.Path.Value visited [] with
                    | Error e -> Error e
                    | Ok (depSources, newVisited) -> Ok (accSources @ depSources, newVisited)
            ) (Ok ([], Set.empty))

        match dependencySourcesResult with
        | Error e -> Error e
        | Ok (dependencySources, _) ->
            // Then resolve project sources
            match resolveProjectSources options.ProjectDirectory options.SourceFiles with
            | Error e -> Error e
            | Ok projectSources ->
                Ok (dependencySources @ projectSources)

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
            // Check if it's in any dependency.
            // dep.Path is a fidproj file path (resolved by FidprojLoader);
            // its parent directory is the dependency's source base.
            options.Dependencies
            |> List.tryPick (fun dep ->
                match dep.Path with
                | Some depPath ->
                    let normalizedDep =
                        match Path.GetDirectoryName(normalizePath depPath) with
                        | null -> normalizePath depPath
                        | dir -> normalizePath dir
                    if normalizedSource.StartsWith(normalizedDep + "/") then
                        Some (normalizedSource.Substring(normalizedDep.Length + 1))
                    else
                        None
                | None -> None)

    /// Determines which dependency (if any) a source file belongs to.
    /// Returns None if the file is a project source (not from any dependency).
    let getDependencyForSource (sourceFile: string) (options: FidprojOptions): FidprojDependency option =
        let normalizedSource = normalizePath sourceFile
        options.Dependencies
        |> List.tryFind (fun dep ->
            match dep.Path with
            | Some depPath ->
                let normalizedDep =
                    match Path.GetDirectoryName(normalizePath depPath) with
                    | null -> normalizePath depPath
                    | dir -> normalizePath dir
                normalizedSource.StartsWith(normalizedDep + "/")
            | None -> false)

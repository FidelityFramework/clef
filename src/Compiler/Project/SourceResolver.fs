/// Source file resolution and ordering.
/// Handles Alloy library ordering and project source resolution.
namespace FSharp.Native.Compiler.Project

open System.IO

module SourceResolver =
    /// Normalizes a path to use forward slashes and be absolute.
    let private normalizePath (path: string) =
        Path.GetFullPath(path).Replace('\\', '/')

    /// Gets ordered Alloy source files by reading Alloy.fidproj.
    /// The Alloy.fidproj file is the single source of truth for file ordering.
    let getAlloySources (alloyPath: string): string list =
        let normalizedPath = normalizePath alloyPath
        if not (Directory.Exists normalizedPath) then
            []
        else
            // Look for Alloy.fidproj in the Alloy directory
            let fidprojPath = Path.Combine(normalizedPath, "Alloy.fidproj")
            if not (File.Exists fidprojPath) then
                // Fallback: no fidproj found, return empty
                eprintfn "[SourceResolver] Warning: Alloy.fidproj not found at %s" fidprojPath
                []
            else
                // Load the Alloy project file to get authoritative source ordering
                match FidprojLoader.load fidprojPath with
                | Error msg ->
                    eprintfn "[SourceResolver] Warning: Failed to load Alloy.fidproj: %s" msg
                    []
                | Ok alloyOptions ->
                    // Resolve source paths relative to Alloy directory
                    alloyOptions.SourceFiles
                    |> List.map (fun sf -> Path.Combine(normalizedPath, sf))
                    |> List.filter File.Exists
                    |> List.map normalizePath

    /// Resolves project source files to absolute paths.
    /// Preserves the order as declared in the fidproj.
    let resolveProjectSources (projectDir: string) (sourceFiles: string list): string list =
        let normalizedDir = normalizePath projectDir
        sourceFiles
        |> List.map (fun sf -> normalizePath (Path.Combine(normalizedDir, sf)))
        |> List.filter File.Exists

    /// Gets all sources in compilation order (Alloy first, then project).
    /// Returns absolute, normalized paths for all source files.
    let getAllSourcesInOrder (options: FidprojOptions): string list =
        let alloySources =
            match options.AlloyPath with
            | Some path -> getAlloySources path
            | None -> []

        let projectSources = resolveProjectSources options.ProjectDirectory options.SourceFiles

        alloySources @ projectSources

    /// Checks if a source file belongs to a project.
    /// Compares normalized absolute paths.
    let containsSourceFile (sourceFile: string) (options: FidprojOptions): bool =
        let normalizedSource = normalizePath sourceFile
        let allSources = getAllSourcesInOrder options
        allSources |> List.exists (fun s -> s = normalizedSource)

    /// Finds which project contains a source file.
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

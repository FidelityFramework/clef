/// Unified project checking entry point.
/// Loads, parses, and checks a complete project from .fidproj.
namespace Clef.Compiler.Project

open System.IO
open Clef.Compiler.Syntax
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
// Import Diagnostics types qualified to avoid shadowing Result.Error/Ok
module SGDiag = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

/// Result of checking a complete project.
type ProjectCheckResult = {
    /// Project configuration.
    Options: FidprojOptions
    /// Check result with SemanticGraph.
    CheckResult: SGDiag.CheckResult
    /// All source files that were checked (absolute path, content).
    SourceFiles: (string * string) list
    /// Parse errors by file (if any).
    ParseErrors: Map<string, string list>
}

module ProjectChecker =
    /// Normalizes a path to use forward slashes and be absolute.
    let private normalizePath (path: string) =
        Path.GetFullPath(path).Replace('\\', '/')

    /// Reads a source file, returning (path, content).
    let private readSourceFile (path: string): Result<string * string, string> =
        let normalizedPath = normalizePath path
        if File.Exists normalizedPath then
            try
                let content = File.ReadAllText normalizedPath
                Ok (normalizedPath, content)
            with ex ->
                Error $"Failed to read {normalizedPath}: {ex.Message}"
        else
            Error $"Source file not found: {normalizedPath}"

    /// Parses a source file, returning the parsed input.
    let private parseSourceFile (path: string) (content: string): Result<ParsedInput, string list> =
        match parseStringWithDefaults content path with
        | ParseSuccess parsed -> Ok parsed
        | ParseError errors -> Error errors

    /// Load and check a project from .fidproj path.
    /// - Parses .fidproj
    /// - Resolves all source files (Alloy + project)
    /// - Reads all source content
    /// - Parses and checks with shared type environment
    /// - Returns unified result with consistent paths
    let checkProject (fidprojPath: string): Result<ProjectCheckResult, string> =
        // Load project configuration
        match FidprojLoader.load fidprojPath with
        | Error msg -> Error msg
        | Ok options ->
            // Resolve all source files in order - MUST succeed, no silent fallbacks
            match SourceResolver.getAllSourcesInOrder options with
            | Error srcError ->
                // Source resolution failed - this is a hard error, not a warning
                Error (SourceResolutionError.format srcError)
            | Ok allSourcePaths ->
                if List.isEmpty allSourcePaths then
                    Error $"No source files found for project {options.Name}"
                else
                    // Read all source files
                    let readResults =
                        allSourcePaths
                        |> List.map readSourceFile

                    let readErrors =
                        readResults
                        |> List.choose (function Result.Error e -> Some e | Result.Ok _ -> None)

                    if not (List.isEmpty readErrors) then
                        Error (String.concat "\n" readErrors)
                    else
                        let sourceFiles =
                            readResults
                            |> List.choose (function Result.Ok f -> Some f | Result.Error _ -> None)

                        // Parse all source files
                        let parseResults =
                            sourceFiles
                            |> List.map (fun (path, content) ->
                                match parseSourceFile path content with
                                | Ok parsed -> (path, Result.Ok parsed)
                                | Error errors -> (path, Result.Error errors))

                        let parseErrors =
                            parseResults
                            |> List.choose (fun (path, result) ->
                                match result with
                                | Result.Error errors -> Some (path, errors)
                                | Result.Ok _ -> None)
                            |> Map.ofList

                        let parsedInputs =
                            parseResults
                            |> List.choose (fun (_, result) ->
                                match result with
                                | Result.Ok parsed -> Some parsed
                                | Result.Error _ -> None)

                        if Map.isEmpty parseErrors |> not then
                            // Return partial result with parse errors
                            let emptyGraph: SemanticGraph = {
                                Nodes = Map.empty
                                EntryPoints = []
                                Modules = Map.empty
                                Types = lazy Map.empty
                                Platform = None
                                ModuleClassifications = lazy Map.empty
                                SeqSaturation = lazy Map.empty
                            }
                            Ok {
                                Options = options
                                CheckResult = { Graph = emptyGraph; Diagnostics = []; PlatformContext = None }
                                SourceFiles = sourceFiles
                                ParseErrors = parseErrors
                            }
                        else
                            // Build platform context BEFORE checking
                            // This is critical: the platform context must be set on the graph
                            // BEFORE the nanopass pipeline runs (which includes entry point elaboration)
                            let platformContext =
                                match options.PlatformPath with
                                | Some platformPath ->
                                    let basePlatformCtx = PlatformContext.fromPlatformPath platformPath
                                    // Set FreestandingStartup if this is a freestanding build
                                    if options.DeploymentMode = DeploymentMode.Freestanding then
                                        Some { basePlatformCtx with
                                                 FreestandingStartup = FreestandingStartup.forPlatform basePlatformCtx.PlatformId }
                                    else
                                        Some basePlatformCtx
                                | None -> None

                            // Check all parsed inputs together with platform context
                            // The platform context is set on the graph BEFORE entry point elaboration
                            let checkResult = checkParsedInputsWithPlatform parsedInputs platformContext

                            Ok {
                                Options = options
                                CheckResult = checkResult
                                SourceFiles = sourceFiles
                                ParseErrors = Map.empty
                            }

    /// Check a project with volatile content override.
    /// volatileContent: Map from absolute file path to in-memory content.
    /// Used by LSP servers for unsaved file changes.
    let checkProjectWithVolatile
        (fidprojPath: string)
        (volatileContent: Map<string, string>)
        : Result<ProjectCheckResult, string> =

        // Load project configuration
        match FidprojLoader.load fidprojPath with
        | Error msg -> Error msg
        | Ok options ->
            // Resolve all source files in order - MUST succeed, no silent fallbacks
            match SourceResolver.getAllSourcesInOrder options with
            | Error srcError ->
                // Source resolution failed - this is a hard error, not a warning
                Error (SourceResolutionError.format srcError)
            | Ok allSourcePaths ->
                if List.isEmpty allSourcePaths then
                    Error $"No source files found for project {options.Name}"
                else
                    // Read all source files, using volatile content where available
                    let sourceFiles =
                        allSourcePaths
                        |> List.choose (fun path ->
                            let normalizedPath = normalizePath path
                            match Map.tryFind normalizedPath volatileContent with
                            | Some content ->
                                // Use volatile (unsaved) content
                                Some (normalizedPath, content)
                            | None ->
                                // Read from disk
                                match readSourceFile path with
                                | Result.Ok f -> Some f
                                | Result.Error _ -> None)

                    if List.length sourceFiles <> List.length allSourcePaths then
                        Error "Some source files could not be read"
                    else
                        // Parse all source files
                        let parseResults =
                            sourceFiles
                            |> List.map (fun (path, content) ->
                                match parseSourceFile path content with
                                | Ok parsed -> (path, Result.Ok parsed)
                                | Error errors -> (path, Result.Error errors))

                        let parseErrors =
                            parseResults
                            |> List.choose (fun (path, result) ->
                                match result with
                                | Result.Error errors -> Some (path, errors)
                                | Result.Ok _ -> None)
                            |> Map.ofList

                        let parsedInputs =
                            parseResults
                            |> List.choose (fun (_, result) ->
                                match result with
                                | Result.Ok parsed -> Some parsed
                                | Result.Error _ -> None)

                        // Build platform context BEFORE checking
                        // This is critical: the platform context must be set on the graph
                        // BEFORE the nanopass pipeline runs (which includes entry point elaboration)
                        let platformContext =
                            match options.PlatformPath with
                            | Some platformPath ->
                                let basePlatformCtx = PlatformContext.fromPlatformPath platformPath
                                // Set FreestandingStartup if this is a freestanding build
                                if options.DeploymentMode = DeploymentMode.Freestanding then
                                    Some { basePlatformCtx with
                                             FreestandingStartup = FreestandingStartup.forPlatform basePlatformCtx.PlatformId }
                                else
                                    Some basePlatformCtx
                            | None -> None

                        // Check all parsed inputs together with platform context
                        let checkResult = checkParsedInputsWithPlatform parsedInputs platformContext

                        Ok {
                            Options = options
                            CheckResult = checkResult
                            SourceFiles = sourceFiles
                            ParseErrors = parseErrors
                        }

    /// Get diagnostics for a specific file from a checked project.
    let getDiagnosticsForFile (result: ProjectCheckResult) (filePath: string): SGDiag.Diagnostic list =
        let normalizedPath = normalizePath filePath
        result.CheckResult.Diagnostics
        |> List.filter (fun d -> normalizePath d.Range.File = normalizedPath)

    /// Check if a project check result has any errors.
    let hasErrors (result: ProjectCheckResult): bool =
        not (Map.isEmpty result.ParseErrors) ||
        SGDiag.CheckResult.hasErrors result.CheckResult

    /// Get all error messages from a project check result.
    let getErrorMessages (result: ProjectCheckResult): string list =
        let parseErrorMsgs =
            result.ParseErrors
            |> Map.toList
            |> List.collect (fun (file, errors) ->
                errors |> List.map (fun e -> $"{file}: {e}"))

        let checkErrorMsgs =
            result.CheckResult.Diagnostics
            |> List.filter (fun d -> d.Severity = SGDiag.NativeDiagnosticSeverity.Error)
            |> List.map (fun d -> $"{d.Range.File}:{d.Range.Start.Line}: {d.Message}")

        parseErrorMsgs @ checkErrorMsgs

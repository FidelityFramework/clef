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
    /// Build the PlatformContext from project options: the identity and runtime
    /// facts of the binding's [platform] section. The width dimensions and the
    /// numeric representations are not here: they are declared by the platform
    /// description compiled into the graph and filled in at saturation
    /// (PlatformDeclaration.fill, plan D8, L-13). No word size is read from a
    /// project file and no target is assumed when the section is absent.
    let private buildPlatformContext (options: FidprojOptions) : PlatformContext option =
        // Libraries are substrate-neutral — no platform context needed
        match options.TargetPlatform with
        | TargetPlatform.Library -> None
        | target ->
        let substrateKind =
            match target with
            | TargetPlatform.CPU  -> SubstrateKind.CPU
            | TargetPlatform.FPGA -> SubstrateKind.FPGA
            | TargetPlatform.GPU  -> SubstrateKind.GPU
            | TargetPlatform.NPU  -> SubstrateKind.NPU
            | TargetPlatform.MCU  -> SubstrateKind.CPU
            | TargetPlatform.Library -> SubstrateKind.CPU // unreachable

        // The binding's identity: its [platform] arch when the section is present, else
        // the binding directory's name (an identity, not a platform fact).
        let platformIdOfPath (path: string) : string =
            let directory =
                if Path.HasExtension path then (match Path.GetDirectoryName path with null -> path | d -> d) else path
            directory.Replace("\\", "/").TrimEnd('/').Split('/') |> Array.tryLast |> Option.defaultValue "unknown"

        match options.PlatformPath, options.PlatformMetadata with
        | None, None -> None
        | platformPath, metadata ->
            let platformId =
                metadata
                |> Option.bind (fun m -> m.Arch)
                |> Option.orElse (platformPath |> Option.map platformIdOfPath)
                |> Option.defaultValue "unknown"
            let runtimeModel = metadata |> Option.map (fun m -> m.RuntimeModel)
            let freestanding =
                match runtimeModel, options.DeploymentMode with
                | Some RuntimeModel.Freestanding, _
                | None, DeploymentMode.Freestanding -> FreestandingStartup.forPlatform platformId
                | _ -> None
            Some {
                PlatformId = platformId
                // Filled from the declaration at saturation; empty until then.
                Dimensions = Map.empty
                Representations = Map.empty
                PlatformLibraryPath = platformPath
                Predicates = Map.empty
                FreestandingStartup = freestanding
                SubstrateKind = Some substrateKind
                RuntimeModel = runtimeModel
                AvailableMemorySpaces = []
                DefaultMemorySpace = None
                // Project clock_mhz overrides binding clock_mhz (design may use PLL/divider)
                ClockFrequencyMhz = options.ClockMhzOverride |> Option.orElse (metadata |> Option.bind (fun m -> m.ClockMhz))
                NsPerWeightUnit = metadata |> Option.bind (fun m -> m.NsPerWeightUnit)
            }

    /// One CCS8205 information diagnostic per [platform] key the binding still carries
    /// but the compiler no longer reads (`word_size`): reported at the binding's
    /// project file, never an error, so an older project does not break silently.
    let private unusedPlatformKeyDiagnostics (options: FidprojOptions) : SGDiag.Diagnostic list =
        let file = options.PlatformPath |> Option.defaultValue options.ProjectPath
        options.PlatformMetadata
        |> Option.map (fun m -> m.UnusedKeys)
        |> Option.defaultValue []
        |> List.map (fun key ->
            { SGDiag.Diagnostic.Severity = SGDiag.NativeDiagnosticSeverity.Info
              Code = Clef.Compiler.NativeTypedTree.Expressions.Types.DiagnosticCodes.CCS8205_UnusedPlatformKey
              Message = sprintf "The [platform] key '%s' is not read: width dimensions and representations come from the platform description, not the project file" key
              Range = { File = file; Start = { Line = 0; Column = 0 }; End = { Line = 0; Column = 0 } }
              RelatedNodes = []
              Reachability = SGDiag.ReachabilityContext.Unknown })

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
                                DeclarationRoots = []
                                Modules = Map.empty
                                Types = lazy Map.empty
                                Platform = None
                                ModuleClassifications = lazy Map.empty
                                SeqSaturation = lazy Map.empty
                                FieldRanges = lazy Map.empty
                                ElementRanges = lazy Map.empty
                                Layouts = lazy Map.empty
                                Escaping = lazy Map.empty
                                Edges = []
                            }
                            Ok {
                                Options = options
                                CheckResult = { Graph = emptyGraph; Diagnostics = []; PlatformContext = None }
                                SourceFiles = sourceFiles
                                ParseErrors = parseErrors
                            }
                        else
                            let platformContext = buildPlatformContext options

                            // Check all parsed inputs together with platform context
                            // The platform context is set on the graph BEFORE entry point elaboration
                            let checkedInputs = checkParsedInputsWithPlatform parsedInputs platformContext
                            let checkResult = { checkedInputs with Diagnostics = checkedInputs.Diagnostics @ unusedPlatformKeyDiagnostics options }

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
                        let platformContext = buildPlatformContext options

                        // Check all parsed inputs together with platform context
                        let checkedInputs = checkParsedInputsWithPlatform parsedInputs platformContext
                        let checkResult = { checkedInputs with Diagnostics = checkedInputs.Diagnostics @ unusedPlatformKeyDiagnostics options }

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
    /// Uses effective severity (unreachable errors demoted to info).
    let getErrorMessages (result: ProjectCheckResult): string list =
        let parseErrorMsgs =
            result.ParseErrors
            |> Map.toList
            |> List.collect (fun (file, errors) ->
                errors |> List.map (fun e -> $"{file}: {e}"))

        let checkErrorMsgs =
            result.CheckResult.Diagnostics
            |> List.filter (fun d -> SGDiag.Diagnostic.effectiveSeverity d = SGDiag.NativeDiagnosticSeverity.Error)
            |> List.map (fun d -> $"{d.Range.File}:{d.Range.Start.Line}: {d.Message}")

        parseErrorMsgs @ checkErrorMsgs

    /// Check if a project check result has any warnings.
    /// Uses effective severity (unreachable warnings demoted to info).
    let hasWarnings (result: ProjectCheckResult): bool =
        result.CheckResult.Diagnostics
        |> List.exists (fun d -> SGDiag.Diagnostic.effectiveSeverity d = SGDiag.NativeDiagnosticSeverity.Warning)

    /// Get all warning messages from a project check result.
    /// Uses effective severity (unreachable warnings demoted to info).
    let getWarningMessages (result: ProjectCheckResult): string list =
        result.CheckResult.Diagnostics
        |> List.filter (fun d -> SGDiag.Diagnostic.effectiveSeverity d = SGDiag.NativeDiagnosticSeverity.Warning)
        |> List.map (fun d -> $"{d.Range.File}:{d.Range.Start.Line}: warning {d.Code}: {d.Message}")

    /// Get all info messages from a project check result.
    /// Includes intrinsic info AND demoted unreachable diagnostics.
    let getInfoMessages (result: ProjectCheckResult): string list =
        result.CheckResult.Diagnostics
        |> List.filter (fun d -> SGDiag.Diagnostic.effectiveSeverity d = SGDiag.NativeDiagnosticSeverity.Info)
        |> List.map (fun d ->
            let reachTag =
                match d.Reachability with
                | SGDiag.Unreachable -> " [unreachable]"
                | _ -> ""
            $"{d.Range.File}:{d.Range.Start.Line}: info {d.Code}: {d.Message}{reachTag}")

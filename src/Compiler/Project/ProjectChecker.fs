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
    /// Exact source and metadata bytes consumed by this check, captured before parsing.
    InputFiles: (string * string) list
    /// Selected binding's declared backend, parsed from the same captured metadata.
    PlatformTarget: TargetPlatform option
    /// Parse errors by file (if any).
    ParseErrors: Map<string, string list>
}

type internal PreparedProject = private {
    Options: FidprojOptions
    PlatformSources: Set<string>
    PlatformTarget: TargetPlatform option
    Sources: (string * string) list
    Inputs: (string * string) list
}

module ProjectChecker =
    /// Build the PlatformContext from project options: the identity and runtime
    /// facts of the binding's [platform] section. The width dimensions and the
    /// numeric representations are not here: they are declared by the platform
    /// description compiled into the graph and filled in at saturation
    /// (PlatformDeclaration.fill, plan D8, L-13). No word size is read from a
    /// project file and no target is assumed when the section is absent.
    let private buildPlatformContext (options: FidprojOptions) (platformSources: Set<string>) : PlatformContext option =
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
                EndpointReturns = Map.empty
                PlatformLibraryPath = platformPath |> Option.orElse (metadata |> Option.map (fun _ -> options.ProjectPath))
                PlatformDescription = metadata |> Option.bind (fun m -> m.Description)
                PlatformSourcePaths = platformSources
                PlatformArchitecture = metadata |> Option.bind (fun m -> m.Arch)
                PlatformOS = metadata |> Option.bind (fun m -> m.OS)
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

    /// Aliases may identify the same source, but cannot assign it two texts.
    let internal normalizeOverrides (volatileContent: Map<string, string>) =
        try
            volatileContent |> Map.toList |> List.fold (fun result (path, text) ->
                result |> Result.bind (fun inputs ->
                    let path = normalizePath path
                    match Map.tryFind path inputs with
                    | Some previous when previous <> text -> Error $"Conflicting volatile input aliases: {path}"
                    | _ -> Ok(Map.add path text inputs))) (Ok Map.empty)
        with error -> Error $"Invalid volatile input path: {error.Message}"

    /// Only declarations owned by this executable can be reported as unused helpers.
    /// Dependency/platform sources remain public library surface, even when compiled together.
    let private ownedApplicationSources (options: FidprojOptions) =
        match options.TargetPlatform, options.DeploymentMode with
        | TargetPlatform.Library, _ | _, DeploymentMode.Library -> Set.empty
        | _ -> options.SourceFiles |> List.map (fun file -> normalizePath (Path.Combine(options.ProjectDirectory, file))) |> Set.ofList

    /// Capture every loader read once. Dependency/platform options and the checker
    /// consume these same bytes; no post-check discovery or cross-edit hash reuse.
    let internal prepare (fidprojPath: string) (volatileContent: Map<string, string>) : Result<PreparedProject, string> =
        try
            let mutable diskInputs = Map.empty
            let read path =
                let path = normalizePath path
                match Map.tryFind path diskInputs with
                | Some text -> text
                | None ->
                    let text = File.ReadAllText path
                    diskInputs <- Map.add path text diskInputs
                    text
            let overrides = normalizeOverrides volatileContent |> Result.defaultWith invalidOp
            match FidprojLoader.loadWith read fidprojPath with
            | Error error -> Error error
            | Ok options ->
                match SourceResolver.getSourcesAndLibrariesWith (FidprojLoader.loadWith read) options with
                | Error error -> Error(SourceResolutionError.format error)
                | Ok resolved when List.isEmpty resolved.SourcePaths -> Error $"No source files found for project {options.Name}"
                | Ok resolved ->
                    let platformTarget =
                        match options.PlatformPath with
                        | None -> Ok None
                        | Some path -> FidprojLoader.loadWith read path |> Result.map (fun platform -> Some platform.TargetPlatform)
                    match platformTarget with
                    | Error error -> Error error
                    | Ok platformTarget ->
                        let sources = resolved.SourcePaths |> List.map (fun path ->
                            let path = normalizePath path
                            let text =
                                match Map.tryFind path overrides, Map.tryFind path diskInputs with
                                | Some text, Some metadata when text <> metadata ->
                                    invalidOp $"Volatile source conflicts with captured project metadata: {path}"
                                | Some text, _ -> text
                                | None, _ -> read path
                            path, text)
                        // Detect edits during capture. All subsequent semantic work uses
                        // this immutable capture, even when files change after validation.
                        let changed = diskInputs |> Map.toList |> List.tryFind (fun (path, text) -> File.ReadAllText path <> text)
                        match changed with
                        | Some (path, _) -> Error $"Project input changed while being captured: {path}"
                        | None ->
                            Ok { Options = { options with LinkedLibraries = resolved.LinkedLibraries }
                                 PlatformSources = resolved.PlatformSourcePaths
                                 PlatformTarget = platformTarget
                                 Sources = sources
                                 Inputs = List.fold (fun inputs (path, text) -> Map.add path text inputs) diskInputs sources |> Map.toList }
        with error -> Error $"Could not capture project inputs: {error.Message}"

    let private emptyGraph : SemanticGraph = {
        Nodes = Map.empty; DeclarationRoots = []; Modules = Map.empty
        Types = lazy Map.empty; Platform = None; ModuleClassifications = lazy Map.empty
        FieldRanges = lazy Map.empty; ElementRanges = lazy Map.empty; Layouts = lazy Map.empty
        StaticStringPool = None; LiteralStorage = Map.empty; Escaping = lazy Map.empty
        Codata = lazy Codata.empty; Edges = []; WitnessProvenance = None
    }

    let internal checkPrepared (prepared: PreparedProject) : ProjectCheckResult =
        Clef.Compiler.CheckExecution.synchronized (fun () ->
            let parsed = prepared.Sources |> List.map (fun (path, content) -> path, parseStringWithDefaults content path)
            let errors = parsed |> List.choose (function path, ParseError errors -> Some(path, errors) | _ -> None) |> Map.ofList
            // A malformed file does not authorize checking a silently shortened project.
            let checkedInputs: SGDiag.CheckResult =
                if not (Map.isEmpty errors) then
                    { Graph = emptyGraph; Diagnostics = []; PlatformContext = None }
                else
                    let inputs = parsed |> List.choose (function _, ParseSuccess input -> Some input | _ -> None)
                    checkParsedInputsWithPlatformAndSources inputs
                        (buildPlatformContext prepared.Options prepared.PlatformSources)
                        (ownedApplicationSources prepared.Options)
            { Options = prepared.Options
              CheckResult = { checkedInputs with Diagnostics = checkedInputs.Diagnostics @ unusedPlatformKeyDiagnostics prepared.Options }
              SourceFiles = prepared.Sources; InputFiles = prepared.Inputs
              PlatformTarget = prepared.PlatformTarget; ParseErrors = errors })

    /// Existing synchronous API uses the same immutable capture and process gate.
    let checkProjectWithVolatile fidprojPath volatileContent : Result<ProjectCheckResult, string> =
        prepare fidprojPath volatileContent |> Result.map checkPrepared

    let checkProject fidprojPath = checkProjectWithVolatile fidprojPath Map.empty

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

    /// CCS owns admission and the sole graph-to-revision publication boundary.
    /// A reader receives Fidelity.PSG; it does not invoke Publication itself.
    let publish (result: ProjectCheckResult) : Result<Fidelity.PSG.Revision, string> =
        Clef.Compiler.CheckExecution.synchronized (fun () ->
            if hasErrors result then Error(String.concat "\n" (getErrorMessages result))
            else
                match result.CheckResult.Graph.Platform with
                | None -> Error "A checked platform context is required to publish a project revision."
                | Some platform ->
                    Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish platform result.CheckResult.Graph
                    |> Result.mapError (fun failures -> sprintf "%A" failures))

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

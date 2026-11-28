module Clef.Compiler.Utilities.HostTools

open System
open System.IO

let samePath left right =
    String.Equals(Path.GetFullPath left, Path.GetFullPath right,
                  if OperatingSystem.IsWindows() then StringComparison.OrdinalIgnoreCase else StringComparison.Ordinal)

let solverName = if OperatingSystem.IsWindows() then "cvc5.exe" else "cvc5"

let solverToolchainPaths =
    let root =
        if OperatingSystem.IsWindows() then
            Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.LocalApplicationData, "Clef", "toolchains")
        else Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.UserProfile, ".local", "toolchains")
    [ yield Path.Combine(root, "cvc5-1.3.0", "bin", solverName)
      if OperatingSystem.IsLinux() then
          for node in ["one"; "two"; "three"] do
              yield Path.Combine("/mnt/apps", "gpu-" + node, "toolchains", "cvc5-1.3.0", "bin", solverName)
          yield Path.Combine(Path.GetTempPath(), "cvc5-toolchain", "bin", solverName) ]

let resolveSolver (pathVariable: string | null) (exists: string -> bool) =
    let path = match pathVariable with null -> "" | value -> value
    let candidates =
        path.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
        |> Array.filter (String.IsNullOrWhiteSpace >> not)
        |> Array.map (fun directory -> Path.Combine(directory, solverName))
        |> Array.toList
    candidates @ solverToolchainPaths |> List.tryFind exists |> Option.defaultValue solverName

let findSolver pathVariable =
    resolveSolver pathVariable (fun path ->
        File.Exists path && (not (OperatingSystem.IsLinux()) || LinuxHostTools.canExecute path))

//=============================================================================
// TOOL IDENTITY (#204)
//=============================================================================

/// What a solver binary *is*, as the tool manifest says. A host adapter that
/// counts solver spawns keys on this identity rather than on a file name, so a
/// renamed or symlinked solver is still the tool the manifest resolved.
type ToolIdentity =
    { Name: string
      Executable: string
      ManifestPath: string
      Version: string option }

/// One manifest line: name<TAB>executable[<TAB>version]. Blank lines, lines
/// starting with '#', and rows with an empty name or executable carry no record.
/// Relative executable paths resolve against the manifest's directory when known.
let parseToolManifest (manifestPath: string) (lines: string list) : Map<string, ToolIdentity> =
    let baseDir =
        if String.IsNullOrWhiteSpace manifestPath then None
        else
            match Path.GetDirectoryName(Path.GetFullPath manifestPath) with
            | null -> None
            | dir when String.IsNullOrWhiteSpace dir -> None
            | dir -> Some dir
    let resolveExecutable (executable: string) =
        if Path.IsPathRooted executable then Path.GetFullPath executable
        else
            match baseDir with
            | Some dir -> Path.GetFullPath(Path.Combine(dir, executable))
            | None -> Path.GetFullPath executable
    let record name executable version =
        let full = resolveExecutable executable
        (full, { Name = name; Executable = full; ManifestPath = manifestPath; Version = version })
    lines
    |> List.choose (fun line ->
        let line = line.Trim()
        if line = "" || line.StartsWith "#" then None
        else
            match line.Split '\t' |> Array.map (fun part -> part.Trim()) with
            | [| name; executable |] when not (String.IsNullOrWhiteSpace name) && not (String.IsNullOrWhiteSpace executable) ->
                Some (record name executable None)
            | parts when parts.Length > 1 && not (String.IsNullOrWhiteSpace parts[0]) && not (String.IsNullOrWhiteSpace parts[1]) ->
                let versionText = String.Join(" ", parts |> Array.skip 2).Trim()
                let version = if String.IsNullOrWhiteSpace versionText then None else Some versionText
                Some (record parts[0] parts[1] version)
            | _ -> None)
    |> Map.ofList

/// The manifest this host declares its tools in. Absent configuration means no
/// manifest, never a guessed one.
let toolManifestPath () =
    match Environment.GetEnvironmentVariable "CLEF_TOOL_MANIFEST" with
    | null | "" -> ""
    | path -> path

/// Fail-closed manifest reader returning distinct errors when the manifest
/// path is unconfigured or does not exist on disk.
let readToolManifestResult (path: string) : Result<Map<string, ToolIdentity>, string> =
    if String.IsNullOrWhiteSpace path then
        Error "CLEF_TOOL_MANIFEST is not configured."
    elif not (File.Exists path) then
        Error (sprintf "Tool manifest does not exist: %s" path)
    else
        Ok (parseToolManifest path (File.ReadAllLines path |> Array.toList))

let readToolManifest (path: string) : Map<string, ToolIdentity> =
    match readToolManifestResult path with
    | Ok manifest -> manifest
    | Error _ -> Map.empty

let private fileDigest (path: string) : string option =
    try Some (File.ReadAllBytes path |> System.Security.Cryptography.SHA256.HashData |> System.Convert.ToHexString)
    with _ -> None

let private isBareCommand (path: string) : bool =
    not (Path.IsPathRooted path)
    && not (path.Contains Path.DirectorySeparatorChar)
    && not (path.Contains Path.AltDirectorySeparatorChar)

let private resolveCommandOnPath (pathVariable: string | null) (command: string) : string option =
    let envPath = match pathVariable with null -> "" | value -> value
    envPath.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
    |> Array.filter (String.IsNullOrWhiteSpace >> not)
    |> Array.map (fun dir -> Path.Combine(dir, command))
    |> Array.tryFind (fun candidate ->
        File.Exists candidate && (not (OperatingSystem.IsLinux()) || LinuxHostTools.canExecute candidate))

let private resolveExecutablePath (path: string) : string option =
    if String.IsNullOrWhiteSpace path then None
    elif isBareCommand path then
        resolveCommandOnPath (Environment.GetEnvironmentVariable "PATH") path
        |> Option.map Path.GetFullPath
    else
        Some (Path.GetFullPath path)

/// Resolve a spawned path (absolute, relative, or bare command on PATH) to the
/// manifest record that owns it. An exact path match wins; otherwise the file's
/// own bytes identify it, which is what makes a renamed or symlinked solver
/// report the identity the manifest recorded.
let resolveToolIdentity (manifest: Map<string, ToolIdentity>) (path: string) : ToolIdentity option =
    match resolveExecutablePath path with
    | None -> None
    | Some full ->
        match Map.tryFind full manifest with
        | Some identity -> Some identity
        | None ->
            if not (File.Exists full) then None
            else
                let digest = fileDigest full
                manifest
                |> Map.toSeq
                |> Seq.tryFind (fun (_, identity) ->
                    match digest, fileDigest identity.Executable with
                    | Some left, Some right -> left = right
                    | _ -> false)
                |> Option.map snd

let private isSolverIdentity (identity: ToolIdentity) : bool =
    String.Equals(identity.Name, "cvc5", StringComparison.OrdinalIgnoreCase)

/// Does this spawned executable belong to the cvc5 solver named by a manifest the
/// caller already resolved? A host adapter counts spawns through this, never
/// through a file-name test; manifested non-solver tools (such as clang) return false.
let isSolverSpawnWith (manifest: Map<string, ToolIdentity>) (path: string) : bool =
    match resolveToolIdentity manifest path with
    | Some identity -> isSolverIdentity identity
    | None -> false

/// Fail-closed solver spawn predicate using the host-configured tool manifest.
/// Returns Error when CLEF_TOOL_MANIFEST is unset or unreadable rather than
/// silently reporting false.
let isSolverSpawnResult (path: string) : Result<bool, string> =
    readToolManifestResult (toolManifestPath ())
    |> Result.map (fun manifest -> isSolverSpawnWith manifest path)

/// Convenience boolean projection for callers that already validated manifest presence.
let isSolverSpawn (path: string) : bool =
    match isSolverSpawnResult path with
    | Ok matched -> matched
    | Error _ -> false

//=============================================================================
// SOLVER TRANSPORT
//=============================================================================

// The host runs cvc5. Callers receive answer lines or the transport's refusal
// text; what an answer means for an obligation is decided by the caller.

let private solverExecutable () =
    match System.Environment.GetEnvironmentVariable "CLEF_CVC5" with
    | null | "" -> findSolver (System.Environment.GetEnvironmentVariable "PATH"), true
    | path ->
        let resolved = resolveExecutablePath path |> Option.defaultValue path
        resolved, false

type private SolverRun =
    | Answered of Result<string list, string>
    | TimedOut
    | Unavailable of string

let internal solverStartInfo (solver: string) (tempPath: string) : System.Diagnostics.ProcessStartInfo =
    let psi = System.Diagnostics.ProcessStartInfo(solver)
    psi.ArgumentList.Add "--lang"
    psi.ArgumentList.Add "smt2"
    psi.ArgumentList.Add tempPath
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.UseShellExecute <- false
    psi

let private isPhaseTimingEnabled () =
    System.Environment.GetEnvironmentVariable "CLEF_PHASE_TIMING" = "1"

let private countCheckSatScopes (text: string) =
    let needle = "(check-sat)"
    let nLen = needle.Length
    let rec matchesAt start offset =
        if offset = nLen then true
        elif text[start + offset] = needle[offset] then matchesAt start (offset + 1)
        else false
    let rec loop i acc =
        if i + nLen > text.Length then acc
        elif matchesAt i 0 then loop (i + nLen) (acc + 1)
        else loop (i + 1) acc
    loop 0 0

/// One cvc5 process over one query, optionally bounded by a wall-clock limit.
let private executeAt (tempDir: string) (solver: string) (limit: System.TimeSpan option) (cacheEntries: int) (text: string) : SolverRun =
    let tempPath = Path.Combine(tempDir, sprintf "clef-proof-%s.smt2" (System.Guid.NewGuid().ToString("N")))
    try
        File.WriteAllText(tempPath, text + "\n")
        let psi = solverStartInfo solver tempPath
        use proc = new System.Diagnostics.Process(StartInfo = psi)
        let started =
            try
                if proc.Start() then
                    if isPhaseTimingEnabled () then
                        Console.Error.WriteLine(
                            sprintf "[HostTools.cvc5] kind=solve binary=%s scopes=%d cache_entries=%d"
                                solver (countCheckSatScopes text) cacheEntries)
                    Ok ()
                else Error "Failed to start cvc5 process"
            with
            | :? System.ComponentModel.Win32Exception as ex -> Error ex.Message
            | :? System.UnauthorizedAccessException as ex -> Error ex.Message
        match started with
        | Error reason -> Unavailable (sprintf "Could not start solver '%s': %s" solver reason)
        | Ok () ->
            let stdoutTask = proc.StandardOutput.ReadToEndAsync()
            let stderrTask = proc.StandardError.ReadToEndAsync()
            let exited =
                match limit with
                | None -> proc.WaitForExit(); true
                | Some limit -> proc.WaitForExit limit
            if not exited then
                // The process may exit between the wait and the kill; it is still past its limit.
                try proc.Kill true with :? System.InvalidOperationException -> ()
                proc.WaitForExit()
                TimedOut
            else
                proc.WaitForExit()
                let stdout = stdoutTask.Result
                let stderr = stderrTask.Result
                if proc.ExitCode <> 0 then
                    Answered (Error (sprintf "cvc5 exited with code %d: %s" proc.ExitCode (stderr.Trim())))
                elif not (System.String.IsNullOrWhiteSpace stderr) then
                    Answered (Error (sprintf "cvc5 reported stderr: %s" (stderr.Trim())))
                else
                    stdout.Split([| '\r'; '\n' |], System.StringSplitOptions.RemoveEmptyEntries)
                    |> Array.map (fun line -> line.Trim())
                    |> Array.filter (fun line -> line <> "")
                    |> Array.toList
                    |> Ok
                    |> Answered
    finally
        if File.Exists tempPath then File.Delete tempPath

let private execute (solver: string) (limit: System.TimeSpan option) (cacheEntries: int) (text: string) : SolverRun =
    let tempDir =
        match System.Environment.GetEnvironmentVariable "CLEF_PROOF_TEMP_DIR" with
        | null | "" -> Path.GetTempPath()
        | value when System.String.IsNullOrWhiteSpace value -> Path.GetTempPath()
        | value -> value
    executeAt tempDir solver limit cacheEntries text

/// Completed answers only. A query cut off by a budget is never recorded.
let private solverCache =
    System.Collections.Concurrent.ConcurrentDictionary<string * string, string list>()

let private tryCachedAnswer solver cacheAllowed query =
    match (if cacheAllowed then solverCache.TryGetValue((solver, query)) else (false, Unchecked.defaultof<_>)) with
    | true, answer ->
        if isPhaseTimingEnabled () then
            Console.Error.WriteLine(
                sprintf "[HostTools.cvc5] kind=cache_hit binary=%s cache_entries=%d"
                    solver solverCache.Count)
        Some answer
    | _ -> None

let private rememberAnswer solver cacheAllowed query answer =
    if cacheAllowed then
        answer |> Result.iter (fun lines -> solverCache.TryAdd((solver, query), lines) |> ignore)
    answer

let private runUnbounded solver query =
    match execute solver None solverCache.Count query with
    | Answered answer -> answer
    | Unavailable reason -> Error reason
    | TimedOut -> Error "An unbounded cvc5 run cannot exceed a limit"

/// The compiler run: unbounded.
let internal runSolver (query: string) : Result<string list, string> =
    let solver, cacheAllowed = solverExecutable ()
    match tryCachedAnswer solver cacheAllowed query with
    | Some answer -> Ok answer
    | None -> runUnbounded solver query |> rememberAnswer solver cacheAllowed query

let internal frameQueries (queries: string list) =
    let rec freshPrefix ordinal =
        let prefix = sprintf "__clef_query_%d_" ordinal
        if queries |> List.exists (fun query -> query.Contains(prefix, StringComparison.Ordinal)) then
            freshPrefix (ordinal + 1)
        else prefix
    let prefix = freshPrefix 0
    let marker ordinal side = sprintf "\"%s%d_%s\"" prefix ordinal side
    let text =
        queries
        |> List.mapi (fun ordinal query ->
            sprintf "(echo %s)\n%s\n(echo %s)" (marker ordinal "begin") query (marker ordinal "end"))
        |> String.concat "\n(reset)\n"
    marker, text

let private isVerdict = function
    | "sat" | "unsat" | "unknown" -> true
    | _ -> false

let private isSingleAnswer = function
    | Ok [ verdict ] -> isVerdict verdict
    | _ -> false

let private readAnswers marker count lines =
    let rec read ordinal answers = function
        | [] when ordinal = count -> Ok (List.rev answers)
        | before :: verdict :: after :: rest
            when ordinal < count && before = marker ordinal "begin" && after = marker ordinal "end" &&
                 isVerdict verdict ->
            read (ordinal + 1) ([verdict] :: answers) rest
        | _ -> Error "cvc5 returned an invalid framed answer batch"
    read 0 [] lines

type internal BudgetedAnswer =
    { Answer: Result<string list, string>
      SolverUnavailable: bool }

type private ChunkAttempt =
    | Returned of BudgetedAnswer
    | DeadlineReached of string

let private response answer = { Answer = answer; SolverUnavailable = false }

let private runChunk solve queries =
    let memberAnswer = function
        | Returned answer -> answer
        | DeadlineReached reason -> response (Error reason)
    let replay () = queries |> List.map (fun query -> query, solve query)
    let results attempts = attempts |> List.map (fun (query, attempt) -> query, memberAnswer attempt)
    match queries with
    | [ query ] -> [ (query, solve query |> memberAnswer) ]
    | _ ->
        let marker, text = frameQueries queries
        match solve text with
        | DeadlineReached _ ->
            // A deadline on the whole frame does not identify a slow member.
            replay () |> results
        | Returned frame ->
            match frame.Answer |> Result.bind (readAnswers marker queries.Length) with
            | Ok answers -> List.zip queries (answers |> List.map (Ok >> response))
            | Error frameReason ->
                let attempts = replay ()
                let reproduced =
                    attempts |> List.exists (function
                        | _, Returned item -> not (isSingleAnswer item.Answer)
                        | _, DeadlineReached _ -> false)
                if reproduced then results attempts
                else
                    // A cutoff did not observe the malformed frame on any singleton.
                    attempts |> List.map (function
                        | query, DeadlineReached reason -> query, response (Error reason)
                        | query, Returned _ -> query, { frame with Answer = Error frameReason })

let private runChunks solve queries =
    queries
    |> List.chunkBySize 64
    |> List.map (fun chunk -> async { return runChunk solve chunk })
    |> fun chunks -> Async.Parallel(chunks, maxDegreeOfParallelism = 4)
    |> Async.RunSynchronously
    |> Array.toList
    |> List.concat

/// Resolve independent, single-verdict compiler queries. Chunk framing
/// changes transport only. The caller associates answers to obligation occurrences.
let internal runSolverBatch (queries: string list) : Map<string, Result<string list, string>> =
    if queries.IsEmpty then Map.empty
    else
        let solver, cacheAllowed = solverExecutable ()
        let hits, misses =
            queries
            |> List.distinct
            |> List.map (fun query -> query, tryCachedAnswer solver cacheAllowed query)
            |> List.partition (snd >> Option.isSome)
        let cached = hits |> List.choose (fun (query, answer) -> answer |> Option.map (fun lines -> query, Ok lines))
        let fresh =
            misses
            |> List.map fst
            |> runChunks (runUnbounded solver >> response >> Returned)
            |> List.map (fun (query, item) -> query, rememberAnswer solver (cacheAllowed && isSingleAnswer item.Answer) query item.Answer)
        Map.ofList (cached @ fresh)

let private milliseconds (span: System.TimeSpan) = int64 span.TotalMilliseconds

/// A design-time invocation shares its wall-clock budget across all stages and replays.
let internal budgetedSolver (perQuery: System.TimeSpan) (total: System.TimeSpan) =
    let clock = System.Diagnostics.Stopwatch.StartNew()
    let attempt query =
        let remaining = total - clock.Elapsed
        if remaining <= System.TimeSpan.Zero then
            DeadlineReached (sprintf "cvc5 was not run: the design-time budget of %d ms was exhausted" (milliseconds total))
        else
            let solver, _ = solverExecutable ()
            let cutByTotal = remaining < perQuery
            match execute solver (Some (if cutByTotal then remaining else perQuery)) solverCache.Count query with
            | Answered answer -> Returned (response answer)
            | Unavailable reason -> Returned { Answer = Error reason; SolverUnavailable = true }
            | TimedOut when cutByTotal ->
                DeadlineReached (sprintf "cvc5 did not answer before the design-time budget of %d ms was exhausted" (milliseconds total))
            | TimedOut ->
                DeadlineReached (sprintf "cvc5 did not answer within the per-query limit of %d ms" (milliseconds perQuery))
    fun queries -> queries |> List.distinct |> runChunks attempt |> Map.ofList

let internal omittedBatchQuery = "cvc5 batch omitted a requested query"

/// Only answers consumed by this occurrence can mark its solver unavailable.
let internal withBudgetedAnswers (answers: Map<string, BudgetedAnswer>) evaluate =
    let mutable unavailable = false
    let resolve query =
        match Map.tryFind query answers with
        | None -> Error omittedBatchQuery
        | Some item ->
            unavailable <- unavailable || item.SolverUnavailable
            item.Answer
    let value = evaluate resolve
    value, unavailable

/// The identity of the solver this run resolves, manifest first. Returns Error
/// when no manifest is configured, the manifest cannot be read, or the resolved
/// executable is not registered as a cvc5 solver in the manifest — never
/// fabricating an unmanifested identity.
let solverIdentity () : Result<ToolIdentity, string> =
    let executable, _ = solverExecutable ()
    readToolManifestResult (toolManifestPath ())
    |> Result.bind (fun manifest ->
        match resolveToolIdentity manifest executable with
        | Some identity when isSolverIdentity identity -> Ok identity
        | Some identity ->
            Error (sprintf "Resolved executable '%s' is manifested as '%s', not cvc5." executable identity.Name)
        | None ->
            Error (sprintf "Resolved solver executable '%s' is not registered in tool manifest." executable))

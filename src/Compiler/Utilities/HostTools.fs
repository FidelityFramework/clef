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
// SOLVER TRANSPORT
//=============================================================================

// The host runs cvc5. Callers receive answer lines or the transport's refusal
// text; what an answer means for an obligation is decided by the caller.

let private solverExecutable () =
    match System.Environment.GetEnvironmentVariable "CLEF_CVC5" with
    | null | "" -> findSolver (System.Environment.GetEnvironmentVariable "PATH"), true
    | path -> path, false

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

/// One cvc5 process over one query, optionally bounded by a wall-clock limit.
let private executeAt (tempDir: string) (solver: string) (limit: System.TimeSpan option) (text: string) : SolverRun =
    let tempPath = Path.Combine(tempDir, sprintf "clef-proof-%s.smt2" (System.Guid.NewGuid().ToString("N")))
    try
        File.WriteAllText(tempPath, text + "\n")
        let psi = solverStartInfo solver tempPath
        use proc = new System.Diagnostics.Process(StartInfo = psi)
        let started =
            try
                if proc.Start() then Ok () else Error "Failed to start cvc5 process"
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

let private execute (solver: string) (limit: System.TimeSpan option) (text: string) : SolverRun =
    let tempDir =
        match System.Environment.GetEnvironmentVariable "CLEF_PROOF_TEMP_DIR" with
        | null | "" -> Path.GetTempPath()
        | value when System.String.IsNullOrWhiteSpace value -> Path.GetTempPath()
        | value -> value
    executeAt tempDir solver limit text

/// Completed answers only. A query cut off by a budget is never recorded.
let private solverCache =
    System.Collections.Concurrent.ConcurrentDictionary<string * string, string list>()

let private tryCachedAnswer solver cacheAllowed query =
    match (if cacheAllowed then solverCache.TryGetValue((solver, query)) else (false, Unchecked.defaultof<_>)) with
    | true, answer -> Some answer
    | _ -> None

let private rememberAnswer solver cacheAllowed query answer =
    if cacheAllowed then
        answer |> Result.iter (fun lines -> solverCache.TryAdd((solver, query), lines) |> ignore)
    answer

let private runUnbounded solver query =
    match execute solver None query with
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

let private runChunk solve queries =
    match queries with
    | [ query ] -> [ (query, solve query) ]
    | _ ->
        let marker, text = frameQueries queries
        match solve text |> Result.bind (readAnswers marker queries.Length) with
        | Ok answers -> List.zip queries (List.map Ok answers)
        | Error batchReason ->
            // Replay isolates a failed member. If the failure cannot be
            // reproduced, the batch evidence remains unavailable for every item.
            let replay = queries |> List.map (fun query -> query, solve query)
            if replay |> List.exists (snd >> isSingleAnswer >> not) then replay
            else queries |> List.map (fun query -> query, Error batchReason)

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
            |> List.chunkBySize 64
            |> List.map (fun chunk -> async { return runChunk (runUnbounded solver) chunk })
            |> fun chunks -> Async.Parallel(chunks, maxDegreeOfParallelism = 4)
            |> Async.RunSynchronously
            |> Array.toList
            |> List.concat
            |> List.map (fun (query, answer) -> query, rememberAnswer solver (cacheAllowed && isSingleAnswer answer) query answer)
        Map.ofList (cached @ fresh)

let private milliseconds (span: System.TimeSpan) = int64 span.TotalMilliseconds

/// A design-time run: every query within `perQuery`, the run within `total`.
let internal budgetedSolver (perQuery: System.TimeSpan) (total: System.TimeSpan) =
    let clock = System.Diagnostics.Stopwatch.StartNew()
    let mutable unavailable = false
    let solve query =
        // A previously successful query does not establish that the currently
        // configured solver is still present and executable.
        let remaining = total - clock.Elapsed
        if remaining <= System.TimeSpan.Zero then
            Error (sprintf "cvc5 was not run: the design-time budget of %d ms was exhausted" (milliseconds total))
        else
            let solver, _ = solverExecutable ()
            let cutByTotal = remaining < perQuery
            match execute solver (Some (if cutByTotal then remaining else perQuery)) query with
            | Answered answer -> answer
            | Unavailable reason ->
                unavailable <- true
                Error reason
            | TimedOut when cutByTotal ->
                Error (sprintf "cvc5 did not answer before the design-time budget of %d ms was exhausted" (milliseconds total))
            | TimedOut ->
                Error (sprintf "cvc5 did not answer within the per-query limit of %d ms" (milliseconds perQuery))
    solve, (fun () -> unavailable), (fun () -> unavailable <- false)

// SPDX-License-Identifier: MIT

/// Obligation Solver Batch -- the Zone B host solver adapter.
///
/// Everything in this module touches the host: cvc5 process invocation,
/// temporary query files, the process-wide `solverCache` of completed answers,
/// and the sentinel-framed batch runner that executes `(reset)`-separated
/// queries in one cvc5 process. `ObligationDischarge` builds the queries and
/// interprets the verdicts; this module only runs them.
module Clef.Compiler.Nanopass.ObligationSolverBatch

open System.IO

let internal solverExecutable () =
    match System.Environment.GetEnvironmentVariable "CLEF_CVC5" with
    | null | "" -> Clef.Compiler.Utilities.HostTools.findSolver (System.Environment.GetEnvironmentVariable "PATH"), true
    | path -> path, false

type private SolverRun =
    | Answered of Result<string list, string>
    | TimedOut
    | Unavailable of string

/// `perQueryLimit` bounds each `(check-sat)` inside the file with cvc5's
/// `--tlimit-per`; a query that reaches it prints `unknown` and cvc5 continues
/// with the next `(reset)`-separated query.
let internal solverStartInfo (solver: string) (perQueryLimit: System.TimeSpan option) (tempPath: string) : System.Diagnostics.ProcessStartInfo =
    let psi = System.Diagnostics.ProcessStartInfo(solver)
    psi.ArgumentList.Add "--lang"
    psi.ArgumentList.Add "smt2"
    match perQueryLimit with
    | Some limit -> psi.ArgumentList.Add(sprintf "--tlimit-per=%d" (max 1L (int64 limit.TotalMilliseconds)))
    | None -> ()
    psi.ArgumentList.Add tempPath
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.UseShellExecute <- false
    psi

/// One cvc5 process over one file, optionally bounded per query and by a
/// wall-clock limit on the whole process.
let private executeAt (tempDir: string) (solver: string) (perQueryLimit: System.TimeSpan option) (limit: System.TimeSpan option) (text: string) : SolverRun =
    let tempPath = Path.Combine(tempDir, sprintf "clef-proof-%s.smt2" (System.Guid.NewGuid().ToString("N")))
    try
        File.WriteAllText(tempPath, text + "\n")
        let psi = solverStartInfo solver perQueryLimit tempPath
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

let private execute (solver: string) (perQueryLimit: System.TimeSpan option) (limit: System.TimeSpan option) (text: string) : SolverRun =
    let tempDir =
        match System.Environment.GetEnvironmentVariable "CLEF_PROOF_TEMP_DIR" with
        | null | "" -> Path.GetTempPath()
        | value when System.String.IsNullOrWhiteSpace value -> Path.GetTempPath()
        | value -> value
    executeAt tempDir solver perQueryLimit limit text

let [<Literal>] internal batchChunkSize = 64

/// The compiler run: unbounded, using caller-supplied cache lookup/recording.
let internal runSolverWithCache
    (tryCached: string -> string -> string list option)
    (recordCache: string -> string -> string list -> unit)
    (query: string)
    : Result<string list, string> =
    let solver, cacheAllowed = solverExecutable ()
    match (if cacheAllowed then tryCached solver query else None) with
    | Some answer -> Ok answer
    | None ->
        match execute solver None None query with
        | Answered (Ok answer) ->
            if cacheAllowed then recordCache solver query answer
            Ok answer
        | Answered (Error reason) | Unavailable reason -> Error reason
        | TimedOut -> Error "An unbounded cvc5 run cannot exceed a limit"

//-----------------------------------------------------------------------------
// Batch framing
//
// A chunk of `(reset)`-separated queries runs in one cvc5 process. Each query
// is enclosed by SMT-LIB `(echo ...)` sentinels carrying its chunk index, and
// the output is accepted only when every query's frame holds exactly one
// verdict line. A query that prints zero or several lines, a missing or
// reordered sentinel, or trailing output refuses the whole chunk; verdicts are
// never paired with queries by position alone.
//-----------------------------------------------------------------------------

let [<Literal>] internal batchMarkerPrefix = "__fidelity_batch_"

let internal batchBeginMarker (index: int) = sprintf "%sbegin_%d__" batchMarkerPrefix index

let internal batchEndMarker (index: int) = sprintf "%send_%d__" batchMarkerPrefix index

/// The line cvc5 prints for `(echo "<marker>")`.
let internal expectedEchoLine (marker: string) = sprintf "\"%s\"" marker

let private isBatchMarkerLine (line: string) =
    line.Contains(batchMarkerPrefix, System.StringComparison.Ordinal)

/// Frame every query of a chunk with its begin and end sentinels. A query that
/// already contains the reserved prefix is refused: its output could forge a frame.
let internal frameBatchQueries (chunk: string list) : Result<string, string> =
    match chunk with
    | [] -> Error "A framed cvc5 batch requires at least one query"
    | _ ->
        match chunk |> List.tryFindIndex (fun (query: string) -> query.Contains(batchMarkerPrefix, System.StringComparison.Ordinal)) with
        | Some index ->
            Error (sprintf "Batch query %d contains the reserved framing sentinel prefix '%s'" index batchMarkerPrefix)
        | None ->
            chunk
            |> List.mapi (fun index query ->
                sprintf "(echo \"%s\")\n%s\n(echo \"%s\")" (batchBeginMarker index) query (batchEndMarker index))
            |> String.concat "\n(reset)\n\n"
            |> Ok

/// Attribute framed cvc5 output to its queries: for each index 0 .. expectedCount-1,
/// exactly the begin sentinel, one non-sentinel verdict line, and the end
/// sentinel, followed by no further output.
let internal parseFramedChunkVerdicts (expectedCount: int) (lines: string list) : Result<string list, string> =
    let rec loop index acc (remaining: string list) =
        if index = expectedCount then
            match remaining with
            | [] -> Ok (List.rev acc)
            | extra ->
                Error (sprintf "Framed cvc5 output has %d trailing line(s) after the last query frame: %s" extra.Length (String.concat " | " extra))
        else
            let beginLine = expectedEchoLine (batchBeginMarker index)
            let endLine = expectedEchoLine (batchEndMarker index)
            match remaining with
            | [] ->
                Error (sprintf "Framed cvc5 output ended before the begin sentinel of query %d" index)
            | first :: _ when first <> beginLine ->
                Error (sprintf "Framed cvc5 output for query %d: expected begin sentinel %s, found %s" index beginLine first)
            | _ :: afterBegin ->
                let body = afterBegin |> List.takeWhile (fun line -> not (isBatchMarkerLine line))
                match body, List.skip body.Length afterBegin with
                | [ verdict ], next :: rest when next = endLine ->
                    loop (index + 1) (verdict :: acc) rest
                | [ _ ], next :: _ ->
                    Error (sprintf "Framed cvc5 output for query %d: expected end sentinel %s, found %s" index endLine next)
                | [ _ ], [] ->
                    Error (sprintf "Framed cvc5 output ended before the end sentinel of query %d" index)
                | _ ->
                    Error (sprintf "Framed cvc5 output for query %d holds %d verdict lines; exactly one is required" index body.Length)
    if expectedCount < 1 then
        Error (sprintf "A framed cvc5 batch requires at least one query, got %d" expectedCount)
    else
        loop 0 [] lines

/// The outcome of one framed chunk in one cvc5 process.
type internal ChunkRun =
    | ChunkAnswered of (string * string) list
    | ChunkRefused of string
    | ChunkTimedOut
    | ChunkUnavailable of string

/// The outcome of one query in a design-time warming chunk.
type internal WarmEntry =
    | WarmAnswer of string list
    | WarmRefused of string
    | WarmUnavailable of string

let internal runFramedChunk (solver: string) (perQueryLimit: System.TimeSpan option) (limit: System.TimeSpan option) (chunk: string list) : ChunkRun =
    match frameBatchQueries chunk with
    | Error reason -> ChunkRefused reason
    | Ok framed ->
        match execute solver perQueryLimit limit framed with
        | Unavailable reason -> ChunkUnavailable reason
        | TimedOut -> ChunkTimedOut
        | Answered (Error reason) -> ChunkRefused reason
        | Answered (Ok lines) ->
            match parseFramedChunkVerdicts chunk.Length lines with
            | Error reason -> ChunkRefused reason
            | Ok verdicts -> ChunkAnswered (List.zip chunk verdicts)

/// Batched compiler run: uncached single-verdict queries in framed chunks of at
/// most `batchChunkSize`, executed one chunk after another. A chunk that cannot
/// be framed, run, or attributed gives its failure to every query in it.
let internal runSolverBatchWithCache
    (tryCached: string -> string -> string list option)
    (recordCache: string -> string -> string list -> unit)
    (queries: string list)
    : Map<string, Result<string list, string>> =
    if queries.IsEmpty then Map.empty
    else
        let solver, cacheAllowed = solverExecutable ()
        let distinctQueries = queries |> List.distinct
        let cached =
            if not cacheAllowed then Map.empty
            else
                distinctQueries
                |> List.choose (fun query -> tryCached solver query |> Option.map (fun answer -> query, Ok answer))
                |> Map.ofList
        let failChunk (reason: string) (chunk: string list) (acc: Map<string, Result<string list, string>>) =
            chunk |> List.fold (fun results query -> Map.add query (Error reason) results) acc
        distinctQueries
        |> List.filter (fun query -> not (Map.containsKey query cached))
        |> List.chunkBySize batchChunkSize
        |> List.fold (fun acc chunk ->
            match runFramedChunk solver None None chunk with
            | ChunkAnswered pairs ->
                pairs
                |> List.fold (fun results (query, verdict) ->
                    if cacheAllowed then recordCache solver query [ verdict ]
                    Map.add query (Ok [ verdict ]) results) acc
            | ChunkRefused reason | ChunkUnavailable reason -> failChunk reason chunk acc
            | ChunkTimedOut -> failChunk "An unbounded cvc5 run cannot exceed a limit" chunk acc) cached

/// The answer `runSolverBatch` produced for a submitted query. Absence is a
/// refusal, never a reason to run the query again outside its batch.
let internal batchAnswer (results: Map<string, Result<string list, string>>) (query: string) : Result<string list, string> =
    match Map.tryFind query results with
    | Some answer -> answer
    | None -> Error "The cvc5 batch returned no answer for a submitted query"

let private milliseconds (span: System.TimeSpan) = int64 span.TotalMilliseconds

/// Pure outcome of one budgeted design-time solver invocation.
type internal BudgetedOutcome =
    | BudgetedResult of Result<string list, string>
    | BudgetedUnavailable of string

/// Execute one single-query design-time solver run bounded by `perQuery` and
/// the remaining `total` wall budget on `clock`.
let internal executeBudgeted (clock: System.Diagnostics.Stopwatch) (perQuery: System.TimeSpan) (total: System.TimeSpan) (query: string) : BudgetedOutcome =
    let remaining = total - clock.Elapsed
    if remaining <= System.TimeSpan.Zero then
        BudgetedResult (Error (sprintf "cvc5 was not run: the design-time budget of %d ms was exhausted" (milliseconds total)))
    else
        let solver, _ = solverExecutable ()
        let cutByTotal = remaining < perQuery
        match execute solver None (Some (if cutByTotal then remaining else perQuery)) query with
        | Answered answer -> BudgetedResult answer
        | Unavailable reason -> BudgetedUnavailable reason
        | TimedOut when cutByTotal ->
            BudgetedResult (Error (sprintf "cvc5 did not answer before the design-time budget of %d ms was exhausted" (milliseconds total)))
        | TimedOut ->
            BudgetedResult (Error (sprintf "cvc5 did not answer within the per-query limit of %d ms" (milliseconds perQuery)))

/// Warm distinct design-time queries in framed chunks bounded per query by
/// `--tlimit-per` (`perQuery`) and per process by remaining `total` wall budget.
let internal warmDesignTimeChunks
    (clock: System.Diagnostics.Stopwatch)
    (solver: string)
    (perQuery: System.TimeSpan)
    (total: System.TimeSpan)
    (allQueries: string list)
    : Map<string, WarmEntry> =
    let chunks = allQueries |> List.chunkBySize batchChunkSize
    let mark entry (queries: string list) (acc: Map<string, WarmEntry>) =
        queries |> List.fold (fun warmed query -> Map.add query entry warmed) acc
    let rec warmChunks (acc: Map<string, WarmEntry>) = function
        | [] -> acc
        | (chunk: string list) :: rest ->
            let remaining = total - clock.Elapsed
            if remaining <= System.TimeSpan.Zero then acc
            else
                match runFramedChunk solver (Some perQuery) (Some remaining) chunk with
                | ChunkAnswered pairs ->
                    let warmed =
                        pairs
                        |> List.filter (fun (_, verdict) -> verdict <> "unknown")
                        |> List.fold (fun acc' (query, verdict) -> Map.add query (WarmAnswer [ verdict ]) acc') acc
                    warmChunks warmed rest
                | ChunkRefused reason -> warmChunks (mark (WarmRefused reason) chunk acc) rest
                | ChunkUnavailable reason -> mark (WarmUnavailable reason) (List.concat (chunk :: rest)) acc
                | ChunkTimedOut -> acc
    warmChunks Map.empty chunks

/// PhaseEmitter - JSON emission for FNCS nanopass intermediates
///
/// Emits phase intermediate files as JSON for debugging and analysis.
/// Each phase checkpoint calls into this module to write its state.
///
/// Output files: fncs_phase_{N}_{suffix}.json
module FSharp.Native.Compiler.Checking.Native.Infrastructure.PhaseEmitter

open System
open System.IO
open System.Text
open FSharp.Native.Compiler.Checking.Native.Infrastructure.PhaseConfig
open FSharp.Native.Compiler.Checking.Native.Infrastructure.PhaseTypes

// ═══════════════════════════════════════════════════════════════════════════
// JSON Serialization (minimal, no external dependencies)
// ═══════════════════════════════════════════════════════════════════════════

/// Escape a string for JSON
let private escapeJsonString (s: string) =
    let sb = StringBuilder()
    sb.Append('"') |> ignore
    for c in s do
        match c with
        | '"' -> sb.Append("\\\"") |> ignore
        | '\\' -> sb.Append("\\\\") |> ignore
        | '\n' -> sb.Append("\\n") |> ignore
        | '\r' -> sb.Append("\\r") |> ignore
        | '\t' -> sb.Append("\\t") |> ignore
        | c when int c < 32 -> sb.Append(sprintf "\\u%04x" (int c)) |> ignore
        | c -> sb.Append(c) |> ignore
    sb.Append('"') |> ignore
    sb.ToString()

/// Format a value for JSON
let private _formatJsonValue (_pretty: bool) (_indent: int) (value: obj) : string =
    match box value with
    | null -> "null"
    | :? bool as b -> if b then "true" else "false"
    | :? int as i -> string i
    | :? int64 as i -> string i
    | :? float as f -> string f
    | :? string as s -> escapeJsonString s
    | :? DateTime as dt -> escapeJsonString (dt.ToString("O"))
    | _ -> escapeJsonString (string value)

/// Build JSON object from key-value pairs
let private buildJsonObject (pretty: bool) (indent: int) (pairs: (string * string) list) : string =
    let indentStr = if pretty then String.replicate indent "  " else ""
    let innerIndent = if pretty then String.replicate (indent + 1) "  " else ""
    let newline = if pretty then "\n" else ""
    let sep = if pretty then ",\n" else ","

    let content =
        pairs
        |> List.map (fun (k, v) -> sprintf "%s%s: %s" innerIndent (escapeJsonString k) v)
        |> String.concat sep

    sprintf "{%s%s%s%s}" newline content newline indentStr

/// Build JSON array from values
let private buildJsonArray (pretty: bool) (indent: int) (values: string list) : string =
    if List.isEmpty values then "[]"
    else
        let indentStr = if pretty then String.replicate indent "  " else ""
        let innerIndent = if pretty then String.replicate (indent + 1) "  " else ""
        let newline = if pretty then "\n" else ""
        let sep = if pretty then ",\n" else ","

        let content =
            values
            |> List.map (fun v -> sprintf "%s%s" innerIndent v)
            |> String.concat sep

        sprintf "[%s%s%s%s]" newline content newline indentStr

// ═══════════════════════════════════════════════════════════════════════════
// Serialization for Phase Types
// ═══════════════════════════════════════════════════════════════════════════

/// Serialize a PhaseSummary to JSON
let private serializeSummary (pretty: bool) (summary: PhaseSummary) : string =
    let pairs = [
        ("phase", string summary.Phase.Number)
        ("phaseName", escapeJsonString summary.Phase.DisplayName)
        ("timestamp", escapeJsonString (summary.Timestamp.ToString("O")))
        ("nodeCount", string summary.NodeCount)
        ("reachableCount",
            match summary.ReachableCount with
            | Some n -> string n
            | None -> "null")
        ("entryPointCount", string summary.EntryPointCount)
        ("diagnosticCount", string summary.DiagnosticCount)
        ("errorCount", string summary.ErrorCount)
        ("elapsedMs", string summary.ElapsedMs)
    ]
    buildJsonObject pretty 1 pairs

/// Serialize a PhaseNodeOutput to JSON
let private serializeNode (pretty: bool) (indent: int) (node: PhaseNodeOutput) : string =
    let pairs = [
        ("id", string node.Id)
        ("kind", escapeJsonString node.Kind)
        ("type", escapeJsonString node.Type)
        ("isReachable", if node.IsReachable then "true" else "false")
        ("children", buildJsonArray false 0 (node.Children |> List.map string))
        ("parent",
            match node.Parent with
            | Some p -> string p
            | None -> "null")
        ("range",
            match node.Range with
            | Some r -> escapeJsonString r
            | None -> "null")
        ("srtpResolution",
            match node.SRTPResolution with
            | Some r -> escapeJsonString r
            | None -> "null")
        ("body",
            match node.Body with
            | Some b -> escapeJsonString b
            | None -> "null")
    ]
    buildJsonObject pretty indent pairs

/// Serialize a PhaseOutput to JSON
let serializePhaseOutput (output: PhaseOutput) : string =
    let config = getConfig()
    let pretty = config.PrettyPrint

    let summaryJson = serializeSummary pretty output.Summary

    let nodesJson =
        output.Nodes
        |> List.map (serializeNode pretty 2)
        |> buildJsonArray pretty 1

    let entryPointsJson =
        output.EntryPoints
        |> List.map string
        |> buildJsonArray false 0

    let diagnosticsJson =
        output.Diagnostics
        |> List.map escapeJsonString
        |> buildJsonArray pretty 1

    let pairs = [
        ("summary", summaryJson)
        ("nodes", nodesJson)
        ("entryPoints", entryPointsJson)
        ("diagnostics", diagnosticsJson)
    ]

    buildJsonObject pretty 0 pairs

// ═══════════════════════════════════════════════════════════════════════════
// Phase Emission API
// ═══════════════════════════════════════════════════════════════════════════

/// Write a phase intermediate to disk
let emitPhase (output: PhaseOutput) : unit =
    let phase = output.Summary.Phase.Number

    if not (shouldEmitPhase phase) then
        ()  // Emission disabled for this phase
    else
        match getPhaseFilePath phase with
        | None -> ()  // No path configured
        | Some path ->
            try
                // Ensure directory exists
                let dir = Path.GetDirectoryName(path) |> Option.ofObj
                match dir with
                | Some d when d.Length > 0 && not (Directory.Exists(d)) ->
                    Directory.CreateDirectory(d) |> ignore
                | _ -> ()

                // Serialize and write
                let json = serializePhaseOutput output
                File.WriteAllText(path, json, Encoding.UTF8)

                // Log if verbose
                printfn "[FNCS] Wrote phase %d intermediate: %s" phase path
            with ex ->
                // Don't fail compilation on emission error, just warn
                printfn "[FNCS] Warning: Failed to write phase %d intermediate: %s" phase ex.Message

/// Emit a phase with automatic timing
let emitPhaseWithTiming (phase: PhaseId) (startTime: DateTime) (buildOutput: unit -> PhaseOutput) : unit =
    if not (shouldEmitPhase phase.Number) then
        ()
    else
        let output = buildOutput()
        let elapsed = (DateTime.UtcNow - startTime).TotalMilliseconds |> int64
        let outputWithTiming = {
            output with
                Summary = { output.Summary with ElapsedMs = elapsed }
        }
        emitPhase outputWithTiming

/// Create a node output from basic info
let createNodeOutput
    (id: int)
    (kind: string)
    (typ: string)
    (isReachable: bool)
    (children: int list)
    (parent: int option)
    : PhaseNodeOutput =
    {
        Id = id
        Kind = kind
        Type = typ
        IsReachable = isReachable
        Children = children
        Parent = parent
        Range = None
        SRTPResolution = None
        Body = None
    }

/// Add optional fields to a node output
let withRange (range: string) (node: PhaseNodeOutput) =
    { node with Range = Some range }

let withSRTPResolution (resolution: string) (node: PhaseNodeOutput) =
    { node with SRTPResolution = Some resolution }

let withBody (body: string) (node: PhaseNodeOutput) =
    { node with Body = Some body }

// ═══════════════════════════════════════════════════════════════════════════
// Diff Emission (for understanding changes between phases)
// ═══════════════════════════════════════════════════════════════════════════

/// Serialize a PhaseDiff to JSON
let serializeDiff (diff: PhaseDiff) : string =
    let config = getConfig()
    let pretty = config.PrettyPrint

    let nodesAddedJson = buildJsonArray false 0 (diff.NodesAdded |> List.map string)
    let nodesRemovedJson = buildJsonArray false 0 (diff.NodesRemoved |> List.map string)

    let typeChangesJson =
        diff.TypeChanges
        |> List.map (fun (id, oldT, newT) ->
            buildJsonObject false 0 [
                ("id", string id)
                ("oldType", escapeJsonString oldT)
                ("newType", escapeJsonString newT)
            ])
        |> buildJsonArray pretty 1

    let reachabilityChangesJson =
        diff.ReachabilityChanges
        |> List.map (fun (id, wasR, isR) ->
            buildJsonObject false 0 [
                ("id", string id)
                ("wasReachable", if wasR then "true" else "false")
                ("isReachable", if isR then "true" else "false")
            ])
        |> buildJsonArray pretty 1

    let newSRTPJson = buildJsonArray false 0 (diff.NewSRTPResolutions |> List.map string)

    let pairs = [
        ("fromPhase", string diff.FromPhase.Number)
        ("toPhase", string diff.ToPhase.Number)
        ("nodesAdded", nodesAddedJson)
        ("nodesRemoved", nodesRemovedJson)
        ("typeChanges", typeChangesJson)
        ("reachabilityChanges", reachabilityChangesJson)
        ("newSRTPResolutions", newSRTPJson)
    ]

    buildJsonObject pretty 0 pairs

/// Write a phase diff to disk
let emitDiff (diff: PhaseDiff) : unit =
    let config = getConfig()
    if not config.EmitIntermediates then ()
    else
        let filename = sprintf "fncs_diff_%d_to_%d.json" diff.FromPhase.Number diff.ToPhase.Number
        let path = Path.Combine(config.OutputDir, filename)
        try
            let json = serializeDiff diff
            File.WriteAllText(path, json, Encoding.UTF8)
            printfn "[FNCS] Wrote phase diff: %s" path
        with ex ->
            printfn "[FNCS] Warning: Failed to write phase diff: %s" ex.Message

/// PhaseEmitter - JSON emission for CCS nanopass intermediates
///
/// Emits phase intermediate files as JSON for debugging and analysis.
/// Each phase checkpoint calls into this module to write its state.
///
/// Output files: ccs_phase_{N}_{suffix}.json
module Clef.Compiler.NativeTypedTree.Infrastructure.PhaseEmitter

open System
open System.IO
open System.Text
open Clef.Compiler.NativeTypedTree.Infrastructure.PhaseConfig
open Clef.Compiler.NativeTypedTree.Infrastructure.PhaseTypes
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

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
/// Only emits fields with meaningful values - no "null" clutter
let private serializeNode (pretty: bool) (indent: int) (node: PhaseNodeOutput) : string =
    // Required fields - always present
    let requiredPairs = [
        ("id", string node.Id)
        ("kind", escapeJsonString node.Kind)
        ("type", escapeJsonString node.Type)
        ("isReachable", if node.IsReachable then "true" else "false")
        ("children", buildJsonArray false 0 (node.Children |> List.map string))
    ]
    // Optional fields - only include when present
    let optionalPairs =
        [
            node.Parent |> Option.map (fun p -> ("parent", string p))
            node.Range |> Option.map (fun r -> ("range", escapeJsonString r))
            node.SRTPResolution |> Option.map (fun r -> ("srtpResolution", escapeJsonString r))
            node.Body |> Option.map (fun b -> ("body", escapeJsonString b))
            node.EmissionStrategy |> Option.map (fun s -> ("emissionStrategy", escapeJsonString s))
            // Elaboration fields (unified - source-based nodes have no elaboration)
            node.ElaborationKind |> Option.map (fun k -> ("elaborationKind", escapeJsonString k))
            node.ElaborationFor |> Option.map (fun f -> ("elaborationFor", escapeJsonString f))
            node.ElaborationId |> Option.map (fun id -> ("elaborationId", string id))
        ]
        |> List.choose id
    buildJsonObject pretty indent (requiredPairs @ optionalPairs)

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

                if PhaseConfig.isVerbose() then
                    printfn "[CCS] Wrote phase %d intermediate: %s" phase path
            with ex ->
                eprintfn "[CCS] Warning: Failed to write phase %d intermediate: %s" phase ex.Message

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
        EmissionStrategy = None
        // Elaboration defaults (None = source-based, not elaborated)
        ElaborationKind = None
        ElaborationFor = None
        ElaborationId = None
    }

/// Add optional fields to a node output
let withRange (range: string) (node: PhaseNodeOutput) =
    { node with Range = Some range }

let withSRTPResolution (resolution: string) (node: PhaseNodeOutput) =
    { node with SRTPResolution = Some resolution }

let withBody (body: string) (node: PhaseNodeOutput) =
    { node with Body = Some body }

let withEmissionStrategy (strategy: string) (node: PhaseNodeOutput) =
    { node with EmissionStrategy = Some strategy }

/// Set elaboration info on a node (for "pierce the veil" debugging)
/// Source-based nodes should NOT call this (they have no elaboration metadata).
let withElaboration (kind: string) (forConstruct: string) (id: int) (node: PhaseNodeOutput) =
    { node with
        ElaborationKind = Some kind
        ElaborationFor = Some forConstruct
        ElaborationId = Some id }

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
        let filename = sprintf "ccs_diff_%d_to_%d.json" diff.FromPhase.Number diff.ToPhase.Number
        let path = Path.Combine(config.OutputDir, filename)
        try
            let json = serializeDiff diff
            File.WriteAllText(path, json, Encoding.UTF8)
            if PhaseConfig.isVerbose() then
                printfn "[CCS] Wrote phase diff: %s" path
        with ex ->
            eprintfn "[CCS] Warning: Failed to write phase diff: %s" ex.Message

// ═══════════════════════════════════════════════════════════════════════════
// ClefExpr Emission (expression-centric view)
// ═══════════════════════════════════════════════════════════════════════════

open Clef.Compiler.NativeTypedTree

/// Serialize ClefExpr to JSON
let rec private serializeExpr (pretty: bool) (indent: int) (expr: ClefExpr) : string =
    // Note: these indent helpers reserved for future complex nesting
    let _indentStr = if pretty then String.replicate indent "  " else ""
    let _innerIndent = if pretty then String.replicate (indent + 1) "  " else ""
    let _newline = if pretty then "\n" else ""

    match expr with
    | ClefExpr.Literal(value, ty) ->
        let valueStr = sprintf "%A" value |> escapeJsonString
        let typeStr = sprintf "%A" ty |> escapeJsonString
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "Literal")
            ("value", valueStr)
            ("type", typeStr)
        ]

    | ClefExpr.Variable(name, ty, isMutable, defId) ->
        let defIdStr =
            match defId with
            | Some (NodeId id) -> string id
            | None -> "null"
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "Variable")
            ("name", escapeJsonString name)
            ("type", sprintf "%A" ty |> escapeJsonString)
            ("isMutable", if isMutable then "true" else "false")
            ("definitionId", defIdStr)
        ]

    | ClefExpr.Application(func, args, returnType, srtp) ->
        let funcJson = serializeExpr pretty (indent + 1) func
        let argsJson = args |> List.map (serializeExpr pretty (indent + 2)) |> buildJsonArray pretty (indent + 1)
        let srtpStr =
            match srtp with
            | Some r -> buildJsonObject pretty (indent + 1) [
                ("operator", escapeJsonString r.Operator)
                ("resolvedMember", escapeJsonString r.ResolvedMember)
              ]
            | None -> "null"
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "Application")
            ("function", funcJson)
            ("arguments", argsJson)
            ("returnType", sprintf "%A" returnType |> escapeJsonString)
            ("srtpResolution", srtpStr)
        ]

    | ClefExpr.Lambda(parameters, body, returnType, srtp, enclosingFunction) ->
        let paramsJson =
            parameters
            |> List.map (fun (name, ty) ->
                buildJsonObject false 0 [
                    ("name", escapeJsonString name)
                    ("type", sprintf "%A" ty |> escapeJsonString)
                ])
            |> buildJsonArray pretty (indent + 1)
        let bodyJson = serializeExpr pretty (indent + 1) body
        let srtpStr =
            match srtp with
            | Some r -> buildJsonObject pretty (indent + 1) [
                ("operator", escapeJsonString r.Operator)
                ("resolvedMember", escapeJsonString r.ResolvedMember)
              ]
            | None -> "null"
        let enclosingStr =
            match enclosingFunction with
            | Some name -> sprintf "{\"Some\": \"%s\"}" (escapeJsonString name)
            | None -> "{\"None\": true}"
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "Lambda")
            ("parameters", paramsJson)
            ("body", bodyJson)
            ("returnType", sprintf "%A" returnType |> escapeJsonString)
            ("srtpResolution", srtpStr)
            ("enclosingFunction", enclosingStr)
        ]

    | ClefExpr.LetBinding(name, isMutable, value, body, ty) ->
        let valueJson = serializeExpr pretty (indent + 1) value
        let bodyJson =
            match body with
            | Some b -> serializeExpr pretty (indent + 1) b
            | None -> "null"
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "LetBinding")
            ("name", escapeJsonString name)
            ("isMutable", if isMutable then "true" else "false")
            ("value", valueJson)
            ("body", bodyJson)
            ("type", sprintf "%A" ty |> escapeJsonString)
        ]

    | ClefExpr.Sequential(exprs, ty) ->
        let exprsJson = exprs |> List.map (serializeExpr pretty (indent + 1)) |> buildJsonArray pretty (indent + 1)
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "Sequential")
            ("expressions", exprsJson)
            ("type", sprintf "%A" ty |> escapeJsonString)
        ]

    | ClefExpr.IfThenElse(guard, thenBranch, elseBranch, ty) ->
        let guardJson = serializeExpr pretty (indent + 1) guard
        let thenJson = serializeExpr pretty (indent + 1) thenBranch
        let elseJson =
            match elseBranch with
            | Some e -> serializeExpr pretty (indent + 1) e
            | None -> "null"
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "IfThenElse")
            ("guard", guardJson)
            ("thenBranch", thenJson)
            ("elseBranch", elseJson)
            ("type", sprintf "%A" ty |> escapeJsonString)
        ]

    | ClefExpr.PlatformBinding(entryPoint, args, ty) ->
        let argsJson = args |> List.map (serializeExpr pretty (indent + 1)) |> buildJsonArray pretty (indent + 1)
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "PlatformBinding")
            ("entryPoint", escapeJsonString entryPoint)
            ("arguments", argsJson)
            ("type", sprintf "%A" ty |> escapeJsonString)
        ]

    | ClefExpr.TraitCall(memberName, constrainedTypes, arg, resolution, ty) ->
        let argJson = serializeExpr pretty (indent + 1) arg
        let typesJson =
            constrainedTypes
            |> List.map (fun t -> sprintf "%A" t |> escapeJsonString)
            |> buildJsonArray pretty (indent + 1)
        let resolutionJson =
            match resolution with
            | Some r -> buildJsonObject pretty (indent + 1) [
                ("operator", escapeJsonString r.Operator)
                ("resolvedMember", escapeJsonString r.ResolvedMember)
              ]
            | None -> "null"
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "TraitCall")
            ("memberName", escapeJsonString memberName)
            ("constrainedTypes", typesJson)
            ("argument", argJson)
            ("resolution", resolutionJson)
            ("type", sprintf "%A" ty |> escapeJsonString)
        ]

    | ClefExpr.ModuleDef(name, members) ->
        let membersJson = members |> List.map (serializeExpr pretty (indent + 1)) |> buildJsonArray pretty (indent + 1)
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "ModuleDef")
            ("name", escapeJsonString name)
            ("members", membersJson)
        ]

    | ClefExpr.Error(message, _range) ->
        buildJsonObject pretty indent [
            ("kind", escapeJsonString "Error")
            ("message", escapeJsonString message)
        ]

    | _ ->
        // Fallback for other expression types - use compact string
        let compactStr = ClefExpr.toCompactString expr
        buildJsonObject pretty indent [
            ("kind", escapeJsonString compactStr)
            ("note", escapeJsonString "Full serialization not yet implemented for this expression type")
        ]

/// Emit ClefExpr views for all entry points
let emitExpressionView (graph: SemanticGraph) : unit =
    let config = getConfig()
    if not config.EmitIntermediates then ()
    else
        try
            let exprs = ClefExpr.fromDeclarationRoots graph
            let exprsJson =
                exprs
                |> List.map (serializeExpr config.PrettyPrint 1)
                |> buildJsonArray config.PrettyPrint 0

            let output = buildJsonObject config.PrettyPrint 0 [
                ("version", escapeJsonString "1.0")
                ("description", escapeJsonString "ClefExpr - Expression-centric view of SemanticGraph")
                ("entryPointCount", string (List.length exprs))
                ("expressions", exprsJson)
            ]

            let path = Path.Combine(config.OutputDir, "ccs_expr.json")
            File.WriteAllText(path, output, Encoding.UTF8)
            if PhaseConfig.isVerbose() then
                printfn "[CCS] Wrote expression view: %s" path
        with ex ->
            eprintfn "[CCS] Warning: Failed to write expression view: %s" ex.Message

/// Emit pretty-printed text view for debugging
let emitExpressionText (graph: SemanticGraph) : unit =
    let config = getConfig()
    if not config.EmitIntermediates then ()
    else
        try
            let exprs = ClefExpr.fromDeclarationRoots graph
            let text =
                exprs
                |> List.mapi (fun i expr ->
                    sprintf "=== Entry Point %d ===\n%s\n" i (ClefExpr.prettyPrint 0 expr))
                |> String.concat "\n"

            let path = Path.Combine(config.OutputDir, "ccs_expr.txt")
            File.WriteAllText(path, text, Encoding.UTF8)
            if PhaseConfig.isVerbose() then
                printfn "[CCS] Wrote expression text: %s" path
        with ex ->
            eprintfn "[CCS] Warning: Failed to write expression text: %s" ex.Message

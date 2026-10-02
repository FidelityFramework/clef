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
open Fidelity.Data.JSON
open Clef.Compiler.NativeTypedTree.Infrastructure.PhaseConfig
open Clef.Compiler.NativeTypedTree.Infrastructure.PhaseTypes
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

type GraphView = {
    Nodes: Map<NodeId, SemanticNode>
    Edges: Hyperedge list
    Metadata: PhaseGraphView
}

/// Select before formatting kinds and types: discarded nodes incur no JSON
/// rendering work. Non-containment evidence is a joint relation, so touching
/// any participant retains the entire relation transitively. Ordinary graph
/// incidence may cross this diagnostic boundary and is reported explicitly.
/// Neither reachability flags nor the compiler's graph are changed.
let selectGraphView mode (graph: SemanticGraph) : GraphView =
    let selectedNodes, selectedEdges =
        match mode with
        | GraphArtifactMode.Full -> graph.Nodes, graph.Edges
        | GraphArtifactMode.Pruned ->
            let retained = System.Collections.Generic.HashSet<NodeId>()
            let pending = System.Collections.Generic.Queue<NodeId>()
            let retain id = if retained.Add id then pending.Enqueue id
            for node in graph.Nodes.Values do if node.IsReachable then retain node.Id
            for id, _ in graph.DeclarationRoots do retain id
            let joint = graph.Edges |> List.filter (fun edge ->
                edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference) |> List.toArray
            let incidence = System.Collections.Generic.Dictionary<NodeId, ResizeArray<int>>()
            for index in 0 .. joint.Length - 1 do
                for id in joint[index].Target :: joint[index].Sources do
                    match incidence.TryGetValue id with
                    | true, rows -> rows.Add index
                    | _ -> incidence[id] <- ResizeArray<int>([index])
            let visited = System.Collections.Generic.HashSet<int>()
            while pending.Count > 0 do
                match incidence.TryGetValue(pending.Dequeue()) with
                | true, rows ->
                    for index in rows do
                        if visited.Add index then
                            for id in joint[index].Target :: joint[index].Sources do retain id
                | _ -> ()
            graph.Nodes |> Map.filter (fun id _ -> retained.Contains id),
            graph.Edges |> List.filter (fun edge ->
                retained.Contains edge.Target || edge.Sources |> List.exists retained.Contains)
    let referenced =
        seq {
            for node in selectedNodes.Values do
                yield! node.Children
                yield! Option.toList node.Parent
                for edge in kindEdges node.Id node.Kind do
                    yield edge.Target
                    yield! edge.Sources
            for edge in selectedEdges do
                yield edge.Target
                yield! edge.Sources
            yield! graph.DeclarationRoots |> List.map fst
        } |> Set.ofSeq
    let outside = referenced |> Set.filter (fun id -> not (selectedNodes.ContainsKey id))
    let existing, missing = outside |> Set.partition graph.Nodes.ContainsKey
    { Nodes = selectedNodes; Edges = selectedEdges
      Metadata = {
        Mode = match mode with GraphArtifactMode.Full -> "full" | GraphArtifactMode.Pruned -> "pruned-with-evidence"
        SourceNodeCount = graph.Nodes.Count; SourceEdgeCount = graph.Edges.Length
        EmittedNodeCount = selectedNodes.Count; EmittedEdgeCount = selectedEdges.Length
        RetainedUnreachableNodeCount = selectedNodes.Values |> Seq.filter (fun node -> not node.IsReachable) |> Seq.length
        ExternalNodeIds = existing |> Set.toList |> List.map NodeId.value
        MissingNodeIds = missing |> Set.toList |> List.map NodeId.value } }

// ═══════════════════════════════════════════════════════════════════════════
// JSON projection through Fidelity.Data
// ═══════════════════════════════════════════════════════════════════════════

let private number (value: int) = JsonValue.ofInt64 (int64 value)
let private numbers values = values |> List.map number |> JsonValue.Array
let private strings values = values |> List.map JsonValue.String |> JsonValue.Array
let private render pretty value =
    if pretty then Json.serializePretty value else Json.serialize value

/// The diagnostic schema is projected explicitly from compiler-owned values.
let private summaryValue (summary: PhaseSummary) =
    JsonValue.Object [
        "phase", number summary.Phase.Number
        "phaseName", JsonValue.String summary.Phase.DisplayName
        "timestamp", JsonValue.String (summary.Timestamp.ToString("O"))
        "nodeCount", number summary.NodeCount
        "reachableCount", summary.ReachableCount |> Option.map number |> Option.defaultValue JsonValue.Null
        "entryPointCount", number summary.EntryPointCount
        "diagnosticCount", number summary.DiagnosticCount
        "errorCount", number summary.ErrorCount
        "elapsedMs", JsonValue.ofInt64 summary.ElapsedMs ]

let private specializationValue (trace: SpecializationTrace) =
    let nodeId = NodeId.value >> number
    let snapshot (value: SpecializationNodeSnapshot) =
        JsonValue.Object ([
            "kind", JsonValue.String value.Kind
            "type", JsonValue.String value.Type
            "children", JsonValue.Array (value.Children |> List.map nodeId) ] @
            (value.Parent |> Option.map (fun id -> ["parent", nodeId id]) |> Option.defaultValue []))
    JsonValue.Object [
        "meaning", JsonValue.String "applied-specialization-snapshot"
        "sourceDeclaration", nodeId trace.SourceDeclaration
        "sourceNode", nodeId trace.SourceNode
        "cloneDeclaration", nodeId trace.CloneDeclaration
        "cloneNode", nodeId trace.CloneNode
        "scheme", JsonValue.String trace.Scheme
        "retiresSource", JsonValue.Bool trace.RetiresSource
        "parameters", JsonValue.Array (trace.Parameters |> List.map (fun (id, kind) ->
            JsonValue.Object ["id", number id; "kind", JsonValue.String kind]))
        "codeArguments", strings trace.CodeArguments
        "requests", JsonValue.Array (trace.Requests |> List.map (fun (id, ty) ->
            JsonValue.Object ["occurrence", nodeId id; "type", JsonValue.String ty]))
        "input", snapshot trace.Input
        "output", snapshot trace.Output ]

/// Optional fields are absent when the compiler has no corresponding value.
let private nodeValue (node: PhaseNodeOutput) =
    let required = [
        "id", number node.Id
        "kind", JsonValue.String node.Kind
        "type", JsonValue.String node.Type
        "isReachable", JsonValue.Bool node.IsReachable
        "children", numbers node.Children ]
    let optional = [
        node.Parent |> Option.map (fun value -> "parent", number value)
        node.Range |> Option.map (fun value -> "range", JsonValue.String value)
        node.SRTPResolution |> Option.map (fun value -> "srtpResolution", JsonValue.String value)
        node.Body |> Option.map (fun value -> "body", JsonValue.String value)
        node.EmissionStrategy |> Option.map (fun value -> "emissionStrategy", JsonValue.String value)
        node.ValueRange |> Option.map (fun value -> "valueRange", JsonValue.String value)
        node.ElaborationKind |> Option.map (fun value -> "elaborationKind", JsonValue.String value)
        node.ElaborationFor |> Option.map (fun value -> "elaborationFor", JsonValue.String value)
        node.ElaborationId |> Option.map (fun value -> "elaborationId", number value)
        node.Specialization |> Option.map (fun value -> "specialization", specializationValue value) ]
    JsonValue.Object (required @ List.choose id optional)

/// Serialize a PhaseOutput to JSON.
let serializePhaseOutput (output: PhaseOutput) : string =
    let view = output.View
    JsonValue.Object [
        "summary", summaryValue output.Summary
        "view", JsonValue.Object [
            "mode", JsonValue.String view.Mode
            "sourceNodeCount", number view.SourceNodeCount
            "sourceEdgeCount", number view.SourceEdgeCount
            "emittedNodeCount", number view.EmittedNodeCount
            "emittedEdgeCount", number view.EmittedEdgeCount
            "retainedUnreachableNodeCount", number view.RetainedUnreachableNodeCount
            "externalNodeIds", numbers view.ExternalNodeIds
            "missingNodeIds", numbers view.MissingNodeIds ]
        "nodes", JsonValue.Array (output.Nodes |> List.map nodeValue)
        "edges", JsonValue.Array (output.Edges |> List.map (fun edge ->
            JsonValue.Object [
                "sources", numbers edge.Sources
                "target", number edge.Target
                "class", JsonValue.String edge.Class
                "role", JsonValue.String edge.Role
                "ordinal", number edge.Ordinal ]))
        "entryPoints", numbers output.EntryPoints
        "diagnostics", strings output.Diagnostics ]
    |> render (getConfig().PrettyPrint)

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
        ValueRange = None
        // Elaboration defaults (None = source-based, not elaborated)
        ElaborationKind = None
        ElaborationFor = None
        ElaborationId = None
        Specialization = None
    }

/// Only the actual historical clone owns this snapshot. Metadata copied by a
/// later recipe cannot silently become a new specialization event.
let specializationSnapshot (node: SemanticNode) =
    match node.Metadata.TryFind SchemeMetadata.Specialization with
    | Some(MetadataValue.Specialization trace) when trace.CloneNode = node.Id -> Some trace
    | _ -> None

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
    JsonValue.Object [
        "fromPhase", number diff.FromPhase.Number
        "toPhase", number diff.ToPhase.Number
        "nodesAdded", numbers diff.NodesAdded
        "nodesRemoved", numbers diff.NodesRemoved
        "typeChanges", JsonValue.Array (diff.TypeChanges |> List.map (fun (id, oldType, newType) ->
            JsonValue.Object [
                "id", number id
                "oldType", JsonValue.String oldType
                "newType", JsonValue.String newType ]))
        "reachabilityChanges", JsonValue.Array (diff.ReachabilityChanges |> List.map (fun (id, wasReachable, isReachable) ->
            JsonValue.Object [
                "id", number id
                "wasReachable", JsonValue.Bool wasReachable
                "isReachable", JsonValue.Bool isReachable ]))
        "newSRTPResolutions", numbers diff.NewSRTPResolutions ]
    |> render (getConfig().PrettyPrint)

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

let private resolutionValue (resolution: WitnessResolution option) =
    match resolution with
    | Some value -> JsonValue.Object [
        "operator", JsonValue.String value.Operator
        "resolvedMember", JsonValue.String value.ResolvedMember ]
    | None -> JsonValue.Null

/// Project the supported expression diagnostics without traversing inference cells.
let rec private expressionValue (expr: ClefExpr) : JsonValue =
    let typeName value = JsonValue.String (sprintf "%A" value)
    let optionalExpression value = value |> Option.map expressionValue |> Option.defaultValue JsonValue.Null
    let expressions values = values |> List.map expressionValue |> JsonValue.Array
    match expr with
    | ClefExpr.Literal(value, ty) ->
        JsonValue.Object [
            "kind", JsonValue.String "Literal"
            "value", typeName value
            "type", typeName ty ]
    | ClefExpr.Variable(name, ty, isMutable, definitionId) ->
        JsonValue.Object [
            "kind", JsonValue.String "Variable"
            "name", JsonValue.String name
            "type", typeName ty
            "isMutable", JsonValue.Bool isMutable
            "definitionId", definitionId |> Option.map (NodeId.value >> number) |> Option.defaultValue JsonValue.Null ]
    | ClefExpr.Application(func, args, returnType, srtp) ->
        JsonValue.Object [
            "kind", JsonValue.String "Application"
            "function", expressionValue func
            "arguments", expressions args
            "returnType", typeName returnType
            "srtpResolution", resolutionValue srtp ]
    | ClefExpr.Lambda(parameters, body, returnType, srtp, enclosingFunction) ->
        let enclosing =
            match enclosingFunction with
            | Some name -> JsonValue.Object ["Some", JsonValue.String name]
            | None -> JsonValue.Object ["None", JsonValue.Bool true]
        JsonValue.Object [
            "kind", JsonValue.String "Lambda"
            "parameters", JsonValue.Array (parameters |> List.map (fun (name, ty) ->
                JsonValue.Object ["name", JsonValue.String name; "type", typeName ty]))
            "body", expressionValue body
            "returnType", typeName returnType
            "srtpResolution", resolutionValue srtp
            "enclosingFunction", enclosing ]
    | ClefExpr.LetBinding(name, isMutable, value, body, ty) ->
        JsonValue.Object [
            "kind", JsonValue.String "LetBinding"
            "name", JsonValue.String name
            "isMutable", JsonValue.Bool isMutable
            "value", expressionValue value
            "body", optionalExpression body
            "type", typeName ty ]
    | ClefExpr.Sequential(exprs, ty) ->
        JsonValue.Object [
            "kind", JsonValue.String "Sequential"
            "expressions", expressions exprs
            "type", typeName ty ]
    | ClefExpr.IfThenElse(guard, thenBranch, elseBranch, ty) ->
        JsonValue.Object [
            "kind", JsonValue.String "IfThenElse"
            "guard", expressionValue guard
            "thenBranch", expressionValue thenBranch
            "elseBranch", optionalExpression elseBranch
            "type", typeName ty ]
    | ClefExpr.PlatformBinding(entryPoint, args, ty) ->
        JsonValue.Object [
            "kind", JsonValue.String "PlatformBinding"
            "entryPoint", JsonValue.String entryPoint
            "arguments", expressions args
            "type", typeName ty ]
    | ClefExpr.TraitCall(memberName, constrainedTypes, argument, resolution, ty) ->
        JsonValue.Object [
            "kind", JsonValue.String "TraitCall"
            "memberName", JsonValue.String memberName
            "constrainedTypes", JsonValue.Array (constrainedTypes |> List.map typeName)
            "argument", expressionValue argument
            "resolution", resolutionValue resolution
            "type", typeName ty ]
    | ClefExpr.ModuleDef(name, members) ->
        JsonValue.Object [
            "kind", JsonValue.String "ModuleDef"
            "name", JsonValue.String name
            "members", expressions members ]
    | ClefExpr.Error(message, _range) ->
        JsonValue.Object ["kind", JsonValue.String "Error"; "message", JsonValue.String message]
    | _ ->
        JsonValue.Object [
            "kind", JsonValue.String (ClefExpr.toCompactString expr)
            "note", JsonValue.String "Full serialization not yet implemented for this expression type" ]

/// Serialize expression diagnostics using the same schema as emitted artifacts.
let serializeExpressionView (expressions: ClefExpr list) : string =
    JsonValue.Object [
        "version", JsonValue.String "1.0"
        "description", JsonValue.String "ClefExpr - Expression-centric view of SemanticGraph"
        "entryPointCount", number expressions.Length
        "expressions", JsonValue.Array (expressions |> List.map expressionValue) ]
    |> render (getConfig().PrettyPrint)

/// Emit ClefExpr views for all entry points.
let emitExpressionView (graph: SemanticGraph) : unit =
    let config = getConfig()
    if not config.EmitIntermediates then ()
    else
        try
            let exprs = ClefExpr.fromDeclarationRoots graph
            let output = serializeExpressionView exprs
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

// SPDX-License-Identifier: MIT
module Clef.Compiler.PSGSaturation.SemanticGraph.StaticStringLayout

open System.Text
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module Declaration = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

/// BAREWire chooses the offsets. The compiler materializes exactly that plan;
/// its immutable bytes and views then travel to both proof and native emission.
let settle (graph: SemanticGraph) : SemanticGraph * Diagnostic list =
    let graph = { graph with StaticStringPool = None }
    let literals =
        graph.Nodes |> Map.toList |> List.map snd
        |> List.filter (fun node -> node.IsReachable)
        |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Literal (NativeLiteral.String content) -> Some (content, node)
            | _ -> None)
        |> List.sortBy (fun (_, node) -> node.Range.File, node.Range.Start.Line, node.Range.Start.Column, node.Id)
        |> List.groupBy fst
    let reading = Declaration.read graph
    match literals, reading.Platform with
    | [], _ | _, None -> graph, []
    | _, Some _ when not reading.Findings.IsEmpty -> graph, [] // The declaration checker reports these defects.
    | (_, (_, first) :: _) :: _, Some platform ->
        let error (site: SemanticNode) message =
            { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8206"
              Message = "Cannot settle BAREWire static string storage: " + message
              Range = site.Range; RelatedNodes = [site.Id]; Reachability = ReachabilityContext.Reachable }
        match Declaration.spaceNamed "rodata" platform with
        | None -> graph, [error first "the platform has no rodata memory-space declaration."]
        | Some declared ->
            let site = SemanticGraph.tryGetNode declared.Node graph |> Option.defaultValue first
            let space: BAREWire.Platform.MemorySpace =
                { Name = declared.Name; Kind = declared.Kind; Capacity = declared.Capacity
                  Alignment = declared.Alignment; Granularity = declared.Granularity
                  Growth = declared.Growth; Access = declared.Access; Base = declared.Base
                  Notes = ""; MapKind = ""; Since = ""; Until = "" }
            let contents = literals |> List.map (fun (content, nodes) -> content, nodes |> List.map (snd >> fun node -> node.Id), Encoding.UTF8.GetBytes content)
            let requests: BAREWire.Platform.StorageRequest array =
                contents |> List.mapi (fun i (_, _, bytes) ->
                    ({ Name = sprintf "literal_%d" i; Length = int64 bytes.Length + 1L; Alignment = 1 }: BAREWire.Platform.StorageRequest)) |> List.toArray
            match BAREWire.Platform.StaticStorage.plan space requests with
            | Result.Error findings -> graph, (findings |> Array.map (fun finding -> error site (finding.Subject + ": " + finding.Message)) |> Array.toList)
            | Result.Ok plan when plan.AllocationSize > int64 System.Array.MaxLength ->
                graph, [error site "the allocation exceeds the compiler's byte-array representation."]
            | Result.Ok plan ->
                let bytes = Array.zeroCreate<byte> (int plan.AllocationSize)
                let entries =
                    (contents, plan.Placements |> Array.toList)
                    ||> List.map2 (fun (content, ids, value) placement ->
                        System.Array.Copy(value, 0, bytes, int placement.Offset, value.Length)
                        // Array initialization supplies each NUL sentinel and all padding.
                        { NodeIds = ids; Content = content; Offset = int placement.Offset
                          Length = value.Length; StorageLength = int placement.Length })
                let pool =
                    { Symbol = "__clef_static_strings"; Bytes = Array.toList bytes
                      Alignment = plan.Alignment; Size = int plan.AllocationSize; UsedSize = int plan.UsedSize
                      Entries = entries; SpaceName = declared.Name; Capacity = declared.Capacity
                      SpaceAlignment = declared.Alignment; Granularity = declared.Granularity; DeclarationNode = declared.Node }
                { graph with StaticStringPool = Some pool }, []
    | _ -> graph, []

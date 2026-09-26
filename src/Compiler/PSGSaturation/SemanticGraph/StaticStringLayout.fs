// SPDX-License-Identifier: MIT
module Clef.Compiler.PSGSaturation.SemanticGraph.StaticStringLayout

open System.Text
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
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
        match Declaration.immutableProgramSpace platform with
        | None -> graph, [error first "the platform has no immutable program-lifetime space designation."]
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

/// A retained string view may cite immutable program backing only while the
/// current literals and selected declaration still establish this exact pool.
/// Rebuilding the source plan validates bytes, sentinels, bounds, alignment and
/// capacity through the same BAREWire authority used by native emission.
let literalEvidence (graph: SemanticGraph) : Map<NodeId, NodeId list> =
    match graph.StaticStringPool with
    | None -> Map.empty
    | Some actual ->
        let expected, diagnostics = settle graph
        let declaration = Declaration.read graph
        match expected.StaticStringPool, declaration.Platform with
        | Some expected, Some platform
            when diagnostics.IsEmpty && declaration.Findings.IsEmpty && expected = actual ->
            let authority = Declaration.immutableProgramAuthority platform
            if authority.IsEmpty then Map.empty else
            // Other literal lengths determine this allocation's plan too.
            // Keep all of those source premises in the dependent storage joint.
            let literals = actual.Entries |> List.collect _.NodeIds
            let participants = authority @ literals |> List.distinct
            literals |> List.map (fun id -> id, id :: participants |> List.distinct) |> Map.ofList
        | _ -> Map.empty

/// Trace a retained immutable string descriptor to its declared program backing.
/// Additional inputs are supplied by the owning callable/lazy reader only after
/// it has checked the exact formal/actual or capture relation. Every alternative
/// must have backing; dependencies are retained for the enclosing storage joint.
/// This establishes backing lifetime, not evaluation demand or environment scope.
let retainedViews (graph: SemanticGraph)
                  (additionalInputs: SemanticNode -> (NodeId list * NodeId list) option) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let backing = lazy (literalEvidence graph)
    let isString ty = Types.tryGetNTUKind (applySubst ty) = Some NTUKind.NTUstring
    let rec trace seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        let follow source = trace seen source |> Option.map (fun dependencies -> id :: dependencies)
        match nodes.TryFind id with
        | Some node when isString node.Type ->
            match node.Kind with
            | SemanticKind.Literal(NativeLiteral.String _) -> backing.Value.TryFind id
            | SemanticKind.VarRef(_, Some source) when node.Children.IsEmpty ->
                match graph.Edges |> List.filter (fun edge -> edge.Target = id && edge.Role = EdgeRole.Definition) with
                // Kind carries the canonical reference even before its derived
                // incidence is materialized. Resident rows must agree with it.
                | [] -> follow source
                | [{ Class = EdgeClass.Reference; Sources = [actual]; Ordinal = 0 }] when actual = source -> follow source
                | _ -> None
            | SemanticKind.TypeAnnotation(source, declared) when isString declared && node.Children = [source] -> follow source
            | SemanticKind.EagerExpr source when ExplicitDemand.operand graph id = Some source -> follow source
            | SemanticKind.Binding(_, false, _, _) when node.Children.Length = 1 -> follow node.Children.Head
            | SemanticKind.Sequential values when node.Children = values -> List.tryLast values |> Option.bind follow
            | SemanticKind.IfThenElse(condition, left, Some right) when node.Children = [condition; left; right] ->
                match trace seen left, trace seen right with
                | Some left, Some right -> Some(id :: condition :: (left @ right))
                | _ -> None
            | _ ->
                additionalInputs node |> Option.bind (fun (dependencies, inputs) ->
                    if inputs.IsEmpty || not (List.forall nodes.ContainsKey dependencies) then None else
                    inputs |> List.fold (fun result input ->
                        Option.map2 (@) result (trace seen input)) (Some(id :: dependencies)))
        | _ -> None
    fun value -> trace Set.empty value |> Option.map List.distinct

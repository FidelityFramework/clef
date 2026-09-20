// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.StringByteStorage

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Nanopass.Recipe
module Recipes = Clef.Compiler.Baker.Recipes.StringByteStorageRecipes

let private settle (graph: SemanticGraph) =
    let plans, enrichment, diagnostics = Recipes.recognize graph
    let plans = plans |> List.filter (fun plan ->
        graph.Edges |> List.exists (fun edge -> edge.Role = EdgeRole.StringByteSnapshot && edge.Target = plan.Site.Id) |> not)
    let byteViews = graph.Edges |> List.choose (fun edge ->
        match edge.Role, edge.Sources with EdgeRole.StringToBytesSnapshot, [_; view; _] -> Some view | _ -> None) |> Set.ofList
    let mutable exportDiagnostics: Diagnostic list = []
    let exports =
        graph.Nodes.Values |> Seq.choose (fun node ->
            if not node.IsReachable || byteViews.Contains node.Id then None else
            match node.Kind with
            | SemanticKind.Application(fn, [input]) ->
                match graph.Nodes.TryFind fn with
                | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.String; Operation = "toBytes" } } ->
                    match Recipes.expandToBytes graph node input with
                    | Some expansion -> Some(node.Id, expansion)
                    | None ->
                        exportDiagnostics <-
                            { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8404"
                              Message = "String.toBytes requires proved byte storage: the platform must offer an unsigned 8-bit representation."
                              Range = node.Range; RelatedNodes = [node.Id; input]; Reachability = ReachabilityContext.Reachable } :: exportDiagnostics
                        None
                | _ -> None
            | _ -> None) |> Seq.toList
    let expansions = (plans |> List.map (fun plan -> plan.Site.Id, Recipes.expand graph plan)) @ exports |> Map.ofList
    let diagnostics = diagnostics @ List.rev exportDiagnostics
    let create (node: SemanticNode) _ =
        let root, nodes, edges = expansions[node.Id]
        RecipeCreated { OriginalNodeId = node.Id; ReplacementRootId = root; NewNodes = nodes; NewEdges = edges
                        ElaborationKind = "Baker"; ElaborationSource = "StringByteStorage" }
    if expansions.IsEmpty then graph, diagnostics else
        let recipes = FanOut.fanOut "StringByteStorage" (fun node -> expansions.ContainsKey node.Id) create graph
        let annotated = graph |> SemanticGraph.addNodes enrichment.Annotated |> SemanticGraph.addEdges enrichment.NewEdges
        // Like the ordinary saturation fold-in, replacing an application can
        // orphan its original intrinsic callee. Retain resident provenance but
        // recompute executable reachability before ranges and witness coverage.
        let folded = FoldIn.foldIn recipes annotated |> Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable
        folded, diagnostics

/// Editor/source checking carries logical intent without inventing a target's
/// encoding storage. A selected native platform must discharge the boundary.
let normalize (graph: SemanticGraph) =
    match graph.Platform with
    | None -> graph, []
    | Some _ -> settle graph

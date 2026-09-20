// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Establish the delimiter of each sequence suspension site without changing
/// the executable graph. Branches and loop bodies retain their structure;
/// lexical ownership does not determine execution order or cut feasibility.
module Clef.Compiler.Baker.Recipes.SequenceOwnershipRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Ingredients.Obligations
open Clef.Compiler.Baker.Ingredients.Suspensions

let invalid (site: SemanticNode) related message : Diagnostic =
    { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8402"
      Message = message; Range = site.Range; RelatedNodes = site.Id :: related |> List.distinct
      Reachability = ReachabilityContext.Reachable }

/// Use the canonical structural relation, not Parent pointers or reference
/// edges. Attached children supply binding values and intrinsic operands.
let private children (node: SemanticNode) =
    let derived =
        kindEdges node.Id node.Kind
        |> List.filter Hyperedge.isStructural
        |> List.collect _.Sources
    match node.Kind with
    | SemanticKind.Binding _ | SemanticKind.Intrinsic _ -> derived @ node.Children
    | _ -> derived

let forOwner (graph: SemanticGraph) (owner: SemanticNode) : Enrichment * Diagnostic list =
    match owner.Kind with
    | SemanticKind.SeqExpr (generatorId, _) ->
        match Map.tryFind generatorId graph.Nodes with
        | Some { Kind = SemanticKind.Lambda (_, body, _, _, LambdaContext.SeqGenerator); IsReachable = true } ->
            // An explicit worklist visits structural incidence once. A nested
            // deferred body gets its own recipe; it cannot inherit this owner.
            let rec visit seen edges diagnostics pending =
                match pending with
                | [] -> List.rev edges, List.rev diagnostics
                | id :: rest when Set.contains id seen -> visit seen edges diagnostics rest
                | id :: rest ->
                    let seen = Set.add id seen
                    match Map.tryFind id graph.Nodes with
                    | None ->
                        let diagnostic = invalid owner [generatorId; id] "Sequence suspension ownership encountered a missing structural node."
                        visit seen edges (diagnostic :: diagnostics) rest
                    | Some node when not node.IsReachable -> visit seen edges diagnostics rest
                    | Some node ->
                        match node.Kind with
                        | SemanticKind.SeqExpr _ | SemanticKind.Lambda _ | SemanticKind.LazyExpr _
                        | SemanticKind.Quote _ -> visit seen edges diagnostics rest
                        | SemanticKind.Yield _ | SemanticKind.YieldBang _ ->
                            visit seen (delimiter owner.Id generatorId node.Id :: edges) diagnostics (children node @ rest)
                        | _ -> visit seen edges diagnostics (children node @ rest)
            let edges, diagnostics = visit Set.empty [] [] [body]
            // A structurally incomplete owner cannot supply a partial ownership
            // certificate. Other owners are handled independently by fan-out.
            { Enrichment.empty with NewEdges = if List.isEmpty diagnostics then edges else [] }, diagnostics
        | _ ->
            Enrichment.empty,
            [invalid owner [generatorId] "Sequence suspension ownership requires its own reachable SeqGenerator body."]
    | _ -> Enrichment.empty, []

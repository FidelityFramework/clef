// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// The immutable direct-capture recipe. Admission is computed over all uses;
/// this composition expresses the selected form through ordinary parameters.
module Clef.Compiler.Baker.Recipes.ClosureRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.DirectCaptures
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Nanopass.FoldIn

type DirectResult = { Structure: Result; Edges: Hyperedge list }

let direct (ctx: Context) (graph: SemanticGraph) (plan: Plan) : DirectResult =
    let state = SaturationState.create ctx.SourceRange ctx.OriginalHOF ctx.ExpansionId ctx.InspiringNode ctx.Platform
    let result, nodes = run state (saturation {
        let! formals = plan.Captures |> List.map (fun capture -> patternBinding capture.Name capture.Type) |> sequence
        let substitutions = List.map2 (fun capture formal -> capture.SourceNodeId.Value, formal) plan.Captures formals |> Map.ofList
        let prefix = List.map2 (fun (capture: CaptureInfo) formal -> capture.Name, capture.Type, formal) plan.Captures formals
        let parameterNodes, body, enclosing, context =
            match plan.Lambda.Kind with
            | SemanticKind.Lambda (parameters, body, _, enclosing, context) -> parameters, body, enclosing, context
            | _ -> failwith "A direct capture plan must name a Lambda"
        let bodyReferences = plan.BodyNodes |> Set.filter (fun id ->
            let node = graph.Nodes[id]
            let captures =
                match node.Kind with
                | SemanticKind.Lambda (_, _, captures, _, _) | SemanticKind.LazyExpr (_, captures)
                | SemanticKind.SeqExpr (_, captures) -> captures
                | _ -> []
            (captures |> List.exists (fun capture -> capture.SourceNodeId |> Option.exists substitutions.ContainsKey)) ||
            (kindEdges id node.Kind |> List.exists (fun edge -> edge.Sources |> List.exists substitutions.ContainsKey)))
        let changed = Set.unionMany [bodyReferences; plan.CalleeNodes; plan.Calls; Set.ofList [body; plan.Binding.Id; plan.Lambda.Id]]
        for id in changed do
            let source = graph.Nodes[id]
            let inBody = plan.BodyNodes.Contains id
            let originalKind = if inBody then remapKindReferences substitutions source.Kind else source.Kind
            let signature = id = plan.Binding.Id || id = plan.Lambda.Id || plan.CalleeNodes.Contains id
            let ty = if signature then prependTypes plan.Captures source.Type else source.Type
            let! kind, children = saturation {
                if id = plan.Lambda.Id then
                    let parameters = prefix @ parameterNodes
                    return SemanticKind.Lambda (parameters, body, [], enclosing, context), (parameters |> List.map (fun (_, _, id) -> id)) @ [body]
                elif plan.Calls.Contains id then
                    match originalKind with
                    | SemanticKind.Application (callee, args) ->
                        let! captures = plan.Captures |> List.map (fun capture ->
                            let original = capture.SourceNodeId.Value
                            let definition = if inBody then substitutions[original] else original
                            captureArgument source capture definition) |> sequence
                        return SemanticKind.Application (callee, captures @ args), callee :: (captures @ args)
                    | _ -> return failwith "A direct capture call plan must name an Application"
                else
                    let children = if inBody then source.Children |> List.map (fun id -> substitutions.TryFind id |> Option.defaultValue id) else source.Children
                    let kind =
                        match originalKind with
                        | SemanticKind.TypeAnnotation (inner, _) when signature -> SemanticKind.TypeAnnotation (inner, ty)
                        | _ -> originalKind
                    return kind, children
            }
            let emission = if id = body then EmissionStrategy.SeparateFunction 0 else source.EmissionStrategy
            do! enrich source kind ty children emission signature
        return substitutions, formals
    })
    match result with
    | Matched (_, formals) ->
        let edgeKey (edge: Hyperedge) = edge.Target, edge.Class, edge.Role, edge.Ordinal, edge.Sources
        let previousIncidence =
            nodes |> List.choose (fun node -> graph.Nodes.TryFind node.Id)
            |> List.collect structuralIncidence |> List.map edgeKey |> Set.ofList
        // Only the relation derived from the old kinds is replaced. Independent
        // resident relations retain their participants and original provenance;
        // adding a formal is not authority to rewrite their propositions.
        let edges =
            graph.Edges |> List.filter (fun edge -> not (previousIncidence.Contains (edgeKey edge)))
        let provenance = List.map2 (fun capture formal -> captureProvenance plan.Lambda.Id capture.SourceNodeId.Value formal) plan.Captures formals
        { Structure = mkResultNoShadow nodes plan.Lambda.Id []; Edges = edges @ (nodes |> List.collect structuralIncidence) @ provenance }
    | NoMatch reason -> failwithf "Direct capture saturation failed: %s" reason

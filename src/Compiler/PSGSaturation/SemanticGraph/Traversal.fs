// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Graph traversal utilities for SemanticGraph.
/// Provides pre-order, post-order, and SCF region-aware traversals.
module Clef.Compiler.PSGSaturation.SemanticGraph.Traversal

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Reachability

//-------------------------------------------------------------------------
// SCF Region Types (for structured control flow witnessing)
//-------------------------------------------------------------------------

/// Kind of SCF region for control flow operations
type RegionKind =
    /// Guard/condition region (while condition, if condition)
    | GuardRegion
    /// Body region (while body, for body)
    | BodyRegion
    /// Then branch region (if-then)
    | ThenRegion
    /// Else branch region (if-then-else)
    | ElseRegion
    /// Start expression region (for loop start bound)
    | StartExprRegion
    /// End expression region (for loop end bound)
    | EndExprRegion
    /// Match case body region (match case index, 0-based)
    | MatchCaseRegion of index: int
    /// Lambda body region (function body)
    | LambdaBodyRegion

/// Hook for SCF region boundary tracking during traversal
/// Called before/after processing each child region of control flow nodes
type SCFRegionHook<'State> = {
    /// Called before entering a region (e.g., before processing guard subtree)
    BeforeRegion: 'State -> NodeId -> RegionKind -> 'State
    /// Called after exiting a region (e.g., after processing guard subtree)
    AfterRegion: 'State -> NodeId -> RegionKind -> 'State
}

//-------------------------------------------------------------------------
// Graph Traversal
//-------------------------------------------------------------------------

/// Fold over all nodes in depth-first pre-order
let foldPreOrder (folder: 'State -> SemanticNode -> 'State)
                 (state: 'State)
                 (graph: SemanticGraph) : 'State =
    let rec walk state nodeId =
        match SemanticGraph.tryGetNode nodeId graph with
        | None -> state
        | Some node ->
            let state = folder state node
            node.Children |> List.fold walk state

    graph.EntryPoints |> List.fold walk state

/// Fold over all nodes in depth-first post-order
let foldPostOrder (folder: 'State -> SemanticNode -> 'State)
                  (state: 'State)
                  (graph: SemanticGraph) : 'State =
    let rec walk state nodeId =
        match SemanticGraph.tryGetNode nodeId graph with
        | None -> state
        | Some node ->
            let state = node.Children |> List.fold walk state
            folder state node

    graph.EntryPoints |> List.fold walk state

/// Fold with pre-order action for Lambda parameters
/// The preBind function is called BEFORE children, specifically for binding Lambda params
/// The folder function is called AFTER children (post-order style for SSA)
///
/// CRITICAL: This traversal follows SEMANTIC dependencies (VarRef.defId), not just
/// structural containment (Children). When a VarRef references a definition, that
/// definition is visited first. This ensures correct-by-construction ordering where
/// definitions are always witnessed before uses.
let foldWithLambdaPreBind
        (preBind: 'State -> SemanticNode -> 'State)  // Called before children (for Lambda params)
        (folder: 'State -> SemanticNode -> 'State)   // Called after children (for code gen)
        (state: 'State)
        (graph: SemanticGraph) : 'State =
    // Track visited nodes to prevent infinite loops on cyclic references
    let visited = System.Collections.Generic.HashSet<int>()

    let rec walk state nodeId =
        let nodeIdVal = NodeId.value nodeId
        // Skip if already visited (handles cycles and shared references)
        if visited.Contains(nodeIdVal) then
            state
        else
            visited.Add(nodeIdVal) |> ignore
            match SemanticGraph.tryGetNode nodeId graph with
            | None -> state
            | Some node ->
                // FIRST: Follow semantic dependencies (VarRef definitions)
                // This ensures definitions are visited before uses
                let state =
                    match node.Kind with
                    | SemanticKind.VarRef (_, Some defId) ->
                        // Visit the definition first if not already visited
                        walk state defId
                    | _ -> state

                // Pre-bind Lambda parameters before processing children
                let state =
                    match node.Kind with
                    | SemanticKind.Lambda _ -> preBind state node
                    | _ -> state

                // Process semantic references from the Kind
                // This handles TypeAnnotation.expr, Application.args, Sequential.nodes, etc.
                let semanticRefs = getSemanticReferences node
                let state = semanticRefs |> List.fold walk state

                // Also process structural children if any
                let state = node.Children |> List.fold walk state

                // Apply main folder (post-order)
                folder state node

    graph.EntryPoints |> List.fold walk state

/// Fold with pre-order action for Lambda parameters AND SCF region hooks
/// Extends foldWithLambdaPreBind with region boundary hooks for control flow nodes.
/// The scfHook is called before/after each child region of WhileLoop, ForLoop, IfThenElse.
let foldWithSCFRegions
        (preBind: 'State -> SemanticNode -> 'State)
        (scfHook: SCFRegionHook<'State> option)
        (folder: 'State -> SemanticNode -> 'State)
        (state: 'State)
        (graph: SemanticGraph) : 'State =

    let visited = System.Collections.Generic.HashSet<int>()

    let rec walk state nodeId =
        let nodeIdVal = NodeId.value nodeId
        if visited.Contains(nodeIdVal) then
            state
        else
            visited.Add(nodeIdVal) |> ignore
            match SemanticGraph.tryGetNode nodeId graph with
            | None -> state
            | Some node ->
                // FIRST: Follow semantic dependencies (VarRef definitions)
                let state =
                    match node.Kind with
                    | SemanticKind.VarRef (_, Some defId) ->
                        walk state defId
                    | _ -> state

                // Pre-bind Lambda parameters before processing children
                let state =
                    match node.Kind with
                    | SemanticKind.Lambda _ -> preBind state node
                    | _ -> state

                // Process children with SCF region hooks for control flow nodes
                let state =
                    match node.Kind, scfHook with
                    // WhileLoop: guard region, then body region
                    // NOTE: Both BeforeRegion and AfterRegion receive parentId (the WhileLoop's Id)
                    // so the hook can look up the parent to extract guardId/bodyId as needed
                    | SemanticKind.WhileLoop (guardId, bodyId), Some hook ->
                        let parentId = node.Id
                        // Guard region
                        let state = hook.BeforeRegion state parentId GuardRegion
                        let state = walk state guardId
                        let state = hook.AfterRegion state parentId GuardRegion
                        // Body region
                        let state = hook.BeforeRegion state parentId BodyRegion
                        let state = walk state bodyId
                        let state = hook.AfterRegion state parentId BodyRegion
                        state

                    // ForLoop: start, end, body regions
                    // NOTE: BeforeRegion receives parentId consistently
                    | SemanticKind.ForLoop (_, startId, endId, _, bodyId), Some hook ->
                        let parentId = node.Id
                        // Start expression region
                        let state = hook.BeforeRegion state parentId StartExprRegion
                        let state = walk state startId
                        let state = hook.AfterRegion state parentId StartExprRegion
                        // End expression region
                        let state = hook.BeforeRegion state parentId EndExprRegion
                        let state = walk state endId
                        let state = hook.AfterRegion state parentId EndExprRegion
                        // Body region
                        let state = hook.BeforeRegion state parentId BodyRegion
                        let state = walk state bodyId
                        let state = hook.AfterRegion state parentId BodyRegion
                        state

                    // IfThenElse: only then/else are regions, guard is just a boolean SSA value
                    // NOTE: BeforeRegion receives parentId consistently
                    | SemanticKind.IfThenElse (guardId, thenId, elseIdOpt), Some hook ->
                        let parentId = node.Id
                        // Guard - walk normally (not a region for scf.if)
                        let state = walk state guardId
                        // Then region
                        let state = hook.BeforeRegion state parentId ThenRegion
                        let state = walk state thenId
                        let state = hook.AfterRegion state parentId ThenRegion
                        // Else region (optional)
                        match elseIdOpt with
                        | Some elseId ->
                            let state = hook.BeforeRegion state parentId ElseRegion
                            let state = walk state elseId
                            hook.AfterRegion state parentId ElseRegion
                        | None -> state

                    // Match: scrutinee is evaluated first, then each case body is a region
                    // NOTE: Pattern bindings are children of Match, processed as part of case body traversal
                    | SemanticKind.Match (scrutineeId, cases), Some hook ->
                        let parentId = node.Id
                        // Scrutinee - walk normally (value to match against)
                        let state = walk state scrutineeId
                        // Each case body is a separate region
                        cases
                        |> List.fold (fun (state, idx) case ->
                            let state = hook.BeforeRegion state parentId (MatchCaseRegion idx)
                            // Walk PatternBinding nodes (for SSA assignment)
                            let state = case.PatternBindings |> List.fold walk state
                            // Walk optional guard
                            let state =
                                match case.Guard with
                                | Some guardId -> walk state guardId
                                | None -> state
                            // Walk case body
                            let state = walk state case.Body
                            let state = hook.AfterRegion state parentId (MatchCaseRegion idx)
                            (state, idx + 1)
                        ) (state, 0)
                        |> fst

                    // Lambda: body is a region, but parameters are walked first
                    | SemanticKind.Lambda (params', bodyId, _captures, _enclosingFunction, _context), Some hook ->
                        let parentId = node.Id
                        // Walk parameter PatternBindings first (for SSA assignment)
                        let paramNodeIds = params' |> List.map (fun (_, _, nodeId) -> nodeId)
                        let state = paramNodeIds |> List.fold walk state
                        // Lambda body is a region
                        let state = hook.BeforeRegion state parentId LambdaBodyRegion
                        let state = walk state bodyId
                        let state = hook.AfterRegion state parentId LambdaBodyRegion
                        state

                    // No SCF hook or non-control-flow node: process normally
                    | _ ->
                        let semanticRefs = getSemanticReferences node
                        let state = semanticRefs |> List.fold walk state
                        node.Children |> List.fold walk state

                // Apply main folder (post-order)
                folder state node

    graph.EntryPoints |> List.fold walk state

/// Map over all nodes
let map (f: SemanticNode -> SemanticNode) (graph: SemanticGraph) : SemanticGraph =
    { graph with
        Nodes = graph.Nodes |> Map.map (fun _ node -> f node) }

/// Filter nodes
let filter (predicate: SemanticNode -> bool) (graph: SemanticGraph) : SemanticGraph =
    { graph with
        Nodes = graph.Nodes |> Map.filter (fun _ node -> predicate node) }

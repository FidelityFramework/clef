// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker HOF Decomposition Pass - Walk PSG and decompose higher-order functions.
///
/// PIPELINE POSITION:
/// This pass runs AFTER reachability but BEFORE Alex:
///   FCS → PSG Construction → Reachability → [BAKER HOF DECOMPOSITION] → Alex
///
/// TRANSFORMATION MODEL:
/// 1. Walk all reachable Application nodes
/// 2. Check if the function is a decomposable collection HOF (List.map, etc.)
/// 3. If decomposable, create new PSG nodes representing the algorithm
/// 4. Replace the original Application with a reference to the decomposed structure
/// 5. Add auxiliary functions (recursive helpers) to the graph
/// 6. Collect shadow trees into a registry for tooling transparency
///
/// SHADOW TREE INTEGRATION:
/// Each decomposition produces both PSG nodes AND a shadow tree. The shadow trees
/// are collected into a ShadowRegistry for tooling access. This enables:
/// - IDE views showing "compiler-saturated" code vs "code I wrote"
/// - Debugging views of expanded HOFs
/// - Documentation of what the compiler synthesized
///
/// ARCHITECTURAL PRINCIPLE:
/// Baker creates PSG structure; Alex witnesses it. This pass ensures that
/// Alex only sees primitives (isEmpty, head, tail, cons, etc.) that it
/// already knows how to witness.
module FSharp.Native.Compiler.Baker.HOFDecomposition

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Core
open FSharp.Native.Compiler.Baker.Recipes.Decomposition
open FSharp.Native.Compiler.Baker.ShadowAST

module ListRecipes = FSharp.Native.Compiler.Baker.Recipes.ListRecipes
module MapRecipes = FSharp.Native.Compiler.Baker.Recipes.MapRecipes
module SetRecipes = FSharp.Native.Compiler.Baker.Recipes.SetRecipes
module OptionRecipes = FSharp.Native.Compiler.Baker.Recipes.OptionRecipes
module SeqRecipes = FSharp.Native.Compiler.Baker.Recipes.SeqRecipes
module MatchRecipes = FSharp.Native.Compiler.Baker.Recipes.MatchRecipes

//-------------------------------------------------------------------------
// Type Extraction Helpers
//-------------------------------------------------------------------------

/// Extract element type from a List type
let private extractListElementType (ty: NativeType) : NativeType option =
    match ty with
    | NativeType.TList elemTy -> Some elemTy
    | _ -> None

/// Extract key and value types from a Map type
let private extractMapTypes (ty: NativeType) : (NativeType * NativeType) option =
    match ty with
    | NativeType.TMap (keyTy, valTy) -> Some (keyTy, valTy)
    | _ -> None

/// Extract element type from a Set type
let private extractSetElementType (ty: NativeType) : NativeType option =
    match ty with
    | NativeType.TSet elemTy -> Some elemTy
    | _ -> None

/// Extract inner type from an Option type
/// Note: Option is represented as TApp(optionTyCon, [innerType])
let private extractOptionInnerType (ty: NativeType) : NativeType option =
    match ty with
    | NativeType.TApp (tycon, [innerTy]) when tycon = Parameterized.optionTyCon -> 
        Some innerTy
    | NativeType.TApp (tycon, [innerTy]) when tycon = Parameterized.voptionTyCon -> 
        Some innerTy
    | _ -> None

/// Extract element type from a Seq type
let private extractSeqElementType (ty: NativeType) : NativeType option =
    match ty with
    | NativeType.TSeq elemTy -> Some elemTy
    | _ -> None

//-------------------------------------------------------------------------
// Decomposition Decision Logic
//-------------------------------------------------------------------------

/// Determine if an intrinsic should be decomposed (vs witnessed directly by Alex)
let private shouldDecompose (info: IntrinsicInfo) : bool =
    match info.Module, info.Operation with
    // List HOFs that need decomposition
    | IntrinsicModule.List, "map" -> true
    | IntrinsicModule.List, "fold" -> true
    | IntrinsicModule.List, "filter" -> true
    | IntrinsicModule.List, "exists" -> true
    | IntrinsicModule.List, "forall" -> true
    | IntrinsicModule.List, "length" -> true
    | IntrinsicModule.List, "rev" -> true
    | IntrinsicModule.List, "append" -> true
    | IntrinsicModule.List, "collect" -> true
    | IntrinsicModule.List, "contains" -> true
    | IntrinsicModule.List, "tryPick" -> true
    | IntrinsicModule.List, "minBy" -> true
    | IntrinsicModule.List, "max" -> true
    | IntrinsicModule.List, "forall2" -> true
    | IntrinsicModule.List, "sumBy" -> true
    
    // Map HOFs - AVL tree algorithms
    | IntrinsicModule.Map, "toList" -> true
    | IntrinsicModule.Map, "toSeq" -> true  // PRD-16: Lazy enumeration
    | IntrinsicModule.Map, "tryFind" -> true
    | IntrinsicModule.Map, "add" -> true
    | IntrinsicModule.Map, "containsKey" -> true
    | IntrinsicModule.Map, "keys" -> true
    | IntrinsicModule.Map, "values" -> true
    | IntrinsicModule.Map, "forall" -> true
    
    // Set HOFs (placeholder - need AVL implementation)
    | IntrinsicModule.Set, "add" -> true
    | IntrinsicModule.Set, "contains" -> true
    | IntrinsicModule.Set, "remove" -> true
    | IntrinsicModule.Set, "union" -> true
    | IntrinsicModule.Set, "intersect" -> true
    | IntrinsicModule.Set, "difference" -> true
    
    // Option HOFs
    | IntrinsicModule.Option, "map" -> true
    | IntrinsicModule.Option, "bind" -> true
    | IntrinsicModule.Option, "filter" -> true

    // Seq HOFs - Producers (return lazy seq)
    | IntrinsicModule.Seq, "map" -> true
    | IntrinsicModule.Seq, "filter" -> true
    | IntrinsicModule.Seq, "collect" -> true
    | IntrinsicModule.Seq, "append" -> true

    // Seq HOFs - Consumers (iterate seq)
    | IntrinsicModule.Seq, "toList" -> true
    | IntrinsicModule.Seq, "toArray" -> true
    | IntrinsicModule.Seq, "fold" -> true
    | IntrinsicModule.Seq, "tryPick" -> true
    | IntrinsicModule.Seq, "max" -> true
    | IntrinsicModule.Seq, "min" -> true
    | IntrinsicModule.Seq, "minBy" -> true
    | IntrinsicModule.Seq, "maxBy" -> true
    | IntrinsicModule.Seq, "exists" -> true
    | IntrinsicModule.Seq, "forall" -> true
    | IntrinsicModule.Seq, "length" -> true
    | IntrinsicModule.Seq, "isEmpty" -> true
    | IntrinsicModule.Seq, "head" -> true
    | IntrinsicModule.Seq, "tryHead" -> true

    // Primitives - Alex witnesses directly
    | IntrinsicModule.List, ("empty" | "isEmpty" | "head" | "tail" | "cons") -> false
    | IntrinsicModule.Map, ("empty" | "isEmpty") -> false
    | IntrinsicModule.Set, ("empty" | "isEmpty") -> false
    | IntrinsicModule.Option, ("isSome" | "isNone" | "get" | "defaultValue" | "some" | "none") -> false
    // Seq primitives - Alex witnesses directly
    | IntrinsicModule.Seq, "empty" -> false
    | IntrinsicModule.Seq, "getEnumerator" -> false

    // Everything else - don't decompose
    | _ -> false

//-------------------------------------------------------------------------
// Recipe Application
//-------------------------------------------------------------------------

/// Apply the appropriate recipe for a collection HOF
let private applyRecipe
    (graph: SemanticGraph)
    (ctx: Context)
    (info: IntrinsicInfo)
    (args: NodeId list)
    (returnType: NativeType)
    : Result option =
    
    match info.Module with
    | IntrinsicModule.List ->
        // Extract element type from the list argument (usually the last arg)
        let listArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun node -> node.Type)
            |> Option.bind extractListElementType
        
        match listArgType with
        | Some elemType ->
            let outputElemType = extractListElementType returnType
            // Extract state type for fold operations
            let stateType =
                if info.Operation = "fold" then
                    args |> List.tryItem 1
                    |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
                    |> Option.map (fun node -> node.Type)
                else None
            ListRecipes.tryDecompose ctx info.Operation args elemType outputElemType stateType
        | None -> None
    
    | IntrinsicModule.Map ->
        // Extract key/value types from the map argument
        let mapArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun node -> node.Type)
            |> Option.bind extractMapTypes
        
        match mapArgType with
        | Some (keyType, valueType) ->
            MapRecipes.tryDecompose ctx info.Operation args keyType valueType
        | None -> None
    
    | IntrinsicModule.Set ->
        let setArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun node -> node.Type)
            |> Option.bind extractSetElementType
        
        match setArgType with
        | Some elemType ->
            SetRecipes.tryDecompose ctx info.Operation args elemType
        | None -> None
    
    | IntrinsicModule.Option ->
        let optionArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun node -> node.Type)
            |> Option.bind extractOptionInnerType
        
        match optionArgType with
        | Some innerType ->
            let outputType = extractOptionInnerType returnType
            OptionRecipes.tryDecompose ctx info.Operation args innerType outputType
        | None -> None
    
    | IntrinsicModule.Seq ->
        // Extract element type from the seq argument (usually the last arg)
        let seqArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun node -> node.Type)
            |> Option.bind extractSeqElementType
        
        match seqArgType with
        | Some elemType ->
            let outputElemType = extractSeqElementType returnType
            // Extract state type for fold operations
            let stateType =
                if info.Operation = "fold" then
                    args |> List.tryItem 1
                    |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
                    |> Option.map (fun node -> node.Type)
                else None
            SeqRecipes.tryDecompose ctx info.Operation args elemType outputElemType stateType
        | None -> None
    
    | _ -> None

//-------------------------------------------------------------------------
// Graph Transformation
//-------------------------------------------------------------------------

/// Result of decomposing a single node
type private NodeDecomposition = {
    OriginalNodeId: NodeId
    NewNodes: SemanticNode list
    ReplacementNodeId: NodeId
    AuxFunctions: SemanticNode list
    ShadowTree: ShadowTree option
}

/// Try to decompose a single Application node or Match expression
let private tryDecomposeNode 
    (graph: SemanticGraph) 
    (node: SemanticNode) 
    : NodeDecomposition option =
    
    match node.Kind with
    | SemanticKind.Application (funcNodeId, argNodeIds) ->
        // Get the function node to check if it's a decomposable intrinsic
        match SemanticGraph.tryGetNode funcNodeId graph with
        | Some funcNode ->
            match funcNode.Kind with
            | SemanticKind.Intrinsic info when shouldDecompose info ->
                // Create decomposition context
                let hofName = sprintf "%A.%s" info.Module info.Operation
                let ctx = mkContext node.Range Types.unitType graph.Platform hofName node.Id
                
                // Apply the appropriate recipe
                match applyRecipe graph ctx info argNodeIds node.Type with
                | Some result ->
                    Some {
                        OriginalNodeId = node.Id
                        NewNodes = result.NewNodes
                        ReplacementNodeId = result.ResultNodeId
                        AuxFunctions = result.AuxFunctions
                        ShadowTree = result.ShadowTree
                    }
                | None -> None
            | _ -> None
        | None -> None
    
    | SemanticKind.Match (scrutineeId, cases) ->
        // Match expressions are decomposed to IfThenElse decision trees
        let ctx = mkContext node.Range node.Type graph.Platform "Match" node.Id
        let result = MatchRecipes.decomposeMatch ctx scrutineeId cases node.Type
        Some {
            OriginalNodeId = node.Id
            NewNodes = result.NewNodes
            ReplacementNodeId = result.ResultNodeId
            AuxFunctions = result.AuxFunctions
            ShadowTree = result.ShadowTree
        }
    
    | _ -> None

/// Apply decomposition to the entire graph
let private applyDecompositions 
    (graph: SemanticGraph) 
    (decompositions: NodeDecomposition list) 
    : SemanticGraph =
    
    // Collect all new nodes
    let allNewNodes = 
        decompositions
        |> List.collect (fun d -> d.NewNodes @ d.AuxFunctions)
    
    // Add new nodes to the graph
    let graphWithNewNodes =
        allNewNodes
        |> List.fold (fun g node -> SemanticGraph.addNode node g) graph
    
    // Update references: for each decomposed node, update parent references
    // to point to the replacement node instead
    let updateNodeReferences (g: SemanticGraph) (decomp: NodeDecomposition) : SemanticGraph =
        // Find nodes that reference the original node and update them
        g.Nodes
        |> Map.fold (fun acc _nodeId node ->
            let updatedChildren =
                node.Children
                |> List.map (fun childId ->
                    if childId = decomp.OriginalNodeId then decomp.ReplacementNodeId
                    else childId)
            
            let updatedKind =
                match node.Kind with
                | SemanticKind.Application (funcId, args) ->
                    let newFuncId = if funcId = decomp.OriginalNodeId then decomp.ReplacementNodeId else funcId
                    let newArgs = args |> List.map (fun a -> if a = decomp.OriginalNodeId then decomp.ReplacementNodeId else a)
                    SemanticKind.Application (newFuncId, newArgs)
                | SemanticKind.IfThenElse (guard, thenBr, elseBrOpt) ->
                    let newGuard = if guard = decomp.OriginalNodeId then decomp.ReplacementNodeId else guard
                    let newThen = if thenBr = decomp.OriginalNodeId then decomp.ReplacementNodeId else thenBr
                    let newElse = elseBrOpt |> Option.map (fun e -> if e = decomp.OriginalNodeId then decomp.ReplacementNodeId else e)
                    SemanticKind.IfThenElse (newGuard, newThen, newElse)
                | SemanticKind.Sequential nodes ->
                    let newNodes = nodes |> List.map (fun n -> if n = decomp.OriginalNodeId then decomp.ReplacementNodeId else n)
                    SemanticKind.Sequential newNodes
                | SemanticKind.Lambda (params', body, captures, enclosing, lambdaCtx) ->
                    let newBody = if body = decomp.OriginalNodeId then decomp.ReplacementNodeId else body
                    if newBody <> body then
                        eprintfn "[BAKER] Updated Lambda %d body: %d -> %d" (NodeId.value node.Id) (NodeId.value body) (NodeId.value newBody)
                    SemanticKind.Lambda (params', newBody, captures, enclosing, lambdaCtx)
                | SemanticKind.LazyExpr (body, captures) ->
                    let newBody = if body = decomp.OriginalNodeId then decomp.ReplacementNodeId else body
                    SemanticKind.LazyExpr (newBody, captures)
                | SemanticKind.SeqExpr (body, captures) ->
                    let newBody = if body = decomp.OriginalNodeId then decomp.ReplacementNodeId else body
                    SemanticKind.SeqExpr (newBody, captures)
                | SemanticKind.WhileLoop (guard, body) ->
                    let newGuard = if guard = decomp.OriginalNodeId then decomp.ReplacementNodeId else guard
                    let newBody = if body = decomp.OriginalNodeId then decomp.ReplacementNodeId else body
                    SemanticKind.WhileLoop (newGuard, newBody)
                | SemanticKind.ForLoop (var, start, finish, isUp, body) ->
                    let newStart = if start = decomp.OriginalNodeId then decomp.ReplacementNodeId else start
                    let newFinish = if finish = decomp.OriginalNodeId then decomp.ReplacementNodeId else finish
                    let newBody = if body = decomp.OriginalNodeId then decomp.ReplacementNodeId else body
                    SemanticKind.ForLoop (var, newStart, newFinish, isUp, newBody)
                | SemanticKind.ForEach (var, coll, body) ->
                    let newColl = if coll = decomp.OriginalNodeId then decomp.ReplacementNodeId else coll
                    let newBody = if body = decomp.OriginalNodeId then decomp.ReplacementNodeId else body
                    SemanticKind.ForEach (var, newColl, newBody)
                | SemanticKind.TryWith (body, handler) ->
                    let newBody = if body = decomp.OriginalNodeId then decomp.ReplacementNodeId else body
                    let newHandler = if handler = decomp.OriginalNodeId then decomp.ReplacementNodeId else handler
                    SemanticKind.TryWith (newBody, newHandler)
                | SemanticKind.TryFinally (body, cleanup) ->
                    let newBody = if body = decomp.OriginalNodeId then decomp.ReplacementNodeId else body
                    let newCleanup = if cleanup = decomp.OriginalNodeId then decomp.ReplacementNodeId else cleanup
                    SemanticKind.TryFinally (newBody, newCleanup)
                | SemanticKind.Binding (_name, _isMut, _isRec, _isEntry) ->
                    // Binding children are the bound value - update if needed
                    node.Kind  // Keep as-is, children update handles this
                | kind -> kind
            
            if updatedChildren <> node.Children || updatedKind <> node.Kind then
                let updatedNode = { node with Children = updatedChildren; Kind = updatedKind }
                SemanticGraph.addNode updatedNode acc
            else
                acc
        ) g
    
    decompositions
    |> List.fold updateNodeReferences graphWithNewNodes

//-------------------------------------------------------------------------
// Shadow Registry Collection
//-------------------------------------------------------------------------

/// Collect shadow trees from decompositions into a registry
let private collectShadowTrees (decompositions: NodeDecomposition list) : ShadowRegistry =
    decompositions
    |> List.fold (fun registry decomp ->
        match decomp.ShadowTree with
        | Some tree -> ShadowRegistry.add decomp.OriginalNodeId tree registry
        | None -> registry
    ) ShadowRegistry.empty

//-------------------------------------------------------------------------
// Main Pass Entry Point
//-------------------------------------------------------------------------

/// Result of running HOF decomposition
type DecompositionResult = {
    /// The transformed semantic graph
    Graph: SemanticGraph
    /// Registry of shadow trees for tooling
    ShadowRegistry: ShadowRegistry
}

/// Run HOF decomposition on the semantic graph.
/// Returns the transformed graph with HOFs decomposed to primitives,
/// plus a shadow registry for tooling transparency.
let run (graph: SemanticGraph) : DecompositionResult =
    // Debug: count Match nodes before decomposition
    let matchNodesBefore = 
        graph.Nodes 
        |> Map.values 
        |> Seq.filter (fun n -> n.IsReachable && match n.Kind with SemanticKind.Match _ -> true | _ -> false)
        |> Seq.length
    if matchNodesBefore > 0 then
        eprintfn "[BAKER] Found %d reachable Match node(s) to decompose" matchNodesBefore
    
    // Find all reachable Application nodes that need decomposition
    let decompositions =
        graph.Nodes
        |> Map.values
        |> Seq.filter (fun node -> node.IsReachable)
        |> Seq.choose (tryDecomposeNode graph)
        |> List.ofSeq
    
    eprintfn "[BAKER] Total decompositions: %d" (List.length decompositions)
    
    if List.isEmpty decompositions then
        // No decompositions needed
        { Graph = graph; ShadowRegistry = ShadowRegistry.empty }
    else
        // Apply all decompositions and collect shadow trees
        let transformedGraph = applyDecompositions graph decompositions
        let shadowRegistry = collectShadowTrees decompositions
        
        // Debug: count Match nodes after decomposition
        let matchNodesAfter = 
            transformedGraph.Nodes 
            |> Map.values 
            |> Seq.filter (fun n -> n.IsReachable && match n.Kind with SemanticKind.Match _ -> true | _ -> false)
            |> Seq.length
        if matchNodesAfter > 0 then
            eprintfn "[BAKER] WARNING: %d Match node(s) still remain after decomposition" matchNodesAfter
        
        { Graph = transformedGraph; ShadowRegistry = shadowRegistry }

/// Run HOF decomposition returning just the graph (for backward compatibility)
let runGraphOnly (graph: SemanticGraph) : SemanticGraph =
    (run graph).Graph

/// Run HOF decomposition with verbose output for debugging
let runWithDiagnostics (graph: SemanticGraph) : DecompositionResult * string list =
    let mutable diagnostics = []
    
    let decompositions =
        graph.Nodes
        |> Map.values
        |> Seq.filter (fun node -> node.IsReachable)
        |> Seq.choose (fun node ->
            match tryDecomposeNode graph node with
            | Some decomp ->
                let (NodeId nodeIdVal) = node.Id
                let shadowInfo = 
                    match decomp.ShadowTree with 
                    | Some tree -> sprintf " (shadow: %d nodes)" (Map.count tree.Nodes)
                    | None -> ""
                diagnostics <- sprintf "[BAKER] Decomposed %A at node %d → %d new nodes%s" 
                                   (match node.Kind with 
                                    | SemanticKind.Application (fid, _) -> 
                                        match SemanticGraph.tryGetNode fid graph with
                                        | Some fn -> 
                                            match fn.Kind with
                                            | SemanticKind.Intrinsic info -> info.FullName
                                            | _ -> "unknown"
                                        | None -> "unknown"
                                    | _ -> "unknown")
                                   nodeIdVal
                                   (List.length decomp.NewNodes)
                                   shadowInfo
                               :: diagnostics
                Some decomp
            | None -> None)
        |> List.ofSeq
    
    let result =
        if List.isEmpty decompositions then 
            { Graph = graph; ShadowRegistry = ShadowRegistry.empty }
        else 
            let transformedGraph = applyDecompositions graph decompositions
            let shadowRegistry = collectShadowTrees decompositions
            { Graph = transformedGraph; ShadowRegistry = shadowRegistry }
    
    result, List.rev diagnostics

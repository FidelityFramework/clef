// SPDX-License-Identifier: MIT

/// Intrinsic Elaboration - Pass 1 (Fan-Out) and Pass 2 (Fold-In)
///
/// Intrinsic elaboration expands high-level intrinsic operations into PSG structure
/// that implements their semantics. This is separate from Baker saturation (HOF decomposition).
///
/// ENTRY POINT ELABORATION (January 2026):
/// For freestanding builds, this module also adds the `_start` wrapper function
/// that calls `main` with argc/argv from the stack, then calls exit.
/// This is a graph-level operation that runs after intrinsic fold-in.
///
/// See: docs/PSG_Elaboration_Fold_Architecture.md
/// See: Serena memory "freestanding_entry_point_knock_list"
module FSharp.Native.Compiler.Nanopass.IntrinsicElaboration

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes

open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Nanopass.Recipe
open FSharp.Native.Compiler.Baker.Recipes.Decomposition

// String operations handled by Baker Saturation (Pass 3), not Intrinsic Elaboration.
// Clean layer separation: no mixing of Pass 1 (intrinsics) and Pass 3 (Baker).

//-------------------------------------------------------------------------
// Pass 1: Intrinsic Fan-Out (Parallel Recipe Creation)
//-------------------------------------------------------------------------

/// Check if two types have the same memory layout (same-size conversion)
let private hasSameLayout (sourceType: NativeType) (targetType: NativeType) : bool =
    let sourceLayout = TypeLayout.baseLayout (layoutOf sourceType)
    let targetLayout = TypeLayout.baseLayout (layoutOf targetType)
    match sourceLayout, targetLayout with
    | TypeLayout.PlatformWord, TypeLayout.PlatformWord -> true
    | TypeLayout.Inline (s1, _), TypeLayout.Inline (s2, _) when s1 = s2 -> true
    | _ -> false

/// Check if a node is a same-size conversion Application that can be eliminated
let private isSameSizeConversion (node: SemanticNode) (graph: SemanticGraph) : (NodeId * IntrinsicInfo) option =
    match node.Kind with
    | SemanticKind.Application (funcId, [argId]) ->
        // Look up the function node
        match Map.tryFind funcId graph.Nodes with
        | Some funcNode ->
            match funcNode.Kind with
            | SemanticKind.Intrinsic info when info.Category = IntrinsicCategory.Conversion ->
                // Get arg type from the arg node
                match Map.tryFind argId graph.Nodes with
                | Some argNode ->
                    // Check if source (arg) and target (result) have same layout
                    if hasSameLayout argNode.Type node.Type then
                        Some (argId, info)
                    else
                        None
                | None -> None
            | _ -> None
        | None -> None
    | _ -> None

// String operations removed - handled by Baker Saturation (Pass 3).
// Intrinsic Elaboration (Pass 1) handles ONLY entry points and simple conversions.

/// Determine if a node needs intrinsic elaboration.
/// Returns true for same-size conversions only (strings handled by Baker Pass 3).
let private needsIntrinsicElaboration (node: SemanticNode) (graph: SemanticGraph) : bool =
    match isSameSizeConversion node graph with
    | Some _ -> true
    | None -> false

/// Create a recipe for intrinsic elaboration.
/// Handles ONLY same-size conversions (strings handled by Baker Pass 3).
let private createIntrinsicRecipe (node: SemanticNode) (graph: SemanticGraph) : RecipeCreationResult =
    match isSameSizeConversion node graph with
    | Some (argId, info) ->
        // Same-size conversion: replace Application with its argument
        // No new nodes needed - we just redirect to the existing argument
        RecipeCreated {
            OriginalNodeId = node.Id
            NewNodes = []  // No new nodes!
            ReplacementRootId = argId  // Replace with the argument
            ElaborationKind = "Intrinsic"
            ElaborationSource = sprintf "Convert.%s (same-size elimination)" info.Operation
        }
    | None ->
        // No other intrinsic elaborations in Pass 1
        NotApplicable "Not a same-size conversion"

/// Run Pass 1: Intrinsic Fan-Out
/// Identifies intrinsics needing elaboration and creates recipes in parallel.
let fanOut (graph: SemanticGraph) : RecipeSet =
    // Use closures to capture the graph for predicate and recipe creation
    let shouldElaborate node = needsIntrinsicElaboration node graph
    let createRecipe node _graph = createIntrinsicRecipe node graph
    FanOut.fanOut "Intrinsic" shouldElaborate createRecipe graph

//-------------------------------------------------------------------------
// Pass 2: Intrinsic Fold-In
//-------------------------------------------------------------------------

/// Run Pass 2: Intrinsic Fold-In
/// Builds fresh PSG with intrinsic elaborations applied.
/// Uses generic FoldIn - the recipes from Pass 1 drive the transformation.
let foldIn (recipeSet: RecipeSet) (graph: SemanticGraph) : SemanticGraph =
    FoldIn.foldIn recipeSet graph

//-------------------------------------------------------------------------
// Entry Point Elaboration (Graph-Level Transformation)
//-------------------------------------------------------------------------

/// Create a fresh NodeId
let private freshNodeId () = NodeId.fresh()

/// Build the _start wrapper function for freestanding builds.
///
/// _start is the true entry point for freestanding binaries. It:
/// 1. Creates an empty string array as argv (F# convention)
/// 2. Calls main(argv)
/// 3. Calls Sys.exit with main's return value
///
/// F# [<EntryPoint>] functions take `string array -> int` (or `string array -> unit`),
/// not the C convention of `(int argc, char** argv)`.
///
/// NOTE: For now, we pass an empty array. Full argc/argv conversion would require
/// C string to F# string conversion, which is a future enhancement.
let private buildStartWrapper
    (startup: FreestandingStartup)
    (mainNodeId: NodeId)
    (mainType: NativeType)
    (sourceRange: SourceRange)
    : SemanticNode list * NodeId =

    // Extract main's return type from TFun(string array, returnType)
    let returnType =
        match mainType with
        | NativeType.TFun (_, ret) -> ret
        | _ -> Types.intType  // Default to int if we can't extract

    // Extract main's parameter type (should be string array)
    let argType =
        match mainType with
        | NativeType.TFun (paramType, _) -> paramType
        | _ -> Types.unitType

    let unitType = Types.unitType

    // Node IDs for the _start body
    // Intrinsics must be wrapped in Application nodes to produce values
    let emptyArgvIntrinsicId = freshNodeId()  // The intrinsic function itself
    let emptyArgvCallId = freshNodeId()        // Application calling the intrinsic
    let mainRefId = freshNodeId()
    let callMainId = freshNodeId()
    let exitIntrinsicId = freshNodeId()        // The exit intrinsic function
    let exitCallId = freshNodeId()             // Application calling exit
    let seqId = freshNodeId()
    let startLambdaId = freshNodeId()
    let startBindingId = freshNodeId()

    // 1. Create the Sys.emptyStringArray intrinsic (the function itself)
    let emptyArgvInfo = {
        Module = IntrinsicModule.Sys
        Operation = "emptyStringArray"
        Category = IntrinsicCategory.Platform
        FullName = "Sys.emptyStringArray"
    }
    let emptyArgvIntrinsicNode = {
        Id = emptyArgvIntrinsicId
        Kind = SemanticKind.Intrinsic emptyArgvInfo
        Range = sourceRange
        Type = NativeType.TFun (unitType, argType)  // unit -> string array
        SRTPResolution = None
        ArenaAffinity = ArenaAffinity.CurrentActor
        LayoutHint = None
        Children = []
        Parent = None
        Metadata = Map.empty
        IsReachable = true
        EmissionStrategy = EmissionStrategy.Inline
    }

    // 2. Call Sys.emptyStringArray() to produce the argv value
    let emptyArgvCallNode = {
        Id = emptyArgvCallId
        Kind = SemanticKind.Application (emptyArgvIntrinsicId, [])  // No args (nullary function)
        Range = sourceRange
        Type = argType  // string array
        SRTPResolution = None
        ArenaAffinity = ArenaAffinity.CurrentActor
        LayoutHint = None
        Children = [emptyArgvIntrinsicId]
        Parent = None
        Metadata = Map.empty
        IsReachable = true
        EmissionStrategy = EmissionStrategy.Inline
    }

    // 3. Reference to main function
    let mainRefNode = {
        Id = mainRefId
        Kind = SemanticKind.VarRef (startup.MainFunction, Some mainNodeId)
        Range = sourceRange
        Type = mainType
        SRTPResolution = None
        ArenaAffinity = ArenaAffinity.CurrentActor
        LayoutHint = None
        Children = []
        Parent = None
        Metadata = Map.empty
        IsReachable = true
        EmissionStrategy = EmissionStrategy.Inline
    }

    // 4. Call main(argv) -> returnType
    let callMainNode = {
        Id = callMainId
        Kind = SemanticKind.Application (mainRefId, [emptyArgvCallId])  // Pass the result of emptyStringArray call
        Range = sourceRange
        Type = returnType
        SRTPResolution = None
        ArenaAffinity = ArenaAffinity.CurrentActor
        LayoutHint = None
        Children = [mainRefId; emptyArgvCallId]
        Parent = None
        Metadata = Map.empty
        IsReachable = true
        EmissionStrategy = EmissionStrategy.Inline
    }

    // 5. Create the Sys.exit intrinsic (the function itself)
    let exitInfo = {
        Module = IntrinsicModule.Sys
        Operation = "exit"
        Category = IntrinsicCategory.Platform
        FullName = "Sys.exit"
    }
    let exitIntrinsicNode = {
        Id = exitIntrinsicId
        Kind = SemanticKind.Intrinsic exitInfo
        Range = sourceRange
        Type = NativeType.TFun (returnType, unitType)  // int -> unit
        SRTPResolution = None
        ArenaAffinity = ArenaAffinity.CurrentActor
        LayoutHint = None
        Children = []
        Parent = None
        Metadata = Map.empty
        IsReachable = true
        EmissionStrategy = EmissionStrategy.Inline
    }

    // 6. Call Sys.exit(result) -> unit
    let exitCallNode = {
        Id = exitCallId
        Kind = SemanticKind.Application (exitIntrinsicId, [callMainId])  // Pass main's result to exit
        Range = sourceRange
        Type = unitType
        SRTPResolution = None
        ArenaAffinity = ArenaAffinity.CurrentActor
        LayoutHint = None
        Children = [exitIntrinsicId; callMainId]
        Parent = None
        Metadata = Map.empty
        IsReachable = true
        EmissionStrategy = EmissionStrategy.Inline
    }

    // 7. Sequential wrapper: call emptyStringArray; call main; call exit
    let seqNode = {
        Id = seqId
        Kind = SemanticKind.Sequential [emptyArgvCallId; callMainId; exitCallId]
        Range = sourceRange
        Type = unitType
        SRTPResolution = None
        ArenaAffinity = ArenaAffinity.CurrentActor
        LayoutHint = None
        Children = [emptyArgvCallId; callMainId; exitCallId]
        Parent = None
        Metadata = Map.empty
        IsReachable = true
        EmissionStrategy = EmissionStrategy.Inline
    }

    // 8. Lambda: () -> unit (the _start function body)
    // Note: _start has no parameters from the language perspective
    let startLambdaNode = {
        Id = startLambdaId
        Kind = SemanticKind.Lambda ([], seqId, [], Some startup.EntrySymbol, LambdaContext.RegularClosure)
        Range = sourceRange
        Type = NativeType.TFun (unitType, unitType)
        SRTPResolution = None
        ArenaAffinity = ArenaAffinity.CurrentActor
        LayoutHint = None
        Children = [seqId]
        Parent = None
        Metadata = Map.empty
        IsReachable = true
        EmissionStrategy = EmissionStrategy.SeparateFunction 0  // No captures
    }

    // 9. Binding: let _start = ... (marked as entry point)
    let startBindingNode = {
        Id = startBindingId
        Kind = SemanticKind.Binding (startup.EntrySymbol, false, false, true)  // name, isMutable, isRecursive, isEntryPoint
        Range = sourceRange
        Type = NativeType.TFun (unitType, unitType)
        SRTPResolution = None
        ArenaAffinity = ArenaAffinity.CurrentActor
        LayoutHint = None
        Children = [startLambdaId]
        Parent = None
        Metadata = Map.empty
        IsReachable = true
        EmissionStrategy = EmissionStrategy.SeparateFunction 0
    }

    let nodes = [
        emptyArgvIntrinsicNode
        emptyArgvCallNode
        mainRefNode
        callMainNode
        exitIntrinsicNode
        exitCallNode
        seqNode
        startLambdaNode
        startBindingNode
    ]

    (nodes, startBindingId)

/// Find the main function node in the graph
/// Searches through all reachable bindings to find one named "main"
let private findMainNode (graph: SemanticGraph) : (NodeId * NativeType) option =
    // Search all nodes for a reachable binding named "main"
    // Entry points may be ModuleDefs, so we need to search their children recursively
    graph.Nodes
    |> Map.toSeq
    |> Seq.tryPick (fun (_nodeId, node) ->
        if node.IsReachable then
            match node.Kind with
            | SemanticKind.Binding (name, _, _, _) when name = "main" ->
                Some (node.Id, node.Type)
            | _ -> None
        else
            None)

/// Elaborate entry points for freestanding builds.
/// Adds the _start wrapper function that calls main.
///
/// This runs AFTER intrinsic fold-in but BEFORE saturation fan-out.
/// The resulting graph has _start as the true entry point.
let elaborateEntryPoints (graph: SemanticGraph) : SemanticGraph =
    match graph.Platform with
    | Some platform when platform.FreestandingStartup.IsSome ->
        let startup = platform.FreestandingStartup.Value

        // Find main function
        match findMainNode graph with
        | Some (mainNodeId, mainType) ->
            // Get source range from main node for _start nodes
            let sourceRange =
                match Map.tryFind mainNodeId graph.Nodes with
                | Some node -> node.Range
                | None -> dummyRange

            // Build _start wrapper nodes
            let (startNodes, startBindingId) =
                buildStartWrapper startup mainNodeId mainType sourceRange

            // Add _start nodes to graph
            let newNodes =
                startNodes
                |> List.fold (fun acc node -> Map.add node.Id node acc) graph.Nodes

            // Update entry points: _start is now the primary entry point
            // Keep main in entry points for debugging/symbol resolution
            let newEntryPoints = startBindingId :: graph.EntryPoints

            { graph with
                Nodes = newNodes
                EntryPoints = newEntryPoints }

        | None ->
            // No main function found - can't create _start wrapper
            // This is likely an error in the source code, let it fail at link time
            graph

    | _ ->
        // Not freestanding mode - no entry point elaboration needed
        graph

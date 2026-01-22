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
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Nanopass.Recipe

//-------------------------------------------------------------------------
// Pass 1: Intrinsic Fan-Out (Parallel Recipe Creation)
//-------------------------------------------------------------------------

/// Determine if a node needs intrinsic elaboration.
/// Currently returns false for all nodes - no intrinsics need PSG elaboration yet.
let private needsIntrinsicElaboration (_node: SemanticNode) : bool =
    // Future: check for intrinsics that need PSG expansion
    // match node.Kind with
    // | SemanticKind.Intrinsic info when requiresElaboration info -> true
    // | _ -> false
    false

/// Create a recipe for intrinsic elaboration.
/// This is called only for nodes where needsIntrinsicElaboration returns true.
/// RecipeCreator signature: SemanticNode -> SemanticGraph -> Recipe option
let private createIntrinsicRecipe (node: SemanticNode) (_graph: SemanticGraph) : Recipe option =
    // Future: implement intrinsic-specific recipe creation
    // For now, this is never called since needsIntrinsicElaboration always returns false
    failwithf "createIntrinsicRecipe: Node %d does not require elaboration" (let (NodeId nid) = node.Id in nid)

/// Run Pass 1: Intrinsic Fan-Out
/// Identifies intrinsics needing elaboration and creates recipes in parallel.
let fanOut (graph: SemanticGraph) : RecipeSet =
    FanOut.fanOut "Intrinsic" needsIntrinsicElaboration createIntrinsicRecipe graph

//-------------------------------------------------------------------------
// Pass 2: Intrinsic Fold-In
//-------------------------------------------------------------------------

/// Run Pass 2: Intrinsic Fold-In
/// Builds fresh PSG with intrinsic elaborations applied.
/// Uses generic FoldIn - the recipes from Pass 1 drive the transformation.
let foldIn (recipeSet: RecipeSet) (graph: SemanticGraph) : SemanticGraph =
    FoldIn.foldIn "Intrinsic Fold-In" recipeSet graph

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

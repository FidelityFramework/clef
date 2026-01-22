// SPDX-License-Identifier: MIT

/// Intrinsic Elaboration - Pass 1 (Fan-Out) and Pass 2 (Fold-In)
///
/// Intrinsic elaboration expands high-level intrinsic operations into PSG structure
/// that implements their semantics. This is separate from Baker saturation (HOF decomposition).
///
/// CURRENT STATE (January 2026):
/// No intrinsics currently require PSG elaboration - they're all witnessed directly by Alex.
/// This infrastructure exists for future expansion (e.g., complex intrinsics that need
/// multiple PSG nodes to implement).
///
/// Examples of future intrinsic elaboration candidates:
/// - Complex string operations requiring buffer management
/// - Async intrinsics requiring state machine structure
/// - Platform operations requiring multiple syscalls
///
/// See: docs/PSG_Elaboration_Fold_Architecture.md
module FSharp.Native.Compiler.Nanopass.IntrinsicElaboration

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
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

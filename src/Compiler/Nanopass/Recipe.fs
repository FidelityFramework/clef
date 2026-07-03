// SPDX-License-Identifier: MIT

/// Recipe types for PSG elaboration nanopasses.
/// 
/// A Recipe represents the replacement structure for a single node.
/// A RecipeSet is the collection of all recipes from a fan-out pass.
/// 
/// See: psg_elaboration_fold_architecture.md (Serena memory)
module Clef.Compiler.Nanopass.Recipe

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

//=============================================================================
// RECIPE: Single node elaboration
//=============================================================================

/// A single elaboration recipe - the replacement structure for one node.
type Recipe = {
    /// The original node being replaced
    OriginalNodeId: NodeId

    /// New nodes that comprise the replacement structure
    NewNodes: SemanticNode list

    /// The root of the replacement (what parent references should point to)
    ReplacementRootId: NodeId

    /// Metadata for debugging/tooling
    ElaborationKind: string   // "Intrinsic" | "Baker"
    ElaborationSource: string // e.g., "Console.writeln" | "Match" | "List.map"
}

//=============================================================================
// RECIPE CREATION RESULT: Diagnostic-aware recipe creation
//=============================================================================

/// Result of recipe creation with diagnostic context.
/// Replaces silent `option` returns with explicit failure reasons.
type RecipeCreationResult =
    | RecipeCreated of Recipe
    | NotApplicable of reason: string
    | CreationFailed of reason: string * context: Map<string, string>

/// Diagnostic artifact for a single recipe creation attempt.
type RecipeDiagnostic = {
    /// Node that was considered for elaboration
    NodeId: NodeId

    /// Type of elaboration attempted ("Intrinsic" | "Baker")
    ElaborationKind: string

    /// Result of the creation attempt
    Result: RecipeCreationResult
}

/// Extract Recipe from successful result
let tryGetRecipe (result: RecipeCreationResult) : Recipe option =
    match result with
    | RecipeCreated recipe -> Some recipe
    | _ -> None

//=============================================================================
// RECIPE SET: Collection from fan-out pass (artifacts 2 and 4)
//=============================================================================

/// The collection of recipes produced by a fan-out pass.
/// This is a discrete artifact that can be inspected independently.
type RecipeSet = {
    /// What kind of elaboration this is
    Kind: string  // "Intrinsic" | "Saturation"

    /// All recipes, keyed by original node ID
    Recipes: Map<NodeId, Recipe>

    /// Replacement map for quick lookup during fold-in
    /// Maps original NodeId → replacement root NodeId
    ReplacementMap: Map<NodeId, NodeId>

    /// Diagnostics for all recipe creation attempts (NEW)
    /// Includes successful, failed, and not-applicable cases
    Diagnostics: RecipeDiagnostic list
}

module RecipeSet =
    /// Create an empty recipe set
    let empty kind = {
        Kind = kind
        Recipes = Map.empty
        ReplacementMap = Map.empty
        Diagnostics = []
    }

    /// Create a recipe set from a list of recipes
    let fromList kind (recipes: Recipe list) : RecipeSet =
        let recipeMap =
            recipes
            |> List.map (fun r -> r.OriginalNodeId, r)
            |> Map.ofList
        let replacementMap =
            recipes
            |> List.map (fun r -> r.OriginalNodeId, r.ReplacementRootId)
            |> Map.ofList
        {
            Kind = kind
            Recipes = recipeMap
            ReplacementMap = replacementMap
            Diagnostics = []  // No diagnostics when using fromList (legacy path)
        }
    
    /// Get total count of new nodes being added
    let totalNewNodes (rs: RecipeSet) : int =
        rs.Recipes |> Map.toSeq |> Seq.map snd |> Seq.sumBy (fun r -> List.length r.NewNodes)
    
    /// Check if a node has a recipe
    let hasRecipe (nodeId: NodeId) (rs: RecipeSet) : bool =
        Map.containsKey nodeId rs.Recipes
    

// SPDX-License-Identifier: MIT

/// Fan-Out pass: sequential recipe creation.
///
/// This is Pass 1 (Intrinsic Fan-Out) or Pass 3 (Saturation Fan-Out).
///
/// Takes a PSG and a recipe-creation function, identifies nodes needing
/// elaboration, creates recipes sequentially, and collects them into a RecipeSet.
///
/// ARCHITECTURAL NOTE: This implementation creates recipes sequentially around
/// the global mutable NodeId.fresh() allocator. Parallel construction requires
/// collision-free allocation, validated proposal independence and coherent
/// fold-in; a scheduling primitive alone supplies none of those guarantees.
///
/// See Composer/docs/PSG_Elaboration_Fold_Architecture.md and
/// Composer/docs/Nanopass_Incremental_Contract_Direction.md.
module Clef.Compiler.Nanopass.FanOut

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe

//=============================================================================
// RECIPE CREATION FUNCTION TYPE
//=============================================================================

/// Function that creates a recipe for a single node.
/// Returns RecipeCreationResult with diagnostic context.
type RecipeCreator = SemanticNode -> SemanticGraph -> RecipeCreationResult

//=============================================================================
// RECIPE FAN-OUT
//=============================================================================

/// Fan-out pass: identify nodes needing elaboration and create recipe proposals.
///
/// Parameters:
/// - kind: "Intrinsic" or "Saturation" - labels the resulting RecipeSet
/// - shouldElaborate: predicate to identify nodes needing elaboration
/// - createRecipe: function to create a recipe for a node (returns RecipeCreationResult)
/// - graph: the input PSG
///
/// Returns: RecipeSet containing all recipes AND diagnostics (artifact 2 or 4)
let fanOut
    (kind: string)
    (shouldElaborate: SemanticNode -> bool)
    (createRecipe: RecipeCreator)
    (graph: SemanticGraph)
    : RecipeSet =

    // Find all nodes that need elaboration (reachability-agnostic)
    let nodesToElaborate =
        graph.Nodes
        |> Map.toSeq |> Seq.map snd
        |> Seq.filter (fun node -> shouldElaborate node)
        |> List.ofSeq

    if List.isEmpty nodesToElaborate then
        RecipeSet.empty kind
    else
        // Create recipes sequentially (deterministic NodeId allocation)
        let results =
            nodesToElaborate
            |> List.map (fun node ->
                let result = createRecipe node graph
                (node.Id, result))

        // Extract successful recipes
        let recipes =
            results
            |> List.choose (fun (_, result) -> tryGetRecipe result)

        // Build diagnostics for all attempts
        let diagnostics =
            results
            |> List.map (fun (nodeId, result) ->
                { NodeId = nodeId
                  ElaborationKind = kind
                  Result = result })

        // Build recipe maps
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
            Diagnostics = diagnostics
        }

// SPDX-License-Identifier: MIT

/// Fan-Out pass: parallel recipe creation using MailboxProcessor.
/// 
/// This is Pass 1 (Intrinsic Fan-Out) or Pass 3 (Saturation Fan-Out).
/// 
/// Takes a PSG and a recipe-creation function, identifies nodes needing
/// elaboration, spawns parallel workers to create recipes, and collects
/// them into a RecipeSet.
/// 
/// See: psg_elaboration_fold_architecture.md (Serena memory)
module FSharp.Native.Compiler.Nanopass.FanOut

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Nanopass.Recipe

//=============================================================================
// RECIPE CREATION FUNCTION TYPE
//=============================================================================

/// Function that creates a recipe for a single node.
/// Returns Some recipe if the node needs elaboration, None otherwise.
type RecipeCreator = SemanticNode -> SemanticGraph -> Recipe option

//=============================================================================
// PARALLEL FAN-OUT
//=============================================================================

/// Fan-out pass: identify nodes needing elaboration and create recipes in parallel.
/// 
/// Parameters:
/// - kind: "Intrinsic" or "Saturation" - labels the resulting RecipeSet
/// - shouldElaborate: predicate to identify nodes needing elaboration
/// - createRecipe: function to create a recipe for a node
/// - graph: the input PSG
/// 
/// Returns: RecipeSet containing all recipes (artifact 2 or 4)
let fanOut 
    (kind: string)
    (shouldElaborate: SemanticNode -> bool)
    (createRecipe: RecipeCreator)
    (graph: SemanticGraph) 
    : RecipeSet =
    
    // Find all reachable nodes that need elaboration
    let nodesToElaborate =
        graph.Nodes
        |> Map.toSeq |> Seq.map snd
        |> Seq.filter (fun node -> node.IsReachable && shouldElaborate node)
        |> List.ofSeq
    
    if List.isEmpty nodesToElaborate then
        RecipeSet.empty kind
    else
        // Create recipes in parallel using Async.Parallel
        let recipes =
            nodesToElaborate
            |> List.map (fun node ->
                async {
                    return createRecipe node graph
                })
            |> Async.Parallel
            |> Async.RunSynchronously
            |> Array.choose id
            |> List.ofArray
        
        RecipeSet.fromList kind recipes

/// Fan-out with diagnostic output
let fanOutWithDiagnostics
    (kind: string)
    (shouldElaborate: SemanticNode -> bool)
    (createRecipe: RecipeCreator)
    (graph: SemanticGraph)
    : RecipeSet * string list =
    
    let mutable diagnostics = []
    
    // Find all reachable nodes that need elaboration
    let nodesToElaborate =
        graph.Nodes
        |> Map.toSeq |> Seq.map snd
        |> Seq.filter (fun node -> node.IsReachable && shouldElaborate node)
        |> List.ofSeq
    
    diagnostics <- sprintf "[%s] Found %d node(s) to elaborate" kind (List.length nodesToElaborate) :: diagnostics
    
    if List.isEmpty nodesToElaborate then
        RecipeSet.empty kind, List.rev diagnostics
    else
        // Create recipes in parallel
        let recipes =
            nodesToElaborate
            |> List.map (fun node ->
                async {
                    let result = createRecipe node graph
                    return (node, result)
                })
            |> Async.Parallel
            |> Async.RunSynchronously
            |> Array.toList
        
        // Collect successful recipes and diagnostics
        let successfulRecipes =
            recipes
            |> List.choose (fun (node, result) ->
                match result with
                | Some recipe ->
                    diagnostics <- sprintf "[%s] Created recipe for node %d (%s)" 
                        kind (NodeId.value node.Id) recipe.ElaborationSource :: diagnostics
                    Some recipe
                | None -> None)
        
        let recipeSet = RecipeSet.fromList kind successfulRecipes
        diagnostics <- sprintf "[%s] Total recipes: %d, total new nodes: %d" 
            kind recipeSet.Recipes.Count (RecipeSet.totalNewNodes recipeSet) :: diagnostics
        
        recipeSet, List.rev diagnostics

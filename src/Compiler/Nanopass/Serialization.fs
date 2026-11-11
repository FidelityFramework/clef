// SPDX-License-Identifier: MIT

/// Serialization for RecipeSet intermediate artifacts.
///
/// Emits artifacts 02 (Intrinsic Recipes) and 04 (Saturation Recipes)
/// using the global ordinal artifact naming scheme.
module Clef.Compiler.Nanopass.Serialization

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Infrastructure.PhaseConfig
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe
open Fidelity.Data.JSON

//=============================================================================
// JSON SERIALIZATION
//=============================================================================

let private ensureDirectoryForFilePath (filePath: string) : unit =
    match System.IO.Path.GetDirectoryName(filePath) |> Option.ofObj with
    | Some dir when not (System.IO.Directory.Exists(dir)) ->
        System.IO.Directory.CreateDirectory(dir) |> ignore
    | _ -> ()

//=============================================================================
// RECIPE SERIALIZATION
//=============================================================================

let private number (value: int) = JsonValue.ofInt64 (int64 value)
let private nodeId = NodeId.value >> number

/// The recipe artifact carries a finite summary, not inference cells.
let private recipeValue (recipe: Recipe) =
    JsonValue.Object [
        "originalNodeId", nodeId recipe.OriginalNodeId
        "replacementRootId", nodeId recipe.ReplacementRootId
        "newNodeIds", JsonValue.Array (recipe.NewNodes |> List.map (fun node -> nodeId node.Id))
        "newNodeCount", number recipe.NewNodes.Length
        "newEdges", JsonValue.Array (recipe.NewEdges |> List.map (fun edge ->
            JsonValue.Object [
                "sources", JsonValue.Array (edge.Sources |> List.map nodeId)
                "target", nodeId edge.Target
                "class", JsonValue.String (sprintf "%A" edge.Class)
                "role", JsonValue.String (sprintf "%A" edge.Role)
                "ordinal", number edge.Ordinal ]))
        "elaborationKind", JsonValue.String recipe.ElaborationKind
        "elaborationSource", JsonValue.String recipe.ElaborationSource ]

/// Serialize a single recipe to JSON.
let serializeRecipe (recipe: Recipe) : string =
    recipeValue recipe |> Json.serializePretty

/// Serialize a RecipeSet to JSON (for intermediate emission).
let serializeRecipeSet (recipeSet: RecipeSet) : string =
    let recipes = recipeSet.Recipes |> Map.toList |> List.map snd
    let newNodes =
        recipes
        |> List.collect (fun recipe -> recipe.NewNodes)
        |> List.map (fun node ->
            let kind = sprintf "%A" node.Kind
            JsonValue.Object [
                "id", nodeId node.Id
                "kind", JsonValue.String (if kind.Length > 50 then kind.Substring(0, 50) + "..." else kind) ])
    JsonValue.Object [
        "kind", JsonValue.String recipeSet.Kind
        "recipeCount", number recipeSet.Recipes.Count
        "totalNewNodes", number (RecipeSet.totalNewNodes recipeSet)
        "recipes", JsonValue.Array (recipes |> List.map recipeValue)
        "newNodes", JsonValue.Array newNodes ]
    |> Json.serializePretty

/// Emit a RecipeSet using the artifact ID system
/// artifactId should be ArtifactId.IntrinsicRecipes (2) or ArtifactId.SaturationRecipes (4)
let emitRecipeSetArtifact (artifactId: int) (recipeSet: RecipeSet) : unit =
    match getArtifactFilePath artifactId with
    | None -> ()  // Emission disabled for this artifact
    | Some path ->
        let json = serializeRecipeSet recipeSet
        ensureDirectoryForFilePath path
        System.IO.File.WriteAllText(path, json)
        if isVerbose() then printfn "[CCS] Wrote artifact: %s" path

/// Emit intrinsic recipes (artifact 02)
let emitIntrinsicRecipes (recipeSet: RecipeSet) : unit =
    emitRecipeSetArtifact ArtifactId.IntrinsicRecipes recipeSet

/// Emit saturation recipes (artifact 04)
let emitSaturationRecipes (recipeSet: RecipeSet) : unit =
    emitRecipeSetArtifact ArtifactId.SaturationRecipes recipeSet

let emitDeadBodyRecipes (recipeSet: RecipeSet) : unit =
    match getArtifactFilePath ArtifactId.SaturationRecipes with
    | None -> ()
    | Some recipePath ->
        let directory = System.IO.Path.GetDirectoryName recipePath |> Option.ofObj |> Option.defaultValue "."
        let path = System.IO.Path.Combine(directory, "01a_dead_body_recipes.json")
        ensureDirectoryForFilePath path
        System.IO.File.WriteAllText(path, serializeRecipeSet recipeSet)

//=============================================================================
// DIAGNOSTIC SERIALIZATION
//=============================================================================

/// Created recipes refer to graph nodes; serialize their artifact summary rather
/// than traversing mutable type-inference cells and non-string measure-map keys.
/// The full node records are available in the corresponding PSG artifact.
let serializeDiagnostics (diagnostics: RecipeDiagnostic list) : string =
    diagnostics
    |> List.map (fun diagnostic ->
        let result =
            match diagnostic.Result with
            | RecipeCreated recipe -> JsonValue.Object ["RecipeCreated", recipeValue recipe]
            | NotApplicable reason -> JsonValue.Object ["NotApplicable", JsonValue.String reason]
            | CreationFailed (reason, context) ->
                JsonValue.Object [
                    "CreationFailed", JsonValue.Array [
                        JsonValue.String reason
                        JsonValue.Object (context |> Map.toList |> List.map (fun (key, value) -> key, JsonValue.String value)) ] ]
        JsonValue.Object [
            "NodeId", nodeId diagnostic.NodeId
            "ElaborationKind", JsonValue.String diagnostic.ElaborationKind
            "Result", result ])
    |> JsonValue.Array
    |> Json.serializePretty

/// Emit intrinsic diagnostics (artifact 02a)
let emitIntrinsicDiagnostics (diagnostics: RecipeDiagnostic list) : unit =
    // Use artifact ID 2 with "a" suffix convention: "02a_intrinsic_diagnostics.json"
    // For now, we'll construct the path manually since artifact IDs are integers
    match getArtifactFilePath ArtifactId.IntrinsicRecipes with
    | None -> ()
    | Some recipePath ->
        // Replace "02_intrinsic_recipes.json" with "02a_intrinsic_diagnostics.json"
        let diagPath = recipePath.Replace("02_intrinsic_recipes.json", "02a_intrinsic_diagnostics.json")
        let json = serializeDiagnostics diagnostics
        ensureDirectoryForFilePath diagPath
        System.IO.File.WriteAllText(diagPath, json)
        if isVerbose() then printfn "[CCS] Wrote intrinsic diagnostics: %s" diagPath

/// Emit saturation diagnostics (artifact 04a)
let emitSaturationDiagnostics (diagnostics: RecipeDiagnostic list) : unit =
    match getArtifactFilePath ArtifactId.SaturationRecipes with
    | None -> ()
    | Some recipePath ->
        // Replace "04_saturation_recipes.json" with "04a_saturation_diagnostics.json"
        let diagPath = recipePath.Replace("04_saturation_recipes.json", "04a_saturation_diagnostics.json")
        let json = serializeDiagnostics diagnostics
        ensureDirectoryForFilePath diagPath
        System.IO.File.WriteAllText(diagPath, json)
        if isVerbose() then printfn "[CCS] Wrote saturation diagnostics: %s" diagPath

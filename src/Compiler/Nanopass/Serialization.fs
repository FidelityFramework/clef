// SPDX-License-Identifier: MIT

/// Serialization for RecipeSet intermediate artifacts.
///
/// Emits artifacts 02 (Intrinsic Recipes) and 04 (Saturation Recipes)
/// using the global ordinal artifact naming scheme.
module Clef.Compiler.Nanopass.Serialization

open System.Text
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Infrastructure.PhaseConfig
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe
open FSharp.Json

//=============================================================================
// JSON SERIALIZATION HELPERS
//=============================================================================

let private escapeJson (s: string | null) : string =
    match Option.ofObj s with
    | None -> "null"
    | Some value ->
        let sb = StringBuilder()
        for c in value do
            match c with
            | '"' -> sb.Append("\\\"") |> ignore
            | '\\' -> sb.Append("\\\\") |> ignore
            | '\n' -> sb.Append("\\n") |> ignore
            | '\r' -> sb.Append("\\r") |> ignore
            | '\t' -> sb.Append("\\t") |> ignore
            | c when int c < 32 -> sb.Append(sprintf "\\u%04x" (int c)) |> ignore
            | c -> sb.Append(c) |> ignore
        sb.ToString()

let private ensureDirectoryForFilePath (filePath: string) : unit =
    match System.IO.Path.GetDirectoryName(filePath) |> Option.ofObj with
    | Some dir when not (System.IO.Directory.Exists(dir)) ->
        System.IO.Directory.CreateDirectory(dir) |> ignore
    | _ -> ()

//=============================================================================
// RECIPE SERIALIZATION
//=============================================================================

/// Serialize a single recipe to JSON
let serializeRecipe (recipe: Recipe) : string =
    let newNodeIds =
        recipe.NewNodes
        |> List.map (fun n -> let (NodeId nid) = n.Id in sprintf "%d" nid)
        |> String.concat ", "

    let (NodeId origId) = recipe.OriginalNodeId
    let (NodeId replId) = recipe.ReplacementRootId

    sprintf """{
    "originalNodeId": %d,
    "replacementRootId": %d,
    "newNodeIds": [%s],
    "newNodeCount": %d,
    "elaborationKind": "%s",
    "elaborationSource": "%s"
  }"""
        origId
        replId
        newNodeIds
        (List.length recipe.NewNodes)
        (escapeJson recipe.ElaborationKind)
        (escapeJson recipe.ElaborationSource)

/// Serialize a RecipeSet to JSON (for intermediate emission)
let serializeRecipeSet (recipeSet: RecipeSet) : string =
    let recipesJson =
        recipeSet.Recipes
        |> Map.toSeq |> Seq.map snd
        |> Seq.map serializeRecipe
        |> String.concat ",\n  "

    let allNewNodes =
        recipeSet.Recipes
        |> Map.toSeq |> Seq.map snd
        |> Seq.collect (fun r -> r.NewNodes)
        |> Seq.map (fun n ->
            let (NodeId nid) = n.Id
            sprintf """{"id": %d, "kind": "%s"}"""
                nid
                (escapeJson (sprintf "%A" n.Kind |> fun s -> if s.Length > 50 then s.Substring(0, 50) + "..." else s)))
        |> String.concat ",\n    "

    sprintf """{
  "kind": "%s",
  "recipeCount": %d,
  "totalNewNodes": %d,
  "recipes": [
  %s
  ],
  "newNodes": [
    %s
  ]
}"""
        (escapeJson recipeSet.Kind)
        recipeSet.Recipes.Count
        (RecipeSet.totalNewNodes recipeSet)
        recipesJson
        allNewNodes

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

//=============================================================================
// DIAGNOSTIC SERIALIZATION (using FSharp.Json)
//=============================================================================

/// Created recipes refer to graph nodes; serialize their artifact summary rather
/// than traversing mutable type-inference cells and non-string measure-map keys.
/// The full node records are available in the corresponding PSG artifact.
let serializeDiagnostics (diagnostics: RecipeDiagnostic list) : string =
    diagnostics
    |> List.map (fun diagnostic ->
        let result =
            match diagnostic.Result with
            | RecipeCreated recipe -> sprintf "{\"RecipeCreated\":%s}" (serializeRecipe recipe)
            | other -> Json.serialize other
        sprintf "{\"NodeId\":%s,\"ElaborationKind\":\"%s\",\"Result\":%s}"
            (Json.serialize diagnostic.NodeId) (escapeJson diagnostic.ElaborationKind) result)
    |> String.concat ",\n"
    |> sprintf "[%s]"

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

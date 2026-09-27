// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Recipes.MemoryExtentRecipes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients

/// The string origin/extent relation was settled by the early borrow recipe.
/// This owner joins that relation with the final scalar carrier, without
/// deriving a replacement width from a descriptor or a length envelope.
let settle (graph: SemanticGraph) (numeric: NumericWitnessProjection) =
    graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringExtent fact -> Some fact | _ -> None)
    |> List.fold (fun (operations, unresolved, required) extent ->
        match numeric.Values.TryFind extent.Site, StringBytes.byteRepresentation graph with
        | Some carrier, Some(element, declaration) ->
            let participants = Set.union extent.Participants carrier.Participants |> Set.add declaration
            let operation = MemoryWitnessOperation.BufferExtent
                                { Site = extent.Site; Source = extent.Source; Element = element; ElementDeclaration = declaration
                                  Result = carrier; Extent = extent; IndexUnsigned = true; Participants = participants }
            (extent.Site, operation) :: operations, unresolved, Set.add extent.Site required
        | _ -> operations, Map.add extent.Site "The string extent lacks its settled scalar carrier or explicit byte representation." unresolved, Set.add extent.Site required)
        ([], Map.empty, Set.empty)

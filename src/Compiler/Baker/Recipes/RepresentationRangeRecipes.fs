// SPDX-License-Identifier: MIT
/// Renew only changed joint support from one representation pass's input and
/// result. The source recurrence and its obligation identity remain stable.
module Clef.Compiler.Baker.Recipes.RepresentationRangeRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Finite = Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges

type Replacement = {
    RetiredEdges: Set<EdgeClass * EdgeRole * int * NodeId list * NodeId>
    Obligations: Set<NodeId>
    Enrichment: Enrichment
}

let edgeKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target

let private rangeRows (bound: Finite.Bound) sources =
    bound.Cell :: (bound.Writes |> List.map _.Value)
    |> List.map (fun target ->
        { Class = EdgeClass.Range; Role = EdgeRole.FiniteCellRange; Ordinal = 0
          Sources = sources; Target = target })

let elaborate (before: SemanticGraph) (graph: SemanticGraph) =
    let changes = Finite.tryRepresentationRenewal before graph |> Option.defaultValue []
    let retired =
        changes |> List.collect (fun change ->
            let sources = Set.toList change.PreviousParticipants
            constrains sources graph.Nodes[change.Obligation] :: rangeRows change.Bound sources)
        |> List.map edgeKey |> Set.ofList
    let added =
        changes |> List.collect (fun change ->
            let sources = Set.toList change.Bound.Participants
            constrains sources graph.Nodes[change.Obligation] :: rangeRows change.Bound sources)
    { RetiredEdges = retired
      Obligations = changes |> List.map _.Obligation |> Set.ofList
      Enrichment = { Enrichment.empty with NewEdges = added } }

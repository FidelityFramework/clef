// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Recipes.ContinuationObligationRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations

/// State the exact placement selected upstream. Source identities travel with
/// their concrete slots; neither solver dispatch invents a field or placement.
/// Persistent frames contain state/current slots, so positive slot sizes imply
/// positive extent. An empty transient activation has extent zero/alignment one.
let layout (enrichId: int) (name: string) (owner: SemanticNode)
           (slots: (NodeId * int * int * int) list) (extent: int) (alignment: int) : Enrichment =
    let node =
        obligationNode owner enrichId
            { Id = name; Kind = "continuation-layout"; Logic = "QF_LIA"
              Statement = "Continuation slots tile their exact extent in source-identity order, with disjoint fields and exact power-of-two alignment padding. Allocation lifetime, captured-view validity and aggregate memory budget are separate contracts."
              Source = fmtRange owner.Range; Refs = []
              Body = ObligationBody.ContinuationLayout(slots |> List.map (fun (_, offset, bytes, align) -> offset, bytes, align), extent, alignment) }
    { NewNodes = [node]
      NewEdges = [constrains (owner.Id :: (slots |> List.map (fun (source, _, _, _) -> source)) |> List.distinct) node]
      Annotated = [] }

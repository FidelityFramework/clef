// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.StringBorrows

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
module Recipes = Clef.Compiler.Baker.Recipes.StringBorrowRecipes

let normalize graph =
    let enrichment = Recipes.elaborate graph
    graph |> SemanticGraph.addNodes enrichment.Annotated |> SemanticGraph.addNodes enrichment.NewNodes
          |> SemanticGraph.addEdges enrichment.NewEdges

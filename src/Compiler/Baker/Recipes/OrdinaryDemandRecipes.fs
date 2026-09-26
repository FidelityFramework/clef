// SPDX-License-Identifier: MIT
/// Publish source absence proofs as joint demand relations. Actual computations
/// and logical signatures remain graph citizens; no reachability rewrite occurs.
module Clef.Compiler.Baker.Recipes.OrdinaryDemandRecipes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Demand = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand

let elaborate graph =
    { Enrichment.empty with NewEdges = Demand.analyze graph |> Demand.edges }

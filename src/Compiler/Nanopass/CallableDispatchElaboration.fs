// SPDX-License-Identifier: MIT
/// Finite callable adaptation is source elaboration through the same Baker
/// recipe and ordinary fan-out/fold-in protocol as closure materialization.
module Clef.Compiler.Nanopass.CallableDispatchElaboration

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Nanopass.Recipe
module Selection = Clef.Compiler.PSGSaturation.SemanticGraph.CallableDispatch
module Construction = Clef.Compiler.Baker.Recipes.CallableDispatchRecipes

let rec normalize graph =
    match Selection.plans graph |> List.tryHead with
    | None -> graph
    | Some plan ->
        let name = "Callable.dispatch"
        let context = mkContext plan.Formal.Range plan.Formal.Type graph.Platform name plan.Formal.Id
        let expansion = Construction.materialize context graph plan
        let create (node: SemanticNode) _ =
            RecipeCreated { OriginalNodeId = node.Id; NewNodes = expansion.Structure.NewNodes
                            ReplacementRootId = node.Id; ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = name }
        let folded = FoldIn.foldIn (FanOut.fanOut name (fun node -> node.Id = plan.Formal.Id) create graph) graph
        let materialized = ClosureEnvironmentElaboration.normalize { folded with Edges = expansion.Edges }
        normalize materialized

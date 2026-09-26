// SPDX-License-Identifier: MIT
/// Source closure formation precedes range, layout and continuation analysis.
/// Each admitted form is one Baker recipe and ordinary fan-out/fold-in step.
module Clef.Compiler.Nanopass.ClosureEnvironmentElaboration

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Recipes.ClosureEnvironmentRecipes
open Clef.Compiler.Nanopass.Recipe

let rec private elaborate (graph: SemanticGraph) =
    match plans graph |> List.tryHead with
    | None -> graph
    | Some plan ->
        let name = "Closure.environment"
        let context = mkContext plan.Source.Range plan.Source.Type graph.Platform name plan.Source.Id
        let result = materialize context graph plan
        let create (node: SemanticNode) _ =
            RecipeCreated { OriginalNodeId = node.Id; NewNodes = result.Structure.NewNodes
                            ReplacementRootId = node.Id; ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = name }
        let folded = FoldIn.foldIn (FanOut.fanOut name (fun node -> node.Id = plan.Source.Id) create graph) graph
        elaborate { folded with Edges = result.Edges }

let normalize (graph: SemanticGraph) =
    let rewritten = elaborate graph
    // EnvironmentWrite replaces the former Set target with the actual
    // environment and value operands. Retain the old nodes and provenance,
    // but refresh executable reachability at this owning rewrite boundary.
    // Open library graphs have no executable roots authorizing that cut.
    if obj.ReferenceEquals(graph, rewritten) || rewritten.DeclarationRoots.IsEmpty then rewritten
    else Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable rewritten

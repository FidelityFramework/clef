// SPDX-License-Identifier: MIT
/// Fold a first-demand recipe before numeric/layout analysis; later settlement
/// only refreshes typed current relations and never changes the schedule.
module Clef.Compiler.Nanopass.BindingDemand

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.Nanopass.Recipe
module Recipes = Clef.Compiler.Baker.Recipes.BindingDemandRecipes
module Demand = Clef.Compiler.Baker.Ingredients.BindingDemand
module Reports = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

let fanOut (expansion: Recipes.Expansion) graph =
    let create (source: SemanticNode) _ =
        RecipeCreated { OriginalNodeId = source.Id; ReplacementRootId = source.Id
                        NewNodes = expansion.Enrichment.Annotated; NewEdges = expansion.Enrichment.NewEdges
                        ElaborationKind = "Baker"; ElaborationSource = "OrdinaryBinding.first-demand" }
    FanOut.fanOut "OrdinaryBinding.first-demand" (fun node -> node.Id = expansion.Input.Binding) create graph

let foldIn (expansion: Recipes.Expansion) graph =
    // Keep the normal reviewable RecipeSet (including RecipeCreated diagnostic)
    // between semantic proposal and application. History retains its original
    // scope/order/types independently of the current proof relation.
    let recipes = fanOut expansion graph
    let retained = graph.Edges |> List.filter (fun edge ->
        not (edge.Class = EdgeClass.Structural && expansion.ReplacedIncidence.Contains edge.Target))
    let draft = { graph with Edges = retained }
    let folded = FoldIn.foldIn recipes draft
    let nodes = folded.Nodes |> Map.map (fun _ node -> { node with ValueRange = None })
    { folded with Nodes = nodes; Types = SemanticGraph.mkTypesIndex nodes
                  ModuleClassifications = SemanticGraph.mkModuleClassifications nodes }

let settle graph =
    let rows = (Recipes.settle graph).NewEdges
    let graph =
        if List.map Demand.key rows = (graph.Edges |> List.filter Demand.owned |> List.map Demand.key) then graph
        else { graph with Edges = (graph.Edges |> List.filter (Demand.owned >> not)) @ rows } |> SemanticGraph.invalidateWitness
    let diagnostics = Demand.failures graph |> List.map (fun failure ->
        ({ Severity = Reports.NativeDiagnosticSeverity.Error; Code = "CCS8403"; Message = failure.Reason
           Range = failure.Occurrence |> Option.bind graph.Nodes.TryFind |> Option.map _.Range |> Option.defaultValue Clef.Compiler.NativeTypedTree.NativeTypes.dummyRange
           RelatedNodes = failure.Participants |> Set.toList; Reachability = Reports.ReachabilityContext.Reachable } : Reports.Diagnostic))
    graph, diagnostics

let normalize graph =
    // Each disjoint mutable-cell snapshot family moves at most once. Independent
    // families can share a scope; re-read that scope after every concrete rewrite.
    let rec loop remaining graph =
        match Recipes.elaborate graph with
        | None -> graph
        | Some expansion when remaining > 0 -> loop (remaining - 1) (foldIn expansion graph)
        | Some _ -> graph // A nonconverging schedule remains an explicit Pending row.
    loop graph.Nodes.Count graph |> settle |> fst

// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.ProgramInitializationOrder

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Ingredients.Obligations
module Uses = Clef.Compiler.Baker.Ingredients.ProgramValueUses
module Recipe = Clef.Compiler.Baker.Recipes.ProgramInitializationOrderRecipes

let private bindingOf = function
    | EdgeRole.ProgramInitializationOrder participants ->
        participants |> List.tryPick (fun p -> if p.Role = ParticipantRole.InitializationBinding && p.Group = p.Node then Some p.Node else None)
    | _ -> None

let birth graph =
    let held = graph.Edges |> List.choose (fun edge -> bindingOf edge.Role) |> Set.ofList
    Uses.bindings graph |> List.filter (held.Contains >> not)
    |> List.map (Recipe.birth graph) |> Enrichment.concat
    |> fun enrichment ->
        // Same fold-in contract as obligation elaboration; callable scope is
        // known before final read participants, which remain explicitly pending.
        { graph with Nodes = enrichment.NewNodes |> List.fold (fun nodes node -> Map.add node.Id node nodes) graph.Nodes
                     Edges = graph.Edges @ enrichment.NewEdges }

let settle graph =
    let graph = birth graph
    let rows = graph.Edges |> List.choose (fun edge -> bindingOf edge.Role |> Option.map (fun binding -> binding, edge))
    let nodes, edges, diagnostics = rows |> List.fold (fun (nodes, edges, diagnostics) (binding, edge) ->
        let reading = Uses.read graph binding
        let obligation = graph.Nodes[edge.Target]
        let next = { obligation with Kind = SemanticKind.Obligation(Recipe.info graph.Nodes[binding] reading.Body) }
        let sources = List.map _.Node reading.Participants
        let edges = edges |> List.map (fun current ->
            if current.Target <> edge.Target then current else
            match current.Role with
            | EdgeRole.ProgramInitializationOrder _ -> { current with Role = EdgeRole.ProgramInitializationOrder reading.Participants; Sources = sources }
            | EdgeRole.Constrains -> { current with Sources = sources }
            | _ -> current)
        let errors = reading.Missing |> List.map (fun reason ->
            { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8403"
              Message = "Program callable initialization order requires further settlement: " + reason
              Range = graph.Nodes[binding].Range; RelatedNodes = binding :: sources
              Reachability = ReachabilityContext.Reachable })
        Map.add next.Id next nodes, edges, diagnostics @ errors) (graph.Nodes, graph.Edges, [])
    { graph with Nodes = nodes; Edges = edges }, diagnostics

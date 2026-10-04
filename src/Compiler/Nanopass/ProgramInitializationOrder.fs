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

/// Return the current ordered accounts without forcing unfinished Codata.
let settleWithAccounts graph =
    let graph = birth graph
    let rows = graph.Edges |> List.choose (fun edge -> bindingOf edge.Role |> Option.map (fun binding -> binding, edge))
    let nodes, edges, diagnostics = rows |> List.fold (fun (nodes, edges, diagnostics) (binding, edge) ->
        let reading = Uses.read graph binding
        let obligation = graph.Nodes[edge.Target]
        let next = { obligation with Kind = SemanticKind.Obligation(Recipe.info graph.Nodes[binding] reading.Body) }
        let sources = reading.Participants |> List.map (fun (participant: Participant) -> participant.Node)
        let edges = edges |> List.map (fun (current: Hyperedge) ->
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
    let accounts = rows |> List.fold (fun accounts (binding, edge) ->
        if Map.containsKey binding accounts then invalidOp "Program initialization order repeated a current binding account."
        let reading = Uses.read graph binding
        let account : ProgramInitializationOrderAccount =
            { Binding = binding; Claim = edge.Target; Participants = reading.Participants }
        Map.add binding account accounts) Map.empty
    { graph with Nodes = nodes; Edges = edges }, diagnostics, accounts

/// Retained component callers consume the graph/diagnostics pair. Production
/// carries the explicit accounts through final source-owned Codata assembly.
let settle graph =
  let settled, diagnostics, accounts = settleWithAccounts graph
  { settled with Codata = lazy { settled.Codata.Value with ProgramInitializationOrders = accounts } }, diagnostics

/// Complete read/scope/phase membership is a source premise. Pending claims
/// remain explicit; they cannot be mapped into a completed public proposition.
let validateAccounts (graph: SemanticGraph) =
    let held = graph.Codata.Value.ProgramInitializationOrders
    let bindings = Uses.bindings graph |> Set.ofList
    let errors = ResizeArray<NodeId * string>()
    for binding in Set.union bindings (held.Keys |> Set.ofSeq) do
        let rows = graph.Edges |> List.filter (fun edge -> bindingOf edge.Role = Some binding)
        let reading = Uses.read graph binding
        let agrees =
            match held.TryFind binding, rows with
            | Some account, [{ Class = EdgeClass.Provenance; Role = EdgeRole.ProgramInitializationOrder participants; Target = claim; Sources = sources; Ordinal = 0 }]
                when bindings.Contains binding && account.Binding = binding && account.Claim = claim &&
                     participants = reading.Participants && account.Participants = participants &&
                     sources = List.map (fun (participant: Participant) -> participant.Node) participants ->
                match graph.Nodes.TryFind claim, graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = claim) with
                | Some { Kind = SemanticKind.Obligation info }, [{ Class = EdgeClass.Obligation; Sources = actual; Ordinal = 0 }] ->
                    info = Recipe.info graph.Nodes[binding] reading.Body && actual = sources
                | _ -> false
            | _ -> false
        if not agrees then errors.Add(binding, "Program initialization order account no longer retains its complete current source reading.")
    List.ofSeq errors

// SPDX-License-Identifier: MIT
/// Establish source premises once the final demand relation is available.
module Clef.Compiler.Nanopass.PremiseEstablishment

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module Borrows = Clef.Compiler.Baker.Recipes.StringBorrowRecipes
module Access = Clef.Compiler.Baker.Recipes.MemoryAccessRecipes
module Demand = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand

let private diagnostic (graph: SemanticGraph) (site, participants, message) : Diagnostic =
    { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8403"; Message = message
      Range = graph.Nodes[site].Range; RelatedNodes = Set.toList participants
      Reachability = ReachabilityContext.Reachable }

let private borrows graph =
    let results = Borrows.establish graph
    let rows = results |> List.collect (function Result.Ok rows -> rows | Result.Error _ -> [])
    let failures = results |> List.choose (function Result.Error failure -> Some failure | Result.Ok _ -> None)
    let views = rows |> List.choose (fun edge -> match edge.Role with EdgeRole.StringByteView _ -> Some edge.Target | _ -> None) |> Set.ofList
    let extents = rows |> List.choose (fun edge -> match edge.Role with EdgeRole.StringExtent _ -> Some edge.Target | _ -> None) |> Set.ofList
    let replaced edge =
        match edge.Role with
        | EdgeRole.StringByteView _ | EdgeRole.StringByteStorage _ -> views.Contains edge.Target
        | EdgeRole.StringExtent _ -> extents.Contains edge.Target
        | _ -> false
    { graph with Edges = (graph.Edges |> List.filter (replaced >> not)) @ rows }, List.map (diagnostic graph) failures

let private storage (deferrals: Map<_, Set<OrdinaryOmission>>) (graph: SemanticGraph) =
    let rows, histories, failures = graph.LiteralStorage |> Map.fold (fun (rows, histories, failures) literal row ->
        let error message = rows, histories, (literal, Set.singleton literal, message) :: failures
        match row, deferrals.TryFind literal with
        | LiteralStorage.NotMaterialized (StoragePremise.Pending early), Some current when not current.IsEmpty ->
            let history =
                { Class = EdgeClass.Provenance; Role = EdgeRole.LiteralStorageHistory { Literal = literal; Early = early }
                  Ordinal = 0; Target = literal
                  Sources = early |> List.collect (fun omission -> [omission.Site; omission.Actual]) }
            Map.add literal (LiteralStorage.NotMaterialized (StoragePremise.Established (Set.toList current))) rows, history :: histories, failures
        | LiteralStorage.NotMaterialized _, None ->
            error "The storage of this string literal was not materialized, and after the final demand rows a demanded position reads it."
        | LiteralStorage.Materialized _, Some _ ->
            error "The storage of this string literal was materialized, and after the final demand rows no demanded position reads it."
        | LiteralStorage.NotMaterialized (StoragePremise.Pending _), Some _ ->
            error "The omission premise of this string literal remains pending after the final demand rows."
        | _ -> rows, histories, failures) (graph.LiteralStorage, [], [])
    { graph with LiteralStorage = rows; Edges = graph.Edges @ List.rev histories },
    failures |> List.rev |> List.map (diagnostic graph)

let private byteRanges (graph: SemanticGraph) =
    let guards =
        graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard)
        |> List.groupBy _.Target |> Map.ofList
    let rows, failures = graph.Edges |> List.fold (fun (rows, failures) edge ->
        match edge.Role, guards.TryFind edge.Target with
        | EdgeRole.StringByteRange _, Some guards ->
            match guards with
            | [guard] ->
                match Access.byteRange graph guard with
                | Some current -> current :: rows, failures
                | None -> rows, edge.Target :: failures
            | _ -> rows, edge.Target :: failures
        | _ -> edge :: rows, failures) ([], [])
    { graph with Edges = List.rev rows },
    failures |> List.rev |> List.distinct |> List.map (fun site ->
        diagnostic graph (site, Set.singleton site,
                          "A string byte read lost the storage evidence of its borrow after the final demand rows."))

let normalize graph =
    match Demand.tryDeferrals graph with
    | Result.Error failures -> graph, Demand.diagnostics graph failures
    | Result.Ok deferrals ->
        let graph, borrowDiagnostics = borrows graph
        let graph, storageDiagnostics = storage deferrals graph
        let graph, byteDiagnostics = byteRanges graph
        SemanticGraph.invalidateWitness graph, borrowDiagnostics @ storageDiagnostics @ byteDiagnostics

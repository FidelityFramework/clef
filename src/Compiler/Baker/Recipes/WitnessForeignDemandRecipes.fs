// SPDX-License-Identifier: MIT
/// Prepare foreign storage, explicit demand and structural incidence under
/// Baker. Publication copies these native rows and runs none of their readers.
module Clef.Compiler.Baker.Recipes.WitnessForeignDemandRecipes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module BorrowedViews = Clef.Compiler.PSGSaturation.SemanticGraph.BorrowedViews
module MappedSpans = Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans
module MappedBindings = Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings
module Mmio = Clef.Compiler.PSGSaturation.SemanticGraph.Mmio
module ExplicitDemand = Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand
module Closures = Clef.Compiler.Baker.Ingredients.Closures

let private layout (value: BorrowedViews.Layout) : WitnessBorrowedViewLayout =
    { Schema = value.Schema; ElementBits = value.ElementBits; Range = value.Range
      Alignment = value.Alignment; Access = value.Access }

/// Preserve the complete current owner account, including unavailable layout
/// premises. Live scope selection does not yet establish boundary closure for
/// these domains and therefore cannot prune this preparation.
let project (graph: SemanticGraph) : WitnessPreparedRows =
    let applications =
        graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with
            | SemanticKind.Application(callee, _) -> Some(id, callee)
            | _ -> None)
    let borrowed =
        applications |> List.choose (fun (id, _) ->
            BorrowedViews.operation graph id
            |> Option.map (fun (operation, view, arguments, declaredLayout) ->
                let span = declaredLayout |> Result.bind (MappedSpans.forLayout graph)
                id, ({ Site = id; Operation = operation; View = view; Arguments = arguments
                       Layout = Result.map layout declaredLayout; Span = span } : WitnessBorrowedViewOperation)))
    let mmio =
        applications |> List.choose (fun (id, _) ->
            Mmio.operation graph id
            |> Option.map (fun (operation, arguments) ->
                id, ({ Site = id; Operation = operation; Arguments = arguments } : WitnessMmioOperation)))
    let mapped =
        applications |> List.choose (fun (id, callee) ->
            MappedBindings.tryFindCall graph callee |> Option.map (fun _ -> id))
    let operands =
        graph.Nodes |> Map.toList |> List.choose (fun (id, _) ->
            ExplicitDemand.operand graph id |> Option.map (fun operand -> id, operand))
    let relations =
        graph.Edges |> List.choose (fun edge ->
            let frontier =
                match edge.Role with
                | EdgeRole.EagerDemand frontier -> Some(Some frontier)
                | EdgeRole.EagerDemandPending -> Some None
                | _ -> None
            frontier |> Option.map (fun frontier ->
                edge.Target, ({ Sources = edge.Sources; Ordinal = edge.Ordinal; Frontier = frontier
                                IsDemand = edge.Class = EdgeClass.Demand } : WitnessEagerDemandRelation)))
        |> List.groupBy fst
        |> List.map (fun (target, rows) -> target, List.map snd rows)
    let implied =
        graph.Nodes |> Map.toList |> List.collect (fun (_, node) -> Closures.structuralIncidence node)
    { Foreign = { BorrowedViews = Map.ofList borrowed; Mmio = Map.ofList mmio; MappedCalls = Set.ofList mapped }
      Demand = { Operands = Map.ofList operands; Relations = Map.ofList relations }
      Edges = implied @ graph.Edges }

/// Source re-observation, never a publication-time reconstruction.
let matches (held: WitnessPreparedRows) (current: WitnessPreparedRows) =
    let edge (row: Hyperedge) = row.Class, row.Role, row.Sources, row.Target, row.Ordinal
    held.Foreign = current.Foreign && held.Demand = current.Demand &&
    List.map edge held.Edges = List.map edge current.Edges

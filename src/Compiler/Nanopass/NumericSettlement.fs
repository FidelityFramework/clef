// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.NumericSettlement

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
module Numeric = Clef.Compiler.Baker.Ingredients.NumericValues

let normalize (graph: SemanticGraph) =
    let previousMeets = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.NumericDomain domain -> Some domain.OperationMeets | _ -> None)
                        |> List.fold (fun combined own -> Map.fold (fun values id meets -> Map.add id meets values) combined own) Map.empty
    let facts = graph.Codata.Value
    let retainedMeets = facts.Meets |> Map.toList |> List.choose (fun (id, meets) ->
        let own = previousMeets.TryFind id |> Option.defaultValue []
        let retained = meets |> List.filter (fun meet -> not(List.contains meet own))
        if retained.IsEmpty then None else Some(id, retained)) |> Map.ofList
    let graph = { graph with Codata = lazy { facts with Meets = retainedMeets } }
    let retired = graph.Nodes |> Map.fold (fun ids id node -> if Numeric.owned node then Set.add id ids else ids) Set.empty
    let edges = graph.Edges |> List.filter (fun edge ->
        let own = match edge.Role with EdgeRole.NumericDomain _ | EdgeRole.NumericCarrier _ | EdgeRole.NumericProof _ | EdgeRole.NumericOperation _ | EdgeRole.NumericOperationProof _ | EdgeRole.NumericIndexTransport _ -> true | _ -> false
        not own && not (retired.Contains edge.Target) && not (edge.Sources |> List.exists retired.Contains))
    let graph = { graph with Nodes = graph.Nodes |> Map.filter (fun id _ -> not (retired.Contains id)); Edges = edges } |> SemanticGraph.invalidateWitness
    let enrichment = Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.elaborate graph
    let graph = graph |> SemanticGraph.addNodes enrichment.NewNodes |> SemanticGraph.addNodes enrichment.Annotated |> SemanticGraph.addEdges enrichment.NewEdges
    let operationMeets = enrichment.NewEdges |> List.choose (fun edge -> match edge.Role with EdgeRole.NumericDomain domain -> Some domain.OperationMeets | _ -> None)
    let meets = operationMeets |> List.fold (fun values own -> Map.fold (fun values site meets ->
        let combined = (values |> Map.tryFind site |> Option.defaultValue []) @ meets |> List.distinct
        if combined.IsEmpty then values else Map.add site combined values) values own) retainedMeets
    { graph with Codata = lazy { facts with Meets = meets; WitnessEmission = None } }

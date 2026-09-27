// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.MemorySettlement

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.Baker.Ingredients.Obligations
module Memory = Clef.Compiler.Baker.Ingredients.MemoryValues
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries

let normalize (graph: SemanticGraph) =
    let retired = graph.Nodes |> Map.fold (fun ids id node -> if Memory.owned node then Set.add id ids else ids) Set.empty
    let edges = graph.Edges |> List.filter (fun edge ->
        let own = match edge.Role with EdgeRole.MemoryDomain _ | EdgeRole.MemoryOperation _ | EdgeRole.MemoryProof _ | EdgeRole.MemoryArrayCopy _ -> true | _ -> false
        not own && not (retired.Contains edge.Target) && not (edge.Sources |> List.exists retired.Contains))
    let graph = { graph with Nodes = graph.Nodes |> Map.filter (fun id _ -> not (retired.Contains id)); Edges = edges } |> SemanticGraph.invalidateWitness
    match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
    | Error _ -> graph
    | Ok numeric ->
        let anchor = Boundary.anchor (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()) graph
                     |> fun node -> { node with Metadata = node.Metadata.Remove "Baker.BoundaryOwned" } |> Memory.markOwned
        let extentOperations, extentFailures, extentRequired = Clef.Compiler.Baker.Recipes.MemoryExtentRecipes.settle graph numeric
        let enrichment, operations, failures, required = Clef.Compiler.Baker.Recipes.MemoryAccessRecipes.settle graph numeric
        let arrayEnrichment,arrayOperations,copies,arrayFailures,arrayRequired =
            Clef.Compiler.Baker.Recipes.ArrayMemoryRecipes.settle graph numeric (extentOperations@operations)
        let viewOperations,viewFailures,viewRequired =
            Clef.Compiler.Baker.Recipes.StringViewRecipes.settle graph numeric
                (Map.ofList(extentOperations@operations@arrayOperations)) (copies |> List.map(fun copy -> copy.Site,copy) |> Map.ofList)
        let enrichment=Enrichment.combine enrichment arrayEnrichment
        let merge left right=Map.fold(fun values id reason -> Map.add id reason values) left right
        let proofs = enrichment.NewEdges |> List.choose (fun edge -> match edge.Role with EdgeRole.MemoryProof proof -> Some proof | _ -> None)
        let domain =
            { Premises = Memory.premises graph; Platform = Boundary.platformPremise graph.Platform
              Meets = graph.Codata.Value.Meets; Guards = Memory.guards graph; Requirements = Memory.requirements graph
              StringRelations = Memory.stringRelations graph
              AllocationConstructions=Memory.allocationConstructions graph; CopyConstructions=Memory.copyConstructions graph; ArrayCopies=copies
              Proofs = proofs
              Required = Set.unionMany [required;extentRequired;arrayRequired;viewRequired]
              Operations = extentOperations @ operations @ arrayOperations @ viewOperations
              Unresolved = merge (merge (merge failures extentFailures) arrayFailures) viewFailures }
        let enrichment = Enrichment.combine enrichment
                            { NewNodes = [anchor]; Annotated = []
                              NewEdges = Memory.domainRow anchor.Id domain :: Memory.domainRewrite anchor.Id domain :: (domain.Operations |> List.map Memory.operationRow) @ (copies |> List.map Memory.copyRow) }
        graph |> SemanticGraph.addNodes enrichment.NewNodes |> SemanticGraph.addNodes enrichment.Annotated |> SemanticGraph.addEdges enrichment.NewEdges

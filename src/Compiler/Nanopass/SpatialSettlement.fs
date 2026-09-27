// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.SpatialSettlement

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.Baker.Ingredients.Obligations
module Spatial = Clef.Compiler.Baker.Ingredients.SpatialValues
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries

let normalize (graph: SemanticGraph) =
    let retired = graph.Nodes |> Map.fold (fun ids id node -> if Spatial.owned node then Set.add id ids else ids) Set.empty
    let edges = graph.Edges |> List.filter (fun edge ->
        let own = match edge.Role with EdgeRole.SpatialModuleDomain _ | EdgeRole.HardwareModule _ | EdgeRole.KernelModule _ | EdgeRole.SpatialProof _ -> true | _ -> false
        not own && not(retired.Contains edge.Target) && not(edge.Sources |> List.exists retired.Contains))
    let graph = { graph with Nodes=graph.Nodes |> Map.filter (fun id _ -> not(retired.Contains id)); Edges=edges } |> SemanticGraph.invalidateWitness
    match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
    | Error _ -> graph
    | Ok numeric ->
        let anchor = Boundary.anchor (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()) graph
                     |> fun node -> { node with Metadata=node.Metadata.Remove "Baker.BoundaryOwned" } |> Spatial.markOwned
        let hardwareEnrichment,hardware,hardwareFailures,hardwareRequired = Clef.Compiler.Baker.Recipes.HardwareModuleRecipes.settle graph numeric
        let kernelEnrichment,kernels,kernelFailures,kernelRequired = Clef.Compiler.Baker.Recipes.KernelModuleRecipes.settle graph numeric
        let enrichment = Enrichment.combine hardwareEnrichment kernelEnrichment
        let proofs = enrichment.NewEdges |> List.choose (fun edge -> match edge.Role with EdgeRole.SpatialProof proof -> Some proof | _ -> None)
        let domain =
            { Premises=Spatial.premises graph; SourceFiles=Spatial.sourceFiles graph; Platform=Boundary.platformPremise graph.Platform; Meets=graph.Codata.Value.Meets
              Representations=numeric.OccurrenceRepresentations; Carriers=numeric.Values; NumericOperations=numeric.Operations
              FieldRanges=graph.FieldRanges.Value; Pins=graph.Codata.Value.Pins
              Required=Set.union hardwareRequired kernelRequired; Hardware=hardware; Kernels=kernels; Proofs=proofs
              Unresolved=Map.fold (fun failures id reason -> Map.add id reason failures) hardwareFailures kernelFailures }
        let enrichment = Enrichment.combine enrichment
                            { NewNodes=[anchor]; Annotated=[]
                              NewEdges=Spatial.domainRow anchor.Id domain :: Spatial.domainRewrite anchor.Id domain ::
                                       (hardware |> List.map Spatial.hardwareRow) @ (kernels |> List.map Spatial.kernelRow) }
        graph |> SemanticGraph.addNodes enrichment.NewNodes |> SemanticGraph.addNodes enrichment.Annotated |> SemanticGraph.addEdges enrichment.NewEdges

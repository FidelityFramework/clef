// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Ingredients.SpatialValues

open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let owned (node: SemanticNode) = node.Metadata.ContainsKey "Baker.SpatialPublicationOwned"
let markOwned (node: SemanticNode) = { node with Metadata = node.Metadata.Add("Baker.SpatialPublicationOwned", MetadataValue.Bool true) }
let premises (graph: SemanticGraph) = graph.Nodes |> Map.fold (fun values id node ->
    if owned node || Boundaries.ownedNode node then values else Map.add id (Boundaries.premise node) values) Map.empty
let sourceFiles (graph: SemanticGraph) = graph.Nodes |> Map.fold (fun values id node ->
    if owned node || Boundaries.ownedNode node then values else Map.add id node.Range.File values) Map.empty
let kernelProofBody (plan: KernelModuleWitness) =
    ObligationBody.SpatialKernelPartition(bigint plan.Elements,bigint plan.Grain,plan.Target.Columns,
        plan.Tiles |> List.map (fun tile -> tile.Column,bigint tile.Offset,bigint tile.Elements),plan.Target.FifoDepth,plan.Target.Iterations)
let row role sources target = { Class = EdgeClass.Spatial; Role = role; Ordinal = 0; Sources = sources; Target = target }
let hardwareRow (plan: HardwareModuleWitness) =
    row (EdgeRole.HardwareModule plan) (plan.Scope :: plan.StepBinding :: plan.Implementation :: (plan.Parameters |> List.map snd) @ [plan.Result] @ Set.toList plan.Participants) plan.Site
let kernelRow (plan: KernelModuleWitness) =
    row (EdgeRole.KernelModule plan) (plan.Scope :: plan.ComputeBinding :: plan.Implementation :: (plan.Parameters |> List.map snd) @ [plan.Result] @ Set.toList plan.Participants) plan.Site
let proofRows (proof: SpatialProof) =
    let sources = proof.Site :: Set.toList proof.Participants
    [ row (EdgeRole.SpatialProof proof) sources proof.Obligation
      { Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = 0; Sources = sources; Target = proof.Obligation }
      { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = sources; Target = proof.Obligation } ]
let domainRow anchor (domain: SpatialModuleDomain) = row (EdgeRole.SpatialModuleDomain domain) (Map.keys domain.Premises |> Seq.toList) anchor
let domainRewrite anchor (domain: SpatialModuleDomain) =
    { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = Map.keys domain.Premises |> Seq.toList; Target = anchor }

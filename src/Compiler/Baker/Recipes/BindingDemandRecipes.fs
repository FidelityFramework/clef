// SPDX-License-Identifier: MIT
/// The source recipe retains its input order and moves a complete pure alias
/// family together. Existing bindings, reads, types and activation identities stay.
module Clef.Compiler.Baker.Recipes.BindingDemandRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Demand = Clef.Compiler.Baker.Ingredients.BindingDemand
module Incidence = Clef.Compiler.Baker.Ingredients.Closures

type Expansion = {
    Input: Demand.Schedule
    ReplacedIncidence: Set<NodeId>
    Enrichment: Enrichment
}

let elaborate (graph: SemanticGraph) =
    Demand.analyze graph |> List.tryFind (fun schedule ->
        schedule.Pending.IsNone && schedule.Desired <> (schedule.Slots |> List.map _.Statement))
    |> Option.map (fun schedule ->
        let replacements = List.zip schedule.Slots schedule.Desired
        let parents = replacements |> List.map (fun (slot, _) -> slot.Parent) |> Set.ofList
        let changedParents =
            parents |> Set.toList |> List.map (fun parent ->
                let node = graph.Nodes[parent]
                let updates = replacements |> List.choose (fun (slot, value) -> if slot.Parent = parent then Some(slot.Ordinal, value) else None) |> Map.ofList
                let children = node.Children |> List.mapi (fun ordinal child -> updates.TryFind ordinal |> Option.defaultValue child)
                { node with Kind = SemanticKind.Sequential children; Children = children })
        let changedStatements = replacements |> List.map (fun (slot, value) -> { graph.Nodes[value] with Parent = Some slot.Parent })
        let history =
            let exists = graph.Edges |> List.exists (fun edge ->
                edge.Target = schedule.Binding && match edge.Role with EdgeRole.OrdinaryBindingDemandHistory _ -> true | _ -> false)
            if exists then [] else
            [{ Class = EdgeClass.Provenance; Role = EdgeRole.OrdinaryBindingDemandHistory schedule.Evidence
               Target = schedule.Binding; Ordinal = 0; Sources = schedule.Evidence.Participants |> List.map _.Node }]
        { Input = schedule; ReplacedIncidence = parents
          Enrichment = { Enrichment.empty with
                            Annotated = changedParents @ changedStatements
                            NewEdges = history @ (changedParents |> List.collect Incidence.structuralIncidence) } })

let settle graph = { Enrichment.empty with NewEdges = Demand.analyze graph |> Demand.edges }

// SPDX-License-Identifier: MIT
/// Realize bounded child allocations inside their owning continuation frame.
/// Descriptors are values; the separately enumerated region is their backing
/// storage. Both have the lifetime of the owning enumeration, not one pull.
module Clef.Compiler.Nanopass.SequenceRegions

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module LayoutProof = Clef.Compiler.Baker.Recipes.ContinuationObligationRecipes

type Residual = { Site: NodeId; Reason: string }
type Settlement = {
    Frames: Map<NodeId, ContinuationFrame>
    Regions: Map<NodeId, ContinuationRegion>
    Evidence: Enrichment
    Unresolved: Residual list
}

let settle (graph: SemanticGraph) (frames: Map<NodeId, ContinuationFrame>)
           (sites: Map<NodeId, NodeId>) (origins: Map<NodeId, NodeId>) =
    let owners = frames.Values |> Seq.map (fun frame -> frame.Generator, frame.Owner) |> Map.ofSeq
    let requests, errors = sites |> Map.toList |> List.fold (fun (requests, errors) (site, generator) ->
        match owners.TryFind generator, origins.TryFind site with
        | Some parent, Some child when frames.ContainsKey child -> (parent, (site, child)) :: requests, errors
        | _ -> requests, { Site = site; Reason = "An owned continuation region requires exact parent and child frame identities." } :: errors) ([], [])
    let requests = requests |> List.groupBy fst |> Map.ofList |> Map.map (fun _ values -> values |> List.map snd |> List.sortBy fst)
    let roundUp value alignment = ((value + alignment - 1L) / alignment) * alignment
    let rec rounds (remaining: Map<NodeId, ContinuationFrame>) (completed: Map<NodeId, ContinuationFrame>) (regions: Map<NodeId, ContinuationRegion>) evidence errors =
        if Map.isEmpty remaining then { Frames = completed; Regions = regions; Evidence = evidence; Unresolved = errors }
        else
            let ready = remaining |> Map.filter (fun owner _ ->
                requests.TryFind owner |> Option.defaultValue [] |> List.forall (fun (_, child) -> Map.containsKey child completed))
            if ready.IsEmpty then
                let unresolved = remaining |> Map.toList |> List.map (fun (owner, _) ->
                    { Site = owner; Reason = "Continuation region dependencies are recursive; a finite owned extent has not been established." })
                { Frames = Map.fold (fun all id frame -> Map.add id frame all) completed remaining
                  Regions = regions; Evidence = evidence; Unresolved = errors @ unresolved }
            else
                let completed, regions, evidence, errors =
                    ready |> Map.fold (fun (completed, regions, evidence, errors) owner frame ->
                        let children = requests.TryFind owner |> Option.defaultValue []
                        if children.IsEmpty then Map.add owner frame completed, regions, evidence, errors
                        else
                            let prefix = frame.Slots |> List.map (fun slot -> slot.Source, slot.Field.Offset.Value, slot.Field.Size.Value, slot.Field.Align.Value)
                            let start = prefix |> List.fold (fun finish (_, offset, size, _) -> max finish (int64 offset + int64 size)) 0L
                            let fields, newRegions, finish, alignment =
                                children |> List.fold (fun (fields, placed, finish, alignment) (site, child) ->
                                    let childFrame = completed[child]
                                    let offset = roundUp finish (int64 childFrame.Alignment)
                                    let region = { ParentOwner = owner; ParentFormal = frame.Formal; ChildOwner = child
                                                   Offset = int offset; Bytes = childFrame.Bytes; Alignment = childFrame.Alignment }
                                    (site, int offset, childFrame.Bytes, childFrame.Alignment) :: fields,
                                    Map.add site region placed, offset + int64 childFrame.Bytes, max alignment childFrame.Alignment)
                                    ([], Map.empty, start, frame.Alignment)
                            let extent = roundUp finish (int64 alignment)
                            if extent > int64 System.Int32.MaxValue then
                                Map.add owner frame completed, regions, evidence,
                                { Site = owner; Reason = "The owned continuation extent exceeds the representable layout bound." } :: errors
                            else
                                let proof = LayoutProof.layout (NodeId.value owner) (sprintf "seq_%d_owned_regions" (NodeId.value owner))
                                                graph.Nodes[owner] (prefix @ List.rev fields) (int extent) alignment
                                let proofEdges = proof.NewEdges |> List.map (fun edge ->
                                    { edge with Sources = List.distinct (edge.Sources @ (children |> List.map snd)) })
                                let proof = { proof with NewEdges = proofEdges }
                                let relationships = children |> List.mapi (fun index (site, child) -> {
                                    Sources = [owner; child; frame.Formal]; Target = site
                                    Class = EdgeClass.Suspension; Role = EdgeRole.ContinuationRegion; Ordinal = index })
                                let frame = { frame with Bytes = int extent; Alignment = alignment
                                                         Obligations = frame.Obligations @ (proof.NewNodes |> List.map _.Id) }
                                Map.add owner frame completed,
                                Map.fold (fun all site region -> Map.add site region all) regions newRegions,
                                Enrichment.combine evidence { proof with NewEdges = proof.NewEdges @ relationships }, errors)
                        (completed, regions, evidence, errors)
                rounds (remaining |> Map.filter (fun owner _ -> not (ready.ContainsKey owner))) completed regions evidence errors
    rounds frames Map.empty Map.empty Enrichment.empty errors

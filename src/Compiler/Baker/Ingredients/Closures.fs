// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Closure ingredients preserve source identities while making direct capture
/// parameters and their ordinary references explicit in the PSG.
module Clef.Compiler.Baker.Ingredients.Closures

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

let rec prependTypes captures ty =
    match ty with
    | NativeType.TForall (variables, body) -> NativeType.TForall (variables, prependTypes captures body)
    | _ -> List.foldBack (fun (capture: CaptureInfo) rest -> NativeType.TFun (capture.Type, rest)) captures ty

/// An in-place semantic enrichment retains the source range, node identity,
/// arena and metadata; only the stated kind/type/structural children change.
let enrich (source: SemanticNode) kind ty children emission signature : SaturationParser<unit> =
    saturation {
        let! state = getUserState
        let metadata =
            if signature && not (source.Metadata.ContainsKey ClosureMetadata.SourceSignature) then
                source.Metadata.Add(ClosureMetadata.SourceSignature, MetadataValue.Type source.Type)
            else source.Metadata
        let node =
            { source with Kind = kind; Type = ty; Children = children; EmissionStrategy = emission; Metadata = metadata }
            |> markBaker state.OriginalHOF state.ExpansionId
        do! emit node
    }

let captureArgument (site: SemanticNode) (capture: CaptureInfo) source : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode { state with SourceRange = site.Range } (SemanticKind.VarRef (capture.Name, Some source)) capture.Type []
        do! emit node
        return node.Id
    }

let captureProvenance lambda source parameter : Hyperedge =
    { Sources = [lambda; source]; Target = parameter
      Class = EdgeClass.Provenance; Role = EdgeRole.CaptureOrigin; Ordinal = 0 }

/// Refresh the kind-derived incidence of enriched nodes. Other relations
/// (including obligations and provenance) survive independently of that table.
let structuralIncidence (node: SemanticNode) =
    let derived = kindEdges node.Id node.Kind
    let represented = derived |> List.filter (fun edge -> edge.Class = EdgeClass.Structural) |> List.collect (fun edge -> edge.Sources) |> Set.ofList
    let attached = node.Children |> List.mapi (fun ordinal source -> ordinal, source) |> List.choose (fun (ordinal, source) ->
        if represented.Contains source then None
        else Some (Hyperedge.edge1 EdgeClass.Structural EdgeRole.Attached ordinal source node.Id))
    derived @ attached

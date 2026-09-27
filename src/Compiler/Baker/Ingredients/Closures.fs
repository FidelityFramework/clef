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

/// Extracted closure code remains a declaration in the source occurrence's
/// lexical module. A reference to that code is not its structural placement.
/// The owning recipe emits the changed module with the new declaration, so
/// ordinary fold-in settles membership, parents and module classification.
let declareInSourceModule (graph: SemanticGraph) (source: SemanticNode) (declaration: SemanticNode) : SaturationParser<unit> =
    let rec owner seen (child: SemanticNode) =
        if Set.contains child.Id seen then Error "The closure source occurrence has a cyclic parent chain."
        else
            let seen = Set.add child.Id seen
            match child.Parent |> Option.bind graph.Nodes.TryFind with
            | Some parent ->
                match parent.Kind with
                | SemanticKind.ModuleDef(name, members) when List.contains child.Id members -> Ok(parent, name, members)
                | SemanticKind.ModuleDef _ -> Error "The closure source occurrence is absent from its lexical module membership."
                // Startup owns executable initialization and therefore clears
                // a module's structural children. Its lexical members remain
                // declaration authority; other steps must retain containment.
                | _ when List.contains child.Id parent.Children -> owner seen parent
                | _ -> Error $"The closure source occurrence {NodeId.value child.Id} is absent from parent {NodeId.value parent.Id}'s structural children {parent.Children |> List.map NodeId.value}."
            | None ->
                Error $"The closure source occurrence {NodeId.value child.Id} has no lexical owner at parent {child.Parent |> Option.map NodeId.value}."
    saturation {
        match owner Set.empty source with
        | Error reason -> return! fail (XParsec.ErrorType.Message reason)
        | Ok(moduleNode, name, members) ->
            do! emit { declaration with Parent = Some moduleNode.Id }
            // Module membership authorizes its definition occurrences through
            // source classification. Preserve the settled execution spine;
            // extracted code must not reopen module initialization children.
            do! enrich moduleNode (SemanticKind.ModuleDef(name, members @ [declaration.Id])) moduleNode.Type
                           moduleNode.Children moduleNode.EmissionStrategy false
    }

/// Refresh the kind-derived incidence of enriched nodes. Other relations
/// (including obligations and provenance) survive independently of that table.
let structuralIncidence (node: SemanticNode) =
    let derived = kindEdges node.Id node.Kind
    let represented = derived |> List.filter (fun edge -> edge.Class = EdgeClass.Structural) |> List.collect (fun edge -> edge.Sources) |> Set.ofList
    let attached = node.Children |> List.mapi (fun ordinal source -> ordinal, source) |> List.choose (fun (ordinal, source) ->
        if represented.Contains source then None
        else Some (Hyperedge.edge1 EdgeClass.Structural EdgeRole.Attached ordinal source node.Id))
    derived @ attached

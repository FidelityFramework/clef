// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Ingredients.NumericValues

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let owned (node: SemanticNode) = node.Metadata.ContainsKey "Baker.NumericOwned"
let markOwned (node: SemanticNode) = { node with Metadata = node.Metadata.Add("Baker.NumericOwned", MetadataValue.Bool true) }
let premises (graph: SemanticGraph) =
    graph.Nodes |> Map.fold (fun values id node ->
        if owned node || Boundaries.ownedNode node || node.Metadata.ContainsKey "Baker.MemoryPublicationOwned" || node.Metadata.ContainsKey "Baker.SpatialPublicationOwned" then values
        else Map.add id (Boundaries.premise node) values) Map.empty

let row role sources target = { Class = EdgeClass.Range; Role = role; Ordinal = 0; Sources = sources; Target = target }
let byteRanges (graph: SemanticGraph) = graph.Edges |> List.choose (fun edge ->
    match edge.Role with
    | EdgeRole.StringByteStorage(lo, hi, representation) -> Some(edge.Target, edge.Sources, lo, hi, representation)
    | _ -> None)
let byteReadRanges (graph: SemanticGraph) = graph.Edges |> List.choose (fun edge ->
    match edge.Role with EdgeRole.StringByteRange(lo,hi) -> Some(edge.Target,edge.Sources,lo,hi) | _ -> None)
let byteViews (graph: SemanticGraph) = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringByteView view -> Some view | _ -> None)
let stringExtents (graph: SemanticGraph) = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringExtent extent -> Some extent | _ -> None)
let carrierRow (carrier: ScalarCarrier) = row (EdgeRole.NumericCarrier carrier) (Set.toList carrier.Participants) carrier.Site
let coverage (carrier: ScalarCarrier) =
    match carrier.Slot, carrier.Range with
    | SettledSlot.Integer(bits, _), ValueRange.Bounded(lo, hi) ->
        let capacity =
            match carrier.Representation with
            | Some representation -> Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange representation
            | None -> Some(if lo >= 0I then ValueRange.unsignedOf bits else ValueRange.twosComplement bits)
        match capacity with
        | Some(ValueRange.Bounded(minimum, maximum)) -> Some(ObligationBody.IntegerRepresentationCoverage(lo, hi, minimum, maximum))
        | _ -> None
    | _ -> None

let proofRows (carrier: ScalarCarrier) obligation body =
    let sources = Set.toList carrier.Participants
    [ { Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = 0; Sources = sources; Target = obligation }
      row (EdgeRole.NumericProof(StringBytes.proofOutcome body)) (obligation :: sources) carrier.Site
      { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = sources; Target = obligation } ]

let indexBody (transport: NumericIndexTransport) =
    match transport.Carrier.Range, transport.Capacity with
    | ValueRange.Bounded(lo, hi), ValueRange.Bounded(minimum, maximum) ->
        Some(ObligationBody.IntegerRepresentationCoverage(lo, hi, minimum, maximum))
    | _ -> None

let indexRows (transport: NumericIndexTransport) =
    let sources = Set.toList transport.Participants
    [ row (EdgeRole.NumericIndexTransport transport) sources transport.Site
      { Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = 0; Sources = sources; Target = transport.Obligation }
      { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = sources; Target = transport.Obligation } ]

let sameRows expected actual =
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    (expected |> List.map key |> List.sort) = (actual |> List.map key |> List.sort)

let domainRow anchor (domain: NumericDomain) = row (EdgeRole.NumericDomain domain) (Map.keys domain.Premises |> Seq.toList) anchor
let domainRewrite anchor (domain: NumericDomain) =
    { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = Map.keys domain.Premises |> Seq.toList; Target = anchor }

// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Ingredients.MemoryValues

open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let owned (node: SemanticNode) = node.Metadata.ContainsKey "Baker.MemoryPublicationOwned"
let markOwned (node: SemanticNode) = { node with Metadata = node.Metadata.Add("Baker.MemoryPublicationOwned", MetadataValue.Bool true) }
let excludedValidated (graph:SemanticGraph) =
    let rec collect seen id =
        if Set.contains id seen then seen else
        match graph.Nodes.TryFind id with
        | Some node -> List.fold collect (Set.add id seen) node.Children
        | None -> Set.add id seen
    let declarations=graph.Edges |> List.fold(fun found edge ->
        match edge.Role with EdgeRole.BoundaryDeclaration declaration -> collect found declaration.Binding | _ -> found) Set.empty
    Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryDeferredOnly graph |> Result.map(Set.union declarations)
let excluded graph =
    match excludedValidated graph with
    | Ok excluded -> excluded
    | Error failures -> invalidOp(sprintf "Source memory demand premises are unsettled: %A" failures)
let executable (graph:SemanticGraph) excluded id =
    not(Set.contains id excluded) && (graph.Nodes.TryFind id |> Option.exists _.IsReachable)
let premises (graph: SemanticGraph) = graph.Nodes |> Map.fold (fun values id node ->
    if owned node || Boundaries.ownedNode node || node.Metadata.ContainsKey "Baker.SpatialPublicationOwned" then values else Map.add id (Boundaries.premise node) values) Map.empty
let guards (graph: SemanticGraph) = graph.Edges |> List.choose (fun edge ->
    match edge.Role with EdgeRole.MemoryAccessGuard -> Some(edge.Target, edge.Sources) | _ -> None)
let requirements (graph: SemanticGraph) = graph.Edges |> List.choose (fun edge ->
    match edge.Role with EdgeRole.MatchRequirement -> Some(edge.Ordinal, edge.Target, edge.Sources) | _ -> None)
let stringRelations (graph: SemanticGraph) = graph.Edges |> List.choose (fun edge ->
    let premise =
        match edge.Role with
        | EdgeRole.StringByteSnapshot -> Some MemoryStringPremise.Snapshot
        | EdgeRole.StringToBytesSnapshot -> Some MemoryStringPremise.ToBytesSnapshot
        | EdgeRole.CopyFrom -> Some MemoryStringPremise.Copy
        | EdgeRole.StringByteStorage(lo,hi,representation) -> Some(MemoryStringPremise.Storage(lo,hi,representation))
        | EdgeRole.StringByteRead -> Some MemoryStringPremise.Read
        | EdgeRole.StringByteRange(lo,hi) -> Some(MemoryStringPremise.ReadRange(lo,hi))
        | EdgeRole.StringAscii -> Some MemoryStringPremise.Ascii
        | EdgeRole.StringUtf8Constant bytes -> Some(MemoryStringPremise.Utf8Constant bytes)
        | EdgeRole.StringByteView view -> Some(MemoryStringPremise.ByteView view)
        | EdgeRole.StringExtent extent -> Some(MemoryStringPremise.Extent extent)
        | _ -> None
    premise |> Option.map (fun premise ->
        { Class=edge.Class; Premise=premise; Ordinal=edge.Ordinal; Sources=edge.Sources; Target=edge.Target }))
let participants = function
    | MemoryWitnessOperation.BufferExtent fact -> fact.Participants
    | MemoryWitnessOperation.ArrayExtent fact -> fact.Participants
    | MemoryWitnessOperation.ArrayAccess fact -> fact.Participants
    | MemoryWitnessOperation.ArrayLiteral fact -> fact.Participants
    | MemoryWitnessOperation.ArrayAllocation fact -> fact.Participants
    | MemoryWitnessOperation.Address fact -> fact.Participants
    | MemoryWitnessOperation.StringView fact -> fact.Participants
let operands = function
    | MemoryWitnessOperation.BufferExtent fact -> [fact.Source]
    | MemoryWitnessOperation.ArrayExtent fact -> [fact.Source]
    | MemoryWitnessOperation.ArrayAccess fact -> [fact.Buffer; fact.Index] @ Option.toList fact.Value
    | MemoryWitnessOperation.ArrayLiteral fact -> fact.Elements |> List.map fst
    | MemoryWitnessOperation.ArrayAllocation fact -> [fact.Count]
    | MemoryWitnessOperation.StringView fact -> [fact.Source]
    | MemoryWitnessOperation.Address fact ->
        match fact.Place with
        | MemoryPlace.MutableCell id | MemoryPlace.ExistingReference id -> [id]
        | MemoryPlace.ArrayElement(buffer, index, _) -> [buffer; index]
        | MemoryPlace.RecordField(receiver, _, _) -> [receiver]
let operationRow (site, operation) = NumericValues.row (EdgeRole.MemoryOperation operation) (operands operation @ Set.toList(participants operation)) site
let allocationConstructions (graph: SemanticGraph) = graph.Edges |> List.choose (fun edge ->
    match edge.Role with EdgeRole.ArrayAllocationConstruction construction -> Some construction | _ -> None)
let copyConstructions (graph: SemanticGraph) = graph.Edges |> List.choose (fun edge ->
    match edge.Role with EdgeRole.ArrayCopyConstruction construction -> Some construction | _ -> None)
let allocationConstructionRow (construction:ArrayAllocationConstruction) =
    {Class=EdgeClass.Provenance;Role=EdgeRole.ArrayAllocationConstruction construction;Ordinal=0
     Sources=construction.Owner::construction.Count.Actual::construction.Count.Binding::construction.Count.Reference::Set.toList construction.Participants
     Target=construction.Site}
let copyConstructionRow (construction:ArrayCopyConstruction) =
    {Class=EdgeClass.Provenance;Role=EdgeRole.ArrayCopyConstruction construction;Ordinal=0
     Sources=[construction.Source.Actual;construction.SourceOffset.Actual;construction.Destination;construction.DestinationOffset.Actual;construction.Count.Actual]@Set.toList construction.Participants
     Target=construction.Site}
let copyRow (copy: MemoryArrayCopyWitness) =
    NumericValues.row (EdgeRole.MemoryArrayCopy copy)
        ([copy.Source;copy.SourceOffset;copy.Destination;copy.DestinationOffset;copy.Count] @ Set.toList copy.Participants) copy.Site
let proofRows (proof: MemoryProof) =
    let sources = proof.Site :: Set.toList proof.Participants
    [ NumericValues.row (EdgeRole.MemoryProof proof) sources proof.Obligation
      { Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = 0; Sources = sources; Target = proof.Obligation }
      { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = sources; Target = proof.Obligation } ]
let domainRow anchor (domain: MemoryDomain) = NumericValues.row (EdgeRole.MemoryDomain domain) (Map.keys domain.Premises |> Seq.toList) anchor
let domainRewrite anchor (domain: MemoryDomain) =
    { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = Map.keys domain.Premises |> Seq.toList; Target = anchor }

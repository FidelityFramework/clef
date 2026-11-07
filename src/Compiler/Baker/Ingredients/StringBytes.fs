// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Ingredients.StringBytes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Expressions.Intrinsics
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module PlatformResolution = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

/// A successful read of a string's logical UTF-8 byte view is in 0..255.
/// This supplies no allocation, bounds, lifetime or physical representation
/// permission. Re-read exact current source structure; old ranges and storage
/// conclusions are not premises. Ordinary arrays retain their own element rules.
let logicalReadRanges (graph: SemanticGraph) =
    let sourceEdge (edge: Hyperedge) =
        edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let incoming =
        graph.Edges |> List.filter sourceEdge |> List.groupBy _.Target
        |> List.map (fun (id, edges) -> id, edges |> List.map key |> List.sort) |> Map.ofList
    let exact (node: SemanticNode) =
        let expected = Closures.structuralIncidence node |> List.filter sourceEdge |> List.map key |> List.sort
        (incoming.TryFind node.Id |> Option.defaultValue []) = expected
    graph.Nodes |> Map.fold (fun ranges id node ->
        match node.Kind with
        | SemanticKind.IndexGet(view, index)
            when node.IsReachable && node.Type = Types.intType && node.Children = [view; index] && exact node ->
            match graph.Nodes.TryFind view, graph.Nodes.TryFind index with
            | Some borrow, Some subscript
                when borrow.IsReachable && borrow.Type = Types.mkArrayType Types.intType &&
                     subscript.IsReachable && Types.isIntegerType subscript.Type && exact borrow ->
                match borrow.Kind with
                | SemanticKind.StringByteBorrow source when borrow.Children = [source] ->
                    match graph.Nodes.TryFind source with
                    | Some value when value.IsReachable && Types.isStringType value.Type ->
                        Map.add id (ValueRange.bounded 0I 255I) ranges
                    | _ -> ranges
                | _ -> ranges
            | _ -> ranges
        | _ -> ranges) Map.empty

/// Shared by copying String.toBytes and borrowing string.Bytes. The logical
/// array element remains native int; this declaration settles its byte carrier.
let byteRepresentation (graph: SemanticGraph) =
    let declarations = PlatformResolution.resolve graph |> Option.bind _.Core |> Option.map _.Representations |> Option.defaultValue []
    graph.Platform |> Option.bind (fun platform ->
        platform.Representations.Values |> Seq.tryPick (fun rep ->
            if rep.Bits = 8 && rep.Family = "uint" && NumericRepresentation.isOffered rep
               && (RangeSources.declaredRange rep |> Option.exists (fun range -> ValueRange.contains range (ValueRange.bounded 0I 255I))) then
                match declarations |> List.filter (fun declaration -> declaration.Representation = rep) with
                | [declaration] -> Some(rep, declaration.Node)
                | _ -> None
            else None))

let rangeRow role sources target = { Class = EdgeClass.Range; Role = role; Ordinal = 0; Sources = sources; Target = target }
let storagePremise (graph: SemanticGraph) = graph.StaticStringPool |> Option.map (fun pool ->
    pool.Symbol, pool.Bytes, pool.Alignment, pool.Size, pool.UsedSize, pool.SpaceName, pool.Capacity,
    pool.SpaceAlignment, pool.Granularity, pool.DeclarationNode,
    pool.Entries |> List.map (fun entry -> entry.NodeIds, entry.Content, entry.Offset, entry.Length, entry.StorageLength))
/// The sources of a borrow row: the nodes of its participants in their order, or the
/// nodes of the early derivation while the participants are pending.
let private incidence (evidence: ParticipantEvidence) =
    match evidence with
    | ParticipantEvidence.Established participants -> participants |> List.map _.Node
    | ParticipantEvidence.Pending early -> early.Derived |> List.map _.Node
let viewRow (view: BoundaryByteView) = rangeRow (EdgeRole.StringByteView view) (incidence view.Participants) view.Site
let rewriteRow (view: BoundaryByteView) =
    { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = [view.Source]; Target = view.Site }
let extentRow (extent: BoundaryStringExtent) = rangeRow (EdgeRole.StringExtent extent) (incidence extent.Participants) extent.Site
let historyRow (history: BorrowHistory) =
    { Class = EdgeClass.Provenance; Role = EdgeRole.StringBorrowHistory history; Ordinal = 0
      Sources = history.Early.Derived |> List.map _.Node; Target = history.Site }
let abiRow site (import: IntrinsicWriteImport) = rangeRow (EdgeRole.IntrinsicWriteAbi import) (import.Identity :: import.Scope :: Set.toList import.Participants) site
let storageRow (view: BoundaryByteView) =
    rangeRow (EdgeRole.StringByteStorage(0I, 255I, view.Representation.Name))
        ([view.Site; view.Source; view.ExtentSource; view.RepresentationDeclaration] @ incidence view.Participants) view.Site

let proofOutcome body =
    let holds =
        match body with
        | ObligationBody.IntegerRepresentationCoverage(lo, hi, minimum, maximum) -> minimum <= lo && lo <= hi && hi <= maximum
        | ObligationBody.StringBorrowBound origins ->
            not origins.IsEmpty && origins |> List.forall (fun (count, extent, storage) -> 0I <= count && count = extent && extent < storage)
        | ObligationBody.InputBufferBound(count, allocation) -> 0L<=count && count<=allocation
        | ObligationBody.SnapshotBorrowBound(count,snapshot,copy,allocation,minimum,maximum,elementBytes,allocationCapacity) ->
            // Source readiness only. Actual solver and satisfiable-premise
            // receipts remain required before backend execution authority.
            let nodeId (NodeId value) = Fidelity.PSG.NodeId value
            Fidelity.PSG.SnapshotBorrowProof.ofBounds (nodeId count) (nodeId snapshot) (nodeId copy) (nodeId allocation) minimum maximum elementBytes allocationCapacity |> Result.isOk
        | _ -> false
    if holds then BoundaryProofOutcome.Proven else BoundaryProofOutcome.Refuted

let proofRows (proof: IntrinsicWriteProof) =
    let sources = proof.Site :: Set.toList proof.Participants
    [ Boundaries.row (EdgeRole.IntrinsicWriteProof proof) proof.Ordinal sources proof.Obligation
      Boundaries.row (EdgeRole.BoundaryProof(proofOutcome proof.Body)) proof.Ordinal (proof.Obligation :: sources) proof.Site
      { Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = proof.Ordinal; Sources = sources; Target = proof.Obligation }
      { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = proof.Ordinal; Sources = sources; Target = proof.Obligation } ]

let importRow (import: IntrinsicWriteImport) = Boundaries.row (EdgeRole.IntrinsicWriteImport import) 0 (import.Scope :: Set.toList import.Participants) import.Identity
let callRows (call: IntrinsicWriteCall) =
    let sources = [call.Import; call.Callee; call.Fd; call.Buffer; call.Count] @ Set.toList call.Participants
    Boundaries.row (EdgeRole.IntrinsicWriteCall call) 0 sources call.Site ::
    ([call.Fd; call.Buffer; call.Count] |> List.mapi (fun ordinal operand -> Boundaries.row (EdgeRole.IntrinsicWriteOperand operand) ordinal sources call.Site)) @
    ([0,call.FdAdaptation; 2,call.CountAdaptation; -1,call.ResultAdaptation] |> List.collect (fun (ordinal, meet) ->
        meet |> Option.toList |> List.map (fun meet -> Boundaries.row (EdgeRole.BoundaryAdaptation meet) ordinal sources call.Site)))

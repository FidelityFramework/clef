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

/// Capture admission depends on the exact incidence, including malformed and
/// duplicate rows. Keep its empty census after the last capture is withdrawn.
let captureRelations (graph: SemanticGraph) =
  graph.Edges
  |> List.choose (fun edge ->
    match edge.Role with
    | EdgeRole.EnvironmentCapture mutable' -> Some(edge.Class, mutable', edge.Ordinal, edge.Sources, edge.Target)
    | _ -> None)
  |> List.sort

/// Range annotations are consequences of the producer's fixed point, not its
/// source premises. Keep source type contracts and ordered shape references;
/// Boundaries.premise already excludes derived obligation-anchor annotations.
let rangeContextPremises (graph: SemanticGraph) =
    premises graph
    |> Map.map (fun _ premise -> { premise with Range = None })

let private sourceRelation owner (edge: Hyperedge) : Result<SourceRangeRelation, string> =
    let kind =
        match edge.Role with
        | EdgeRole.SequencePullComposition(label, budget) -> Ok(SourceRangeRelationKind.Composition(label, budget))
        | EdgeRole.EvaluationOperand access -> Ok(SourceRangeRelationKind.EvaluationOperand access)
        | EdgeRole.EvaluationFlow(before, after, transfer) -> Ok(SourceRangeRelationKind.EvaluationFlow(before, after, transfer))
        | EdgeRole.EnvironmentCapture mutable' -> Ok(SourceRangeRelationKind.EnvironmentCapture mutable')
        | EdgeRole.SequenceCaptureInitializer mutable' -> Ok(SourceRangeRelationKind.SequenceCaptureInitializer mutable')
        | EdgeRole.ContinuationCase tag -> Ok(SourceRangeRelationKind.ContinuationCase tag)
        | EdgeRole.SuspensionCut state -> Ok(SourceRangeRelationKind.SuspensionCut state)
        | EdgeRole.SuspensionResume state -> Ok(SourceRangeRelationKind.SuspensionResume state)
        | EdgeRole.SuspensionResumeAction state -> Ok(SourceRangeRelationKind.SuspensionResumeAction state)
        | EdgeRole.EvaluationPending residual -> Ok(SourceRangeRelationKind.EvaluationPending residual)
        | EdgeRole.EagerDemand frontier -> Ok(SourceRangeRelationKind.EagerDemand frontier)
        | EdgeRole.LazyCapture mutable' -> Ok(SourceRangeRelationKind.LazyCapture mutable')
        | EdgeRole.StringExtent extent -> Ok(SourceRangeRelationKind.StringExtent extent)
        | EdgeRole.StringByteView view -> Ok(SourceRangeRelationKind.StringByteView view)
        | EdgeRole.StringByteStorage(lo, hi, representation) -> Ok(SourceRangeRelationKind.StringByteStorage(lo, hi, representation))
        | EdgeRole.StringByteRange(lo, hi) -> Ok(SourceRangeRelationKind.StringByteRange(lo, hi))
        | EdgeRole.StringUtf8Constant bytes -> Ok(SourceRangeRelationKind.StringUtf8Constant bytes)
        | EdgeRole.ArrayAllocationConstruction construction -> Ok(SourceRangeRelationKind.ArrayAllocationConstruction construction)
        | EdgeRole.LoopInduction(ascending, inclusive) -> Ok(SourceRangeRelationKind.LoopInduction(ascending, inclusive))
        | EdgeRole.LoopRangePending residual -> Ok(SourceRangeRelationKind.LoopRangePending residual)
        | EdgeRole.OrdinaryBindingDemand evidence -> Ok(SourceRangeRelationKind.OrdinaryBindingDemand evidence)
        | EdgeRole.OrdinaryBindingDemandPending(reason, evidence) -> Ok(SourceRangeRelationKind.OrdinaryBindingDemandPending(reason, evidence))
        | EdgeRole.OrdinaryBindingDemandHistory evidence -> Ok(SourceRangeRelationKind.OrdinaryBindingDemandHistory evidence)
        | EdgeRole.KernelIngress ingress -> Ok(SourceRangeRelationKind.KernelIngress ingress)
        | role ->
            let case, fields = Microsoft.FSharp.Reflection.FSharpValue.GetUnionFields(role, typeof<EdgeRole>)
            if fields.Length = 0 then Ok(SourceRangeRelationKind.Named case.Name)
            else Error(owner + " incidence has an unsupported payload: " + case.Name + ".")
    kind |> Result.map (fun kind ->
        { Class = edge.Class; Kind = kind; Ordinal = edge.Ordinal; Sources = edge.Sources; Target = edge.Target })

/// Range inputs include callable incidence, validated storage/demand protocols,
/// and source byte/array facts. Preserve malformed rows, absence, duplicates and
/// order: environment formal lookup uses first/last matching rows.
let rangeContextRelations (graph: SemanticGraph) =
    let publicationOwned id =
        graph.Nodes.TryFind id |> Option.exists (fun node ->
            owned node || Boundaries.ownedNode node || node.Metadata.ContainsKey "Baker.MemoryPublicationOwned" ||
            node.Metadata.ContainsKey "Baker.SpatialPublicationOwned")
    graph.Edges
    |> List.filter (fun edge ->
        let sourceRole =
            match edge.Role with
            | EdgeRole.EnvironmentFormal | EdgeRole.EnvironmentCapture _ | EdgeRole.EnvironmentInvocation
            | EdgeRole.EnvironmentInitializer | EdgeRole.EnvironmentResultDestination | EdgeRole.EnvironmentResultCall
            | EdgeRole.CaptureOrigin | EdgeRole.CaptureReferenceOrigin | EdgeRole.CallableReferenceOrigin
            | EdgeRole.LazyInstance | EdgeRole.LazyCapture _ | EdgeRole.LazyMemoization
            | EdgeRole.LazyResultDestination | EdgeRole.LazyResultCall | EdgeRole.LazyEffectRange
            | EdgeRole.SequenceCaptureFormation | EdgeRole.SequenceCaptureInitializer _
            | EdgeRole.ContinuationValue | EdgeRole.ContinuationSlotAccess
            | EdgeRole.Delimiter | EdgeRole.SuspensionCut _ | EdgeRole.SuspensionResume _
            | EdgeRole.SuspensionResumeAction _ | EdgeRole.SuspensionCompleted | EdgeRole.SuspensionLiveAcross
            | EdgeRole.IteratorCurrentAdmitted | EdgeRole.SequenceElementAdmission | EdgeRole.SequenceElementOwner
            | EdgeRole.SequenceElementPayload | EdgeRole.SequenceElementUnknown | EdgeRole.SequencePullBody
            | EdgeRole.SequenceInitialize | EdgeRole.SequenceEffectUnknown | EdgeRole.SequenceTemplateCopy
            | EdgeRole.SequencePullBound | EdgeRole.SequencePullComposition _ | EdgeRole.SequenceAccumulation
            | EdgeRole.LoopInduction _ | EdgeRole.LoopAccumulation | EdgeRole.LoopLinearRecurrence | EdgeRole.LoopRangePending _
            | EdgeRole.FiniteCellRange | EdgeRole.ProgramInitialization | EdgeRole.ProgramInitializer
            | EdgeRole.ProgramEntryCall | EdgeRole.ProgramValueIntent | EdgeRole.ProgramActivationCall | EdgeRole.ProgramActivationCoverage
            | EdgeRole.OrdinaryUnusedFormal | EdgeRole.OrdinaryUnusedActual | EdgeRole.OrdinaryInactiveImplementation
            | EdgeRole.OrdinaryBindingDemand _ | EdgeRole.OrdinaryBindingDemandPending _ | EdgeRole.OrdinaryBindingDemandHistory _
            | EdgeRole.EagerDemand _ | EdgeRole.EagerDemandPending
            | EdgeRole.KernelIngress _
            | EdgeRole.StringExtent _ | EdgeRole.StringByteView _ | EdgeRole.StringByteStorage _ | EdgeRole.StringByteRange _
            | EdgeRole.StringByteRead | EdgeRole.StringByteSnapshot | EdgeRole.StringToBytesSnapshot
            | EdgeRole.StringAscii | EdgeRole.StringUtf8Constant _ | EdgeRole.ArrayAllocationConstruction _ -> true
            | _ -> false
        sourceRole ||
        (not (publicationOwned edge.Target) &&
         (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference ||
          edge.Class = EdgeClass.Evaluation || edge.Class = EdgeClass.Suspension || edge.Class = EdgeClass.Demand)))
    |> List.fold (fun state edge ->
        match state, sourceRelation "Invocation-context" edge with
        | Ok rows, Ok row -> Ok(row :: rows)
        | Error reason, _ | _, Error reason -> Error reason) (Ok [])
    |> Result.map List.rev

/// Compare producer evidence without rerunning RangeAnalysis or rebasing an
/// old invocation solution onto the current source graph.
let rangeContextCurrent (graph: SemanticGraph) (facts: RangeContextFacts) =
    let relationsCurrent =
        match facts.SourceRelations, rangeContextRelations graph with
        | Ok expected, Ok current -> expected = current
        | _ -> false
    facts.Premises = rangeContextPremises graph &&
    relationsCurrent &&
    facts.CaptureRelations = captureRelations graph &&
    facts.Platform = Boundaries.platformPremise graph.Platform &&
    facts.Roots = graph.DeclarationRoots

let sequenceRangeObligations (graph: SemanticGraph) =
    graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Obligation info when
            info.Kind = "finite-sequence-pulls" || info.Kind = "sequence-inner-finite-pulls" ||
            info.Kind = "sequence-additive-invariant" -> Some(id, info)
        | _ -> None)

let private sequenceRangeRow (edge: Hyperedge) =
    match edge.Role with
    | EdgeRole.SequencePullBound | EdgeRole.SequencePullComposition _ | EdgeRole.SequenceAccumulation -> true
    | _ -> false

let sequenceRangeActive (graph: SemanticGraph) =
    graph.SequenceRangeProvenance.IsSome || not (sequenceRangeObligations graph).IsEmpty ||
    (graph.Edges |> List.exists sequenceRangeRow)

/// Proof-anchor annotations can change after the representation handoff.
/// Source shape, reachability, captures, types and held ranges cannot change
/// under the transferred finite-sequence authority.
let private sequencePremise node =
    let premise = Boundaries.premise node
    { premise with Metadata = premise.Metadata.Remove ObligationMetadata.Anchors }

let private sequenceSnapshot (participants: Set<NodeId>) enumerators (graph: SemanticGraph) =
    let finite = sequenceRangeObligations graph |> List.map fst |> Set.ofList
    let obligations = graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Obligation info when finite.Contains id || participants.Contains id || info.Kind = "continuation-state-range" -> Some(id, info)
        | _ -> None)
    let proofIds = obligations |> List.map fst |> Set.ofList
    let sourceNode node =
        not (owned node || Boundaries.ownedNode node || node.Metadata.ContainsKey "Baker.MemoryPublicationOwned" ||
             node.Metadata.ContainsKey "Baker.SpatialPublicationOwned") &&
        // Later owners may add non-executable proof citizens. Preserve every
        // protected source/machine proof body, without treating unrelated
        // obligations as new source uses, writes or captures.
        (match node.Kind with SemanticKind.Obligation _ -> proofIds.Contains node.Id | _ -> true)
    let candidates = graph.Nodes |> Map.filter (fun _ node -> sourceNode node) |> Map.map (fun _ node -> sequencePremise node)
    // Recognition reads the global use/write/capture census, including absence
    // of additional users. Retain its complete source domain: a one-hop support
    // filter cannot account for an outside alias followed by a new write.
    let observed = candidates
    let related (edge: Hyperedge) =
        observed.ContainsKey edge.Target || (edge.Sources |> List.exists observed.ContainsKey)
    let selected (edge: Hyperedge) =
        sequenceRangeRow edge ||
        (edge.Role = EdgeRole.Constrains && proofIds.Contains edge.Target) ||
        (related edge &&
         (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference || edge.Class = EdgeClass.Evaluation ||
          match edge.Role with
          | EdgeRole.EnvironmentFormal | EdgeRole.EnvironmentCapture _ | EdgeRole.IteratorCurrentAdmitted
          | EdgeRole.SequenceCaptureFormation | EdgeRole.SequenceCaptureInitializer _
          | EdgeRole.ContinuationValue | EdgeRole.ContinuationSlotAccess
          | EdgeRole.Delimiter | EdgeRole.SuspensionCut _ | EdgeRole.SuspensionResume _
          | EdgeRole.SuspensionResumeAction _ | EdgeRole.SuspensionCompleted | EdgeRole.SuspensionLiveAcross
          | EdgeRole.SequenceElementAdmission | EdgeRole.SequenceElementOwner
          | EdgeRole.SequenceElementPayload | EdgeRole.SequenceElementUnknown
          | EdgeRole.SequencePullBody | EdgeRole.SequenceInitialize | EdgeRole.SequenceEffectUnknown -> true
          | _ -> false))
    graph.Edges |> List.filter selected |> List.fold (fun state edge ->
        match state, sourceRelation "Finite-sequence" edge with
        | Ok rows, Ok row -> Ok(row :: rows)
        | Error reason, _ | _, Error reason -> Error reason) (Ok [])
    |> Result.map (fun rows ->
        { Participants = participants; Enumerators = enumerators; Premises = observed
          Relations = List.sort rows; Obligations = obligations })

/// Called only by SequenceRuntime after successful current source handoff and
/// checked generation of every producer machine supporting the source bound.
let internal recordSequenceRangeHandoff (graph: SemanticGraph) =
    let proofs = sequenceRangeObligations graph |> List.map fst |> Set.ofList
    if proofs.IsEmpty && not (graph.Edges |> List.exists sequenceRangeRow) then
        { graph with SequenceRangeProvenance = None }
    else
        let roots =
            graph.Edges
            |> List.collect (fun edge ->
                if sequenceRangeRow edge || (edge.Role = EdgeRole.Constrains && proofs.Contains edge.Target) then
                    edge.Target :: edge.Sources
                else [])
            |> Set.ofList
        // Follow all source dependencies, including captured callback bodies and
        // their original mutable cells. A participant list alone is not closure.
        let rec close seen pending =
            match pending with
            | [] -> seen
            | id :: rest when Set.contains id seen -> close seen rest
            | id :: rest ->
                let dependencies = graph.Nodes.TryFind id |> Option.map (fun node -> (Boundaries.premise node).Shape.References) |> Option.defaultValue []
                close (Set.add id seen) (dependencies @ rest)
        let participants = close Set.empty (Set.toList roots)
        let enumerators =
            graph.Edges
            |> List.choose (fun edge ->
                match edge.Role, edge.Sources with
                | EdgeRole.SequencePullBound, _ :: _ :: _ :: enumerator :: _
                | EdgeRole.SequencePullComposition _, _ :: _ :: enumerator :: _ -> Some enumerator
                | _ -> None)
            |> Set.ofList
        { graph with SequenceRangeProvenance = sequenceSnapshot participants enumerators graph |> Result.toOption }

/// Compare the complete recorded receipt. This reads stored source observations;
/// it never recognizes an iterator, derives a bound or repairs a missing proof.
let sequenceRangeCurrent (graph: SemanticGraph) (authority: SequenceRangeAuthority) =
    sequenceSnapshot authority.Participants authority.Enumerators graph = Ok authority

let finiteCellObligations (graph: SemanticGraph) =
    graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Obligation info when info.Kind = "finite-cell-effects" -> Some(id, info)
        | _ -> None)

/// Complete recorded relation census for finite-cell source readers. Keep
/// ordering, duplicate rows and typed payloads; participant IDs alone omit
/// contradictory incidence and the absence of additional uses.
/// Scope is the whole current source graph. The additional snapshot is active
/// while finite-cell evidence or a generated integer frame read is resident.
/// Frame reads depend on the same current storage/write census even when their
/// finite range comes from arithmetic rather than an activation certificate.
let finiteCellRelations (graph: SemanticGraph) : Result<FiniteCellSourceRelation list option, string> =
    let obligations = finiteCellObligations graph |> List.map fst |> Set.ofList
    let supportObligations =
        graph.Nodes |> Map.fold (fun found id node ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind = "continuation-state-range" -> Set.add id found
            | _ -> found) obligations
    let frameReads = graph.Nodes.Values |> Seq.exists (fun node ->
        node.IsReachable &&
        (match node.Kind with SemanticKind.FrameRead _ -> true | _ -> false) &&
        (Types.tryGetNTUKind node.Type |> Option.exists Clef.Compiler.NativeTypedTree.NativeTypes.NTUKind.isInteger))
    let liftedCurrent = graph.Edges |> List.exists (fun edge ->
        edge.Role = EdgeRole.IteratorCurrentAdmitted && edge.Sources.Length > 3 &&
        (graph.Nodes.TryFind edge.Target |> Option.exists (fun node ->
            node.IsReachable && (Types.tryGetNTUKind node.Type |> Option.exists Clef.Compiler.NativeTypedTree.NativeTypes.NTUKind.isInteger))))
    let active = frameReads || liftedCurrent || not obligations.IsEmpty || (graph.Edges |> List.exists (fun edge -> edge.Role = EdgeRole.FiniteCellRange))
    if not active then Ok None else
    let sourceTarget (edge: Hyperedge) =
        graph.Nodes.TryFind edge.Target |> Option.forall (fun node ->
            not (owned node || Boundaries.ownedNode node || node.Metadata.ContainsKey "Baker.MemoryPublicationOwned" ||
                 node.Metadata.ContainsKey "Baker.SpatialPublicationOwned"))
    let selected (edge: Hyperedge) =
        sourceTarget edge &&
        (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference || edge.Class = EdgeClass.Evaluation ||
         match edge.Role with
         | EdgeRole.ProgramInitialization | EdgeRole.ProgramEntryCall | EdgeRole.ProgramInitializer
         | EdgeRole.ProgramValueIntent | EdgeRole.EnvironmentFormal | EdgeRole.EnvironmentCapture _
         | EdgeRole.SequenceCaptureFormation | EdgeRole.SequenceCaptureInitializer _
         | EdgeRole.ContinuationValue | EdgeRole.ContinuationSlotAccess
         | EdgeRole.Delimiter | EdgeRole.SuspensionCut _ | EdgeRole.SuspensionResume _
         | EdgeRole.SuspensionResumeAction _ | EdgeRole.SuspensionCompleted | EdgeRole.SuspensionLiveAcross
         | EdgeRole.IteratorCurrentAdmitted | EdgeRole.SequenceElementAdmission | EdgeRole.SequenceElementOwner
         | EdgeRole.SequenceElementPayload | EdgeRole.SequenceElementUnknown
         | EdgeRole.SequencePullBody | EdgeRole.SequenceInitialize | EdgeRole.SequenceEffectUnknown
         | EdgeRole.FiniteCellRange -> true
         | EdgeRole.Constrains -> supportObligations.Contains edge.Target
         | _ -> false)
    graph.Edges |> List.filter selected |> List.fold (fun state (edge: Hyperedge) ->
        let kind =
            match edge.Role with
            | EdgeRole.ContinuationCase tag -> Ok(FiniteCellRelationKind.ContinuationCase tag)
            | EdgeRole.EnvironmentCapture mutable' -> Ok(FiniteCellRelationKind.EnvironmentCapture mutable')
            | EdgeRole.SequenceCaptureInitializer mutable' -> Ok(FiniteCellRelationKind.SequenceCaptureInitializer mutable')
            | EdgeRole.EvaluationOperand access -> Ok(FiniteCellRelationKind.EvaluationOperand access)
            | EdgeRole.EvaluationFlow(before, after, transfer) -> Ok(FiniteCellRelationKind.EvaluationFlow(before, after, transfer))
            | EdgeRole.SuspensionCut state -> Ok(FiniteCellRelationKind.SuspensionCut state)
            | EdgeRole.SuspensionResume state -> Ok(FiniteCellRelationKind.SuspensionResume state)
            | EdgeRole.SuspensionResumeAction state -> Ok(FiniteCellRelationKind.SuspensionResumeAction state)
            | role ->
                let case, fields = Microsoft.FSharp.Reflection.FSharpValue.GetUnionFields(role, typeof<EdgeRole>)
                if fields.Length = 0 then Ok(FiniteCellRelationKind.Named case.Name)
                else Error("Finite-cell source incidence has an unsupported payload: " + case.Name + ".")
        match state, kind with
        | Error reason, _ | _, Error reason -> Error reason
        | Ok rows, Ok kind ->
            Ok(({ Class = edge.Class; Kind = kind; Ordinal = edge.Ordinal
                  Sources = edge.Sources; Target = edge.Target } : FiniteCellSourceRelation) :: rows)) (Ok [])
    |> Result.map (List.rev >> Some)

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

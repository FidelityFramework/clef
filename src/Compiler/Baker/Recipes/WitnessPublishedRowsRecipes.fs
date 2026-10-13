// SPDX-License-Identifier: MIT
/// Freeze Baker's selected facts before the single passive publication exit.
/// This recipe returns leaf tables, never a Revision or an alternate graph.
module Clef.Compiler.Baker.Recipes.WitnessPublishedRowsRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.PublishedFactRows

let private failure occurrence reason : WitnessProjectionFailure =
    { Kind = WitnessProjectionFailureKind.Settlement; Occurrence = occurrence; Participants = Set.ofList (Option.toList occurrence)
      Reason = "Frozen publication rows: " + reason }

let private freezeNode (node: SemanticNode) =
    try
        let anchors =
            match node.Metadata.TryFind ObligationMetadata.Anchors with
            | None -> []
            | Some(MetadataValue.StringList names) -> names
            | Some other -> invalidOp (sprintf "Obligation anchors are recorded as %A, not as a list of names." other)
        Ok ({ Id = nodeId node.Id
              Kind = mapSemanticKind node.Kind
              Range = { File = node.Range.File
                        Start = { Line = node.Range.Start.Line; Column = node.Range.Start.Column }
                        End = { Line = node.Range.End.Line; Column = node.Range.End.Column } }
              Type = freeze node.Type
              Children = List.map nodeId node.Children
              Parent = Option.map nodeId node.Parent
              IsReachable = node.IsReachable
              EmissionStrategy = mapEmissionStrategy node.EmissionStrategy
              ValueRange = Option.map mapValueRange node.ValueRange
              ObligationAnchors = anchors } : Fidelity.PSG.SemanticNode)
    with error -> Error(failure (Some node.Id) ("The node cannot be frozen: " + error.Message))

let private freezeCodata (facts: WitnessLiveCodata) : Fidelity.PSG.Codata =
    let ids = Map.toSeq >> Seq.map (fun (key, value) -> nodeId key, nodeId value) >> Map.ofSeq
    let rows map (table: Map<NodeId, _>) = table |> Map.toSeq |> Seq.map (fun (key, value) -> nodeId key, map value) |> Map.ofSeq
    { WitnessSegmentation = Option.map mapWitnessSegmentation facts.WitnessSegmentation
      Escapes = rows mapEscapeKind facts.Escapes
      Curry = mapCurryInfo facts.Curry
      Meets = rows (List.map mapMeet) facts.Meets
      ReturnMeets = rows mapMeet facts.ReturnMeets
      Closures = rows mapClosurePlacement facts.Closures
      EnvironmentLayouts = rows mapEnvironmentLayout facts.EnvironmentLayouts
      EnvironmentDestinations = ids facts.EnvironmentDestinations
      EnvironmentOrigins = ids facts.EnvironmentOrigins
      LazyLayouts = rows mapLazyLayout facts.LazyLayouts
      LazyOrigins = ids facts.LazyOrigins
      LazyDestinations = ids facts.LazyDestinations
      KnownCallables = rows mapKnownCallable facts.KnownCallables
      CallableContracts = rows mapCallableContract facts.CallableContracts
      CallableCarriers = rows mapCallableCarrier facts.CallableCarriers
      CallableJoins = rows mapCallableJoin facts.CallableJoins
      CallableFlows = rows mapCallableFlow facts.CallableFlows
      CallableAggregateSlots = rows mapCallableAggregateSlot facts.CallableAggregateSlots
      CallableAggregateValues = rows (List.map mapCallableAggregateValue) facts.CallableAggregateValues
      CallableAggregateDependencies = rows mapCallableAggregateDependencyAccount facts.CallableAggregateDependencies
      CallableBranches = mapCallableBranchAuthority facts.CallableBranches
      MutableCallableStorage = rows mapMutableCallableStorage facts.MutableCallableStorage
      ContinuationFrames = rows mapContinuationFrame facts.ContinuationFrames
      SequenceOrigins = ids facts.SequenceOrigins
      SequenceFlows = rows mapSequenceFlow facts.SequenceFlows
      SequenceFamilies = rows mapSequenceFamily facts.SequenceFamilies
      SequenceTemplateCopies = rows mapSequenceTemplateCopy facts.SequenceTemplateCopies
      ContinuationStorage = ids facts.ContinuationStorage
      ContinuationRegions = rows mapContinuationRegion facts.ContinuationRegions
      SequenceInitializers = rows (List.map (fun (slot, value) -> nodeId slot, nodeId value)) facts.SequenceInitializers
      SequenceDestinations = ids facts.SequenceDestinations
      SequenceCurrentReads = Set.map nodeId facts.SequenceCurrentReads
      Pins = Option.map mapPinMapping facts.Pins
      DeclarationRootLambdas = rows mapDeclRoot facts.DeclarationRootLambdas
      FunctionPointers = rows mapFunctionPointerPlan facts.FunctionPointers
      Mmio = rows mapMmioAccessEvidence facts.Mmio
      ProgramStorage = mapProgramStorageInventory facts.ProgramStorage }

let project (graph: SemanticGraph) (scope: WitnessLiveScopePlan) (selected: WitnessLiveRows)
            (dispatch: ProofDispatchPlan) : Result<WitnessPublishedRows, WitnessProjectionFailure list> =
    match graph.Platform, dispatch.Query with
    | None, _ -> Error [failure None "The source graph has no declared platform for physical publication."]
    | _, Error unavailable ->
        Error (unavailable |> List.map (fun (id, reasons) -> failure (Some id) ("Source proof dispatch is unavailable: " + String.concat "; " reasons)))
    | Some platform, Ok query ->
        let bodies = scope.Occurrences.Values |> Seq.map (fun occurrence -> freezeNode occurrence.Body) |> Seq.toList
        let errors = bodies |> List.choose (function Error error -> Some error | Ok _ -> None)
        if not errors.IsEmpty then Error errors else
        try
            let nodes = bodies |> List.choose (function Ok node -> Some(node.Id, node) | Error _ -> None) |> Map.ofList
            let width dimension = PlatformContext.tryWidth platform (WidthDimension.name dimension)
            Ok { SourcePlatform = platform
                 Nodes = nodes; SourceReadings = mapWitnessSourceReadings scope
                 Edges = List.map mapHyperedge selected.Edges
                 DeclarationRoots = selected.DeclarationRoots |> List.map (fun (id, root) -> nodeId id, mapDeclRoot root)
                 ModuleClassifications = selected.ModuleClassifications |> Map.toSeq |> Seq.map (fun (id, row) -> nodeId id, mapModuleClassification row) |> Map.ofSeq
                 Platform = { Register = width WidthDimension.Register; Pointer = width WidthDimension.Pointer }
                 StaticStringPool = Option.map mapStaticStringPool selected.StaticStringPool
                 LiteralStorage = selected.LiteralStorage |> Map.toSeq |> Seq.map (fun (id, row) -> nodeId id, mapLiteralStorage row) |> Map.ofSeq
                 Codata = freezeCodata selected.Codata; Emission = mapWitnessEmissionProjection selected.Emission
                 Foreign = mapWitnessForeignStorage selected.Foreign; Demand = mapWitnessExplicitDemand selected.Demand
                 Obligations = dispatch.Required |> List.map (snd >> mapObligationInfo)
                 CurrentClaims = dispatch.Required |> List.map (fun (id, claim) -> nodeId id, mapObligationInfo claim) |> Map.ofList
                 ObligationSources = dispatch.SourceGroups |> Map.toSeq |> Seq.map (fun (id, groups) -> nodeId id, groups |> List.map (List.map nodeId)) |> Map.ofSeq
                 ObligationQuery = query }
        with error -> Error [failure None ("The selected source facts cannot be frozen: " + error.Message)]

/// Source re-observation compares the complete frozen leaf tables. The native
/// platform is the exact source input object; it is never reconstructed here.
let matches (held: WitnessPublishedRows) (current: WitnessPublishedRows) =
    obj.ReferenceEquals(held.SourcePlatform, current.SourcePlatform) &&
    held.Nodes = current.Nodes && held.SourceReadings = current.SourceReadings &&
    held.Edges = current.Edges && held.DeclarationRoots = current.DeclarationRoots &&
    held.ModuleClassifications = current.ModuleClassifications && held.Platform = current.Platform &&
    held.StaticStringPool = current.StaticStringPool && held.LiteralStorage = current.LiteralStorage &&
    held.Codata = current.Codata && held.Emission = current.Emission &&
    held.Foreign = current.Foreign && held.Demand = current.Demand &&
    held.Obligations = current.Obligations && held.CurrentClaims = current.CurrentClaims &&
    held.ObligationSources = current.ObligationSources && held.ObligationQuery = current.ObligationQuery

/// An explicitly demanded diagnostic reading of Baker's already selected live
/// occurrences. This does not copy retained premises, edges, claims or codata,
/// and cannot establish semantic, proof or artifact completeness. Unknown
/// references refuse this diagnostic stage rather than expanding its scope.
type OccurrenceRows = {
    Occurrences: Map<Fidelity.PSG.NodeId, Fidelity.PSG.LiveOccurrence>
    ContextHeaders: Fidelity.PSG.SourceContextHeader list
    ContextRoots: Fidelity.PSG.NodeId list
}

let occurrenceRows (rows: WitnessPublishedRows) =
    let readings = rows.SourceReadings
    let bodies = rows.Nodes |> Map.map (fun id body ->
        ({ Body = body; Children = readings.Children[id]
           OccurrenceContexts = readings.Contexts[id] } : Fidelity.PSG.LiveOccurrence))
    let known = Set.union (bodies.Keys |> Set.ofSeq) (readings.ContextHeaders.Keys |> Set.ofSeq)
    let omitted (occurrence: Fidelity.PSG.LiveOccurrence) =
        occurrence.Children |> List.choose (fun child ->
            match child.Traversal with
            | Fidelity.PSG.ChildTraversal.SourceOmitted(_, id) -> Some id
            | _ -> None) |> Set.ofList
    let unknownBodies =
        bodies |> Map.toSeq |> Seq.collect (fun (id, occurrence) ->
            let permitted = Set.union known (omitted occurrence)
            Fidelity.PSG.IntegrityNamed.nodeReferences occurrence.Body
            |> Seq.filter (permitted.Contains >> not)
            |> Seq.map (fun missing -> sprintf "Occurrence %A requires unavailable identity %A." id missing))
    let unknownHeaders =
        readings.ContextHeaders.Values |> Seq.collect (fun header ->
            Fidelity.PSG.IntegrityNamed.contextHeaderReferences header
            |> Seq.filter (known.Contains >> not)
            |> Seq.map (fun missing -> sprintf "Context %A requires unavailable identity %A." header.Identity missing))
    let failures = Seq.append unknownBodies unknownHeaders |> Seq.truncate 33 |> Seq.toList
    if not failures.IsEmpty then
        let messages = failures |> List.truncate 32
        let suffix = if failures.Length > 32 then " [Additional unavailable identities omitted.]" else ""
        Error(String.concat " " messages + suffix)
    else
        let roots = readings.Contexts |> Map.toList |> List.choose (fun (id, paths) ->
            if paths |> List.contains [] then Some id else None)
        Ok { Occurrences = bodies; ContextHeaders = readings.ContextHeaders.Values |> Seq.toList; ContextRoots = roots }

/// Bind an immutable source reading to its actual workspace revision and
/// consumer demand. This operation has no native graph or compiler cells.
let occurrences (revision: Fidelity.PSG.CheckedRevisionId) (demand: string) (rows: OccurrenceRows) =
    let bodies = rows.Occurrences
    let content: Fidelity.PSG.ScopeContentStamp =
        { Identity = "ccs:live-occurrences:" + revision.Session; Version = revision.Ordinal }
    let supports =
        bodies.Values |> Seq.collect (fun occurrence -> occurrence.Children)
        |> Seq.choose (fun child ->
            match child.Traversal with
            | Fidelity.PSG.ChildTraversal.SourceOmitted(support, _) -> Some support
            | _ -> None) |> Set.ofSeq
    let descriptor: Fidelity.PSG.ScopeDescriptor =
        { Content = content; LiveOccurrences = bodies.Keys |> Set.ofSeq
          ContextBreadcrumbs = bodies |> Map.map (fun _ occurrence -> occurrence.OccurrenceContexts)
          RequiredBoundaries = Set.empty; RequiredSupports = supports; OwnedArtifacts = Set.empty }
    let authorization: Fidelity.PSG.ScopeAuthorization =
        { Content = content; CheckedRevision = revision; Boundaries = []
          Supports = supports |> Set.toList |> List.map (fun key -> { Key = key; Version = revision.Ordinal }) }
    let delivery: Fidelity.PSG.OccurrenceDelivery =
        { Transaction =
            { BaseCursor = { Subscription = demand; Ordinal = 0UL }; BaseRevision = revision
              TargetCursor = { Subscription = demand; Ordinal = 1UL }; TargetRevision = revision
              Changes = [Fidelity.PSG.ScopeChange.Add descriptor]; Authorizations = [authorization]
              Withdrawals = []; ArtifactTransitions = [] }
          Sections = [{ Descriptor = descriptor; Occurrences = bodies }] }
    match Fidelity.PSG.ScopedPublication.start demand revision with
    | Error errors -> Error(sprintf "Occurrence diagnostic identity refused: %A" errors)
    | Ok catalog ->
        match Fidelity.PSG.ScopedPublication.apply delivery.Transaction catalog,
              Fidelity.PSG.OccurrenceDelivery.check delivery with
        | Ok _, [] -> Ok(delivery, rows.ContextHeaders, rows.ContextRoots)
        | transaction, sections ->
            Error(sprintf "Occurrence diagnostic structure refused: %A; %A" (transaction |> Result.map ignore) sections)

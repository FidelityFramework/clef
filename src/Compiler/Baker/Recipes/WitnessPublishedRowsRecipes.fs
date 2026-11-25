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

let private describeMetadataValue (value: MetadataValue) =
    match value with
    | MetadataValue.String _ -> "MetadataValue.String"
    | MetadataValue.Int _ -> "MetadataValue.Int"
    | MetadataValue.Int64 _ -> "MetadataValue.Int64"
    | MetadataValue.Bool _ -> "MetadataValue.Bool"
    | MetadataValue.Float _ -> "MetadataValue.Float"
    | MetadataValue.RealLiteral _ -> "MetadataValue.RealLiteral"
    | MetadataValue.Type _ -> "MetadataValue.Type"
    | MetadataValue.NodeId _ -> "MetadataValue.NodeId"
    | MetadataValue.SourceRange _ -> "MetadataValue.SourceRange"
    | MetadataValue.StringList _ -> "MetadataValue.StringList"
    | MetadataValue.NodeIdList _ -> "MetadataValue.NodeIdList"
    | MetadataValue.Specialization _ -> "MetadataValue.Specialization"

let private freezeNode (admittedClaim: NodeId * ObligationInfo -> Result<Fidelity.PSG.ObligationInfo, string>) (node: SemanticNode) =
    let anchorsResult =
        match node.Metadata.TryFind ObligationMetadata.Anchors with
        | None -> Ok []
        | Some(MetadataValue.StringList names) -> Ok names
        | Some other -> Error (sprintf "Obligation anchors are recorded as %s, not as a list of names." (describeMetadataValue other))
    let kindResult =
        match node.Kind with
        | SemanticKind.Obligation info -> admittedClaim (node.Id, info) |> Result.map Fidelity.PSG.SemanticKind.Obligation
        | kind -> Ok (mapSemanticKind kind)
    match anchorsResult, kindResult with
    | Error reason, _ | _, Error reason -> Error(failure (Some node.Id) ("The node cannot be frozen: " + reason))
    | Ok anchors, Ok kind ->
        Ok ({ Id = nodeId node.Id
              Kind = kind
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

let private freezeCodata claim (facts: WitnessLiveCodata) : Fidelity.PSG.Codata =
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
      CallableAggregateDependencies = rows (mapCallableAggregateDependencyAccountUsing claim) facts.CallableAggregateDependencies
      CallableBranches = mapCallableBranchAuthority facts.CallableBranches
      MutableCallableStorage = rows mapMutableCallableStorage facts.MutableCallableStorage
      ContinuationFrames = rows mapContinuationFrame facts.ContinuationFrames
      SequenceOrigins = ids facts.SequenceOrigins
      SequenceFlows = rows mapSequenceFlow facts.SequenceFlows
      SequenceFamilies = rows mapSequenceFamily facts.SequenceFamilies
      SequenceTemplateCopies = rows mapSequenceTemplateCopy facts.SequenceTemplateCopies
      ContinuationStorage = ids facts.ContinuationStorage
      ContinuationRegions = rows mapContinuationRegion facts.ContinuationRegions
      AsyncFormations = rows mapAsyncFormation facts.AsyncFormations
      AsyncActivations = rows mapAsyncActivation facts.AsyncActivations
      AsyncSuspensions = rows mapAsyncSuspension facts.AsyncSuspensions
      AsyncOrchestrations = rows mapAsyncOrchestration facts.AsyncOrchestrations
      RegionAllocations = rows mapRegionAllocation facts.RegionAllocations
      RegionCallPassings = rows mapRegionCallPassing facts.RegionCallPassings
      RegionCopyEndpoints = rows mapRegionCopyEndpoint facts.RegionCopyEndpoints
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
        let pending = dispatch.Required |> List.filter (fun (_, info) ->
            match info.Body with ObligationBody.Pending _ | ObligationBody.OptionalEntryArgumentConversion _ | ObligationBody.OptionalEntryAbsenceArgumentConversion _ -> true | _ -> false)
        let unadmitted = pending |> List.filter (ProofDispatchRecipes.optionalEntryPending graph selected.Emission.Boundary >> not)
        let current = ProofDispatchRecipes.matchesInventory graph dispatch
        let boundaryCurrent =
            if pending.IsEmpty then true else
            let authored = ProofDispatchRecipes.boundaryCalls graph
            authored.Length = selected.Emission.Boundary.Calls.Count &&
            (authored |> List.forall (fun call -> selected.Emission.Boundary.Calls.TryFind call.Site = Some call))
        if not unadmitted.IsEmpty then
            Error (unadmitted |> List.map (fun (id, _) -> failure (Some id) "Source proof dispatch is unavailable: The Pending claim lacks its exact current optional-entry conversion account."))
        elif not current || not boundaryCurrent then Error [failure None "The source proof dispatch inventory, optional-entry accounts or exact query changed before publication."]
        else
            let admittedClaim (id, info) =
                if ProofDispatchRecipes.optionalEntryPending graph selected.Emission.Boundary (id, info) then
                    Ok (mapObligationInfo info)
                else tryMapObligationInfo info
            let claim (_, info) = mapObligationInfo info
            let bodies = scope.Occurrences.Values |> Seq.map (fun occurrence -> freezeNode admittedClaim occurrence.Body) |> Seq.toList
            let errors = bodies |> List.choose (function Error error -> Some error | Ok _ -> None)
            if not errors.IsEmpty then Error errors else
            let codataClaims =
                (selected.Codata.CallableAggregateDependencies.Values |> Seq.collect _.Claims)
                |> Seq.append (selected.Emission.Callable.AggregateDependencies.Values |> Seq.collect _.Claims)
                |> Seq.append dispatch.Required
                |> Seq.toList
            let claimError = codataClaims |> List.tryPick (fun pair -> match admittedClaim pair with Ok _ -> None | Error reason -> Some reason)
            match claimError with
            | Some reason -> Error [failure None ("The selected source facts cannot be frozen: " + reason)]
            | None ->
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
                     Codata = freezeCodata claim selected.Codata; Emission = mapWitnessEmissionProjection selected.Emission
                     Foreign = mapWitnessForeignStorage selected.Foreign; Demand = mapWitnessExplicitDemand selected.Demand
                     Obligations = dispatch.Required |> List.map claim
                     CurrentClaims = dispatch.Required |> List.map (fun (id, info) -> nodeId id, claim (id, info)) |> Map.ofList
                     ObligationSources = dispatch.SourceGroups |> Map.toSeq |> Seq.map (fun (id, groups) -> nodeId id, groups |> List.map (List.map nodeId)) |> Map.ofSeq
                     ObligationQuery = query }

/// Source re-observation compares the complete frozen leaf tables. The native
/// platform is the exact source input object; it is never reconstructed here.
let private sameFreestandingStartup (left: FreestandingStartup option) (right: FreestandingStartup option) =
    match left, right with
    | None, None -> true
    | Some a, Some b ->
        a.EntrySymbol = b.EntrySymbol && a.MainFunction = b.MainFunction &&
        a.ArgcOffset = b.ArgcOffset && a.ArgvOffset = b.ArgvOffset &&
        a.ExitSyscall = b.ExitSyscall && a.SyscallRegister = b.SyscallRegister &&
        a.Arg0Register = b.Arg0Register
    | _ -> false

let private samePlatformContext (left: PlatformContext) (right: PlatformContext) =
    left.PlatformId = right.PlatformId &&
    left.Dimensions = right.Dimensions &&
    left.Representations = right.Representations &&
    left.EndpointReturns = right.EndpointReturns &&
    left.PlatformLibraryPath = right.PlatformLibraryPath &&
    left.PlatformDescription = right.PlatformDescription &&
    left.PlatformLoading = right.PlatformLoading &&
    left.PlatformSourcePaths = right.PlatformSourcePaths &&
    left.PlatformArchitecture = right.PlatformArchitecture &&
    left.PlatformOS = right.PlatformOS &&
    left.Predicates = right.Predicates &&
    sameFreestandingStartup left.FreestandingStartup right.FreestandingStartup &&
    left.SubstrateKind = right.SubstrateKind &&
    left.RuntimeModel = right.RuntimeModel &&
    left.ProjectMemoryPolicy = right.ProjectMemoryPolicy &&
    left.AvailableMemorySpaces = right.AvailableMemorySpaces &&
    left.DefaultMemorySpace = right.DefaultMemorySpace &&
    left.ClockFrequencyMhz = right.ClockFrequencyMhz &&
    left.NsPerWeightUnit = right.NsPerWeightUnit

let matches (held: WitnessPublishedRows) (current: WitnessPublishedRows) =
    samePlatformContext held.SourcePlatform current.SourcePlatform &&
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
    let nodeIdValue (Fidelity.PSG.NodeId n) = n
    let unknownBodies =
        bodies |> Map.toSeq |> Seq.collect (fun (id, occurrence) ->
            let permitted = Set.union known (omitted occurrence)
            Fidelity.PSG.IntegrityNamed.nodeReferences occurrence.Body
            |> Seq.filter (permitted.Contains >> not)
            |> Seq.map (fun missing -> sprintf "Occurrence %d requires unavailable identity %d." (nodeIdValue id) (nodeIdValue missing)))
    let unknownHeaders =
        readings.ContextHeaders.Values |> Seq.collect (fun header ->
            Fidelity.PSG.IntegrityNamed.contextHeaderReferences header
            |> Seq.filter (known.Contains >> not)
            |> Seq.map (fun missing -> sprintf "Context %d requires unavailable identity %d." (nodeIdValue header.Identity) (nodeIdValue missing)))
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
    | Error errors -> Error(sprintf "Occurrence diagnostic identity refused: %d errors" errors.Length)
    | Ok catalog ->
        match Fidelity.PSG.ScopedPublication.apply delivery.Transaction catalog,
              Fidelity.PSG.OccurrenceDelivery.check delivery with
        | Ok _, [] -> Ok(delivery, rows.ContextHeaders, rows.ContextRoots)
        | transaction, sections ->
            let txStatus = match transaction with Ok _ -> "Ok" | Error errs -> sprintf "Error(%d)" errs.Length
            Error(sprintf "Occurrence diagnostic structure refused: %s; %d section violations" txStatus sections.Length)

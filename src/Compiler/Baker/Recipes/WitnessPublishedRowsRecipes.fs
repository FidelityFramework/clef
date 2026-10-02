// SPDX-License-Identifier: MIT
/// Freeze Baker's selected facts before the single passive publication exit.
/// This recipe returns leaf tables, never a Revision or an alternate graph.
module Clef.Compiler.Baker.Recipes.WitnessPublishedRowsRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.PublishedFactRows

let private failure occurrence reason : WitnessProjectionFailure =
    { Occurrence = occurrence; Participants = Set.ofList (Option.toList occurrence)
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
      CallableCarriers = rows mapCallableCarrier facts.CallableCarriers
      CallableJoins = rows mapCallableJoin facts.CallableJoins
      CallableFlows = rows mapCallableFlow facts.CallableFlows
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

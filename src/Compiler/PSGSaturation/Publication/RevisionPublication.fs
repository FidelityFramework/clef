// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Publication of one revision of the Program Semantic Graph.
///
/// This is the only place a graph leaves the compiler service. The value it returns
/// (Fidelity.PSG.Revision) holds every fact a witness may read, as data. A reader of a
/// revision holds no reference to this assembly and calls no function in it.
///
/// Debt carried here, to be retired into Baker recipes: the projections read below
/// (WitnessEmission, BorrowedViews, MappedSpans, MappedBindings, Mmio, ExplicitDemand)
/// compute at publication what saturation should already have settled on the graph.
/// They run here, under the source owner, so that no reader runs them.
module Clef.Compiler.PSGSaturation.Publication.RevisionPublication

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.Publication.RevisionMappers

module Contract = Fidelity.PSG.Revision

/// The implementation that publishes; carried in every revision header.
[<Literal>]
let Producer = "Clef.Compiler.Service"

/// One refusal of publication, naming the node it concerns where there is one.
type PublicationFailure = {
    Occurrence: NodeId option
    Reason: string
}

let private refusal occurrence reason = { Occurrence = occurrence; Reason = reason }

let private anchors (node: SemanticNode) : Result<string list, PublicationFailure> =
    match Map.tryFind ObligationMetadata.Anchors node.Metadata with
    | None -> Ok []
    | Some (MetadataValue.StringList names) -> Ok names
    | Some other ->
        Error (refusal (Some node.Id) (sprintf "Obligation anchors are recorded as %A, not as a list of names." other))

/// A checker type is frozen under the source owner. A type the checker left in a
/// state it cannot name is a refusal at this node, never a published placeholder.
let private frozenType (node: SemanticNode) : Result<Fidelity.PSG.TypeIdentity, PublicationFailure> =
    try Ok (freeze node.Type)
    with failure -> Error (refusal (Some node.Id) ("The node's type cannot be frozen: " + failure.Message))

let private publishNode (node: SemanticNode) : Result<Fidelity.PSG.SemanticNode, PublicationFailure> =
    match frozenType node, anchors node with
    | Error failure, _ | _, Error failure -> Error failure
    | Ok frozen, Ok names ->
        try
            Ok ({ Id = nodeId node.Id
                  Kind = mapSemanticKind node.Kind
                  Range = { File = node.Range.File
                            Start = { Line = node.Range.Start.Line; Column = node.Range.Start.Column }
                            End = { Line = node.Range.End.Line; Column = node.Range.End.Column } }
                  Type = frozen
                  Children = List.map nodeId node.Children
                  Parent = Option.map nodeId node.Parent
                  IsReachable = node.IsReachable
                  EmissionStrategy = mapEmissionStrategy node.EmissionStrategy
                  ValueRange = Option.map mapValueRange node.ValueRange
                  ObligationAnchors = names } : Fidelity.PSG.SemanticNode)
        with failure -> Error (refusal (Some node.Id) ("The node cannot be published: " + failure.Message))

let private publishNodes (graph: SemanticGraph) =
    let published = graph.Nodes |> Map.toList |> List.map (fun (_, node) -> publishNode node)
    let failures = published |> List.choose (function Error failure -> Some failure | Ok _ -> None)
    match failures with
    | [] ->
        published
        |> List.choose (function Ok node -> Some (node.Id, node) | Error _ -> None)
        |> Map.ofList
        |> Ok
    | _ -> Error failures

let private publishCodata (facts: Codata) : Fidelity.PSG.Codata =
    let ids = Map.toSeq >> Seq.map (fun (key, value) -> nodeId key, nodeId value) >> Map.ofSeq
    let rows map (table: Map<NodeId, _>) = table |> Map.toSeq |> Seq.map (fun (key, value) -> nodeId key, map value) |> Map.ofSeq
    { Escapes = rows mapEscapeKind facts.Escapes
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

let private publishLayout (layout: Clef.Compiler.PSGSaturation.SemanticGraph.BorrowedViews.Layout) : Fidelity.PSG.BorrowedViewLayout =
    { Schema = layout.Schema
      ElementBits = layout.ElementBits
      Range = mapValueRange layout.Range
      Alignment = layout.Alignment
      Access = layout.Access }

let private publishForeign (graph: SemanticGraph) : Fidelity.PSG.ForeignStorageProjection =
    let applications =
        graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with
            | SemanticKind.Application (callee, _) -> Some (id, callee)
            | _ -> None)
    let borrowedViews =
        applications |> List.choose (fun (id, _) ->
            Clef.Compiler.PSGSaturation.SemanticGraph.BorrowedViews.operation graph id
            |> Option.map (fun (operation, view, arguments, layout) ->
                let span = layout |> Result.bind (Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans.forLayout graph)
                nodeId id,
                ({ Site = nodeId id
                   Operation = operation
                   View = nodeId view
                   Arguments = List.map nodeId arguments
                   Layout = Result.map publishLayout layout
                   Span = Result.map mapMappedSpanModel span } : Fidelity.PSG.BorrowedViewOperation)))
    let mmio =
        applications |> List.choose (fun (id, _) ->
            Clef.Compiler.PSGSaturation.SemanticGraph.Mmio.operation graph id
            |> Option.map (fun (operation, arguments) ->
                nodeId id,
                ({ Site = nodeId id; Operation = operation; Arguments = List.map nodeId arguments } : Fidelity.PSG.MmioOperation)))
    let mapped =
        applications |> List.choose (fun (id, callee) ->
            Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings.tryFindCall graph callee
            |> Option.map (fun _ -> nodeId id))
    { BorrowedViews = Map.ofList borrowedViews
      Mmio = Map.ofList mmio
      MappedCalls = Set.ofList mapped }

let private publishDemand (graph: SemanticGraph) : Fidelity.PSG.ExplicitDemandProjection =
    let operands =
        graph.Nodes |> Map.toList |> List.choose (fun (id, _) ->
            Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand.operand graph id
            |> Option.map (fun operand -> nodeId id, nodeId operand))
    let relations =
        graph.Edges
        |> List.choose (fun edge ->
            let frontier =
                match edge.Role with
                | EdgeRole.EagerDemand frontier -> Some (Some (mapEagerFrontier frontier))
                | EdgeRole.EagerDemandPending -> Some None
                | _ -> None
            frontier |> Option.map (fun frontier ->
                nodeId edge.Target,
                ({ Sources = List.map nodeId edge.Sources
                   Ordinal = edge.Ordinal
                   Frontier = frontier
                   IsDemand = (edge.Class = EdgeClass.Demand) } : Fidelity.PSG.EagerDemandRelation)))
        |> List.groupBy fst
        |> List.map (fun (target, rows) -> target, List.map snd rows)
    { Operands = Map.ofList operands; Relations = Map.ofList relations }

let private publishObligationSources (graph: SemanticGraph) : Map<Fidelity.PSG.NodeId, Fidelity.PSG.NodeId list list> =
    graph.Edges
    |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains)
    |> List.groupBy (fun edge -> edge.Target)
    |> List.map (fun (target, edges) -> nodeId target, edges |> List.map (fun edge -> List.map nodeId edge.Sources))
    |> Map.ofList

let private publishWidths (platform: PlatformContext) : Fidelity.PSG.PlatformWidths =
    let width dimension = PlatformContext.tryWidth platform (WidthDimension.name dimension)
    { Register = width WidthDimension.Register; Pointer = width WidthDimension.Pointer }

/// Publish the prepared graph as one revision. The graph must carry the complete
/// source witness projection (WitnessEmission.prepare); a graph that does not is refused.
let publish (platform: PlatformContext) (graph: SemanticGraph) : Result<Fidelity.PSG.Revision, PublicationFailure list> =
    match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.tryRead graph with
    | Error reason -> Error [ refusal None ("Source emission admission: " + reason) ]
    | Ok projection ->
        match publishNodes graph with
        | Error failures -> Error failures
        | Ok nodes ->
            try
                let obligations = Clef.Compiler.Nanopass.ObligationDischarge.ofGraph graph
                Ok ({ Header = { Schema = Contract.Schema; Producer = Producer }
                      Nodes = nodes
                      DeclarationRoots = graph.DeclarationRoots |> List.map (fun (id, root) -> nodeId id, mapDeclRoot root)
                      ModuleClassifications =
                        graph.ModuleClassifications.Value
                        |> Map.toSeq
                        |> Seq.map (fun (id, classification) -> nodeId id, mapModuleClassification classification)
                        |> Map.ofSeq
                      Platform = publishWidths platform
                      StaticStringPool = Option.map mapStaticStringPool graph.StaticStringPool
                      Codata = publishCodata graph.Codata.Value
                      Emission = mapWitnessEmissionProjection projection
                      Foreign = publishForeign graph
                      Demand = publishDemand graph
                      Obligations = List.map mapObligationInfo obligations
                      ObligationSources = publishObligationSources graph
                      ObligationQuery = Clef.Compiler.Nanopass.ObligationDischarge.smtLib obligations } : Fidelity.PSG.Revision)
            with failure -> Error [ refusal None ("The graph cannot be published: " + failure.Message) ]

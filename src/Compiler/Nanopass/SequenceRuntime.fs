// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Settle suspension control, finite frame placement and resume bodies in Baker.
/// Alex receives these facts; it neither reconstructs source control nor chooses
/// the storage of a live value.
module Clef.Compiler.Nanopass.SequenceRuntime

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Ingredients.Obligations
open Clef.Compiler.Nanopass.Recipe
module Control = Clef.Compiler.Baker.Recipes.SequenceControlRecipes
module Machine = Clef.Compiler.Baker.Recipes.SequenceMachineRecipes
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins
module Evidence = Clef.Compiler.Baker.Recipes.SequenceContinuationEvidence
module LayoutProof = Clef.Compiler.Baker.Recipes.ContinuationObligationRecipes

type Settlement = {
    Frames: Map<NodeId, ContinuationFrame>
    Origins: Map<NodeId, NodeId>
    Storage: Map<NodeId, NodeId>
    Regions: Map<NodeId, ContinuationRegion>
    Initializers: Map<NodeId, (NodeId * NodeId) list>
    CurrentReads: Set<NodeId>
    Destinations: Map<NodeId, NodeId>
    Curry: CurryInfo
    Residences: Map<NodeId, EscapeKind>
    Diagnostics: Diagnostic list
}

let private empty = {
    Frames = Map.empty; Origins = Map.empty; Storage = Map.empty; Regions = Map.empty
    Initializers = Map.empty; CurrentReads = Set.empty; Destinations = Map.empty; Curry = Codata.empty.Curry; Residences = Map.empty; Diagnostics = [] }

let private residual (node: SemanticNode) related reason = {
    Severity = NativeDiagnosticSeverity.Error; Code = "CCS8403"
    Message = "Sequence suspension requires further settlement: " + reason
    Range = node.Range; RelatedNodes = node.Id :: related
    Reachability = ReachabilityContext.Unknown }

let private slotNode (owner: SemanticNode) name ty range =
    { owner with Id = NodeId.fresh(); Kind = SemanticKind.PatternBinding name
                 Type = ty; ValueRange = range; Children = []; Parent = None
                 Metadata = Map.empty; SRTPResolution = None }

let private framePlan (graph: SemanticGraph) (owner: SemanticNode) =
    match Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.sequenceInitializers graph owner, Control.forOwner graph owner with
    | None, _ -> Result.Error (residual owner [] "The child capture initializer incidence is missing or contradictory.")
    | _, Result.Error pending -> Result.Error (residual graph.Nodes[pending.Site] [owner.Id] pending.Reason)
    | Some initializers, Ok control ->
        match owner.Kind, owner.Type, graph.Nodes[control.Generator].Kind with
        | SemanticKind.SeqExpr(_, captures), NativeType.TSeq item, SemanticKind.Lambda([_, _, formal], _, _, _, _) ->
            let cuts = control.ResumeEntries.Count - 1
            let state = slotNode owner "__continuation_state" Types.intType (Some (ValueRange.bounded -1I (bigint cuts)))
            let payloadRanges =
                control.Steps.Values |> Seq.choose (fun step ->
                    match step.Instruction with
                    | Control.Instruction.Suspend(payload, _) -> Some graph.Nodes[payload].ValueRange
                    | _ -> None) |> Seq.toList
            let currentRange =
                if payloadRanges |> List.forall Option.isSome then
                    payloadRanges |> List.choose id |> List.fold ValueRange.join ValueRange.Empty |> Some
                else None
            let current = slotNode owner "__continuation_current" item currentRange
            let graph = { graph with Nodes = graph.Nodes.Add(state.Id, state).Add(current.Id, current) }
            let captures = captures |> List.filter (fun capture ->
                capture.SourceNodeId |> Option.forall (Machine.isSymbolic graph Set.empty >> not))
            let captured = captures |> List.choose _.SourceNodeId |> Set.ofList
            let defined = control.Steps.Values |> Seq.fold (fun ids step -> Set.union ids step.Defines) Set.empty
            let required = Machine.requiredValues graph control |> Set.filter (fun id -> defined.Contains id || captured.Contains id)
            // A nested frame can retain the storage of a mutable cell after
            // the outer source stops reading that cell directly. Its borrow
            // extends storage liveness independently of scalar value liveness.
            let retainedCells =
                control.Steps.Values |> Seq.collect (fun step ->
                    match step.Instruction with
                    | Control.Instruction.Evaluate site ->
                        match graph.Nodes[site].Kind with
                        | SemanticKind.SeqExpr(_, nestedCaptures) ->
                            nestedCaptures |> List.choose (fun capture ->
                                if capture.IsMutable then capture.SourceNodeId |> Option.map (fun source -> site, source) else None)
                        | _ -> []
                    | _ -> []) |> Seq.toList
            let retained = retainedCells |> List.map snd |> Set.ofList |> Set.intersect required
            let live = control.LiveAcross.Values |> Seq.fold Set.union Set.empty |> Set.union retained |> Set.intersect required |> fun ids -> Set.difference ids captured
            let transient = Set.difference required (Set.union captured live)
            let persistentPlacement =
                if cuts = 0 then Placement.placeEmptyContinuation graph state.Id captures
                else Placement.placeContinuation graph state.Id current.Id captures (Set.toList live)
            match persistentPlacement,
                  Placement.placeContinuationLocals graph (Set.toList transient) with
            | Ok (SettledLayout.Record(_, Some bytes, Some alignment), slots),
              Ok (SettledLayout.Record(_, Some scratchBytes, Some scratchAlignment), scratchSlots) ->
                let slot (field: Placement.ContinuationField) : ContinuationSlot = {
                    Source = field.Source; ValueType = graph.Nodes[field.Source].Type
                    Field = field.Field; Holds = field.Holds
                    IsCapture = field.Role = Placement.ContinuationRole.Capture }
                let layout name fields extent align =
                    fields |> List.map (fun (field: Placement.ContinuationField) ->
                        field.Source, field.Field.Offset.Value, field.Field.Size.Value, field.Field.Align.Value)
                    |> fun fields -> LayoutProof.layout (NodeId.value owner.Id) name owner fields extent align
                let obligations = Enrichment.concat [
                    layout (sprintf "seq_%d_frame" (NodeId.value owner.Id)) slots bytes alignment
                    layout (sprintf "seq_%d_activation" (NodeId.value owner.Id)) scratchSlots scratchBytes scratchAlignment ]
                let constructionParticipants = graph.Edges |> List.collect (fun edge ->
                    if edge.Target = owner.Id then
                        match edge.Role with
                        | EdgeRole.SequenceCaptureFormation | EdgeRole.SequenceCaptureInitializer _
                        | EdgeRole.SequenceEnvironmentBorrow -> edge.Sources
                        | _ -> []
                    else [])
                let constructionEdges = obligations.NewEdges |> List.map (fun edge ->
                    { edge with Sources = List.distinct (edge.Sources @ constructionParticipants) })
                let obligations = { obligations with NewEdges = constructionEdges }
                let borrowEdges = retainedCells |> List.map (fun (site, source) -> {
                    Sources = [owner.Id; control.Generator; source]; Target = site
                    Class = EdgeClass.Suspension; Role = EdgeRole.ContinuationBorrow; Ordinal = 0 })
                let obligations = { obligations with NewEdges = obligations.NewEdges @ borrowEdges }
                let frame = {
                    Owner = owner.Id; Generator = control.Generator; Formal = formal
                    State = state.Id; Current = current.Id
                    Slots = List.map slot slots; Bytes = bytes; Alignment = alignment
                    ScratchSlots = List.map slot scratchSlots; ScratchBytes = scratchBytes; ScratchAlignment = scratchAlignment
                    Initializers = initializers |> List.filter (fst >> captured.Contains)
                    ResumeStates = control.ResumeEntries |> Map.toList |> List.map fst
                    Obligations = obligations.NewNodes |> List.map _.Id }
                Ok (control, frame, [ { state with IsReachable = false }; { current with IsReachable = false } ], obligations)
            | Result.Error error, _ | _, Result.Error error -> Result.Error (residual owner [] (sprintf "%A" error))
            | _ -> Result.Error (residual owner [] "The declared target has no concrete continuation extent and alignment.")
        | _ -> Result.Error (residual owner [control.Generator] "A sequence needs its typed, single-environment generator formal.")

/// A proven zero-cut generator can only finish on its first pull. Keep that
/// pull (including all source effects); the true branch has no attainable value.
let rec private emptyConsumers (graph: SemanticGraph) origins =
    let emptyOwners =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.SeqExpr _ when node.IsReachable ->
                match Control.forOwner graph node with
                | Ok control when control.ResumeEntries.Count = 1 -> Some node.Id
                | _ -> None
            | _ -> None) |> Set.ofSeq
    let _, certificates = SequenceCurrentAdmission.certify graph
    let loops =
        certificates |> List.choose (fun edge ->
            match edge.Sources with
            | [iterator; guard; loop] ->
                Map.tryFind iterator origins |> Option.bind (fun owner ->
                    if emptyOwners.Contains owner then Some(loop, guard) else None)
            | _ -> None) |> Map.ofList
    if loops.IsEmpty then graph
    else
        let create (source: SemanticNode) _ =
            let unitValue = { source with Id = NodeId.fresh(); Kind = SemanticKind.Literal NativeLiteral.Unit
                                          Children = []; Parent = None; Type = Types.unitType; ValueRange = None }
            let children = [loops[source.Id]; unitValue.Id]
            let replacement = { source with Kind = SemanticKind.Sequential children; Children = children }
            RecipeCreated { OriginalNodeId = source.Id; ReplacementRootId = source.Id
                            NewNodes = [unitValue; replacement]
                            ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Seq.emptyConsumption" }
        let rewritten = FoldIn.foldIn (FanOut.fanOut "SequenceEmptyConsumers" (fun node -> loops.ContainsKey node.Id) create graph) graph
        { rewritten with FieldRanges = graph.FieldRanges; ElementRanges = graph.ElementRanges
                         Layouts = graph.Layouts; StaticStringPool = graph.StaticStringPool }
        |> Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable
        |> SequenceEvaluation.normalize
        |> fun rewritten -> emptyConsumers rewritten origins

let normalizeWhenSourceAdmitted sourceAdmitted (graph: SemanticGraph) (curry: CurryInfo) =
    let realize = sourceAdmitted && graph.Platform.IsSome
    let prepared =
        if realize then SequenceFactoryResults.prepare graph curry
        else { SequenceFactoryResults.Graph = graph; Curry = curry; Destinations = Map.empty
               AllocationOrigins = Map.empty; FactoryCalls = Map.empty; Unresolved = [] }
    let graph = if prepared.Destinations.IsEmpty then prepared.Graph else SequenceEvaluation.normalize prepared.Graph
    let curry = prepared.Curry
    let origins, _ = Origins.settle graph curry
    let graph = if realize then emptyConsumers graph origins else graph
    let admitted, currentEdges = SequenceCurrentAdmission.certify graph
    let snapshots =
        if realize then SequenceAggregateValues.prepare graph admitted currentEdges
        else { SequenceAggregateValues.Graph = graph; Reads = admitted; Certificates = currentEdges; Residences = Map.empty; Unresolved = [] }
    let snapshotsChanged = snapshots.Graph.Nodes.Count <> graph.Nodes.Count
    let admitted, currentEdges = snapshots.Reads, snapshots.Certificates
    let graph = { snapshots.Graph with Edges = (snapshots.Graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.IteratorCurrentAdmitted)) @ currentEdges }
    let graph = if snapshotsChanged then SequenceEvaluation.normalize graph else graph
    let origins, _ = Origins.settle graph curry
    if not realize then graph, { empty with Origins = origins; CurrentReads = admitted; Curry = curry }
    else
        let currentDiagnostics =
            graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Application(callee, _) when node.IsReachable && not (admitted.Contains node.Id) ->
                    match graph.Nodes.TryFind callee with
                    | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.SeqEnumerator; Operation = "current" } } ->
                        Some (residual node [] "Reading current requires a settled successful-pull prerequisite for this exact iterator.")
                    | _ -> None
                | _ -> None) |> Seq.toList
        let residence = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeWithRegions graph prepared.Destinations prepared.FactoryCalls
        let graph = ObligationElaboration.foldIn { Enrichment.empty with NewEdges = residence.Evidence } graph
        let residenceDiagnostics = residence.Unresolved |> List.map (fun pending ->
            residual graph.Nodes[pending.Site] [] (sprintf "Allocation residence is unresolved: %A" pending.Reason))
        let planned =
            graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with SemanticKind.SeqExpr _ when node.IsReachable -> Some (framePlan graph node) | _ -> None) |> Seq.toList
        let plans = planned |> List.choose (function Ok plan -> Some plan | _ -> None)
        let regionPlan = SequenceRegions.settle graph
                            (plans |> List.map (fun (_, frame, _, _) -> frame.Owner, frame) |> Map.ofList)
                            residence.Regions origins
        let plans = plans |> List.map (fun (control, frame, slots, proof) -> control, regionPlan.Frames[frame.Owner], slots, proof)
        let diagnostics =
            (snapshots.Unresolved |> List.map (fun (site, consumer) -> residual graph.Nodes[site] [consumer] "The Option current snapshot lacks a finite covering activation for every use."))
            @ (regionPlan.Unresolved |> List.map (fun pending -> residual graph.Nodes[pending.Site] [] pending.Reason))
            @ (planned |> List.choose (function Result.Error diagnostic -> Some diagnostic | _ -> None))
            @ (prepared.Unresolved |> List.map (fun pending -> residual graph.Nodes[pending.Factory] [] pending.Reason))
        let graph = plans |> List.fold (fun graph (_, _, slots, obligations) ->
            ObligationElaboration.foldIn { obligations with NewNodes = slots @ obligations.NewNodes } graph) graph
        let graph = ObligationElaboration.foldIn regionPlan.Evidence graph
        let realized = plans |> List.map (fun (control, frame, _, _) ->
            let machine = Machine.build graph control frame
            match Evidence.forMachine graph control frame machine with
            | Ok evidence -> Ok (frame, machine, evidence)
            | Result.Error pending -> Result.Error (residual graph.Nodes[pending.Site] [pending.Owner] pending.Reason))
        let evidence = realized |> List.choose (function
            | Ok (_, machine, proof) -> Some { proof with NewEdges = machine.AggregateEvidence @ proof.NewEdges }
            | _ -> None) |> Enrichment.concat
        let diagnostics = diagnostics @ (realized |> List.choose (function Result.Error error -> Some error | _ -> None))
        let machines = realized |> List.choose (function Ok (frame, machine, _) -> Some (frame, machine) | _ -> None)
        let byGenerator = machines |> List.map (fun (frame, machine) -> frame.Generator, machine) |> Map.ofList
        let create (source: SemanticNode) _ = RecipeCreated {
            OriginalNodeId = source.Id; NewNodes = byGenerator[source.Id].Nodes
            ReplacementRootId = source.Id
            ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Seq.resume" }
        let rewritten =
            if byGenerator.IsEmpty then graph
            else FoldIn.foldIn (FanOut.fanOut "SequenceRuntime" (fun node -> byGenerator.ContainsKey node.Id) create graph) graph
        // These source placements precede this representation-only recipe.
        // It adds no source aggregate type and preserves every existing slot.
        let rewritten = { rewritten with FieldRanges = graph.FieldRanges; ElementRanges = graph.ElementRanges
                                         Layouts = graph.Layouts; StaticStringPool = graph.StaticStringPool }
        let values = machines |> List.collect (fun (_, machine) -> machine.ValueSources)
        let edges = values |> List.map (fun (value, source) -> {
            Sources = [source]; Target = value; Class = EdgeClass.Provenance
            Role = EdgeRole.ContinuationValue; Ordinal = 0 })
        let propagated = values |> List.fold (fun (facts: Map<NodeId, NodeId>) (value, source) ->
            match origins.TryFind source with Some owner -> facts.Add(value, owner) | None -> facts) origins
        let propagated = machines |> List.fold (fun facts (frame, machine) ->
            machine.PersistentReferences |> List.fold (fun (facts: Map<NodeId, NodeId>) id -> facts.Add(id, frame.Owner)) facts) propagated
        let storage = machines |> List.collect (fun (frame, machine) -> machine.ScratchReferences |> List.map (fun id -> id, frame.Owner)) |> Map.ofList
        let regions = values |> List.fold (fun (facts: Map<NodeId, ContinuationRegion>) (value, source) ->
            match regionPlan.Regions.TryFind source with Some region -> facts.Add(value, region) | None -> facts) regionPlan.Regions
        let initializers =
            let originals = plans |> List.map (fun (_, frame, _, _) -> frame.Owner, frame.Initializers) |> Map.ofList
            machines |> List.fold (fun facts (_, machine) -> machine.Initializers |> Map.fold (fun facts id values -> Map.add id values facts) facts) originals
        let currentBySource = currentEdges |> List.map (fun edge -> edge.Target, edge) |> Map.ofList
        let liftedCurrent =
            values |> List.choose (fun (value, source) ->
                match currentBySource.TryFind source, rewritten.Nodes.TryFind value with
                | Some proof, Some { Kind = SemanticKind.Application(_, arguments) } ->
                    Some { proof with Target = value; Sources = List.distinct (source :: proof.Sources @ arguments) }
                | _ -> None)
        let currentReads = liftedCurrent |> List.fold (fun ids edge -> Set.add edge.Target ids) admitted
        let rewritten = { rewritten with Edges = rewritten.Edges @ edges @ liftedCurrent } |> ObligationElaboration.foldIn evidence
        let rewritten =
            if List.isEmpty machines then rewritten
            else Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable rewritten
        rewritten, {
            Frames = plans |> List.map (fun (_, frame, _, _) -> frame.Owner, frame) |> Map.ofList
            Origins = propagated; Storage = storage; Regions = regions; Initializers = initializers
            CurrentReads = currentReads; Destinations = prepared.Destinations; Curry = curry; Residences = snapshots.Residences |> Map.fold (fun facts id site -> Map.add id site facts) residence.Sites; Diagnostics = diagnostics @ residenceDiagnostics @ currentDiagnostics }

/// Standalone graph callers supply an already admitted source graph.
let normalize graph curry = normalizeWhenSourceAdmitted true graph curry

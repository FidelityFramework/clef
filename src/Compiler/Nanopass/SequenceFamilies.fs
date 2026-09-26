// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Source-owned common sequence protocols. Complete flow alternatives connect
/// actual constructors; a matching element type or byte size never connects
/// unrelated values. Physical placement and fresh-copy evidence are separate
/// from the successful-pull premise required by every current read.
module Clef.Compiler.Nanopass.SequenceFamilies

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Control = Clef.Compiler.Baker.Recipes.SequenceControlRecipes

type Residual = { Site: NodeId; Reason: string }
type Plan = {
    Identity: NodeId
    Owners: Set<NodeId>
    Participants: Set<NodeId>
    ElementType: NativeType
    StateRange: ValueRange
    CurrentRange: ValueRange option
    Payloads: Map<NodeId, NodeId list>
}

type Planning = {
    Plans: Map<NodeId, Plan>
    ByOwner: Map<NodeId, NodeId>
    Unresolved: Residual list
}

let private element ty =
    match applySubst ty with
    | NativeType.TSeq item | NativeType.TSeqEnumerator item -> Some item
    | _ -> None

/// Connected components retain all alternatives, including transitively shared
/// inputs at different callable boundaries. Open alternatives are not silently
/// removed to make a finite family appear complete.
let plan (graph: SemanticGraph) (flows: Map<NodeId, SequenceFlow>)
         (controls: Map<NodeId, Control.Control>) : Planning =
    let addGroup groups owners =
        if Set.isEmpty owners then groups else
        let overlapping, separate = groups |> List.partition (fun group -> not (Set.intersect group owners).IsEmpty)
        (overlapping |> List.fold Set.union owners) :: separate
    let groups =
        flows.Values |> Seq.fold (fun groups flow -> addGroup groups flow.Owners) []
        |> List.fold addGroup []
    let mutable unresolved = []
    let fail site reason = unresolved <- { Site = site; Reason = reason } :: unresolved
    let plans = groups |> List.choose (fun owners ->
        let identity = Set.minElement owners
        let participants = flows |> Map.filter (fun _ flow -> not (Set.intersect owners flow.Owners).IsEmpty)
        let closed = participants |> Map.forall (fun id flow ->
            if not flow.Unknown.IsEmpty then
                fail id "A common sequence protocol requires every flow alternative; an opaque origin remains."
                false
            else true)
        let members = owners |> Set.toList |> List.choose (fun owner ->
            match graph.Nodes.TryFind owner, controls.TryFind owner with
            | Some { Kind = SemanticKind.SeqExpr(generator, _); Type = NativeType.TSeq item }, Some control
                when control.Owner = owner && control.Generator = generator -> Some(owner, item, control)
            | _ -> fail owner "A sequence family member lacks its exact constructor and source control owner."; None)
        match members with
        | [] -> None
        | (_, item, _) :: _ ->
            let typesAgree =
                (members |> List.forall (fun (_, other, _) -> applySubst other = applySubst item)) &&
                (participants |> Map.forall (fun id flow ->
                    flow.Occurrence = id && applySubst flow.ElementType = applySubst item &&
                    (graph.Nodes.TryFind id |> Option.bind (fun node -> element node.Type)
                     |> Option.exists (fun actual -> applySubst actual = applySubst item))))
            if not typesAgree then fail identity "Connected sequence alternatives disagree on their retained element type or dimensions."
            if not closed || not typesAgree || members.Length <> owners.Count then None
            else
                let payloads = members |> List.map (fun (owner, _, control) ->
                    owner, (control.Steps.Values |> Seq.choose (fun step ->
                        match step.Instruction with Control.Instruction.Suspend(payload, _) -> Some payload | _ -> None)
                        |> Seq.distinct |> Seq.toList)) |> Map.ofList
                let ranges = payloads.Values |> Seq.collect id |> Seq.map (fun id -> graph.Nodes[id].ValueRange) |> Seq.toList
                let currentRange =
                    if not ranges.IsEmpty && (ranges |> List.forall Option.isSome) then
                        ranges |> List.choose id |> List.fold ValueRange.join ValueRange.Empty |> Some
                    else None
                let maximumState = members |> List.collect (fun (_, _, control) -> control.ResumeEntries |> Map.keys |> Seq.toList) |> List.fold max 0
                Some(identity, { Identity = identity; Owners = owners; Participants = participants |> Map.keys |> Set.ofSeq
                                 ElementType = item; StateRange = ValueRange.bounded -1I (bigint maximumState)
                                 CurrentRange = currentRange; Payloads = payloads })) |> Map.ofList
    { Plans = plans
      ByOwner = plans |> Map.toList |> List.collect (fun (family, plan) -> plan.Owners |> Set.toList |> List.map (fun owner -> owner, family)) |> Map.ofList
      Unresolved = List.rev unresolved }

let private sameField (left: SettledField) (right: SettledField) =
    left.Slot = right.Slot && left.Offset = right.Offset && left.Size = right.Size && left.Align = right.Align

/// Read back actual generated boundaries and placements. The family contract
/// is admitted only after every member agrees; it never patches a signature.
let settle (graph: SemanticGraph) (planning: Planning) (frames: Map<NodeId, ContinuationFrame>)
           (flows: Map<NodeId, SequenceFlow>) =
    let mutable residuals = []
    let mutable evidence = Enrichment.empty
    let fail site reason = residuals <- { Site = site; Reason = reason } :: residuals
    let families = planning.Plans |> Map.toList |> List.choose (fun (identity, plan) ->
        let mutable valid = true
        let reject site reason = valid <- false; fail site reason
        let members = plan.Owners |> Set.toList |> List.choose (fun owner ->
            match frames.TryFind owner with
            | None -> reject owner "A sequence family member has no settled frame."; None
            | Some frame ->
                let state = frame.Slots |> List.tryFind (fun slot -> slot.Source = frame.State)
                let current = frame.Slots |> List.tryFind (fun slot -> slot.Source = frame.Current)
                let signature =
                    match graph.Nodes.TryFind frame.Generator, graph.Nodes.TryFind frame.Formal with
                    | Some { Kind = SemanticKind.Lambda([_, parameterType, formal], body, _, _, LambdaContext.SeqGenerator); Type = signature },
                      Some { Kind = SemanticKind.PatternBinding _; Type = formalType }
                        when formal = frame.Formal && applySubst parameterType = applySubst formalType &&
                             applySubst formalType = NativeType.TSeqEnumerator(applySubst plan.ElementType) &&
                             applySubst signature = NativeType.TFun(applySubst formalType, Types.boolType) &&
                             (graph.Nodes.TryFind body |> Option.exists (fun node -> applySubst node.Type = Types.boolType)) -> Some signature
                    | _ -> None
                let hasYield = not plan.Payloads[owner].IsEmpty
                if signature.IsNone || state.IsNone || hasYield <> current.IsSome then
                    reject owner "A sequence family generator, state or successful-current field differs from its source plan."
                    None
                else
                    let captures = frame.Slots |> List.filter _.IsCapture |> List.map _.Source |> Set.ofList
                    let uninitialized = frame.Slots |> List.filter (fun slot -> not slot.IsCapture && slot.Source <> frame.State) |> List.map _.Source |> Set.ofList
                    Some(owner, (frame, state.Value.Field, current,
                        { Generator = frame.Generator; Formal = frame.Formal; Signature = signature.Value
                          State = frame.State; Current = current |> Option.map _.Source
                          Slots = frame.Slots
                          Captures = captures; Uninitialized = uninitialized; Obligations = frame.Obligations })))
        match members with
        | [] -> None
        | (_, (first, state, _, _)) :: _ ->
            let currents = members |> List.choose (fun (_, (_, _, current, _)) -> current)
            let current = List.tryHead currents
            if members |> List.exists (fun (_, (frame, field, _, _)) ->
                frame.Bytes <> first.Bytes || frame.Alignment <> first.Alignment || not (sameField state field)) then
                reject identity "Sequence family members do not share an admitted state field, extent and alignment."
            if current |> Option.exists (fun common -> currents |> List.exists (fun actual ->
                not (sameField common.Field actual.Field) || common.Holds <> actual.Holds ||
                applySubst common.ValueType <> applySubst actual.ValueType)) then
                reject identity "Successful sequence alternatives do not share a settled current field representation and offset."
            if not valid || members.Length <> plan.Owners.Count then None
            else
                let participants = flows |> Map.toList |> List.choose (fun (id, flow) ->
                    if flow.Unknown.IsEmpty && not flow.Owners.IsEmpty && Set.isSubset flow.Owners plan.Owners then Some id else None) |> Set.ofList
                let contracts = members |> List.map (fun (owner, (_, _, _, memberContract)) -> owner, memberContract) |> Map.ofList
                let dependencies = plan.Owners |> Set.toList
                let edges = members |> List.collect (fun (owner, (_, _, _, memberContract)) ->
                    let layout = {
                        Sources = List.distinct (dependencies @ [memberContract.Generator; memberContract.Formal; memberContract.State]
                                                @ (memberContract.Slots |> List.map _.Source) @ memberContract.Obligations)
                        Target = owner; Class = EdgeClass.Suspension; Role = EdgeRole.SequenceFamilyLayout; Ordinal = 0 }
                    let yields = plan.Payloads[owner] |> List.mapi (fun index payload -> {
                        Sources = [identity; owner; memberContract.Generator; memberContract.Current.Value; payload]
                        Target = memberContract.Current.Value; Class = EdgeClass.Suspension; Role = EdgeRole.SequenceFamilyCurrent; Ordinal = index })
                    layout :: yields)
                evidence <- Enrichment.combine evidence { Enrichment.empty with NewEdges = edges }
                Some(identity, { Identity = identity; ElementType = plan.ElementType; Participants = participants; Members = contracts
                                 Bytes = first.Bytes; Alignment = first.Alignment; StateField = state
                                 CurrentField = current |> Option.map _.Field
                                 CurrentRepresentation = current |> Option.map (fun slot -> slot.ValueType, slot.Holds) })) |> Map.ofList
    families, evidence, List.rev residuals

/// Certify a representation copy only for the actual fresh-acquisition
/// operation and its already admitted storage. This adds no evaluation edge,
/// runs no generator/capture initializer, and grants no current-read premise.
let copies (graph: SemanticGraph) (families: Map<NodeId, SequenceFamily>)
           (flows: Map<NodeId, SequenceFlow>) (residences: Map<NodeId, EscapeKind>)
           (regions: Map<NodeId, ContinuationRegion>)
           (initializers: Map<NodeId, (NodeId * NodeId) list>) (destinations: Map<NodeId, NodeId>) =
    let calls = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
    let actuals formal =
        calls.ParameterInputs.TryFind formal |> Option.bind (fun inputs ->
            if inputs.IsEmpty || inputs |> List.exists (fun (call, actual) ->
                match calls.Calls.TryFind call with
                | Some resolved when not resolved.Unknown ->
                    not (resolved.Targets |> List.exists (fun target ->
                        List.zip target.Parameters target.Arguments |> List.exists (fun ((_, _, parameter), argument) ->
                            parameter = formal && argument = actual)))
                | _ -> true) then None
            else Some(inputs |> List.map snd |> List.distinct))
    let unionAll values =
        values |> List.fold (fun found next -> Option.map2 Set.union found next) (Some Set.empty)
    let originalValue id =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources with
            | EdgeClass.Provenance, EdgeRole.ContinuationValue, [source] when edge.Target = id && edge.Ordinal = 0 -> Some source
            | _ -> None)
        |> List.distinct
        |> function [source] -> Some source | _ -> None
    let rec allocations seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.ContinuationAllocate _ } -> Some(Set.singleton id)
        | Some { Kind = SemanticKind.SeqExpr _ } ->
            match destinations.TryFind id with
            | Some formal -> allocations seen formal
            | None -> Some(Set.singleton id)
        | Some { Kind = SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _) } -> allocations seen value
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> allocations seen value
        | Some { Kind = SemanticKind.PatternBinding _ } ->
            actuals id |> Option.bind (List.map (allocations seen) >> unionAll)
        | Some { Kind = SemanticKind.FrameRead _ } -> originalValue id |> Option.bind (allocations seen)
        | _ -> None
    // Only source-published alias/input relations can establish that a copied
    // descriptor does not point into its own template. An unrecognized pointer
    // producer cannot gain that premise from a matching type or allocation size.
    let rec externalCapture owner seen id =
        if Set.contains id seen then false else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _) } -> externalCapture owner seen value
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> externalCapture owner seen value
        | Some { Kind = SemanticKind.FrameRead(frame, _) } ->
            match originalValue id with
            | Some source -> externalCapture owner seen source
            | None -> flows.TryFind frame |> Option.exists (fun flow -> flow.Unknown.IsEmpty && not (flow.Owners.Contains owner))
        | Some { Kind = SemanticKind.FrameBorrow(frame, _) } ->
            flows.TryFind frame |> Option.exists (fun flow -> flow.Unknown.IsEmpty && not (flow.Owners.Contains owner))
        | Some { Kind = SemanticKind.PatternBinding _ } ->
            actuals id |> Option.exists (List.forall (externalCapture owner seen))
        | Some { Kind = SemanticKind.Sequential values } ->
            List.tryLast values |> Option.exists (externalCapture owner seen)
        | Some { Kind = SemanticKind.EnvironmentRead(environment, slot) } ->
            Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.tryEnvironmentOwner graph environment
            |> Option.bind (Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.capturedInitializers graph)
            |> Option.bind (List.tryFind (fun (source, _, _) -> source = slot))
            |> Option.exists (fun (_, value, _) -> externalCapture owner seen value)
        | Some { Kind = SemanticKind.EnvironmentReference environment | SemanticKind.ClosureValue(_, environment) } ->
            externalCapture owner seen environment
        | Some { Kind = SemanticKind.SeqExpr _ | SemanticKind.ContinuationAllocate _ } -> id <> owner
        | Some { Kind = SemanticKind.Binding(_, true, _, _) | SemanticKind.EnvironmentCreate _ | SemanticKind.EnvironmentAllocate _ } -> true
        | Some node ->
            match applySubst node.Type with
            | NativeType.TSeq _ | NativeType.TSeqEnumerator _ ->
                flows.TryFind id |> Option.exists (fun flow -> flow.Unknown.IsEmpty && not flow.Owners.IsEmpty && not (flow.Owners.Contains owner))
            | NativeType.TNativePtr _ -> false
            | _ -> true
        | None -> false
    let templateFacts (family: SequenceFamily) owners =
        let validStorage owner allocation =
            let actualOwner =
                match graph.Nodes.TryFind allocation with
                | Some { Kind = SemanticKind.ContinuationAllocate actual } -> Some actual
                | Some { Kind = SemanticKind.SeqExpr _ } -> Some allocation
                | _ -> None
            actualOwner = Some owner &&
            (match regions.TryFind allocation, residences.TryFind allocation with
             | Some region, _ -> region.ChildOwner = owner && region.Bytes = family.Bytes && region.Alignment = family.Alignment
             | None, Some (EscapeKind.StackScoped | EscapeKind.StaticLifetime) -> true
             | _ -> false)
        let readings = owners |> Set.toList |> List.map (fun owner ->
            match allocations Set.empty owner, initializers.TryFind owner with
            | Some storage, Some values when not storage.IsEmpty &&
                (values |> List.map fst |> Set.ofList) = family.Members[owner].Captures &&
                values.Length = family.Members[owner].Captures.Count &&
                (values |> List.forall (fun (_, value) -> externalCapture owner Set.empty value)) &&
                (storage |> Set.forall (validStorage owner)) -> Some(owner, storage, values)
            | _ -> None)
        if readings |> List.exists Option.isNone then None
        else Some(readings |> List.choose id)
    let rec intrinsic seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Intrinsic info } -> Some info
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> intrinsic seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [source] } -> intrinsic seen source
        | _ -> None
    let acquisition id =
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Application(callee, [template]); Type = NativeType.TSeqEnumerator item } ->
            match intrinsic Set.empty callee, graph.Nodes.TryFind template with
            | Some { Module = IntrinsicModule.Seq; Operation = "getEnumerator" }, Some { Type = NativeType.TSeq input }
                when applySubst input = applySubst item -> Some template
            | _ -> None
        | _ -> None
    let rec sourceSite seen id =
        if Set.contains id seen then None else
        let predecessors =
            graph.Edges
            |> List.choose (fun edge ->
                match edge.Class, edge.Role, edge.Sources with
                | EdgeClass.Provenance, EdgeRole.ContinuationValue, [source] when edge.Target = id && edge.Ordinal = 0 -> Some source
                | _ -> None)
            |> List.distinct
        match predecessors with
        | [] -> if acquisition id |> Option.isSome then Some id else None
        | [source] when acquisition source |> Option.isSome -> sourceSite (Set.add id seen) source
        | _ -> None
    let mutable residuals = []
    let mutable edges = []
    let reject site reason = residuals <- { Site = site; Reason = reason } :: residuals; None
    let plans = graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        if not node.IsReachable then None else
        match acquisition id with
        | None -> None
        | Some template ->
            match flows.TryFind template, flows.TryFind id with
            | Some source, Some target when source.Occurrence = template && target.Occurrence = id &&
                                           not source.IsEnumerator && target.IsEnumerator && source.Unknown.IsEmpty &&
                                           target.Unknown.IsEmpty && not source.Owners.IsEmpty && source.Owners = target.Owners &&
                                           applySubst source.ElementType = applySubst target.ElementType ->
                let candidates = families.Values |> Seq.filter (fun family ->
                    family.Participants.Contains template && family.Participants.Contains id &&
                    (source.Owners |> Set.forall family.Members.ContainsKey)) |> Seq.toList
                match candidates, sourceSite Set.empty id with
                | [family], Some original ->
                    let storage =
                        match regions.TryFind id, residences.TryFind original with
                        | Some region, _ when source.Owners = Set.singleton region.ChildOwner &&
                                              family.Members.ContainsKey region.ChildOwner && region.Bytes = family.Bytes &&
                                              region.Alignment = family.Alignment -> Some(original, EscapeKind.StackScoped, Some region)
                        | None, Some ((EscapeKind.StackScoped | EscapeKind.StaticLifetime) as residence) -> Some(original, residence, None)
                        | _ -> None
                    match storage, templateFacts family source.Owners, graph.Platform with
                    | None, _, _ -> reject id "A fresh sequence family copy lacks its exact admitted allocation or owned-region residence."
                    | _, None, _ -> reject id "A sequence template lacks exhaustive backing storage, capture identity or absence of initialized interior views."
                    | _, _, None -> reject id "A sequence representation copy lacks its source memory-space declaration."
                    | Some(storageSite, residence, region), Some templates, Some platform ->
                        let disjoint = templates |> List.forall (fun (owner, allocations, _) ->
                            not (allocations.Contains storageSite) &&
                            (region |> Option.forall (fun destination ->
                                destination.ParentOwner <> owner &&
                                allocations |> Set.forall (fun allocation ->
                                    match regions.TryFind allocation with
                                    | Some source when source.ParentOwner = destination.ParentOwner ->
                                        int64 source.Offset + int64 source.Bytes <= int64 destination.Offset ||
                                        int64 destination.Offset + int64 destination.Bytes <= int64 source.Offset
                                    | _ -> allocation <> destination.ParentOwner))))
                        if not disjoint then reject id "Fresh enumeration storage may overlap its sequence template."
                        else
                        let selected = family.Members |> Map.filter (fun owner _ -> source.Owners.Contains owner)
                        let captures = selected |> Map.map (fun _ memberContract -> memberContract.Captures)
                        let uninitialized = selected |> Map.map (fun _ memberContract -> memberContract.Uninitialized)
                        let dependencies = selected |> Map.toList |> List.collect (fun (owner, memberContract) ->
                            [owner; memberContract.Generator; memberContract.Formal; memberContract.State]
                            @ (memberContract.Slots |> List.map _.Source) @ memberContract.Obligations)
                        let templateDependencies = templates |> List.collect (fun (_, storage, values) ->
                            Set.toList storage @ (values |> List.collect (fun (slot, value) -> [slot; value])))
                        let regionDependencies = region |> Option.map (fun region -> [region.ParentOwner; region.ParentFormal; region.ChildOwner]) |> Option.defaultValue []
                        edges <- {
                            Sources = List.distinct ([family.Identity; template; original; storageSite] @ dependencies @ templateDependencies @ regionDependencies)
                            Target = id; Class = EdgeClass.Suspension; Role = EdgeRole.SequenceTemplateCopy; Ordinal = 0 } :: edges
                        Some(id, { Family = family.Identity; Template = template; SourceAcquisition = original
                                   StorageSite = storageSite; Residence = residence; Region = region
                                   Bytes = family.Bytes; Alignment = family.Alignment; AddressSpace = PlatformContext.defaultMemorySpace platform
                                   TemplateStorage = templates |> List.map (fun (owner, storage, _) -> owner, storage) |> Map.ofList
                                   Initializers = templates |> List.map (fun (owner, _, values) -> owner, values) |> Map.ofList
                                   UninitializedRegions = selected |> Map.map (fun owner _ ->
                                       regions |> Map.toList |> List.choose (fun (site, region) -> if region.ParentOwner = owner then Some site else None))
                                   Captures = captures; Uninitialized = uninitialized })
                | _ -> reject id "Fresh sequence acquisition does not retain one exact settled family and source occurrence."
            | _ -> reject id "Fresh sequence acquisition has incomplete or mismatched template/iterator flow alternatives.") |> Map.ofList
    plans, { Enrichment.empty with NewEdges = List.rev edges }, List.rev residuals

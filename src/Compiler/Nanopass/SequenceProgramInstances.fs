// SPDX-License-Identifier: MIT
/// Program sequence templates keep their original generator and one actual
/// initialized allocation. Each acquisition still requires fresh storage and
/// the separate representation-copy contract; a template is never an iterator.
module Clef.Compiler.Nanopass.SequenceProgramInstances

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Authority = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority
module Program = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module Residence = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence
module Calls = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module Demand = Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

type ProgramInstance = {
    Owner: NodeId
    Generator: NodeId
    Allocation: NodeId
    Participants: Set<NodeId>
}

type Inputs = {
    Frames: Map<NodeId, ContinuationFrame>
    Families: Map<NodeId, SequenceFamily>
    Flows: Map<NodeId, SequenceFlow>
    Initializers: Map<NodeId, (NodeId * NodeId) list>
    Destinations: Map<NodeId, NodeId>
}

let private sameType (graph: SemanticGraph) left right =
    match graph.Nodes.TryFind left, graph.Nodes.TryFind right with
    | Some left, Some right -> applySubst left.Type = applySubst right.Type
    | _ -> false

let private referenceAgrees (graph: SemanticGraph) occurrence source =
    let rows = graph.Edges |> List.filter (fun edge -> edge.Target = occurrence && edge.Role = EdgeRole.Definition)
    match rows with
    | [] -> true
    | [row] -> row.Class = EdgeClass.Reference && row.Ordinal = 0 && row.Sources = [source]
    | _ -> false

let private finalPath (graph: SemanticGraph) =
    let rec read seen id =
        if Set.contains id seen then None else
        let follow source =
            if sameType graph id source then
                read (Set.add id seen) source |> Option.map (fun (last, path) -> last, id :: path)
            else None
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Sequential values; Children = children } when values = children ->
            List.tryLast values |> Option.bind follow
        | Some { Kind = SemanticKind.TypeAnnotation(source, declared); Children = [child]; Type = ty }
            when source = child && applySubst ty = applySubst declared -> follow source
        | Some { Kind = SemanticKind.EagerExpr _ } -> Demand.operand graph id |> Option.bind follow
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [source] } -> follow source
        | Some { Kind = SemanticKind.VarRef(_, Some source) } when referenceAgrees graph id source -> follow source
        | Some { IsReachable = true } -> Some(id, [id])
        | _ -> None
    read Set.empty

/// Re-derive the complete caller destination relation. Neither a stored map
/// nor the public seq type establishes which allocation a factory returned.
let private factoryCalls (graph: SemanticGraph) (inputs: Inputs) =
    let resolution = Calls.resolve graph
    resolution.Calls |> Map.toList |> List.choose (fun (call, resolved) ->
        match resolved.Complete, resolved.Targets with
        | true, [target] when target.Parameters.Length = target.Arguments.Length ->
            finalPath graph target.Body |> Option.bind (fun (owner, path) ->
                inputs.Destinations.TryFind owner |> Option.bind (fun formal ->
                    match List.zip target.Parameters target.Arguments |> List.filter (fun ((_, _, id), _) -> id = formal) with
                    | [((_, ty, _), actual)] when applySubst ty = applySubst graph.Nodes[owner].Type && sameType graph call owner ->
                        finalPath graph actual |> Option.bind (fun (allocation, actualPath) ->
                            match graph.Nodes.TryFind allocation with
                            | Some { Kind = SemanticKind.ContinuationAllocate source; IsReachable = true }
                                when source = owner && sameType graph formal actual && sameType graph owner allocation ->
                                Some(call, (owner, allocation, target.Lambda :: formal :: actual :: (path @ actualPath)))
                            | _ -> None)
                    | _ -> None))
        | _ -> None) |> Map.ofList

let private validFrame (graph: SemanticGraph) (inputs: Inputs) owner (family: SequenceFamily) =
    match inputs.Frames.TryFind owner, family.Members.TryFind owner, graph.Nodes.TryFind owner with
    | Some frame, Some memberContract, Some { Kind = SemanticKind.SeqExpr(generator, _); Type = NativeType.TSeq item; IsReachable = true }
        when frame.Owner = owner && frame.Generator = generator && generator = memberContract.Generator &&
             frame.Formal = memberContract.Formal && frame.State = memberContract.State &&
             frame.Bytes = family.Bytes && frame.Alignment = family.Alignment &&
             frame.Slots = memberContract.Slots && frame.Obligations = memberContract.Obligations &&
             applySubst item = applySubst family.ElementType ->
        let signature =
            match graph.Nodes.TryFind generator, graph.Nodes.TryFind frame.Formal with
            | Some { Kind = SemanticKind.Lambda([_, ty, formal], body, _, _, LambdaContext.SeqGenerator); Type = signature; IsReachable = true },
              Some { Kind = SemanticKind.PatternBinding _; Type = formalType; IsReachable = true }
                when formal = frame.Formal && applySubst ty = NativeType.TSeqEnumerator(applySubst item) &&
                     applySubst formalType = applySubst ty && applySubst signature = applySubst memberContract.Signature &&
                     applySubst signature = NativeType.TFun(applySubst ty, Types.boolType) ->
                graph.Nodes.TryFind body |> Option.exists (fun node -> applySubst node.Type = Types.boolType)
            | _ -> false
        let dependencies =
            List.distinct (List.ofSeq family.Members.Keys @ [generator; frame.Formal; frame.State] @
                           (frame.Slots |> List.map _.Source) @ frame.Obligations)
        let layoutRows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceFamilyLayout && edge.Target = owner)
        let rowAgrees =
            match layoutRows with
            | [row] -> row.Class = EdgeClass.Suspension && row.Ordinal = 0 && row.Sources = dependencies
            | _ -> false
        let fields (slots: ContinuationSlot list) =
            slots |> List.map (fun slot -> slot.Field.Offset, slot.Field.Size, slot.Field.Align)
        let proof id slots bytes alignment =
            let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = id)
            match graph.Nodes.TryFind id, rows with
            | Some { Kind = SemanticKind.Obligation info }, [row] when row.Class = EdgeClass.Obligation && row.Ordinal = 0 && row.Sources |> List.contains owner ->
                match info.Body with
                | ObligationBody.ContinuationLayout(actual, extent, align) ->
                    extent = bytes && align = alignment &&
                    (actual |> List.map (fun (offset, size, align) -> Some offset, Some size, Some align)) = fields slots &&
                    slots |> List.forall (fun slot -> row.Sources |> List.contains slot.Source)
                | _ -> false
            | _ -> false
        let proofs =
            match frame.Obligations with
            | [persistent; scratch] -> proof persistent frame.Slots frame.Bytes frame.Alignment &&
                                       proof scratch frame.ScratchSlots frame.ScratchBytes frame.ScratchAlignment
            | _ -> false
        let slots =
            frame.Slots @ frame.ScratchSlots |> List.forall (fun slot ->
                graph.Nodes.TryFind slot.Source |> Option.exists (fun source -> applySubst source.Type = applySubst slot.ValueType))
        let captures = frame.Slots |> List.filter _.IsCapture |> List.map _.Source |> Set.ofList
        let initializers = inputs.Initializers.TryFind owner
        let initialized = initializers |> Option.exists (fun actual ->
            actual = frame.Initializers && actual.Length = captures.Count &&
            (actual |> List.map fst |> Set.ofList) = captures &&
            (Environments.sequenceInitializers graph graph.Nodes[owner]
             |> Option.exists (fun declared -> declared |> List.filter (fst >> captures.Contains) = actual)) &&
            actual |> List.forall (fun (slot, value) -> graph.Nodes.ContainsKey slot && graph.Nodes.ContainsKey value))
        signature && rowAgrees && proofs && slots && initialized &&
        captures = memberContract.Captures &&
        (frame.Slots |> List.filter (fun slot -> not slot.IsCapture && slot.Source <> frame.State) |> List.map _.Source |> Set.ofList) = memberContract.Uninitialized
    | _ -> false

let private backing (graph: SemanticGraph) (inputs: Inputs) owner allocation =
    let families = inputs.Families.Values |> Seq.filter (fun family -> family.Members.ContainsKey owner) |> Seq.toList
    match families, Authority.authority graph allocation with
    | [family], Some(authority, participants) when family.Members |> Map.forall (fun owner _ -> validFrame graph inputs owner family) ->
        let powerOfTwo value = value > 0 && (value &&& (value - 1)) = 0
        let space = authority.Space
        let bytes, granularity = bigint family.Bytes, bigint space.Granularity
        if family.Bytes <= 0 || not (powerOfTwo family.Alignment && powerOfTwo space.Alignment && powerOfTwo space.Granularity) ||
           space.Alignment % family.Alignment <> 0 || bytes + ((granularity - bytes % granularity) % granularity) > bigint space.Capacity ||
           not (Platform.read graph).Findings.IsEmpty then None
        else
            let frame = inputs.Frames[owner]
            let dependencies =
                family.Members |> Map.toList |> List.collect (fun (memberOwner, memberContract) ->
                    memberOwner :: memberContract.Generator :: memberContract.Formal :: memberContract.State ::
                    ((memberContract.Slots |> List.map _.Source) @ memberContract.Obligations @
                     (inputs.Initializers[memberOwner] |> List.collect (fun (slot, value) -> [slot; value]))))
            Some { Class = EdgeClass.Provenance; Role = EdgeRole.SequenceProgramStorage; Target = allocation; Ordinal = 0
                   Sources = List.distinct ([allocation; owner; frame.Generator; frame.Formal; authority.Initializer.Binding; family.Identity] @
                                            dependencies @ (participants |> Set.toList)) }
    | _ -> None

/// Placement grants static residence only to the source allocation. Acquisition
/// storage remains independently owned, and copying creates no current value.
let prepare (graph: SemanticGraph) inputs (factoryMap: Map<NodeId, NodeId>) (residences: Map<NodeId, EscapeKind>) =
    let isTemplate site =
        match graph.Nodes.TryFind site with
        | Some { Kind = SemanticKind.SeqExpr _ | SemanticKind.ContinuationAllocate _ } -> true
        | _ -> false
    let hasCandidate = residences |> Map.exists (fun site _ -> isTemplate site && not (Authority.candidates graph site).IsEmpty)
    // Retraction is required even when the last program candidate disappears.
    let graph =
        if graph.Edges |> List.exists (fun edge -> edge.Role = EdgeRole.SequenceProgramStorage) then
            { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.SequenceProgramStorage) }
        else graph
    if not hasCandidate then graph, residences else
    let calls = factoryCalls graph inputs
    let completeFactories = calls |> Map.map (fun _ (_, allocation, _) -> allocation)
    let residence = Residence.analyzeWithRegions graph inputs.Destinations completeFactories
    let candidates = residences |> Map.toList |> List.choose (fun (site, _) ->
        let owner =
            match graph.Nodes.TryFind site with
            | Some { Kind = SemanticKind.SeqExpr _ } when not (inputs.Destinations.ContainsKey site) -> Some site
            | Some { Kind = SemanticKind.ContinuationAllocate owner } ->
                let actual = completeFactories |> Map.filter (fun _ allocation -> allocation = site)
                if actual.IsEmpty || actual |> Map.exists (fun call allocation -> factoryMap.TryFind call <> Some allocation) then None
                else Some owner
            | _ -> None
        owner |> Option.bind (fun owner ->
            if residence.Sites.ContainsKey site then backing graph inputs owner site |> Option.map (fun row -> site, row)
            else None))
    let edges = candidates |> List.map snd
    let graph = { graph with Edges = graph.Edges @ edges }
    graph, (candidates |> List.fold (fun sites (site, _) -> Map.add site EscapeKind.StaticLifetime sites) residences)

/// Explicit-input reader for program inventory settlement before final Codata
/// construction. It rereads residence and every exact destination participant.
let allocations (graph: SemanticGraph) inputs (residences: Map<NodeId, EscapeKind>) =
    let residences = residences |> Map.filter (fun site kind ->
        kind = EscapeKind.StaticLifetime &&
        match graph.Nodes.TryFind site with
        | Some { Kind = SemanticKind.SeqExpr _ | SemanticKind.ContinuationAllocate _ } -> true
        | _ -> false)
    if residences.IsEmpty then Map.empty else
    let calls = factoryCalls graph inputs
    let residence = Residence.analyzeWithRegions graph inputs.Destinations (calls |> Map.map (fun _ (_, allocation, _) -> allocation))
    residences |> Map.toList |> List.choose (fun (allocation, kind) ->
        if kind <> EscapeKind.StaticLifetime || not (residence.Sites.ContainsKey allocation) then None else
        let owner =
            match graph.Nodes.TryFind allocation with
            | Some { Kind = SemanticKind.SeqExpr _ } when not (inputs.Destinations.ContainsKey allocation) -> Some allocation
            | Some { Kind = SemanticKind.ContinuationAllocate owner } when calls |> Map.exists (fun _ (actualOwner, site, _) -> actualOwner = owner && site = allocation) -> Some owner
            | _ -> None
        owner |> Option.bind (fun owner -> backing graph inputs owner allocation |> Option.bind (fun expected ->
            let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceProgramStorage && edge.Target = allocation)
            match rows with
            | [row] when row.Class = expected.Class && row.Ordinal = expected.Ordinal && row.Sources = expected.Sources ->
                Some(allocation, { Owner = owner; Generator = inputs.Frames[owner].Generator; Allocation = allocation
                                   Participants = Set.ofList expected.Sources })
            | _ -> None))) |> Map.ofList

let private readings = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, Map<NodeId, ProgramInstance>>()

let programInstance (graph: SemanticGraph) binding =
    let read (graph: SemanticGraph) =
        let codata = graph.Codata.Value
        let inputs = { Frames = codata.ContinuationFrames; Families = codata.SequenceFamilies; Flows = codata.SequenceFlows
                       Initializers = codata.SequenceInitializers; Destinations = codata.SequenceDestinations }
        let calls = factoryCalls graph inputs
        let settled = allocations graph inputs codata.Escapes
        let rec actual seen id =
            if Set.contains id seen then None else
            let follow source =
                if sameType graph id source then actual (Set.add id seen) source |> Option.map (fun (owner, site, path) -> owner, site, id :: path)
                else None
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.SeqExpr _; IsReachable = true } when not (inputs.Destinations.ContainsKey id) -> Some(id, id, [id])
            | Some { Kind = SemanticKind.Application _; IsReachable = true } ->
                calls.TryFind id |> Option.map (fun (owner, site, path) -> owner, site, id :: path)
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [source]; IsReachable = true } -> follow source
            | Some { Kind = SemanticKind.VarRef(_, Some source); IsReachable = true } when referenceAgrees graph id source -> follow source
            | Some { Kind = SemanticKind.TypeAnnotation(source, ty); Type = actualType; Children = [child]; IsReachable = true }
                when source = child && applySubst ty = applySubst actualType -> follow source
            | Some { Kind = SemanticKind.EagerExpr _; IsReachable = true } -> Demand.operand graph id |> Option.bind follow
            | Some { Kind = SemanticKind.Sequential values; Children = children; IsReachable = true } when values = children -> List.tryLast values |> Option.bind follow
            | _ -> None
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind, Program.tryValueAuthority graph node.Id, inputs.Flows.TryFind node.Id with
            | SemanticKind.Binding(_, false, _, _), Some _, Some flow when flow.Unknown.IsEmpty && not flow.IsEnumerator ->
                actual Set.empty node.Id |> Option.bind (fun (owner, allocation, path) ->
                    if flow.Occurrence <> node.Id || flow.Owners <> Set.singleton owner then None
                    else settled.TryFind allocation |> Option.bind (fun instance ->
                        if instance.Owner <> owner then None
                        else Some(node.Id, { instance with Participants = Set.union (Set.ofList path) instance.Participants })))
            | _ -> None) |> Map.ofSeq
    readings.GetValue(graph, System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, Map<NodeId, ProgramInstance>>.CreateValueCallback(fun current -> read current)).TryFind binding

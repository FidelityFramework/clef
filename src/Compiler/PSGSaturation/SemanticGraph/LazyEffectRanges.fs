// SPDX-License-Identifier: MIT
/// Finite additive effects of actual explicit-lazy instances. Formation counts
/// are upper bounds, never a demand to execute an initializer. Code/schema
/// identity alone supplies no count and aliases create no new instances.
module Clef.Compiler.PSGSaturation.SemanticGraph.LazyEffectRanges

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Incidence = Clef.Compiler.Baker.Ingredients.Closures

type Contribution = { Store: NodeId; Value: NodeId; Formation: NodeId; Count: bigint; Delta: bigint }
type Bound = {
    Cell: NodeId
    Initializer: NodeId
    Initial: bigint
    Contributions: Contribution list
    Lower: bigint
    Upper: bigint
    Participants: Set<NodeId>
}

/// Only exact current syntax is read. Missing cached derived rows are legal;
/// contradictory/duplicate recorded rows, malformed children and changed full
/// types retract the proof instead of retaining earlier numeric annotations.
let recognize (graph: SemanticGraph) : Bound list =
    let settled = LazyValues.settle graph
    match ProgramInitialization.read graph with
    | None -> []
    | Some _ when settled.Instances.IsEmpty || not settled.Residuals.IsEmpty -> []
    | Some startup ->
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
    let uses = incidence |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
               |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
               |> List.groupBy fst |> List.map (fun (source, rows) -> source, rows |> List.map snd) |> Map.ofList
    let parents id = uses.TryFind id |> Option.defaultValue [] |> List.filter Hyperedge.isStructural
    let valid id =
        match nodes.TryFind id with
        | None -> false
        | Some node ->
            let expected = Incidence.structuralIncidence node
            let recorded = graph.Edges |> List.filter (fun edge ->
                edge.Target = id && (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference))
            let children = kindEdges id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
            let childAgreement =
                match node.Kind with
                | SemanticKind.Binding _ | SemanticKind.Intrinsic _ -> true
                | _ -> node.Children = children
            childAgreement && recorded.Length = (recorded |> List.distinctBy key |> List.length) &&
            (recorded |> List.forall (fun edge -> expected |> List.exists (fun candidate -> key candidate = key edge)))
    let same left right =
        valid left && valid right && applySubst nodes[left].Type = applySubst nodes[right].Type
    let resolution = CallableOrigins.resolve graph
    let complete site implementation =
        resolution.Calls.TryFind site |> Option.filter (fun call ->
            valid site && call.Complete && not call.Unknown && not call.Targets.IsEmpty &&
            call.Targets |> List.forall (fun target ->
                target.Lambda = implementation && valid target.Lambda && valid target.Body &&
                target.Parameters.Length = target.Arguments.Length &&
                List.zip target.Parameters target.Arguments |> List.forall (fun ((_, ty, formal), actual) ->
                    valid formal && valid actual && applySubst nodes[formal].Type = applySubst ty &&
                    applySubst nodes[actual].Type = applySubst ty)))
    let rawCapture source = nodes.Values |> Seq.exists (fun node ->
        let captures =
            match node.Kind with
            | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures)
            | SemanticKind.LazyExpr(_, captures) -> captures
            | _ -> []
        captures |> List.exists (fun capture -> capture.SourceNodeId = Some source))
    let closedCache = System.Collections.Generic.Dictionary<NodeId, (NodeId list * Set<NodeId>) option>()
    let closedCalls implementation =
        match closedCache.TryGetValue implementation with
        | true, result -> result
        | _ ->
            let rec follow seen source =
                if Set.contains source seen || not (valid source) || rawCapture source then None else
                let seen = Set.add source seen
                if graph.DeclarationRoots |> List.exists (fun (root, _) -> root = source) then None else
                let all = uses.TryFind source |> Option.defaultValue []
                all |> List.fold (fun accumulated edge ->
                    let next =
                        if not (valid edge.Target) then None else
                        match nodes[edge.Target].Kind, edge.Class, edge.Role with
                        | SemanticKind.ModuleDef(_, members), EdgeClass.Reference, EdgeRole.Member
                            when List.tryItem edge.Ordinal members = Some source -> Some([], Set.singleton edge.Target)
                        | SemanticKind.Binding(_, false, false, None), EdgeClass.Structural, _
                            when nodes[edge.Target].Children = [source] && same source edge.Target -> follow seen edge.Target
                        | SemanticKind.VarRef(_, Some actual), EdgeClass.Reference, EdgeRole.Definition
                            when actual = source && same source edge.Target -> follow seen edge.Target
                        | SemanticKind.TypeAnnotation(actual, declared), EdgeClass.Structural, _
                            when actual = source && same source edge.Target && applySubst declared = applySubst nodes[source].Type -> follow seen edge.Target
                        | SemanticKind.EagerExpr actual, EdgeClass.Structural, _
                            when actual = source && ExplicitDemand.operand graph edge.Target = Some source -> follow seen edge.Target
                        | SemanticKind.Application(callee, _), EdgeClass.Structural, EdgeRole.Callee when callee = source ->
                            complete edge.Target implementation |> Option.map (fun call ->
                                let participants = call.Targets |> List.collect (fun target ->
                                    target.Lambda :: target.Body :: (target.Arguments @ (target.Parameters |> List.map (fun (_, _, formal) -> formal))))
                                [edge.Target], Set.ofList (source :: edge.Target :: participants))
                        | _ -> None
                    match accumulated, next with
                    | Some(calls, participants), Some(more, required) -> Some(calls @ more, Set.union participants required)
                    | _ -> None) (Some([], Set.singleton source))
            let result = follow Set.empty implementation |> Option.bind (fun (calls, participants) ->
                if calls.IsEmpty then None else Some(List.distinct calls, participants))
            closedCache[implementation] <- result
            result
    let startupParticipants =
        graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.ProgramInitialization || edge.Role = EdgeRole.ProgramEntryCall || edge.Role = EdgeRole.ProgramInitializer)
        |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList
    let thunkOwners = settled.Instances.Values |> Seq.map (fun instance -> instance.Thunk, instance) |> Map.ofSeq
    let entryUncalled = resolution.Calls.Values |> Seq.forall (fun call -> call.Targets |> List.forall (fun target -> target.Lambda <> startup.EntryLambda))
    let thunkUsesClosed (instance: LazyValues.Instance) forceCalls =
        uses.TryFind instance.Thunk |> Option.defaultValue [] |> List.forall (fun edge ->
            if not (valid edge.Target) then false else
            match nodes[edge.Target].Kind, edge.Class, edge.Role with
            | SemanticKind.LazyValue(code, _), EdgeClass.Structural, EdgeRole.Body ->
                code = instance.Thunk && edge.Target = instance.Formation
            | SemanticKind.VarRef(_, Some code), EdgeClass.Reference, EdgeRole.Definition when code = instance.Thunk ->
                uses.TryFind edge.Target |> Option.defaultValue [] |> List.forall (fun callEdge ->
                    callEdge.Class = EdgeClass.Structural && callEdge.Role = EdgeRole.Callee &&
                    Set.contains callEdge.Target forceCalls && (complete callEdge.Target instance.Thunk).IsSome)
            | _ -> false)
    let rec count seen id =
        if Set.contains id seen || not (valid id) then None else
        let seen = Set.add id seen
        let sum inputs =
            inputs |> List.fold (fun total input ->
                match total, count seen input with
                | Some(bound, participants), Some(more, required) -> Some(bound + more, Set.union participants required)
                | _ -> None) (Some(0I, Set.singleton id))
        if id = startup.EntryLambda then
            if entryUncalled then Some(1I, startupParticipants) else None
        else
        match nodes[id].Kind with
        | SemanticKind.Lambda _ when thunkOwners.ContainsKey id ->
            let instance = thunkOwners[id]
            let forceCalls = settled.Forces.Values |> Seq.filter (fun force -> force.Formation = instance.Formation) |> Seq.map _.Invocation |> Set.ofSeq
            let directCalls = resolution.Calls |> Map.toList |> List.filter (fun (_, call) -> call.Targets |> List.exists (fun target -> target.Lambda = id))
            if not (thunkUsesClosed instance forceCalls) || directCalls |> List.exists (fun (site, _) -> not (forceCalls.Contains site) || (complete site id).IsNone) then None
            else count seen instance.Formation
        | SemanticKind.Lambda _ ->
            closedCalls id |> Option.bind (fun (calls, participants) ->
                sum calls |> Option.map (fun (bound, required) -> bound, Set.union participants required))
        | _ ->
            let incoming = parents id
            if incoming.IsEmpty || incoming |> List.exists (fun edge ->
                match nodes[edge.Target].Kind with
                | SemanticKind.WhileLoop _ | SemanticKind.ForLoop _ | SemanticKind.ForEach _ | SemanticKind.SeqExpr _ -> true
                | _ -> false) then None
            else sum (incoming |> List.map _.Target)
    let forceOperands = settled.Forces.Values |> Seq.map (fun force -> force.Operand, force.EnvironmentBinding) |> Seq.groupBy fst |> Map.ofSeq
    let rec closedValue seen id =
        if Set.contains id seen || not (valid id) || rawCapture id then None else
        let seen = Set.add id seen
        let next target = closedValue seen target
        uses.TryFind id |> Option.defaultValue []
        |> List.fold (fun result edge ->
            let proof =
                if not (valid edge.Target) then None else
                match nodes[edge.Target].Kind, edge.Class with
                | SemanticKind.ModuleDef _, EdgeClass.Reference -> Some(Set.singleton edge.Target)
                | SemanticKind.Binding(_, false, false, None), EdgeClass.Structural
                    when nodes[edge.Target].Children = [id] && same id edge.Target -> next edge.Target
                | SemanticKind.VarRef(_, Some source), EdgeClass.Reference when source = id && same id edge.Target -> next edge.Target
                | SemanticKind.TypeAnnotation(source, declared), EdgeClass.Structural
                    when source = id && same id edge.Target && applySubst declared = applySubst nodes[id].Type -> next edge.Target
                | SemanticKind.EagerExpr source, EdgeClass.Structural
                    when source = id && ExplicitDemand.operand graph edge.Target = Some id -> next edge.Target
                | SemanticKind.Sequential values, EdgeClass.Structural ->
                    if List.tryLast values = Some id then next edge.Target else Some(Set.singleton edge.Target)
                | SemanticKind.LazyEnvironmentReference source, EdgeClass.Structural when source = id && forceOperands.ContainsKey id ->
                    let validUse = forceOperands[id] |> Seq.exists (fun (_, binding) -> nodes[binding].Children = [edge.Target])
                    if validUse then Some(Set.singleton edge.Target) else None
                | SemanticKind.Lambda(_, body, _, _, _), EdgeClass.Structural when body = id ->
                    closedCalls edge.Target |> Option.bind (fun (calls, participants) ->
                        calls |> List.fold (fun result call ->
                            match result, next call with
                            | Some required, Some more -> Some(Set.union required more)
                            | _ -> None) (Some participants))
                | _ -> None
            match result, proof with
            | Some participants, Some required -> Some(Set.union participants required)
            | _ -> None) (Some(Set.singleton id))
    let rec literal seen expected id =
        if Set.contains id seen || not (valid id) || applySubst nodes[id].Type <> expected then None else
        let seen = Set.add id seen
        match nodes[id].Kind with
        | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> Some(bigint value, Set.singleton id)
        | SemanticKind.Literal(NativeLiteral.UInt(value, _)) -> Some(bigint value, Set.singleton id)
        | SemanticKind.VarRef(_, Some source) -> literal seen expected source |> Option.map (fun (value, path) -> value, Set.add id path)
        | SemanticKind.Binding(_, false, false, None) when nodes[id].Children.Length = 1 ->
            literal seen expected nodes[id].Children.Head |> Option.map (fun (value, path) -> value, Set.add id path)
        | SemanticKind.TypeAnnotation(source, declared) when applySubst declared = expected ->
            literal seen expected source |> Option.map (fun (value, path) -> value, Set.add id path)
        | SemanticKind.EagerExpr source when ExplicitDemand.operand graph id = Some source ->
            literal seen expected source |> Option.map (fun (value, path) -> value, Set.add id path)
        | _ -> None
    let readCell cell id =
        if not (same cell id) then false else
        match nodes[id].Kind with
        | SemanticKind.VarRef(_, Some source) -> source = cell
        | SemanticKind.LazyRead(_, slot) ->
            slot = cell && settled.CaptureUses.Values |> Seq.exists (List.contains id)
        | _ -> false
    let stores cell =
        nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Set(target, value) when readCell cell target -> Some(node.Id, target, value)
            | SemanticKind.LazyWrite(_, slot, value) when slot = cell && (settled.CaptureUses.Values |> Seq.exists (List.contains node.Id)) ->
                Some(node.Id, cell, value)
            | _ -> None) |> Seq.toList
    let ownerOfStore store =
        let rec ascend seen id =
            if Set.contains id seen || not (valid id) then None else
            let seen = Set.add id seen
            match nodes[id].Kind with
            | SemanticKind.Lambda _ -> thunkOwners.TryFind id
            | SemanticKind.WhileLoop _ | SemanticKind.ForLoop _ | SemanticKind.ForEach _ | SemanticKind.SeqExpr _ -> None
            | _ ->
                match parents id with
                | [edge] -> ascend seen edge.Target
                | _ -> None
        ascend Set.empty store
    nodes.Values |> Seq.choose (fun cell ->
        match cell.Kind, cell.Children with
        | SemanticKind.Binding(_, true, false, None), [initializer] when valid cell.Id && Types.isIntegerType cell.Type ->
            let sourceType = applySubst cell.Type
            let dangerous = nodes.Values |> Seq.exists (fun node ->
                match node.Kind with
                | SemanticKind.VarRef(_, Some source) when source = cell.Id -> not (same cell.Id node.Id)
                | SemanticKind.AddressOf(value, _) -> readCell cell.Id value
                | SemanticKind.EnvironmentBorrow(_, slot) | SemanticKind.EnvironmentWrite(_, slot, _)
                | SemanticKind.FrameBorrow(_, slot) | SemanticKind.FrameWrite(_, slot, _) | SemanticKind.LazyBorrow(_, slot) -> slot = cell.Id
                | SemanticKind.EnvironmentCreate(_, initializers) -> initializers |> List.exists (fun (slot, value) -> slot = cell.Id || value = cell.Id)
                | _ -> false)
            let invalidUse =
                uses.TryFind cell.Id |> Option.defaultValue [] |> List.exists (fun edge -> not (valid edge.Target))
                || (graph.Edges |> List.exists (fun edge ->
                    (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) &&
                    List.contains cell.Id edge.Sources && nodes.ContainsKey edge.Target && not (valid edge.Target)))
            let writes = stores cell.Id
            if dangerous || invalidUse || rawCapture cell.Id || writes.IsEmpty then None else
            match literal Set.empty sourceType initializer, count Set.empty cell.Id with
            | Some(seed, initialPath), Some(_, cellPath) ->
                let contributions = writes |> List.map (fun (store, target, value) ->
                    if not (valid store && valid value) || applySubst nodes[store].Type <> Types.unitType ||
                       applySubst nodes[value].Type <> sourceType || parents value |> List.map _.Target <> [store] then None else
                    match ownerOfStore store, nodes[value].Kind with
                    | Some instance, SemanticKind.Application(callee, [left; right]) when same cell.Id left && same cell.Id right ->
                        let operation =
                            match nodes.TryFind callee with
                            | Some { Kind = SemanticKind.Intrinsic info } when valid callee && info.Module = IntrinsicModule.Operators -> Some info.Operation
                            | _ -> None
                        let delta =
                            match operation with
                            | Some "op_Addition" when readCell cell.Id left -> literal Set.empty sourceType right
                            | Some "op_Addition" when readCell cell.Id right -> literal Set.empty sourceType left
                            | Some "op_Subtraction" when readCell cell.Id left -> literal Set.empty sourceType right |> Option.map (fun (value, path) -> -value, path)
                            | _ -> None
                        match delta, count Set.empty store, closedValue Set.empty instance.Formation with
                        | Some(delta, deltaPath), Some(maximum, countPath), Some(valuePath) ->
                            let sourceRows = graph.Edges |> List.filter (fun edge ->
                                edge.Role = EdgeRole.LazyInstance && edge.Target = instance.Formation ||
                                edge.Role = EdgeRole.LazyMemoization && List.tryHead edge.Sources = Some instance.Formation ||
                                (match edge.Role with EdgeRole.LazyCapture _ -> edge.Target = instance.Environment | _ -> false))
                            let participants = sourceRows |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList
                            let participants = [participants; deltaPath; countPath; valuePath; Set.ofList [store; target; value; callee; left; right]] |> Set.unionMany
                            Some({ Store = store; Value = value; Formation = instance.Formation; Count = maximum; Delta = delta }, participants)
                        | _ -> None
                    | _ -> None)
                if contributions |> List.exists Option.isNone then None else
                let rows = contributions |> List.choose id
                let changes = rows |> List.map (fun (item, _) -> item.Count * item.Delta)
                Some { Cell = cell.Id; Initializer = initializer; Initial = seed; Contributions = List.map fst rows
                       Lower = seed + (changes |> List.sumBy (min 0I)); Upper = seed + (changes |> List.sumBy (max 0I))
                       Participants = Set.unionMany (initialPath :: cellPath :: (rows |> List.map snd)) }
            | _ -> None
        | _ -> None) |> Seq.toList

/// Retain exact joint proof participants and reuse unchanged obligation nodes.
/// Removed or changed premises retract the old range relation and obligation.
let settle (bounds: Bound list) (graph: SemanticGraph) =
    let old = graph.Nodes |> Map.filter (fun _ node ->
        match node.Kind with SemanticKind.Obligation { Body = ObligationBody.FiniteAdditiveEffects _ } -> true | _ -> false)
    let oldIds = old.Keys |> Set.ofSeq
    let oldNames = old.Values |> Seq.choose (fun node ->
        match node.Kind with SemanticKind.Obligation info -> Some info.Id | _ -> None) |> Set.ofSeq
    let retained = graph.Edges |> List.filter (fun edge ->
        edge.Role <> EdgeRole.LazyEffectRange && not (oldIds.Contains edge.Target) && not (edge.Sources |> List.exists oldIds.Contains))
    let mutable nodes = graph.Nodes |> Map.filter (fun id _ -> not (oldIds.Contains id)) |> Map.map (fun _ node ->
        match node.Metadata.TryFind ObligationMetadata.Anchors with
        | Some(MetadataValue.StringList names) ->
            { node with Metadata = node.Metadata.Add(ObligationMetadata.Anchors, MetadataValue.StringList(names |> List.filter (oldNames.Contains >> not))) }
        | _ -> node)
    let mutable edges = retained
    for bound in bounds do
        let sources = bound.Participants |> Set.toList
        let name = sprintf "lazy_effect_%d" (NodeId.value bound.Cell)
        let body = ObligationBody.FiniteAdditiveEffects(bound.Initial, bound.Contributions |> List.map (fun item -> item.Count, item.Delta), bound.Lower, bound.Upper)
        let existing = old.Values |> Seq.tryFind (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Id = name && info.Body = body ->
                let rows = graph.Edges |> List.filter (fun edge -> edge.Target = node.Id && edge.Role = EdgeRole.Constrains)
                match rows with [edge] -> edge.Class = EdgeClass.Obligation && edge.Sources = sources | _ -> false
            | _ -> false)
        let obligation = existing |> Option.defaultWith (fun () ->
            Clef.Compiler.Baker.Ingredients.Obligations.obligationNode nodes[bound.Cell] 0
                { Id = name; Kind = "finite-lazy-additive-effects"; Logic = "QF_LIA"
                  Statement = "Every prefix and store is enclosed by complete finite instance activations and exact signed source increments."
                  Source = Clef.Compiler.Baker.Ingredients.Obligations.fmtRange nodes[bound.Cell].Range
                  Refs = []; Body = body })
        nodes <- nodes.Add(obligation.Id, obligation)
        edges <- Clef.Compiler.Baker.Ingredients.Obligations.constrains sources obligation :: edges
        for target in bound.Cell :: (bound.Contributions |> List.map _.Value) do
            edges <- { Class = EdgeClass.Range; Role = EdgeRole.LazyEffectRange; Sources = sources; Target = target; Ordinal = 0 } :: edges
            let node = nodes[target]
            let anchors = match node.Metadata.TryFind ObligationMetadata.Anchors with Some(MetadataValue.StringList names) -> names | _ -> []
            nodes <- nodes.Add(target, { node with Metadata = node.Metadata.Add(ObligationMetadata.Anchors, MetadataValue.StringList(name :: anchors)) })
    { graph with Nodes = nodes; Edges = edges }

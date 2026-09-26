// SPDX-License-Identifier: MIT
/// Finite ordinary activations bound affine updates to program-owned cells.
/// Counts are conservative upper bounds, not demands to execute an expression.
/// Unknown calls, escaping storage and repeated activations without a proof
/// remain unresolved. This owner selects no runtime width or memory capacity.
module Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Incidence = Clef.Compiler.Baker.Ingredients.Closures
module Certificates = Clef.Compiler.Baker.Recipes.LoopRangeRecipes

type Write = { Store: NodeId; Value: NodeId; MaximumActivations: bigint; Scale: bigint; Offset: bigint }
type Bound = {
    Cell: NodeId
    Writes: Write list
    Certificate: FiniteLinearRecurrenceModel
    Participants: Set<NodeId>
}

let range bound =
    let magnitude = bound.Certificate.Upper.Head
    ValueRange.Bounded(-magnitude, magnitude)

/// Fresh source validation deliberately ignores previously inferred ranges.
/// A formal's coefficient comes from every exact closed actual, not its cached
/// numeric annotation, and every possible cell write contributes to the count.
let recognize (graph: SemanticGraph) : Bound list =
    match ProgramInitialization.read graph with
    | None -> []
    | Some startup ->
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
    let uses = incidence |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
               |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
               |> List.groupBy fst |> List.map (fun (id, rows) -> id, List.map snd rows) |> Map.ofList
    let recorded = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
                   |> List.groupBy _.Target |> Map.ofList
    let validCache = System.Collections.Generic.Dictionary<NodeId, bool>()
    let valid id =
        match validCache.TryGetValue id with
        | true, result -> result
        | _ ->
            let result =
                match nodes.TryFind id with
                | None -> false
                | Some node ->
                    let expected = Incidence.structuralIncidence node
                    let actual = recorded.TryFind id |> Option.defaultValue []
                    let children = kindEdges id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                    let childAgreement =
                        match node.Kind with
                        | SemanticKind.Binding _ | SemanticKind.Intrinsic _ -> true
                        | _ -> node.Children = children
                    childAgreement && actual.Length = (actual |> List.distinctBy key |> List.length) &&
                    actual |> List.forall (fun row -> expected |> List.exists (fun candidate -> key candidate = key row))
            validCache[id] <- result
            result
    let same left right = valid left && valid right && applySubst nodes[left].Type = applySubst nodes[right].Type
    let parents id = uses.TryFind id |> Option.defaultValue [] |> List.filter Hyperedge.isStructural
    let captures = nodes.Values |> Seq.collect (fun node ->
        match node.Kind with
        | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures)
        | SemanticKind.LazyExpr(_, captures) -> captures |> Seq.choose _.SourceNodeId
        | SemanticKind.EnvironmentCreate(_, initializers) -> initializers |> Seq.collect (fun (slot, value) -> [slot; value])
        | SemanticKind.EnvironmentRead(_, slot) | SemanticKind.EnvironmentBorrow(_, slot)
        | SemanticKind.EnvironmentWrite(_, slot, _) | SemanticKind.FrameRead(_, slot)
        | SemanticKind.FrameBorrow(_, slot) | SemanticKind.FrameWrite(_, slot, _)
        | SemanticKind.LazyRead(_, slot) | SemanticKind.LazyBorrow(_, slot)
        | SemanticKind.LazyWrite(_, slot, _) -> Seq.singleton slot
        | _ -> Seq.empty) |> Set.ofSeq
    let calls = CallableOrigins.resolve graph
    let complete site implementation =
        calls.Calls.TryFind site |> Option.filter (fun call ->
            valid site && call.Complete && not call.Unknown && not call.Targets.IsEmpty &&
            call.Targets |> List.forall (fun target ->
                target.Lambda = implementation && valid target.Lambda && valid target.Body &&
                target.Parameters.Length = target.Arguments.Length &&
                List.zip target.Parameters target.Arguments |> List.forall (fun ((_, ty, formal), actual) ->
                    same formal actual && applySubst nodes[formal].Type = applySubst ty)))
    let closedCache = System.Collections.Generic.Dictionary<NodeId, (NodeId list * Set<NodeId>) option>()
    let closedCalls implementation =
        match closedCache.TryGetValue implementation with
        | true, result -> result
        | _ ->
            let rec follow seen source =
                if Set.contains source seen || not (valid source) || captures.Contains source ||
                   (graph.DeclarationRoots |> List.exists (fun (root, _) -> root = source)) then None else
                let seen = Set.add source seen
                uses.TryFind source |> Option.defaultValue [] |> List.fold (fun accumulated edge ->
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
                                    target.Lambda :: target.Body :: target.Arguments @ (target.Parameters |> List.map (fun (_, _, id) -> id)))
                                [edge.Target], Set.ofList (source :: edge.Target :: participants))
                        | _ -> None
                    match accumulated, next with
                    | Some(sites, dependencies), Some(more, required) -> Some(sites @ more, Set.union dependencies required)
                    | _ -> None) (Some([], Set.singleton source))
            let result = follow Set.empty implementation |> Option.bind (fun (sites, dependencies) ->
                if sites.IsEmpty then None else Some(List.distinct sites, dependencies))
            closedCache[implementation] <- result
            result
    let startupParticipants = graph.Edges |> List.filter (fun edge ->
        edge.Role = EdgeRole.ProgramInitialization || edge.Role = EdgeRole.ProgramEntryCall || edge.Role = EdgeRole.ProgramInitializer)
                              |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList
    let entryUncalled =
        let lambdaUses = uses.TryFind startup.EntryLambda |> Option.defaultValue []
        let bindingUses = uses.TryFind startup.EntryBinding |> Option.defaultValue []
        not (captures.Contains startup.EntryLambda || captures.Contains startup.EntryBinding) &&
        (lambdaUses |> List.forall (fun edge ->
            edge.Class = EdgeClass.Structural && edge.Target = startup.EntryBinding && valid edge.Target &&
            nodes[edge.Target].Children = [startup.EntryLambda])) &&
        (bindingUses |> List.forall (fun edge ->
            match nodes.TryFind edge.Target with
            | Some { Kind = SemanticKind.ModuleDef(_, members) } ->
                valid edge.Target && edge.Class = EdgeClass.Reference && edge.Role = EdgeRole.Member &&
                List.tryItem edge.Ordinal members = Some startup.EntryBinding
            | _ -> false)) &&
        (calls.Calls.Values |> Seq.forall (fun call -> call.Targets |> List.forall (fun target -> target.Lambda <> startup.EntryLambda)))
    let rec count seen id =
        if Set.contains id seen || not (valid id) then None else
        let seen = Set.add id seen
        let sum inputs =
            inputs |> List.fold (fun total input ->
                match total, count seen input with
                | Some(bound, dependencies), Some(more, required) -> Some(bound + more, Set.union dependencies required)
                | _ -> None) (Some(0I, Set.singleton id))
        if id = startup.EntryLambda then
            if entryUncalled then Some(1I, startupParticipants) else None
        else
            match nodes[id].Kind with
            | SemanticKind.Lambda(_, _, _, _, LambdaContext.RegularClosure) ->
                closedCalls id |> Option.bind (fun (sites, dependencies) ->
                    sum sites |> Option.map (fun (bound, required) -> bound, Set.union dependencies required))
            | SemanticKind.Lambda _ | SemanticKind.WhileLoop _ | SemanticKind.ForLoop _
            | SemanticKind.ForEach _ | SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ -> None
            | _ ->
                let incoming = parents id
                if incoming.IsEmpty then None else sum (incoming |> List.map _.Target)
    let formalOwners =
        nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.Lambda(parameters, _, _, _, _) -> parameters |> Seq.map (fun (_, _, id) -> id, node.Id)
            | _ -> Seq.empty)
        |> Seq.groupBy fst
        |> Seq.choose (fun (formal, owners) ->
            match owners |> Seq.map snd |> Seq.distinct |> Seq.toList with
            | [owner] -> Some(formal, owner)
            | _ -> None)
        |> Map.ofSeq
    let rec constant seen expected id =
        if Set.contains id seen || not (valid id) || applySubst nodes[id].Type <> expected then None else
        let seen = Set.add id seen
        let wrap = Option.map (fun (magnitude, required) -> magnitude, Set.add id required)
        match nodes[id].Kind with
        | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> Some(abs (bigint value), Set.singleton id)
        | SemanticKind.Literal(NativeLiteral.UInt(value, _)) -> Some(bigint value, Set.singleton id)
        | SemanticKind.VarRef(_, Some source) -> constant seen expected source |> wrap
        | SemanticKind.Binding(_, false, false, None) when nodes[id].Children.Length = 1 -> constant seen expected nodes[id].Children.Head |> wrap
        | SemanticKind.TypeAnnotation(source, declared) when applySubst declared = expected -> constant seen expected source |> wrap
        | SemanticKind.EagerExpr source when ExplicitDemand.operand graph id = Some source -> constant seen expected source |> wrap
        | SemanticKind.PatternBinding _ ->
            formalOwners.TryFind id |> Option.bind (fun owner ->
                closedCalls owner |> Option.bind (fun (sites, dependencies) ->
                    sites |> List.fold (fun result site ->
                        let actual = complete site owner |> Option.bind (fun call ->
                            match call.Targets with
                            | [target] -> List.zip target.Parameters target.Arguments |> List.tryPick (fun ((_, _, formal), actual) -> if formal = id then Some actual else None)
                            | _ -> None)
                        match result, actual |> Option.bind (constant seen expected) with
                        | Some(bound, required), Some(value, more) -> Some(max bound value, Set.union required more)
                        | _ -> None) (Some(0I, Set.add id dependencies))))
        | _ -> None
    let operator id =
        if not (valid id) then None else
        match nodes[id].Kind with
        | SemanticKind.Application(callee, [left; right]) when valid callee && valid left && valid right ->
            let rec supplied args ty =
                match args, applySubst ty with
                | [], result -> result = applySubst nodes[id].Type
                | actual :: rest, NativeType.TFun(parameter, result) ->
                    applySubst parameter = applySubst nodes[actual].Type && supplied rest result
                | _ -> false
            match nodes[callee].Kind with
            | SemanticKind.Intrinsic info when info.Module = IntrinsicModule.Operators && supplied [left; right] nodes[callee].Type ->
                Some(info.Operation, callee, left, right)
            | _ -> None
        | _ -> None
    let readCell cell id = same cell id && (match nodes[id].Kind with SemanticKind.VarRef(_, Some source) -> source = cell | _ -> false)
    let rec affine cell seen id =
        if Set.contains id seen || not (same cell id) then None else
        let seen = Set.add id seen
        let ty = applySubst nodes[cell].Type
        if readCell cell id then Some(1I, 0I, Set.ofList [cell; id]) else
        match constant Set.empty ty id with
        | Some(value, dependencies) -> Some(0I, value, dependencies)
        | None ->
            match operator id with
            | Some(("op_Addition" | "op_Subtraction"), callee, left, right) ->
                match affine cell seen left, affine cell seen right with
                | Some(a, b, p), Some(c, d, q) -> Some(a + c, b + d, Set.unionMany [p; q; Set.ofList [id; callee]])
                | _ -> None
            | Some("op_Multiply", callee, left, right) ->
                let multiply value factor =
                    match applySubst nodes[factor].Type with
                    | NativeType.TNum(_, dimension) when dimension = Dimension.one &&
                        Types.tryGetNTUKind nodes[factor].Type = Types.tryGetNTUKind ty ->
                        match affine cell seen value, constant Set.empty (applySubst nodes[factor].Type) factor with
                        | Some(a, b, p), Some(coefficient, q) -> Some(a * coefficient, b * coefficient, Set.unionMany [p; q; Set.ofList [id; callee]])
                        | _ -> None
                    | _ -> None
                multiply left right |> Option.orElseWith (fun () -> multiply right left)
            | _ -> None
    startup.ValueBindings |> Set.toList |> List.choose (fun cell ->
        match nodes.TryFind cell with
        | Some node when valid cell && Types.isIntegerType node.Type && not (captures.Contains cell) ->
            match node.Kind, node.Children with
            | SemanticKind.Binding(_, true, false, None), [initializer] ->
                let dangerous = nodes.Values |> Seq.exists (fun useNode ->
                    match useNode.Kind with
                    | SemanticKind.VarRef(_, Some source) when source = cell -> not (same cell useNode.Id)
                    | SemanticKind.AddressOf(value, _) -> readCell cell value
                    | _ -> false)
                let invalidUses =
                    uses.TryFind cell |> Option.defaultValue [] |> List.exists (fun edge -> not (valid edge.Target)) ||
                    (graph.Edges |> List.exists (fun edge ->
                        (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) &&
                        List.contains cell edge.Sources && nodes.ContainsKey edge.Target && not (valid edge.Target)))
                let writes = nodes.Values |> Seq.choose (fun store ->
                    match store.Kind with
                    | SemanticKind.Set(target, value) when readCell cell target -> Some(store.Id, target, value)
                    | _ -> None) |> Seq.toList
                if dangerous || invalidUses || writes.IsEmpty then None else
                match constant Set.empty (applySubst node.Type) initializer with
                | None -> None
                | Some(seed, initialDependencies) ->
                    let contributions = writes |> List.map (fun (store, target, value) ->
                        if not (valid store) || applySubst nodes[store].Type <> Types.unitType then None else
                        match affine cell Set.empty value, count Set.empty store with
                        | Some(scale, offset, required), Some(activations, execution) ->
                            Some({ Store = store; Value = value; MaximumActivations = activations; Scale = scale; Offset = offset },
                                 Set.unionMany [required; execution; Set.ofList [store; target; value]])
                        | _ -> None)
                    if contributions |> List.exists Option.isNone then None else
                    let contributions = contributions |> List.choose id
                    let writes = List.map fst contributions
                    let count = writes |> List.sumBy _.MaximumActivations
                    let scale = max 1I (writes |> List.map _.Scale |> List.max)
                    let offset = writes |> List.map _.Offset |> List.max
                    let matrix = [[scale; offset]; [0I; 1I]]
                    match Certificates.certifyLinearWithBudget Certificates.defaultCertificateBits count [seed; 1I] [seed; 1I] matrix matrix with
                    | Error _ -> None
                    | Ok(certificate, _) ->
                        Some { Cell = cell; Writes = writes; Certificate = certificate
                               Participants = Set.unionMany (startupParticipants :: initialDependencies :: (contributions |> List.map snd)) }
            | _ -> None
        | _ -> None)

/// A resident arithmetic certificate remains tied to its source transition,
/// complete call ingress, startup authority, every writer and activation path.
let settle (bounds: Bound list) (graph: SemanticGraph) =
    let owned (node: SemanticNode) =
        match node.Kind with SemanticKind.Obligation info -> info.Kind = "finite-cell-effects" | _ -> false
    let old = graph.Nodes |> Map.filter (fun _ node -> owned node)
    let oldIds = old.Keys |> Set.ofSeq
    let oldNames = old.Values |> Seq.choose (fun node -> match node.Kind with SemanticKind.Obligation info -> Some info.Id | _ -> None) |> Set.ofSeq
    let mutable nodes = graph.Nodes |> Map.filter (fun id _ -> not (oldIds.Contains id)) |> Map.map (fun _ node ->
        match node.Metadata.TryFind ObligationMetadata.Anchors with
        | Some(MetadataValue.StringList names) -> { node with Metadata = node.Metadata.Add(ObligationMetadata.Anchors, MetadataValue.StringList(names |> List.filter (oldNames.Contains >> not))) }
        | _ -> node)
    let mutable edges = graph.Edges |> List.filter (fun edge ->
        edge.Role <> EdgeRole.FiniteCellRange && not (oldIds.Contains edge.Target) && not (edge.Sources |> List.exists oldIds.Contains))
    for bound in bounds do
        let sources = Set.toList bound.Participants
        let name = sprintf "finite_cell_%d" (NodeId.value bound.Cell)
        let body = ObligationBody.FiniteLinearRecurrence bound.Certificate
        let existing = old.Values |> Seq.tryFind (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Id = name && info.Body = body ->
                match graph.Edges |> List.filter (fun edge -> edge.Target = node.Id && edge.Role = EdgeRole.Constrains) with
                | [edge] -> edge.Class = EdgeClass.Obligation && edge.Sources = sources
                | _ -> false
            | _ -> false)
        let obligation = existing |> Option.defaultWith (fun () ->
            Clef.Compiler.Baker.Ingredients.Obligations.obligationNode nodes[bound.Cell] 0
                { Id = name; Kind = "finite-cell-effects"; Logic = "QF_LIA"
                  Statement = "Absolute cell magnitude at every store is enclosed by a finite monotone affine trajectory; exact source transitions and complete activation bounds are joint premises."
                  Source = Clef.Compiler.Baker.Ingredients.Obligations.fmtRange nodes[bound.Cell].Range; Refs = []; Body = body })
        nodes <- nodes.Add(obligation.Id, obligation)
        edges <- Clef.Compiler.Baker.Ingredients.Obligations.constrains sources obligation :: edges
        for target in bound.Cell :: (bound.Writes |> List.map _.Value) do
            edges <- { Class = EdgeClass.Range; Role = EdgeRole.FiniteCellRange; Sources = sources; Target = target; Ordinal = 0 } :: edges
    { graph with Nodes = nodes; Edges = edges }

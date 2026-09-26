// SPDX-License-Identifier: MIT
/// Read the actual lazy formation and memoization algorithm minted by Baker.
/// These facts neither choose a layout nor establish allocation residence,
/// concurrency ownership, successful termination, or ordinary binding demand.
module Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Closures

module Contracts = Clef.Compiler.PSGSaturation.SemanticGraph.LazyContracts
let environmentType = Contracts.environmentType
type Instance = Contracts.Instance
let instance = Contracts.instance
let instances = Contracts.instances

/// Capture access belongs to an invocation's exact environment formal. A
/// formation/allocation with the same schema is not an interchangeable value.
/// Only immutable, type-preserving references are transparent here.
let captureEnvironment (graph: SemanticGraph) (contract: Instance) environment =
    let rec trace seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        let follow source = trace seen source |> Option.map (fun path -> id :: path)
        match graph.Nodes.TryFind id with
        | Some node when node.IsReachable && applySubst node.Type = environmentType ->
            if id = contract.Formal then
                match node.Kind with SemanticKind.PatternBinding _ -> Some [id] | _ -> None
            else
                match node.Kind with
                | SemanticKind.VarRef(_, Some source) -> follow source
                | SemanticKind.TypeAnnotation(source, declared) when applySubst declared = environmentType -> follow source
                | SemanticKind.EagerExpr source when ExplicitDemand.operand graph id = Some source -> follow source
                | SemanticKind.Binding(_, false, _, _) when node.Children.Length = 1 -> follow node.Children.Head
                | _ -> None
        | _ -> None
    trace Set.empty environment

/// Read every structural occurrence, stopping at each actual lambda boundary.
/// A node shared with another function, detached from its body, or reachable
/// through a structural cycle has no single admitted capture-access scope.
let private captureScopes (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let parents =
        nodes.Values |> Seq.collect structuralIncidence |> Seq.filter Hyperedge.isStructural
        |> Seq.collect (fun edge -> edge.Sources |> Seq.map (fun source -> source, edge.Target))
        |> Seq.groupBy fst |> Seq.map (fun (source, rows) -> source, rows |> Seq.map snd |> Seq.distinct |> Seq.toList)
        |> Map.ofSeq
    let cache = System.Collections.Generic.Dictionary<NodeId, (Set<NodeId> * Set<NodeId>) option>()
    let rec ascend seen id =
        if Set.contains id seen then None else
        match cache.TryGetValue id with
        | true, result -> result
        | _ ->
            let seen = Set.add id seen
            let result =
                match nodes.TryFind id with
                | Some { Kind = SemanticKind.Lambda _ } -> Some(Set.singleton id, Set.singleton id)
                | Some _ ->
                    match parents.TryFind id with
                    | Some enclosing when not enclosing.IsEmpty ->
                        enclosing |> List.fold (fun result parent ->
                            match result, ascend seen parent with
                            | Some(owners, participants), Some(actual, path) -> Some(Set.union owners actual, Set.union participants path)
                            | _ -> None) (Some(Set.empty, Set.singleton id))
                    | _ -> None
                | _ -> None
            cache[id] <- result
            result
    fun (contract: Instance) occurrences ->
        occurrences |> List.fold (fun result occurrence ->
            match result, ascend Set.empty occurrence with
            | Some participants, Some(owners, path) when owners = Set.singleton contract.Thunk -> Some(Set.union participants path)
            | _ -> None) (Some Set.empty)
        |> Option.map Set.toList

type Plan = { Source: SemanticNode; Thunk: SemanticNode; Body: NodeId; Captures: CaptureInfo list }

/// Preserve an original captured source reference without treating the
/// generated computed/cache reads as source occurrences. This projects source
/// identity only; it grants neither force demand nor cache-read permission.
let tryCapturedSourceReference (graph: SemanticGraph) =
    let formations = instances graph
    let scope = captureScopes graph
    let origins = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.CaptureReferenceOrigin)
                  |> List.groupBy _.Target |> Map.ofList
    fun occurrence ->
        match graph.Nodes.TryFind occurrence, origins.TryFind occurrence with
        | Some ({ Kind = SemanticKind.LazyRead(environment, slot); Children = [actual]; IsReachable = true } as value),
          Some [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [owner; declaration] }]
            when actual = environment && slot = declaration ->
            match formations.TryFind owner, graph.Nodes.TryFind declaration with
            | Some contract, Some ({ Kind = SemanticKind.Binding _ | SemanticKind.PatternBinding _ } as source)
                when applySubst value.Type = applySubst source.Type &&
                     (contract.Captured |> List.exists (fun (captured, _, _) -> captured = declaration)) &&
                     (captureEnvironment graph contract environment |> Option.isSome) &&
                     (scope contract [occurrence; environment] |> Option.isSome) -> Some declaration
            | _ -> None
        | _ -> None

type Force = {
    Site: NodeId
    Operand: NodeId
    Formation: NodeId
    EnvironmentBinding: NodeId
    Condition: NodeId
    CachedRead: NodeId
    Invocation: NodeId
    ResultBinding: NodeId
    ResultStore: NodeId
    Publication: NodeId
    UncachedBranch: NodeId
    Conditional: NodeId
}

let private live (graph: SemanticGraph) id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
let private single = function [value] -> Some value | _ -> None
let private rows role (graph: SemanticGraph) target =
    graph.Edges |> List.filter (fun edge -> edge.Role = role && edge.Target = target)

/// A missing/changed capture identity is never silently omitted. The first
/// formation recipe consumes existing typed captures without forcing them.
let plans (graph: SemanticGraph) =
    graph.Nodes.Values |> Seq.choose (fun node ->
        match node.Kind, applySubst node.Type with
        | SemanticKind.LazyExpr(thunk, captures), NativeType.TLazy element when node.IsReachable ->
            match live graph thunk with
            | Some ({ Kind = SemanticKind.Lambda(_, body, actualCaptures, _, LambdaContext.LazyThunk) } as code)
                when captures = actualCaptures && (live graph body |> Option.exists (fun result -> applySubst result.Type = element)) ->
                let valid capture =
                    capture.SourceNodeId |> Option.bind (live graph) |> Option.exists (fun source ->
                        applySubst source.Type = applySubst capture.Type &&
                        (capture.IsMutable = (match source.Kind with SemanticKind.Binding(_, true, _, _) -> true | _ -> false)))
                if List.forall valid captures && (captures |> List.choose _.SourceNodeId |> Set.ofList).Count = captures.Length then
                    Some { Source = node; Thunk = code; Body = body; Captures = captures }
                else None
            | _ -> None
        | _ -> None) |> Seq.toList

/// This is only an exact formation/layout origin. Calls and formals retain
/// their own runtime environment operands; same code is not instance equality.
let tryOwner (graph: SemanticGraph) =
    let formations = instances graph
    let calls = lazy (CallableOrigins.resolve graph)
    let resultFormals =
        graph.Edges
        |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources with
            | EdgeClass.Provenance, EdgeRole.LazyResultDestination, [factory; owner; formal] ->
                match formations.TryFind owner, live graph factory, live graph formal with
                | Some contract, Some { Kind = SemanticKind.Lambda(parameters, _, _, _, _) },
                  Some { Kind = SemanticKind.PatternBinding _; Type = ty }
                    when edge.Target = contract.Environment && applySubst ty = environmentType &&
                         (parameters |> List.exists (fun (_, actualType, actual) -> actual = formal && applySubst actualType = environmentType)) ->
                    Some(formal, owner)
                | _ -> None
            | _ -> None)
        |> List.groupBy fst
        |> List.choose (function formal, [(_, owner)] -> Some(formal, owner) | _ -> None) |> Map.ofList
    let rec follow seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        let same sources =
            match sources |> List.map (follow seen) |> List.distinct with [Some owner] -> Some owner | _ -> None
        match live graph id with
        | Some { Kind = SemanticKind.LazyValue _ } when formations.ContainsKey id -> Some id
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _)
                      | SemanticKind.LazyEnvironmentReference source } -> follow seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [source] } -> follow seen source
        | Some { Kind = SemanticKind.EagerExpr source } when ExplicitDemand.operand graph id = Some source -> follow seen source
        | Some { Kind = SemanticKind.Sequential actions } -> List.tryLast actions |> Option.bind (follow seen)
        | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } -> same [yes; no]
        | Some { Kind = SemanticKind.Application _ } ->
            calls.Value.Calls.TryFind id |> Option.bind (fun call ->
                if call.Unknown || not call.Complete then None else same (call.Targets |> List.map _.Body))
        | Some { Kind = SemanticKind.PatternBinding _ } ->
            formations.Values |> Seq.filter (fun value -> value.Formal = id) |> Seq.map _.Formation |> Seq.toList
            |> function
               | [owner] -> Some owner
               | [] -> resultFormals.TryFind id |> Option.orElseWith (fun () -> calls.Value.ParameterInputs.TryFind id |> Option.bind (List.map snd >> same))
               | _ -> None
        | Some { Kind = SemanticKind.LazyEnvironment(owner, _) }
            when formations.TryFind owner |> Option.exists (fun contract -> contract.Environment = id) -> Some owner
        | Some { Kind = SemanticKind.LazyAllocate owner } when formations.ContainsKey owner -> Some owner
        | _ -> None
    follow Set.empty

let private consumers (graph: SemanticGraph) =
    graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.collect structuralIncidence
    |> Seq.filter Hyperedge.isStructural
    |> Seq.collect (fun edge -> edge.Sources |> Seq.map (fun source -> source, edge.Target))
    |> Seq.groupBy fst |> Seq.map (fun (id, uses) -> id, uses |> Seq.map snd |> Seq.toList) |> Map.ofSeq

/// Validate the real guard and store-before-publication spine. In particular,
/// one guarded occurrence cannot authorize another use of the cached read.
let force (graph: SemanticGraph) site : Force option =
    let ownerOf = tryOwner graph
    let uses = consumers graph
    let sole source target = uses.TryFind source = Some [target]
    let reference declaration id =
        match live graph id, live graph declaration with
        | Some { Kind = SemanticKind.VarRef(_, Some actual); Type = actualType }, Some source ->
            actual = declaration && applySubst actualType = applySubst source.Type
        | _ -> false
    match rows EdgeRole.LazyMemoization graph site |> single with
    | Some { Class = EdgeClass.Provenance; Ordinal = 0
             Sources = [owner; operand; environmentBinding; condition; cachedRead; invocation; resultBinding; store; publication; uncached; conditional] } ->
        match instance graph owner, live graph site, live graph environmentBinding, live graph conditional, live graph uncached with
        | Some contract, Some { Kind = SemanticKind.Sequential [actualEnvironment; actualConditional]; Type = siteType },
          Some { Kind = SemanticKind.Binding(_, false, false, None); Children = [environmentReference]; Type = environmentType' },
          Some { Kind = SemanticKind.IfThenElse(actualCondition, actualCached, Some actualUncached); Type = conditionalType },
          Some { Kind = SemanticKind.Sequential [actualBinding; actualStore; actualPublication; result]; Type = branchType }
            when actualEnvironment = environmentBinding && actualConditional = conditional &&
                 applySubst siteType = contract.ElementType && applySubst conditionalType = contract.ElementType &&
                 applySubst branchType = contract.ElementType && applySubst environmentType' = environmentType &&
                 actualCondition = condition && actualCached = cachedRead && actualUncached = uncached &&
                 actualBinding = resultBinding && actualStore = store && actualPublication = publication &&
                 reference resultBinding result && ownerOf operand = Some owner &&
                 sole environmentBinding site && sole conditional site && sole cachedRead conditional &&
                 sole condition conditional && sole uncached conditional && sole resultBinding uncached &&
                 sole store uncached && sole publication uncached && sole invocation resultBinding ->
            let read slot expected id =
                match live graph id with
                | Some { Kind = SemanticKind.LazyRead(environment, actual); Type = actualType } ->
                    actual = slot && reference environmentBinding environment && applySubst actualType = expected
                | _ -> false
            match live graph environmentReference, live graph resultBinding, live graph invocation, live graph store, live graph publication with
            | Some { Kind = SemanticKind.LazyEnvironmentReference actualOperand; Type = environmentReferenceType },
              Some { Kind = SemanticKind.Binding(_, false, false, None); Children = [actualInvocation]; Type = resultType },
              Some { Kind = SemanticKind.Application(callee, [argument]); Type = invocationType },
              Some { Kind = SemanticKind.LazyWrite(storeEnvironment, storedSlot, storedValue); Type = storeType },
              Some { Kind = SemanticKind.LazyWrite(publishEnvironment, publishedSlot, publishedValue); Type = publicationType }
                when actualOperand = operand && actualInvocation = invocation &&
                     applySubst environmentReferenceType = environmentType && storeType = Types.unitType && publicationType = Types.unitType &&
                     applySubst resultType = contract.ElementType && applySubst invocationType = contract.ElementType &&
                     reference contract.Thunk callee && reference environmentBinding argument &&
                     read contract.Computed Types.boolType condition && read contract.Cached contract.ElementType cachedRead &&
                     reference environmentBinding storeEnvironment && storedSlot = contract.Cached && reference resultBinding storedValue &&
                     reference environmentBinding publishEnvironment && publishedSlot = contract.Computed &&
                     (live graph publishedValue |> Option.exists (fun node -> node.Kind = SemanticKind.Literal(NativeLiteral.Bool true))) ->
                Some { Site = site; Operand = operand; Formation = owner; EnvironmentBinding = environmentBinding
                       Condition = condition; CachedRead = cachedRead; Invocation = invocation; ResultBinding = resultBinding
                       ResultStore = store; Publication = publication; UncachedBranch = uncached; Conditional = conditional }
            | _ -> None
        | _ -> None
    | _ -> None

type Residual = { Site: NodeId; Participants: NodeId list; Reason: string }
type Settlement = {
    Instances: Map<NodeId, Instance>
    Forces: Map<NodeId, Force>
    CaptureUses: Map<NodeId, NodeId list>
    Residuals: Residual list
}

/// Admission is joint across every internal cache access. An otherwise good
/// force does not authorize a second unguarded read or a premature publication.
/// Capture residence and single-forcer ownership are separate later premises.
let settle (graph: SemanticGraph) : Settlement =
    let contracts = instances graph
    let ownerOf = tryOwner graph
    let forceSites = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyMemoization)
                     |> List.map _.Target |> List.distinct
    let proofs = forceSites |> List.choose (fun site -> force graph site |> Option.map (fun proof -> site, proof)) |> Map.ofList
    let residuals = ResizeArray<Residual>()
    let scopes = lazy (captureScopes graph)
    let mutable captureUses = Map.empty
    let reject site participants reason = residuals.Add { Site = site; Participants = participants; Reason = reason }
    for node in graph.Nodes.Values do
        if node.IsReachable then
            match node.Kind with
            | SemanticKind.LazyExpr _ | SemanticKind.LazyForce _ ->
                reject node.Id [] "Lazy source structure still requires an admitted formation or exact force origin."
            | SemanticKind.LazyValue _ when not (contracts.ContainsKey node.Id) ->
                reject node.Id [] "Lazy formation, typed declarations and exact initialization incidence disagree."
            | SemanticKind.LazyRead(environment, slot) | SemanticKind.LazyBorrow(environment, slot)
            | SemanticKind.LazyWrite(environment, slot, _) ->
                let admitted = ownerOf environment |> Option.bind contracts.TryFind |> Option.exists (fun contract ->
                    let own = proofs.Values |> Seq.filter (fun proof -> proof.Formation = contract.Formation)
                    if slot = contract.Computed then
                        own |> Seq.exists (fun proof -> node.Id = proof.Condition || node.Id = proof.Publication)
                    elif slot = contract.Cached then
                        own |> Seq.exists (fun proof -> node.Id = proof.CachedRead || node.Id = proof.ResultStore)
                    else
                        let typed = contract.Captured |> List.exists (fun (source, _, mutableCell) ->
                            source = slot &&
                            (match node.Kind with
                             | SemanticKind.LazyRead _ -> applySubst node.Type = applySubst graph.Nodes[slot].Type
                             | SemanticKind.LazyBorrow _ ->
                                 mutableCell && applySubst node.Type = NativeType.TByref(applySubst graph.Nodes[slot].Type, ByrefKind.InOut)
                             | SemanticKind.LazyWrite(_, _, value) ->
                                 mutableCell && node.Type = Types.unitType &&
                                 (live graph value |> Option.exists (fun value -> applySubst value.Type = applySubst graph.Nodes[slot].Type))
                             | _ -> false))
                        let access =
                            if not typed then None else
                            captureEnvironment graph contract environment
                            |> Option.bind (fun path -> scopes.Value contract (node.Id :: path))
                        match access with
                        | Some participants ->
                            let previous = captureUses.TryFind contract.Formation |> Option.defaultValue []
                            captureUses <- captureUses.Add(contract.Formation, List.distinct (previous @ (slot :: participants)))
                            true
                        | None -> false)
                if not admitted then reject node.Id [environment; slot] "Lazy storage access lacks its exact capture mode, invocation scope, or guarded cache/publication protocol."
            | _ -> ()
    for site in forceSites do
        if not (proofs.ContainsKey site) then reject site [] "Lazy memoization incidence disagrees with the actual guard, invocation, store, or publication."
    { Instances = contracts; Forces = proofs; CaptureUses = captureUses; Residuals = List.ofSeq residuals }

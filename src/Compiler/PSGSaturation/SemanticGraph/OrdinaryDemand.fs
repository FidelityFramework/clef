// SPDX-License-Identifier: MIT
/// Source-owned absence of ordinary formal demand. Logical formals, actuals
/// and their source types remain resident; only a proved physical projection
/// omits transport. This is not a general strictness or memoization analysis.
module Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Incidence = Clef.Compiler.Baker.Ingredients.Closures

type Formal = {
    Implementation: NodeId
    Formal: NodeId
    Ordinal: int
    Participants: Set<NodeId>
}
type Call = {
    Site: NodeId
    Callee: NodeId
    Implementation: NodeId
    Parameters: NodeId list
    Actuals: NodeId list
    Omitted: Set<int>
    Eager: Set<int>
    Participants: Set<NodeId>
}
type Reading = { Formals: Map<NodeId, Formal>; Calls: Map<NodeId, Call> }

let private key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
let private owned edge = edge.Role = EdgeRole.OrdinaryUnusedFormal || edge.Role = EdgeRole.OrdinaryUnusedActual

let analyze (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
    let recorded = graph.Edges |> List.filter (fun edge ->
        edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
    let uses =
        incidence @ recorded
        |> List.filter (fun edge -> nodes.ContainsKey edge.Target)
        |> List.distinctBy key
        |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ rows -> List.map snd rows)
    let valid id =
        match nodes.TryFind id with
        | None -> false
        | Some node ->
            let expected = Incidence.structuralIncidence node
            // Resides is a resource constraint, not a competing spelling of
            // syntactic containment/reference. It remains in the complete use
            // census above, including any formal it names as a premise.
            let actual = recorded |> List.filter (fun edge ->
                edge.Target = id && not (edge.Class = EdgeClass.Reference && edge.Role = EdgeRole.Resides))
            let children = kindEdges id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
            let childrenAgree =
                match node.Kind with
                | SemanticKind.Binding _ | SemanticKind.Intrinsic _ -> true
                | SemanticKind.EnvironmentCreate(_, initializers) | SemanticKind.LazyEnvironment(_, initializers) ->
                    // Kind carries every initializer reference, including
                    // direct captures whose already-available value needs no
                    // attached traversal. Forwarded reads may be attached by
                    // their owning recipe; no unrelated or repeated child is
                    // an admitted part of this formation.
                    node.Children = List.distinct node.Children &&
                    node.Children |> List.forall (fun child -> initializers |> List.exists (fun (_, value) -> value = child))
                | _ -> node.Children = children
            childrenAgree && actual.Length = (actual |> List.distinctBy key |> List.length) &&
            (actual |> List.forall (fun edge -> expected |> List.exists (fun candidate -> key candidate = key edge)))
    let resolution = CallableOrigins.resolve graph
    let ingress = CallableIngress.analyzeWith graph resolution
    let rawCapture formal = nodes.Values |> Seq.exists (fun node ->
        let captures =
            match node.Kind with
            | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures)
            | SemanticKind.LazyExpr(_, captures) -> captures
            | _ -> []
        captures |> List.exists (fun capture -> capture.SourceNodeId = Some formal))
    let hidden =
        graph.Edges |> List.collect (fun edge ->
            match edge.Role, edge.Sources with
            | EdgeRole.EnvironmentFormal, _ | EdgeRole.CaptureOrigin, _ -> [edge.Target]
            | EdgeRole.EnvironmentResultDestination, [_; _; formal]
            | EdgeRole.LazyResultDestination, [_; _; formal] -> [formal]
            | EdgeRole.EnrichedWith, _ ->
                match nodes.TryFind edge.Target with Some { Kind = SemanticKind.PatternBinding _ } -> [edge.Target] | _ -> []
            | _ -> []) |> Set.ofList
    let bodyParticipants root =
        let rec visit pending found =
            match pending with
            | [] -> found
            | id :: rest when Set.contains id found -> visit rest found
            | id :: rest ->
                match nodes.TryFind id with
                | Some node -> visit (node.Children @ rest) (Set.add id found)
                | None -> visit rest (Set.add id found)
        visit [root] Set.empty
    // This first projection requires declaration/alias/direct-call closure.
    // Higher-order and captured callable conventions need a common projection
    // across their complete family before any member can omit a component.
    let directUses (proof: CallableIngress.Evidence) =
        proof.Uses |> Map.forall (fun _ rows -> rows |> List.forall (fun edge ->
            match nodes.TryFind edge.Target, edge.Class, edge.Role with
            | Some { Kind = SemanticKind.ModuleDef _ }, EdgeClass.Reference, EdgeRole.Member
            | Some { Kind = SemanticKind.VarRef _ }, EdgeClass.Reference, EdgeRole.Definition
            | Some { Kind = SemanticKind.Binding _ | SemanticKind.TypeAnnotation _ | SemanticKind.EagerExpr _ }, EdgeClass.Structural, _
            | Some { Kind = SemanticKind.Application _ }, EdgeClass.Structural, EdgeRole.Callee -> true
            | _ -> false))
    let formals =
        nodes.Values |> Seq.collect (fun code ->
            match code.Kind, CallableIngress.tryClosedImplementation ingress code.Id with
            | SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure), Some proof
                when valid code.Id && valid body && directUses proof ->
                let bodyNodes = bodyParticipants body
                let incoming = proof.Calls |> List.collect (fun call ->
                    call.Site :: call.Implementation :: (call.Parameters @ call.Arguments)) |> Set.ofList
                let entryParticipants =
                    graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ProgramInitialization || edge.Role = EdgeRole.ProgramEntryCall)
                    |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList
                let fullType = List.foldBack (fun (_, ty, _) result -> NativeType.TFun(ty, result)) parameters nodes[body].Type
                if applySubst code.Type <> applySubst fullType || bodyNodes |> Set.exists (valid >> not) then [] else
                parameters |> List.mapi (fun ordinal (_, ty, formal) ->
                    let declared =
                        match nodes.TryFind formal with
                        | Some { Kind = SemanticKind.PatternBinding _; Type = actual } -> valid formal && applySubst actual = applySubst ty
                        | _ -> false
                    let allUses = uses.TryFind formal |> Option.defaultValue []
                    let absent = allUses |> List.forall (fun edge ->
                        edge.Class = EdgeClass.Structural && edge.Role = EdgeRole.Parameter &&
                        edge.Target = code.Id && edge.Ordinal = ordinal && edge.Sources = [formal])
                    if not declared || not absent || hidden.Contains formal || rawCapture formal then None else
                    Some(formal, { Implementation = code.Id; Formal = formal; Ordinal = ordinal
                                   Participants = Set.unionMany [proof.Participants; incoming; entryParticipants; bodyNodes
                                                                 Set.ofList(code.Id :: (parameters |> List.map (fun (_, _, id) -> id)))] }))
                |> List.choose id
            | _ -> []) |> Map.ofSeq
    let calls =
        resolution.Calls |> Map.toList |> List.choose (fun (site, resolved) ->
            match nodes.TryFind site, resolved.Targets with
            | Some { Kind = SemanticKind.Application(callee, actuals); Children = children }, [target]
                when resolved.Complete && not resolved.Unknown && valid site && valid callee &&
                     children = callee :: actuals && target.Arguments = actuals &&
                     target.Parameters.Length = actuals.Length ->
                let selected = target.Parameters |> List.indexed |> List.choose (fun (ordinal, (_, _, formal)) ->
                    formals.TryFind formal |> Option.filter (fun proof -> proof.Implementation = target.Lambda && proof.Ordinal = ordinal)
                    |> Option.map (fun proof -> ordinal, proof))
                let typed = List.zip target.Parameters actuals |> List.forall (fun ((_, ty, formal), actual) ->
                    valid formal && valid actual && applySubst nodes[formal].Type = applySubst ty &&
                    applySubst nodes[actual].Type = applySubst ty)
                if selected.IsEmpty || not typed then None else
                let eager = selected |> List.map (fun (ordinal, _) ->
                    match ExplicitDemand.direct graph actuals[ordinal] with
                    | Ok None -> Some(ordinal, false, Set.empty)
                    | Ok(Some marker) ->
                        let rows = graph.Edges |> List.filter (fun edge ->
                            edge.Class = EdgeClass.Demand && edge.Role = EdgeRole.EagerDemand EagerFrontier.Actual &&
                            edge.Target = site && edge.Sources |> List.contains marker.Marker)
                        match rows with
                        | [row] when List.contains marker.Operand row.Sources -> Some(ordinal, true, Set.ofList row.Sources)
                        | _ -> None
                    | Error _ -> None)
                if eager |> List.exists Option.isNone then None else
                let eager = List.choose id eager
                let participants =
                    [ Set.ofList(site :: callee :: target.Lambda :: target.Body :: actuals @ (target.Parameters |> List.map (fun (_, _, id) -> id)))
                      selected |> List.map (snd >> _.Participants) |> Set.unionMany
                      eager |> List.map (fun (_, _, participants) -> participants) |> Set.unionMany ] |> Set.unionMany
                Some(site, { Site = site; Callee = callee; Implementation = target.Lambda
                             Parameters = target.Parameters |> List.map (fun (_, _, id) -> id); Actuals = actuals
                             Omitted = selected |> List.map fst |> Set.ofList
                             Eager = eager |> List.choose (fun (ordinal, demanded, _) -> if demanded then Some ordinal else None) |> Set.ofList
                             Participants = participants })
            | _ -> None) |> Map.ofList
    // All source calls to an omitted implementation must use the same admitted
    // projection. A partial, opaque, mismatched or unadapted call retracts it.
    let admitted =
        formals.Values |> Seq.map _.Implementation |> Set.ofSeq |> Set.filter (fun implementation ->
            let sites = resolution.Calls |> Map.toList |> List.filter (fun (_, call) -> call.Targets |> List.exists (fun target -> target.Lambda = implementation))
            not sites.IsEmpty && sites |> List.forall (fun (site, _) -> calls.ContainsKey site))
    { Formals = formals |> Map.filter (fun _ proof -> admitted.Contains proof.Implementation)
      Calls = calls |> Map.filter (fun _ proof -> admitted.Contains proof.Implementation) }

let edges reading =
    [ for proof in reading.Formals.Values do
          yield { Class = EdgeClass.Demand; Role = EdgeRole.OrdinaryUnusedFormal; Target = proof.Formal; Ordinal = proof.Ordinal
                  Sources = proof.Implementation :: (proof.Participants.Remove proof.Implementation |> Set.toList) }
      for call in reading.Calls.Values do
          for ordinal in call.Omitted do
              yield { Class = EdgeClass.Demand; Role = EdgeRole.OrdinaryUnusedActual; Target = call.Site; Ordinal = ordinal
                      Sources = [call.Implementation; call.Parameters[ordinal]; call.Actuals[ordinal]; call.Callee]
                                @ (call.Participants |> Set.toList) } ]

let private cache = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, Reading>()
/// Recompute against the immutable graph and require its exact current joint
/// rows. An old codata/edge projection supplies no independent authority.
let read graph =
    cache.GetValue(graph, fun graph ->
        let fresh = analyze graph
        let expected = edges fresh |> List.map key |> List.sort
        let actual = graph.Edges |> List.filter owned |> List.map key |> List.sort
        if actual = expected then fresh else { Formals = Map.empty; Calls = Map.empty })

let parameters graph implementation =
    (read graph).Formals.Values |> Seq.filter (fun proof -> proof.Implementation = implementation) |> Seq.map _.Formal |> Set.ofSeq

/// Exact actual occurrences whose computation is not entered at this call.
let deferredActuals graph site =
    (read graph).Calls.TryFind site |> Option.map (fun call -> Set.difference call.Omitted call.Eager) |> Option.defaultValue Set.empty

/// Source coverage may omit only nodes with no remaining demanding use. Shared
/// nodes used elsewhere remain required. This changes neither IsReachable nor
/// source/proof incidence and does not claim an emitted operation for a skip.
let private deferredFrom graph (reading: Reading) =
    let omitted = reading.Calls.Values |> Seq.collect (fun call ->
        Set.difference call.Omitted call.Eager |> Seq.map (fun ordinal -> call.Site, ordinal, call.Actuals[ordinal])) |> Set.ofSeq
    let incidence =
        (graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.collect Incidence.structuralIncidence |> Seq.toList)
        @ (graph.Edges |> List.filter (fun edge ->
            (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) &&
            graph.Nodes.TryFind edge.Target |> Option.exists _.IsReachable))
        |> List.distinctBy key
    let uses = incidence |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
               |> List.groupBy fst |> Map.ofList |> Map.map (fun _ rows -> List.map snd rows)
    let rec expand pending found =
        match pending with
        | [] -> found
        | id :: rest when Set.contains id found -> expand rest found
        | id :: rest ->
            match graph.Nodes.TryFind id with
            | Some node when node.IsReachable ->
                let dependencies = Incidence.structuralIncidence node |> List.collect _.Sources
                expand (dependencies @ rest) (Set.add id found)
            | _ -> expand rest found
    let candidates = expand (omitted |> Set.toList |> List.map (fun (_, _, id) -> id)) Set.empty
    let roots = graph.DeclarationRoots |> List.map fst |> Set.ofList
    let rec retain found =
        let next = found |> Set.filter (fun id ->
            not (roots.Contains id) &&
            (uses.TryFind id |> Option.defaultValue [] |> List.forall (fun edge ->
                found.Contains edge.Target ||
                (edge.Class = EdgeClass.Reference && edge.Role = EdgeRole.Member) ||
                (edge.Class = EdgeClass.Structural && edge.Role = EdgeRole.Argument && omitted.Contains(edge.Target, edge.Ordinal, id)))))
        if next = found then found else retain next
    retain candidates

let deferredOnly graph = deferredFrom graph (read graph)

let private projectionFrom graph (reading: Reading) : OrdinaryDemandProjection =
    { Parameters =
        reading.Formals.Values
        |> Seq.groupBy _.Implementation
        |> Seq.map (fun (implementation, formals) -> implementation, formals |> Seq.map _.Formal |> Set.ofSeq)
        |> Map.ofSeq
      Calls =
        reading.Calls |> Map.map (fun _ call ->
            ({ Implementation = call.Implementation; Actuals = call.Actuals
               Omitted = call.Omitted; Eager = call.Eager }: OrdinaryCallProjection))
      DeferredOnly = deferredFrom graph reading }

/// Final source projection. Analysis and the complete use census belong to CCS;
/// consumers receive only these settled transport and occurrence decisions.
let project graph = projectionFrom graph (read graph)

/// Compute and validate the final use proof once while the source stage owns
/// publication. An absent or extra relation cannot become an empty admission.
let projectValidated graph : Result<OrdinaryDemandProjection, WitnessProjectionFailure list> =
    let fresh = analyze graph
    let expected = edges fresh
    let actual = graph.Edges |> List.filter owned
    if (expected |> List.map key |> List.sort) = (actual |> List.map key |> List.sort) then
        Ok (projectionFrom graph fresh)
    else
        let targets = (expected @ actual) |> List.map _.Target |> Set.ofList
        let failures =
            targets |> Set.toList |> List.choose (fun target ->
                let expectedAt = expected |> List.filter (fun edge -> edge.Target = target)
                let actualAt = actual |> List.filter (fun edge -> edge.Target = target)
                if (expectedAt |> List.map key |> List.sort) = (actualAt |> List.map key |> List.sort) then None
                else Some {
                    Occurrence = Some target
                    Reason = "Ordinary-demand source relations do not match the current complete use proof."
                    Participants = (expectedAt @ actualAt) |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList })
        Error failures

let private emissionSeals =
    System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, OrdinaryDemandProjection>()

/// Seal the exact completed graph after all source graph copies and codata
/// settlement. A rejected or missing joint cannot masquerade as a valid empty
/// projection. Re-sealing the same unchanged graph preserves its authority.
let sealEmission graph : Result<unit, string> =
    let reject message =
        emissionSeals.Remove graph |> ignore
        Error message
    match projectValidated graph with
    | Error failures -> reject (failures |> List.map _.Reason |> String.concat " ")
    | Ok projection ->
        if graph.Codata.Value.OrdinaryDemand <> projection then
            reject "Ordinary-demand emission projection differs from the settled source proof."
        else
            let admitted = emissionSeals.GetValue(graph, fun _ -> projection)
            if admitted = projection then Ok ()
            else reject "Ordinary-demand authority was revised after this graph was sealed."

/// Emission performs an exact graph-reference lookup only: no edge scan, origin
/// discovery, type inference, demand analysis or fallback proof is permitted.
let tryEmission graph : Result<OrdinaryDemandProjection, string> =
    match emissionSeals.TryGetValue graph with
    | true, projection -> Ok projection
    | _ -> Error "The current graph has no sealed ordinary-demand emission projection."

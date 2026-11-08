// SPDX-License-Identifier: MIT
/// Source-owned ordinary demand. Physical omissions retain logical arguments;
/// separate complete inactivity premises exclude execution without erasing
/// a callable's transport or residence. This is not general memoization.
module Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Reports = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
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
type SourceBodyInactivity = {
    Entry: NodeId
    Roots: (NodeId * DeclRoot) list
    Participants: Set<NodeId>
    Uses: Map<NodeId, Hyperedge list>
}
type InactivityPremise =
    | ClosedFamily of CallableIngress.Family
    | UnobservedCell of SourceBodyInactivity
    | IgnoredPayload of SourceBodyInactivity
type InactiveImplementation = {
    Implementation: NodeId
    Body: NodeId
    Parameters: NodeId list
    Excluded: Set<NodeId>
    Calls: Set<NodeId>
    Premise: InactivityPremise
}
type UnusedInitializer = {
    Binding: NodeId
    Initializer: NodeId
    Definition: Hyperedge
    /// A used mutable cell retains its binding; only this exact initial-value use is cut.
    InitializerUse: Hyperedge option
    ExcludesBinding: bool
    Participants: Set<NodeId>
}
type Reading = {
    Formals: Map<NodeId, Formal>
    Calls: Map<NodeId, Call>
    Inactivity: Map<NodeId, InactiveImplementation>
    Initializers: Map<NodeId, UnusedInitializer>
}
/// Execution joins are separate from the physical argument omissions above.
type InactivityReading = {
    Implementations: Map<NodeId, InactiveImplementation>
    Formals: Set<NodeId>
    Excluded: Set<NodeId>
    Calls: Set<NodeId>
}

let private key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
let private owned edge =
    edge.Role = EdgeRole.OrdinaryUnusedFormal || edge.Role = EdgeRole.OrdinaryUnusedActual ||
    edge.Role = EdgeRole.OrdinaryInactiveImplementation ||
    edge.Role = EdgeRole.OrdinaryUnusedBindingInitializer

let private inactivitySupport inactive =
    match inactive.Premise with
    | ClosedFamily family ->
        family.Evidence.Entry.Value, family.Evidence.Roots, family.Evidence.Participants, family.Evidence.Uses
    | UnobservedCell cell | IgnoredPayload cell -> cell.Entry, cell.Roots, cell.Participants, cell.Uses

let inactivityParticipants inactive =
    let _, _, participants, _ = inactivitySupport inactive
    participants

let analyze (graph: SemanticGraph) : Reading =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    // An external declaration's placeholder is not the foreign function's
    // implementation. Its lack of formal reads proves no argument unused:
    // foreign argument demand belongs to the declared boundary contract.
    let externalImplementations =
        graph.Edges |> List.choose (fun edge ->
            match edge.Role with EdgeRole.BoundaryDeclaration declaration -> Some declaration.Implementation | _ -> None) |> Set.ofList
    let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
    let recorded = graph.Edges |> List.filter (fun edge ->
        edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
    let uses =
        incidence @ recorded
        |> List.filter (fun edge -> nodes.ContainsKey edge.Target)
        |> List.distinctBy key
        |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ rows -> List.map snd rows)
    // Resides is a resource constraint, not a competing spelling of
    // syntactic containment/reference. It remains in the complete use
    // census above, including any formal it names as a premise. The recorded
    // rows are read per target; the order within a target is the edge order.
    let recordedAt =
        recorded
        |> List.filter (fun edge -> not (edge.Class = EdgeClass.Reference && edge.Role = EdgeRole.Resides))
        |> List.groupBy _.Target |> Map.ofList
    // Each node's agreement with its recorded incidence is one fact of this
    // graph, derived once for every reachable node (clef #131).
    let validity =
        nodes |> Map.map (fun id node ->
            let expected = Incidence.structuralIncidence node
            let actual = recordedAt.TryFind id |> Option.defaultValue []
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
            (actual |> List.forall (fun edge -> expected |> List.exists (fun candidate -> key candidate = key edge))))
    let valid id = validity.TryFind id = Some true
    let resolution = CallableOrigins.resolve graph
    let ingress = CallableIngress.analyzeWith graph resolution
    // Every source node a lambda, sequence or lazy expression captures raw.
    let rawCaptured =
        nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures)
            | SemanticKind.LazyExpr(_, captures) -> captures
            | _ -> [])
        |> Seq.choose _.SourceNodeId |> Set.ofSeq
    let rawCapture formal = rawCaptured.Contains formal
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
    let entryParticipants =
        graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ProgramInitialization || edge.Role = EdgeRole.ProgramEntryCall)
        |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList
    let formals =
        nodes.Values |> Seq.collect (fun code ->
            match code.Kind, CallableIngress.tryClosedImplementation ingress code.Id with
            | SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure), Some proof
                when not (externalImplementations.Contains code.Id) && valid code.Id && valid body && directUses proof ->
                let bodyNodes = bodyParticipants body
                let incoming = proof.Calls |> List.collect (fun call ->
                    call.Site :: call.Implementation :: (call.Parameters @ call.Arguments)) |> Set.ofList
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
    let sitesByImplementation =
        resolution.Calls |> Map.toList
        |> List.collect (fun (site, call) -> call.Targets |> List.map (fun target -> target.Lambda, site) |> List.distinct)
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ rows -> List.map snd rows)
    let admitted =
        formals.Values |> Seq.map _.Implementation |> Set.ofSeq |> Set.filter (fun implementation ->
            let sites = sitesByImplementation.TryFind implementation |> Option.defaultValue []
            not sites.IsEmpty && sites |> List.forall calls.ContainsKey)
    let structuralParents =
        incidence |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge.Target))
        |> List.groupBy fst |> List.map (fun (child, rows) -> child, rows |> List.map snd |> List.distinct) |> Map.ofList
    let excludedByImplementation implementation =
        let ownedByImplementation id =
            // Read the finite owner chain iteratively. A nested lambda owns
            // itself, so only its unique structural parent supplies the next
            // owner. Ambiguous parents and revisited owners refuse exclusion.
            Seq.unfold (function
                | None -> None
                | Some(id, seen) ->
                    match CallableIngress.tryExecutionOwner ingress id with
                    | Some owner when owner = implementation -> Some(true, None)
                    | Some owner when owner = id ->
                        match structuralParents.TryFind id with
                        | Some [parent] when not (Set.contains parent seen) ->
                            Some(false, Some(parent, Set.add id seen))
                        | _ -> Some(false, None)
                    | Some owner when not (Set.contains owner seen) ->
                        Some(false, Some(owner, Set.add owner seen))
                    | _ -> Some(false, None)) (Some(id, Set.empty))
            |> Seq.tryLast |> Option.defaultValue false
        let excluded = nodes.Keys |> Seq.filter (fun id ->
            id <> implementation && ownedByImplementation id) |> Set.ofSeq
        excluded
    let inactivity =
        nodes.Values |> Seq.choose (fun code ->
            match code.Kind, CallableIngress.tryFamily ingress code.Id with
            | SemanticKind.Lambda(parameters, body, _, _, LambdaContext.RegularClosure), Some family
                when not (family.Activated.Contains code.Id) && family.Evidence.Entry.IsSome &&
                     family.Evidence.UsedLazyForces.IsEmpty &&
                     not (externalImplementations.Contains code.Id) && valid code.Id && valid body ->
                let parametersAgree =
                    parameters |> List.forall (fun (_, ty, formal) ->
                        match nodes.TryFind formal with
                        | Some { Kind = SemanticKind.PatternBinding _; Type = actual } ->
                            // A current callable boundary can already include
                            // this formal before Curry absorbs its inner
                            // lambda. Its suppliers still own the execution
                            // join; lexical ownership alone cannot empty it.
                            let suppliersInactive =
                                resolution.ParameterInputs.TryFind formal |> Option.defaultValue []
                                |> List.forall (fun (site, _) ->
                                    match CallableIngress.tryExecutionOwner ingress site with
                                    | Some owner -> family.Evidence.Implementations.Contains owner && not (family.Activated.Contains owner)
                                    | None -> false)
                            valid formal && applySubst actual = applySubst ty &&
                            CallableIngress.tryExecutionOwner ingress formal = Some code.Id && suppliersInactive
                        | _ -> false)
                if not parametersAgree then None else
                // The same structural ownership reader that assigns callers
                // identifies the body's occurrences. Shared/ambiguous owners
                // remain demanded; the callable formation itself is retained.
                // Ownership is followed through nested owners (a sequence
                // generator or closure formed inside the body): an
                // implementation that is never entered forms none of them, so
                // their bodies are the same unreachable computation and commit
                // no integer of their own (width-inference §78, §80).
                let excluded = excludedByImplementation code.Id
                let calls = excluded |> Set.filter (fun id ->
                    match nodes[id].Kind with SemanticKind.Application _ -> true | _ -> false)
                Some(code.Id,
                    { Implementation = code.Id; Body = body
                      Parameters = parameters |> List.map (fun (_, _, id) -> id)
                      Excluded = excluded; Calls = calls; Premise = ClosedFamily family })
            | _ -> None) |> Map.ofSeq
    let roots = graph.DeclarationRoots |> List.map fst |> Set.ofList
    let startupSupport =
        graph.Edges |> List.filter (fun edge ->
            edge.Class = EdgeClass.Provenance &&
            (edge.Role = EdgeRole.ProgramInitialization || edge.Role = EdgeRole.ProgramInitializer ||
             edge.Role = EdgeRole.ProgramValueIntent || edge.Role = EdgeRole.ProgramEntryCall))
        |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList
    // Startup still forms and stores this value. A complete unobserved cell
    // census proves only that its implementation body is never entered; an
    // opaque replacing write remains outside physical family admission.
    let cellInactivity =
        match ProgramInitialization.read graph with
        | None -> Map.empty
        | Some plan ->
            let cells = MutableCallableStorage.sourceCensuses graph |> fst
            cells.Values
            |> Seq.choose (fun cell ->
                let formation =
                    match nodes[cell.Initial].Kind with
                    | SemanticKind.Lambda _ -> Some(cell.Initial, None)
                    | SemanticKind.TypeAnnotation(inner, _) -> Some(inner, Some cell.Initial)
                    | _ -> None
                let slot = plan.Initializers |> List.filter (fun slot -> slot.Binding = cell.Binding && slot.Initializer = cell.Initial)
                match formation, slot, nodes[cell.Binding].Kind with
                | Some(codeId, wrapper), [_], SemanticKind.Binding(_, true, false, None)
                    when cell.Reads.IsEmpty && cell.Captures.IsEmpty && cell.Borrows.IsEmpty &&
                         plan.ValueBindings.Contains cell.Binding && not (roots.Contains cell.Binding) &&
                         not (roots.Contains cell.Initial) && not (roots.Contains codeId) &&
                         not (externalImplementations.Contains codeId) && valid cell.Binding && valid cell.Initial ->
                    let onlyFormation id target =
                        (uses.TryFind id |> Option.defaultValue []) |> List.forall (fun edge ->
                            edge.Class = EdgeClass.Structural && edge.Target = target && edge.Sources = [id])
                    let formationOnly =
                        onlyFormation cell.Initial cell.Binding &&
                        (wrapper |> Option.forall (fun wrapper -> onlyFormation codeId wrapper)) &&
                        not (rawCapture cell.Initial || rawCapture codeId)
                    match nodes.TryFind codeId with
                    | Some { Kind = SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure) }
                        when formationOnly && valid codeId && valid body && not (roots.Contains body) &&
                             applySubst nodes[codeId].Type = applySubst cell.SourceType &&
                             applySubst nodes[codeId].Type = applySubst (List.foldBack (fun (_, ty, _) result -> NativeType.TFun(ty, result)) parameters nodes[body].Type) &&
                             (resolution.Calls.Values |> Seq.forall (fun call -> call.Targets |> List.forall (fun target -> target.Lambda <> codeId))) &&
                             (parameters |> List.forall (fun (_, ty, formal) ->
                                 valid formal && not (roots.Contains formal) &&
                                 (match nodes[formal].Kind with SemanticKind.PatternBinding _ -> true | _ -> false) &&
                                 applySubst nodes[formal].Type = applySubst ty &&
                                 CallableIngress.tryExecutionOwner ingress formal = Some codeId &&
                                 (resolution.ParameterInputs.TryFind formal |> Option.defaultValue [] |> List.isEmpty))) ->
                        let excluded = excludedByImplementation codeId
                        let calls = excluded |> Set.filter (fun id -> match nodes[id].Kind with SemanticKind.Application _ -> true | _ -> false)
                        let participants =
                            [cell.Participants; excluded; roots; startupSupport
                             Set.ofList(codeId :: cell.Initial :: body :: (parameters |> List.map (fun (_, _, id) -> id)))] |> Set.unionMany
                        let useProof = participants |> Set.toList |> List.map (fun id -> id, uses.TryFind id |> Option.defaultValue []) |> Map.ofList
                        Some(codeId, { Implementation = codeId; Body = body
                                       Parameters = parameters |> List.map (fun (_, _, id) -> id)
                                       Excluded = excluded; Calls = calls
                                       Premise = UnobservedCell { Entry = plan.EntryLambda; Roots = graph.DeclarationRoots
                                                                  Participants = participants; Uses = useProof } })
                    | _ -> None
                | _ -> None)
            |> Map.ofSeq
    let inactivity = Map.fold (fun found id proof -> Map.add id proof found) inactivity cellInactivity
    // A source pull transports a callable value; it does not invoke it. This
    // sufficient route admits one direct producer and its complete current
    // snapshot account, with every snapshot read consumed by known ignore.
    // The existing Current owner renews the exact guard at every read here.
    let payloadInactivity =
        match ProgramInitialization.read graph with
        | None -> Map.empty
        | Some plan ->
            let consumers = Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes.structuralConsumers graph
            let allUses id admit = uses.TryFind id |> Option.defaultValue [] |> List.forall admit
            let soleFormation id target = allUses id (fun edge ->
                edge.Class = EdgeClass.Structural && edge.Target = target && edge.Sources = [id])
            let operation modl operation id =
                match nodes.TryFind id with
                | Some { Kind = SemanticKind.Application(callee, [argument]) } when valid id && valid callee ->
                    match nodes[callee].Kind with
                    | SemanticKind.Intrinsic info when info.Module = modl && info.Operation = operation -> Some argument
                    | _ -> None
                | _ -> None
            let declarationUse binding (edge: Hyperedge) =
                edge.Class = EdgeClass.Structural && edge.Sources = [binding] &&
                (match nodes.TryFind edge.Target with
                 | Some { Kind = SemanticKind.Sequential actions } -> List.tryLast actions <> Some binding
                 | _ -> false)
            nodes.Values |> Seq.choose (fun loop ->
                match Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes.forLoop graph consumers loop with
                | Some ({ Sources = [enumerator; guard; _]; Target = current } as receipt)
                    when graph.Edges |> List.filter (fun edge -> key edge = key receipt) |> List.length = 1 ->
                    match nodes[enumerator].Children, loop.Kind with
                    | [acquisition], SemanticKind.WhileLoop(_, loopBody) ->
                        match operation IntrinsicModule.Seq "getEnumerator" acquisition, nodes[loopBody].Kind,
                              operation IntrinsicModule.SeqEnumerator "moveNext" guard,
                              operation IntrinsicModule.SeqEnumerator "current" current with
                        | Some producer, SemanticKind.Sequential [currentBinding; currentRef; action], Some guardRef, Some enumRef ->
                            match nodes[producer].Kind, nodes[action].Kind with
                            | SemanticKind.SeqExpr(generator, []), SemanticKind.Sequential [snapshot; ignored] ->
                                match nodes[generator].Kind, nodes[snapshot].Kind, nodes[snapshot].Children,
                                      operation IntrinsicModule.Operators "ignore" ignored with
                                | SemanticKind.Lambda(_, yielded, [], _, LambdaContext.SeqGenerator),
                                  SemanticKind.Binding(_, false, false, None), [snapshotValue], Some read
                                    when snapshotValue = currentRef ->
                                    match nodes[yielded].Kind, nodes[read].Kind with
                                    | SemanticKind.Yield codeId, SemanticKind.VarRef(_, Some actualSnapshot) when actualSnapshot = snapshot ->
                                        let exactUses =
                                            soleFormation producer acquisition && soleFormation generator producer &&
                                            soleFormation yielded generator && soleFormation codeId yielded &&
                                            soleFormation acquisition enumerator &&
                                            allUses enumerator (fun edge ->
                                                declarationUse enumerator edge ||
                                                (edge.Class = EdgeClass.Reference && edge.Role = EdgeRole.Definition &&
                                                 edge.Sources = [enumerator] && (edge.Target = guardRef || edge.Target = enumRef))) &&
                                            soleFormation guardRef guard && soleFormation enumRef current &&
                                            allUses currentRef (fun edge ->
                                                edge.Class = EdgeClass.Structural && edge.Sources = [currentRef] &&
                                                (edge.Target = loopBody || edge.Target = snapshot)) &&
                                            allUses snapshot (fun edge ->
                                                declarationUse snapshot edge ||
                                                (edge.Class = EdgeClass.Reference && edge.Role = EdgeRole.Definition &&
                                                 edge.Sources = [snapshot] && edge.Target = read)) &&
                                            allUses read (fun edge ->
                                                edge.Class = EdgeClass.Structural && edge.Role = EdgeRole.Argument &&
                                                edge.Ordinal = 0 && edge.Sources = [read] && edge.Target = ignored)
                                        let route = Set.ofList [producer; generator; yielded; codeId; enumerator; acquisition; guard; guardRef;
                                                                loop.Id; loopBody; current; currentBinding; currentRef; action; snapshot; read; ignored; plan.EntryLambda]
                                        match nodes[codeId].Kind with
                                        | SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure)
                                            when exactUses && (route |> Set.forall valid) &&
                                                 (route |> Set.forall (fun id -> not (roots.Contains id) && not (rawCapture id))) &&
                                                 not (externalImplementations.Contains codeId) && valid body && not (roots.Contains body) &&
                                                 applySubst nodes[codeId].Type = applySubst nodes[snapshot].Type &&
                                                 applySubst nodes[codeId].Type = applySubst (List.foldBack (fun (_, ty, _) result -> NativeType.TFun(ty, result)) parameters nodes[body].Type) &&
                                                 (resolution.Calls.Values |> Seq.forall (fun call -> call.Targets |> List.forall (fun target -> target.Lambda <> codeId))) &&
                                                 (parameters |> List.forall (fun (_, ty, formal) ->
                                                     valid formal && not (roots.Contains formal) &&
                                                     (match nodes[formal].Kind with SemanticKind.PatternBinding _ -> true | _ -> false) &&
                                                     applySubst nodes[formal].Type = applySubst ty &&
                                                     CallableIngress.tryExecutionOwner ingress formal = Some codeId &&
                                                     (resolution.ParameterInputs.TryFind formal |> Option.defaultValue [] |> List.isEmpty))) ->
                                            let excluded = excludedByImplementation codeId
                                            let calls = excluded |> Set.filter (fun id -> match nodes[id].Kind with SemanticKind.Application _ -> true | _ -> false)
                                            let operationSupport =
                                                [acquisition; guard; current; ignored]
                                                |> List.collect (fun id -> kindEdges id nodes[id].Kind |> List.collect _.Sources)
                                                |> Set.ofList
                                            let participants = Set.unionMany [route; operationSupport; startupSupport; excluded; roots; Set.ofList (body :: (parameters |> List.map (fun (_, _, id) -> id)))]
                                            let useProof = participants |> Set.toList |> List.map (fun id -> id, uses.TryFind id |> Option.defaultValue []) |> Map.ofList
                                            Some(codeId, { Implementation = codeId; Body = body
                                                           Parameters = parameters |> List.map (fun (_, _, id) -> id)
                                                           Excluded = excluded; Calls = calls
                                                           Premise = IgnoredPayload { Entry = plan.EntryLambda; Roots = graph.DeclarationRoots
                                                                                      Participants = participants; Uses = useProof } })
                                        | _ -> None
                                    | _ -> None
                                | _ -> None
                            | _ -> None
                        | _ -> None
                    | _ -> None
                | _ -> None) |> Map.ofSeq
    let inactivity = Map.fold (fun found id proof -> Map.add id proof found) inactivity payloadInactivity
    let initializers =
        nodes.Values |> Seq.choose (fun binding ->
            match binding.Kind, binding.Children, binding.Parent with
            | SemanticKind.Binding(_, false, false, None), [initializer], Some parent
                when binding.Metadata.TryFind "SourceBinding.Local" = Some(MetadataValue.Bool true) &&
                     not (roots.Contains binding.Id) && valid binding.Id && valid initializer && valid parent ->
                match nodes[parent].Kind, uses.TryFind binding.Id, ExplicitDemand.direct graph initializer with
                | SemanticKind.Sequential statements, Some [definition], Ok None
                    when not statements.IsEmpty && List.last statements <> binding.Id &&
                         definition.Class = EdgeClass.Structural && definition.Target = parent &&
                         definition.Sources = [binding.Id] ->
                    Some(binding.Id, { Binding = binding.Id; Initializer = initializer; Definition = definition
                                       InitializerUse = None; ExcludesBinding = true; Participants = Set.empty })
                | _ -> None
            | _ -> None) |> Map.ofSeq
    // A mutable cell's logical source census is independent of whether an
    // opaque consumer admits its physical family. No callback actual vector is
    // invented here: only an unconditional replacing write can exclude its
    // earlier initializer, and every current read remains in this proof.
    let sourceCells = MutableCallableStorage.sourceFamilies graph |> fst
    let activations =
        if sourceCells.IsEmpty then [] else Clef.Compiler.Baker.Ingredients.BindingDemand.activationFacts graph
    let overwritten =
        sourceCells.Values
        |> Seq.choose (fun cell ->
            let binding = nodes[cell.Binding]
            let parents = uses.TryFind binding.Id |> Option.defaultValue [] |> List.filter Hyperedge.isStructural
            let owners = activations |> List.filter (fun activation ->
                activation.Entry.IsEmpty && (activation.Slots |> List.exists (fun slot -> slot.Statement = binding.Id)))
            let formation =
                let code =
                    match nodes[cell.Initial].Kind with
                    | SemanticKind.Lambda _ -> Some cell.Initial
                    | SemanticKind.TypeAnnotation(inner, _) -> Some inner
                    | _ -> None
                code |> Option.bind (fun code ->
                    match nodes.TryFind code with
                    | Some ({ Kind = SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure) } as implementation)
                        when valid cell.Initial && valid code && valid body &&
                             not (externalImplementations.Contains code) &&
                             applySubst implementation.Type = applySubst nodes[cell.Initial].Type &&
                             (parameters |> List.forall (fun (_, ty, formal) -> valid formal && applySubst nodes[formal].Type = applySubst ty)) &&
                             applySubst implementation.Type = applySubst (List.foldBack (fun (_, ty, _) result -> NativeType.TFun(ty, result)) parameters nodes[body].Type) ->
                        Some(Set.ofList(cell.Initial :: code :: body :: (parameters |> List.map (fun (_, _, id) -> id))))
                    | _ -> None)
            let initializerUses = incidence |> List.filter (fun edge ->
                edge.Target = binding.Id && edge.Sources = [cell.Initial] && Hyperedge.isStructural edge)
            match binding.Kind, parents, owners, formation, initializerUses, ExplicitDemand.direct graph cell.Initial with
            | SemanticKind.Binding(_, true, false, None), [definition], [activation], Some formation, [initializerUse], Ok None
                when binding.Metadata.TryFind "SourceBinding.Local" = Some(MetadataValue.Bool true) &&
                     cell.Captures.IsEmpty && cell.Borrows.IsEmpty && not cell.Reads.IsEmpty &&
                     not (roots.Contains binding.Id) && (Set.intersect roots formation |> Set.isEmpty) &&
                     valid binding.Id && valid definition.Target && valid activation.Owner && valid activation.Body &&
                     // Attached binding children are canonical incidence even
                     // before a recipe records a matching edge. An absent row
                     // is no competing use; duplicates still fail validation.
                     (recorded |> List.filter (fun edge -> key edge = key initializerUse) |> List.length) <= 1 ->
                let slots = activation.Slots |> List.indexed
                let uniqueSlots = slots |> List.forall (fun (_, slot) ->
                    let parents = uses.TryFind slot.Statement |> Option.defaultValue [] |> List.filter Hyperedge.isStructural
                    match nodes.TryFind slot.Statement, parents with
                    | Some statement, [edge] ->
                        valid slot.Statement && valid slot.Parent && statement.Parent = Some slot.Parent &&
                        edge.Target = slot.Parent && edge.Ordinal = slot.Ordinal
                    | _ -> false)
                let slotOf id =
                    slots |> List.choose (fun (index, slot) ->
                        if (bodyParticipants slot.Statement).Contains id then Some index else None)
                    |> function [index] -> Some index | _ -> None
                let bindingAt = slotOf binding.Id
                let replacing = cell.Writes |> List.choose (fun (site, _, value) ->
                    match slots |> List.tryFind (fun (_, slot) -> slot.Statement = site), bindingAt with
                    | Some(index, _), Some first when first < index && valid site && valid value -> Some(index, site)
                    | _ -> None)
                let beforeEveryRead = replacing |> List.filter (fun (at, _) ->
                    cell.Reads |> Set.forall (fun read ->
                        valid read && CallableIngress.tryExecutionOwner ingress read = Some activation.Owner &&
                        (slotOf read |> Option.exists (fun later -> at < later))))
                match uniqueSlots, beforeEveryRead with
                | true, (_, writer) :: _ ->
                    let participants =
                        [ cell.Participants; formation; roots
                          Set.ofList [activation.Owner; activation.Body; writer]
                          activation.Slots |> List.collect (fun slot -> [slot.Parent; slot.Statement]) |> Set.ofList ] |> Set.unionMany
                    Some(binding.Id, { Binding = binding.Id; Initializer = cell.Initial; Definition = definition
                                       InitializerUse = Some initializerUse; ExcludesBinding = false; Participants = participants })
                | _ -> None
            | _ -> None)
        |> Map.ofSeq
    let initializers = Map.fold (fun found id proof -> Map.add id proof found) initializers overwritten
    { Formals = formals |> Map.filter (fun _ proof -> admitted.Contains proof.Implementation)
      Calls = calls |> Map.filter (fun _ proof -> admitted.Contains proof.Implementation)
      Inactivity = inactivity
      Initializers = initializers }

let edges (reading: Reading) =
    [ for proof in reading.Formals.Values do
          yield { Class = EdgeClass.Demand; Role = EdgeRole.OrdinaryUnusedFormal; Target = proof.Formal; Ordinal = proof.Ordinal
                  Sources = proof.Implementation :: (proof.Participants.Remove proof.Implementation |> Set.toList) }
      for call in reading.Calls.Values do
          for ordinal in call.Omitted do
              yield { Class = EdgeClass.Demand; Role = EdgeRole.OrdinaryUnusedActual; Target = call.Site; Ordinal = ordinal
                      Sources = [call.Implementation; call.Parameters[ordinal]; call.Actuals[ordinal]; call.Callee]
                                @ (call.Participants |> Set.toList) }
      for inactive in reading.Inactivity.Values do
          let entry, _, participants, _ = inactivitySupport inactive
          yield { Class = EdgeClass.Demand; Role = EdgeRole.OrdinaryInactiveImplementation
                  Target = inactive.Implementation; Ordinal = inactive.Parameters.Length
                  Sources = [entry; inactive.Body]
                            @ inactive.Parameters
                            @ Set.toList participants
                            @ Set.toList inactive.Excluded
                            @ Set.toList inactive.Calls }
      for initializer in reading.Initializers.Values do
          yield { Class = EdgeClass.Demand; Role = EdgeRole.OrdinaryUnusedBindingInitializer
                  Target = initializer.Binding; Ordinal = initializer.Definition.Ordinal
                  Sources = [initializer.Initializer; initializer.Definition.Target]
                            @ (initializer.Participants.Remove initializer.Initializer |> Set.remove initializer.Definition.Target |> Set.toList) } ]

/// Recompute against the immutable graph and require its exact current joint
/// rows. An old codata/edge projection supplies no independent authority, and
/// an absent or extra relation is a located failure, never an empty admission.
let private validate graph : Result<Reading, WitnessProjectionFailure list> =
    let derived = analyze graph
    // No claimed inactivity is no exclusion. A held claim is checked against
    // the complete current family, including new callers and negative uses.
    let claimed =
        graph.Edges |> List.choose (fun edge ->
            if edge.Role = EdgeRole.OrdinaryInactiveImplementation then Some edge.Target else None) |> Set.ofList
    let fresh = { derived with Inactivity = derived.Inactivity |> Map.filter (fun implementation _ -> claimed.Contains implementation) }
    let expected = edges fresh
    let actual = graph.Edges |> List.filter owned
    if (expected |> List.map key |> List.sort) = (actual |> List.map key |> List.sort) then Ok fresh
    else
        let targets = (expected @ actual) |> List.map _.Target |> Set.ofList
        targets |> Set.toList |> List.choose (fun target ->
            let expectedAt = expected |> List.filter (fun edge -> edge.Target = target)
            let actualAt = actual |> List.filter (fun edge -> edge.Target = target)
            if (expectedAt |> List.map key |> List.sort) = (actualAt |> List.map key |> List.sort) then None
            else
              let reason =
                  if expectedAt @ actualAt |> List.exists (fun edge -> edge.Role = EdgeRole.OrdinaryInactiveImplementation) then
                      sprintf "PSG settlement (OrdinaryDemand inactivity) did not settle the demand relations for node %d: the published rows do not match the current complete use proof." (NodeId.value target)
                  else
                      sprintf "PSG settlement (OrdinaryDemand) did not settle the ordinary-demand relations for node %d: the published OrdinaryUnusedFormal/OrdinaryUnusedActual rows do not match the current complete use proof." (NodeId.value target)
              Some {
                Kind = WitnessProjectionFailureKind.Settlement; Occurrence = Some target
                Reason = reason
                Participants = (expectedAt @ actualAt) |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList })
        |> Error

type private Validated = { Result: Result<Reading, WitnessProjectionFailure list> }
let private cache = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, Validated>()

/// The validated reading, or the located failures of the current graph.
let tryRead graph = (cache.GetValue(graph, fun graph -> { Result = validate graph })).Result

/// Validate once for the immutable graph. Consumers must retain all demand
/// on Error; the owning diagnostic path reports the corrupted claimed proof.
let tryInactivity graph : Result<InactivityReading, WitnessProjectionFailure list> =
    tryRead graph |> Result.map (fun reading ->
        { Implementations = reading.Inactivity
          Formals = reading.Inactivity.Values |> Seq.collect _.Parameters |> Set.ofSeq
          Excluded = reading.Inactivity.Values |> Seq.map _.Excluded |> Set.unionMany
          Calls = reading.Inactivity.Values |> Seq.map _.Calls |> Set.unionMany })

/// The same failures as CCS8403 diagnostics, for a source stage that owns a diagnostic list.
let diagnostics (graph: SemanticGraph) (failures: WitnessProjectionFailure list) : Reports.Diagnostic list =
    failures |> List.map (fun failure ->
        let site = failure.Occurrence |> Option.bind graph.Nodes.TryFind
        let code = if failure.Reason.StartsWith "PSG settlement (OrdinaryDemand inactivity)" then "CCS8415" else "CCS8403"
        ({ Severity = Reports.NativeDiagnosticSeverity.Error; Code = code; Message = failure.Reason
           Range = site |> Option.map _.Range |> Option.defaultValue { File = ""; Start = { Line = 0; Column = 0 }; End = { Line = 0; Column = 0 } }
           RelatedNodes = Option.toList failure.Occurrence @ (failure.Participants |> Set.toList)
           Reachability = Reports.ReachabilityContext.Reachable } : Reports.Diagnostic))

/// A reader with no diagnostic channel of its own. A mismatch between the
/// published rows and the current proof stops here, naming the nodes.
let read graph =
    match tryRead graph with
    | Ok reading -> reading
    | Error failures ->
        let sites = failures |> List.choose _.Occurrence |> List.map (NodeId.value >> string) |> String.concat ", "
        invalidOp (sprintf "PSG settlement (OrdinaryDemand) did not settle the ordinary-demand relations for the current graph: the published OrdinaryUnusedFormal/OrdinaryUnusedActual rows do not match the current complete use proof at nodes [%s]." sites)

let parameters graph implementation =
    (read graph).Formals.Values |> Seq.filter (fun proof -> proof.Implementation = implementation) |> Seq.map _.Formal |> Set.ofSeq

/// Exact actual occurrences whose computation is not entered at this call.
let deferredActuals graph site =
    (read graph).Calls.TryFind site |> Option.map (fun call -> Set.difference call.Omitted call.Eager) |> Option.defaultValue Set.empty

/// Source coverage may omit only nodes with no remaining demanding use. Shared
/// nodes used elsewhere remain required. This changes neither IsReachable nor
/// source/proof incidence and does not claim an emitted operation for a skip.
/// Each deferred node is keyed to the omissions whose actual contains it.
let private deferralsFrom graph (reading: Reading) : Map<NodeId, Set<OrdinaryOmission>> =
    let omitted = reading.Calls.Values |> Seq.collect (fun call ->
        Set.difference call.Omitted call.Eager |> Seq.map (fun ordinal ->
            call.Site, ordinal, call.Actuals[ordinal])) |> Set.ofSeq
    let calls = omitted |> Set.map (fun (site, ordinal, actual) ->
        ({ Site = site; Origin = OrdinaryOmissionOrigin.CallArgument ordinal
           Actual = actual }: OrdinaryOmission))
    let initializers = reading.Initializers.Values |> Seq.map (fun initializer ->
        ({ Site = initializer.Binding; Origin = OrdinaryOmissionOrigin.BindingInitializer
           Actual = initializer.Initializer }: OrdinaryOmission)) |> Set.ofSeq
    let omissions = Set.union calls initializers
    let definitions = reading.Initializers.Values |> Seq.choose (fun proof ->
        if proof.ExcludesBinding then Some(key proof.Definition) else proof.InitializerUse |> Option.map key) |> Set.ofSeq
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
    let containing = omissions |> Set.toList |> List.map (fun omission ->
        let seeds =
            match omission.Origin with
            | OrdinaryOmissionOrigin.CallArgument _ -> [omission.Actual]
            | OrdinaryOmissionOrigin.BindingInitializer ->
                if reading.Initializers[omission.Site].ExcludesBinding then [omission.Site; omission.Actual] else [omission.Actual]
        omission, expand seeds Set.empty)
    let candidates = containing |> List.map snd |> Set.unionMany
    let roots = graph.DeclarationRoots |> List.map fst |> Set.ofList
    let rec retain found =
        let next = found |> Set.filter (fun id ->
            not (roots.Contains id) &&
            (uses.TryFind id |> Option.defaultValue [] |> List.forall (fun edge ->
                found.Contains edge.Target ||
                (edge.Class = EdgeClass.Reference && edge.Role = EdgeRole.Member) ||
                definitions.Contains(key edge) ||
                (edge.Class = EdgeClass.Structural && edge.Role = EdgeRole.Argument && omitted.Contains(edge.Target, edge.Ordinal, id)))))
        if next = found then found else retain next
    retain candidates |> Seq.map (fun id ->
        id, containing |> List.filter (snd >> Set.contains id) |> List.map fst |> Set.ofList) |> Map.ofSeq

let private deferredFrom graph reading = deferralsFrom graph reading |> Map.keys |> Set.ofSeq

let deferredOnly graph = deferredFrom graph (read graph)
let tryDeferredOnly graph = tryRead graph |> Result.map (deferredFrom graph)

/// Each node that only omitted actuals demand, with the omission relations
/// whose actual contains it. A call among these nodes is never entered. The
/// static string pool excludes the same nodes and states these relations as the
/// premise of each literal it does not place (`tryDeferrals`); the calls that
/// reach a formal are read through `Baker.Ingredients.FormalDemand`.
let deferrals graph = deferralsFrom graph (read graph)

/// The same reading, or the located failures of the current graph, for a stage
/// that owns a diagnostic list.
let tryDeferrals graph = tryRead graph |> Result.map (deferralsFrom graph)

let private inactivityProjection (graph: SemanticGraph) (reading: Reading) : Map<NodeId, OrdinaryInactivityProjection> =
    reading.Inactivity |> Map.map (fun _ inactive ->
        let entry, roots, participants, currentUses = inactivitySupport inactive
        let uses = currentUses |> Map.map (fun _ uses -> uses |> List.map key |> List.sort)
        let support =
            [inactive.Implementation; entry; inactive.Body] @ inactive.Parameters @
            (roots |> List.map fst) @ Set.toList participants @ Set.toList inactive.Excluded @ Set.toList inactive.Calls @
            (uses |> Map.toList |> List.collect (fun (source, edges) ->
                source :: (edges |> List.collect (fun (_, _, _, sources, target) -> target :: sources))))
            |> Set.ofList
        { Implementation = inactive.Implementation
          Entry = entry
          Body = inactive.Body
          Parameters = inactive.Parameters
          Roots = roots |> List.map fst |> Set.ofList
          Excluded = inactive.Excluded
          Calls = inactive.Calls
          Uses = uses
          SourcePremises =
            support |> Set.toList |> List.choose (fun id ->
                graph.Nodes.TryFind id |> Option.map (fun node ->
                    id, Clef.Compiler.Baker.Ingredients.Boundaries.premise node)) |> Map.ofList })

/// Reuse the current demand proof when another source recipe consumes an
/// exclusion. No claim means no dependency on an unrelated omission recipe.
let tryInactivityProjection graph =
    if graph.Edges |> List.exists (fun edge -> edge.Role = EdgeRole.OrdinaryInactiveImplementation) then
        tryRead graph |> Result.map (inactivityProjection graph)
    else Ok Map.empty

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
      DeferredOnly = deferredFrom graph reading
      Inactivity = inactivityProjection graph reading }

/// Final source projection. Analysis and the complete use census belong to CCS;
/// consumers receive only these settled transport and occurrence decisions.
let project graph = projectionFrom graph (read graph)

/// Compute and validate the final use proof once while the source stage owns
/// publication. An absent or extra relation cannot become an empty admission.
let projectValidated graph : Result<OrdinaryDemandProjection, WitnessProjectionFailure list> =
    match Clef.Compiler.Baker.Ingredients.BindingDemand.failures graph with
    | [] -> tryRead graph |> Result.map (projectionFrom graph)
    | failures -> Error failures

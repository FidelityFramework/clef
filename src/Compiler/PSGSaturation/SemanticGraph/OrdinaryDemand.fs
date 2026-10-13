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
type InactiveImplementation = {
    Implementation: NodeId
    Body: NodeId
    Parameters: NodeId list
    Excluded: Set<NodeId>
    Calls: Set<NodeId>
    Family: CallableIngress.Family
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
                when not (externalImplementations.Contains code.Id) && valid code.Id && valid body && directUses proof ->
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
    let structuralParents =
        incidence |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge.Target))
        |> List.groupBy fst |> List.map (fun (child, rows) -> child, rows |> List.map snd |> List.distinct) |> Map.ofList
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
                let rec ownedByImplementation seen id =
                    match CallableIngress.tryExecutionOwner ingress id with
                    | Some owner when owner = code.Id -> true
                    | Some owner when owner = id ->
                        // A nested lambda owns itself; its own owner is read
                        // at its unique structural parent.
                        match structuralParents.TryFind id with
                        | Some [parent] when not (Set.contains parent seen) -> ownedByImplementation (Set.add id seen) parent
                        | _ -> false
                    | Some owner when not (Set.contains owner seen) -> ownedByImplementation (Set.add owner seen) owner
                    | _ -> false
                let excluded = nodes.Keys |> Seq.filter (fun id ->
                    id <> code.Id && ownedByImplementation Set.empty id) |> Set.ofSeq
                let calls = excluded |> Set.filter (fun id ->
                    match nodes[id].Kind with SemanticKind.Application _ -> true | _ -> false)
                Some(code.Id,
                    { Implementation = code.Id; Body = body
                      Parameters = parameters |> List.map (fun (_, _, id) -> id)
                      Excluded = excluded; Calls = calls; Family = family })
            | _ -> None) |> Map.ofSeq
    let roots = graph.DeclarationRoots |> List.map fst |> Set.ofList
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
          yield { Class = EdgeClass.Demand; Role = EdgeRole.OrdinaryInactiveImplementation
                  Target = inactive.Implementation; Ordinal = inactive.Parameters.Length
                  Sources = [inactive.Family.Evidence.Entry.Value; inactive.Body]
                            @ inactive.Parameters
                            @ Set.toList inactive.Family.Evidence.Participants
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
        let evidence = inactive.Family.Evidence
        let uses = evidence.Uses |> Map.map (fun _ uses -> uses |> List.map key |> List.sort)
        let support =
            [inactive.Implementation; evidence.Entry.Value; inactive.Body] @ inactive.Parameters @
            (evidence.Roots |> List.map fst) @ Set.toList inactive.Excluded @ Set.toList inactive.Calls @
            (uses |> Map.toList |> List.collect (fun (source, edges) ->
                source :: (edges |> List.collect (fun (_, _, _, sources, target) -> target :: sources))))
            |> Set.ofList
        { Implementation = inactive.Implementation
          Entry = evidence.Entry.Value
          Body = inactive.Body
          Parameters = inactive.Parameters
          Roots = evidence.Roots |> List.map fst |> Set.ofList
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

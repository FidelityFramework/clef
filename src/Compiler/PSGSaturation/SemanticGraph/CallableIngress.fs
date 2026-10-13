// SPDX-License-Identifier: MIT
/// Observed actual arguments are not a closed callable ingress contract. This
/// reader proves the complete incoming use graph before a formal or a returned
/// alias may inherit those arguments' callable identities. It never forces codata.
module Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open System.Collections.Generic
module Incidence = Clef.Compiler.Baker.Ingredients.Closures
module ControlInputs = Clef.Compiler.PSGSaturation.SemanticGraph.ContinuationCurrentInputs
module Borrows = Clef.Compiler.Baker.Ingredients.SourceStorageBorrows
module AggregateProjections = Clef.Compiler.Baker.Ingredients.CallableAggregateProjections

type Call = { Site: NodeId; Implementation: NodeId; Parameters: NodeId list; Arguments: NodeId list }
type Evidence = {
    Entry: NodeId option
    Roots: (NodeId * DeclRoot) list
    Formals: Set<NodeId>
    Implementations: Set<NodeId>
    Participants: Set<NodeId>
    /// Consuming any of these protocols requires current whole-graph lazy
    /// validation; Participants is not an exhaustive selective proof key.
    UsedLazyForces: Set<NodeId>
    Uses: Map<NodeId, Hyperedge list>
    Calls: Call list
}
/// The existing complete incoming-use family, before requiring a connection
/// from every member to the program entry. A missing connection is meaningful
/// only with this valid complete census; it is not inferred from empty calls.
type Family = { Evidence: Evidence; Activated: Set<NodeId> }
type FormalInputs = {
    Inputs: (NodeId * NodeId) list
    Closure: Evidence
    Participants: Set<NodeId>
}
type Access = { Source: NodeId; Participants: Set<NodeId> }
type StorageAccess = {
    Source: NodeId
    /// Exact current writes, or the immutable initializer at its formation.
    Inputs: (NodeId * NodeId) list
    /// A mutable capture preserves the logical cell, not its formation value.
    /// Readers must account for every current store to this shared cell.
    SharedCell: NodeId option
    /// State zero at the checked initial resume, independently of later writes.
    InitialState: (NodeId * bigint) option
    Participants: Set<NodeId>
}
type Reading = private {
    Evidence: Map<NodeId, Evidence>
    RetainedEvidence: Map<NodeId, Evidence>
    Access: NodeId -> Access option
    StorageAccess: NodeId -> StorageAccess option
    SlotAccess: NodeId -> NodeId -> StorageAccess option
    ValueIdentity: NodeId -> Access option
    Correspondence: NodeId -> NodeId -> Set<NodeId> option
    ClosedImplementation: NodeId -> Evidence option
    Family: NodeId -> Family option
    ExecutionOwner: NodeId -> NodeId option
}
type private Closed = { Dependencies: Set<NodeId>; Callers: Set<NodeId>; Participants: Set<NodeId>; UsedLazyForces: Set<NodeId>; Calls: Call list; Valid: bool }

let analyzeWith (graph: SemanticGraph) (resolution: CallableOrigins.Resolution) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let initialization = ProgramInitialization.read graph
    let entry = initialization |> Option.map _.EntryLambda
    let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
    let edgeKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let grouped (rows: Hyperedge list) =
        rows |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ values -> values |> List.map snd |> List.distinctBy edgeKey)
    let uses = incidence |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) |> grouped
    let recorded = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) |> grouped
    let getUses id = uses.TryFind id |> Option.defaultValue []
    let getRecorded id = recorded.TryFind id |> Option.defaultValue [] |> List.filter (fun edge -> nodes.ContainsKey edge.Target || not (graph.Nodes.ContainsKey edge.Target))
    // Binding children and other owned syntax are authoritative even before
    // their Attached incidence has been materialized. Independent resident
    // references are additional uses, never erased by this structural view.
    let observedUses id = getUses id @ getRecorded id |> List.distinctBy edgeKey
    let owners =
        nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.Lambda(parameters, _, _, _, _) -> parameters |> List.map (fun (_, _, formal) -> formal, node.Id)
            | _ -> []) |> Seq.groupBy fst
        |> Seq.choose (fun (formal, rows) -> match rows |> Seq.map snd |> Seq.distinct |> Seq.toList with [owner] -> Some(formal, owner) | _ -> None)
        |> Map.ofSeq
    let structuralParents =
        incidence |> List.filter Hyperedge.isStructural |> grouped
    let activation occurrence =
        let rec visit seen pending found missing =
            match pending with
            | [] -> if not missing && Set.count found = 1 then Some(Set.minElement found) else None
            | id :: rest when Set.contains id seen -> visit seen rest found missing
            | id :: rest ->
                let seen = Set.add id seen
                match nodes.TryFind id with
                | Some { Kind = SemanticKind.Lambda _ } -> visit seen rest (Set.add id found) missing
                | _ ->
                    match structuralParents.TryFind id with
                    | Some parents when not parents.IsEmpty -> visit seen ((parents |> List.map _.Target) @ rest) found missing
                    | _ -> visit seen rest found true
        visit Set.empty [occurrence] Set.empty false
    let complete site =
        resolution.Calls.TryFind site |> Option.filter (fun call -> call.Complete && not call.Unknown && not call.Targets.IsEmpty)
    let discards (application: SemanticNode) callee argument =
        match nodes.TryFind callee, nodes.TryFind argument, applySubst application.Type with
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Operators; Operation = "ignore" }; Type = calleeType },
          Some actual, NativeType.TApp(unitType, []) when unitType.NTUKind = Some NTUKind.NTUunit && application.Children = [callee; argument] ->
            match applySubst calleeType with
            | NativeType.TFun(domain, result) ->
                applySubst domain = applySubst actual.Type && applySubst result = applySubst application.Type
            | _ -> false
        | _ -> false
    let row site (target: CallableOrigins.CallTarget) =
        { Site = site; Implementation = target.Lambda; Parameters = target.Parameters |> List.map (fun (_, _, formal) -> formal); Arguments = target.Arguments }
    let invocations implementation =
        resolution.Calls |> Map.toList |> List.choose (fun (site, call) ->
            if call.Targets |> List.exists (fun target -> target.Lambda = implementation) then Some(site, call) else None)
    let environmentOrigins = lazy (ClosureEnvironments.origins graph)
    let environmentOwner id = environmentOrigins.Value.TryFind id
    let environmentCalls = lazy (ClosureEnvironments.callEnvironments graph)
    let capturedValue = ClosureEnvironments.tryCapturedValue graph
    let sourceDeclaration = ClosureEnvironments.trySourceDeclaration graph
    let scopedDeclarations = lazy (ScopedDeclarations.read graph)
    let promotedReferences = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.CallableReferenceOrigin) |> List.map _.Target |> Set.ofList
    let capturedReads owner slot =
        nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.EnvironmentRead(environment, actual) when actual = slot && environmentOwner environment = Some owner -> Some node.Id
            | _ -> None) |> Seq.toList
    let captureUses =
        nodes.Values |> Seq.collect (fun node ->
            let captures =
                match node.Kind with
                | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures) | SemanticKind.LazyExpr(_, captures) -> captures
                | _ -> []
            captures |> List.choose (fun capture -> capture.SourceNodeId |> Option.map (fun source -> source, (node, capture))))
        |> Seq.groupBy fst |> Seq.map (fun (source, rows) -> source, rows |> Seq.map snd |> Seq.toList) |> Map.ofSeq
    let mutableCells = lazy (MutableCallableStorage.sourceFamilies graph |> fst)
    let lazyThunk = LazyValues.closedThunk graph
    let emptyClosed = { Dependencies = Set.empty; Callers = Set.empty; Participants = Set.empty; UsedLazyForces = Set.empty; Calls = []; Valid = true }
    let classify implementation =
        let mutable proof = emptyClosed
        let reject () = proof <- { proof with Valid = false }
        let dependency id = proof <- { proof with Dependencies = Set.add id proof.Dependencies }
        let rec follow pending seen =
            match pending with
            | [] -> ()
            | id :: rest when Set.contains id seen -> follow rest seen
            | id :: rest ->
                let seen = Set.add id seen
                proof <- { proof with Participants = Set.add id proof.Participants }
                let mutable next = rest
                let forward target = next <- target :: next
                if graph.DeclarationRoots |> List.exists (fun (root, _) -> root = id) then reject ()
                let storage binding =
                    mutableCells.Value.TryFind binding |> Option.filter (fun _ -> activation binding |> Option.isSome)
                let retain (cell: MutableCallableStorage.SourceFamily) =
                    proof <- { proof with Participants = Set.union proof.Participants cell.Participants }
                match nodes.TryFind id with
                | Some { Kind = SemanticKind.Binding(_, _, _, Some _) } -> reject ()
                | Some { Kind = SemanticKind.Binding(_, true, _, _) } ->
                    match storage id with
                    | Some cell ->
                        retain cell
                        for read in cell.Reads do forward read
                        for writer, _, _ in cell.Writes do
                            match activation writer with
                            | Some owner when Some owner <> entry -> dependency owner
                            | Some _ -> ()
                            | None -> reject ()
                    | None -> reject ()
                | Some node when (Clef.Compiler.Baker.Ingredients.Boundaries.premise node).HasExtern -> reject ()
                | None -> reject ()
                | _ -> ()
                for edge in observedUses id do
                    let target = nodes.TryFind edge.Target
                    let declared = getUses id |> List.exists (fun expected -> edgeKey expected = edgeKey edge)
                    match target, edge.Class, edge.Role with
                    | Some { Kind = SemanticKind.ModuleDef(_, members) }, EdgeClass.Reference, EdgeRole.Member
                        when edge.Sources = [id] && List.tryItem edge.Ordinal members = Some id -> ()
                    | Some { Kind = SemanticKind.VarRef(_, Some source) }, EdgeClass.Reference, EdgeRole.Definition
                        when declared && source = id && edge.Sources = [id] -> forward edge.Target
                    | Some { Kind = SemanticKind.EnvironmentCreate(owner, initializers) }, EdgeClass.Reference, EdgeRole.EnvironmentInitializer
                        when declared && List.tryItem edge.Ordinal initializers |> Option.exists (fun (_, value) -> value = id) ->
                        match ClosureEnvironments.capturedInitializers graph owner with
                        | Some values ->
                            let selected = values |> List.filter (fun (slot, value, mutableCell) ->
                                value = id && (not mutableCell ||
                                    (slot = id && storage id |> Option.exists (fun cell ->
                                        cell.Captures.Contains edge.Target))))
                            if selected.IsEmpty then reject () else
                            match nodes.TryFind owner with
                            | Some { Kind = SemanticKind.ClosureValue(code, _) } ->
                                dependency code
                                for slot, _, _ in selected do capturedReads owner slot |> List.iter forward
                            | _ -> reject ()
                        | None -> reject ()
                    | Some node, EdgeClass.Structural, _ when declared ->
                        match node.Kind, edge.Role with
                        | SemanticKind.Binding(_, true, _, None), _ when node.Children = [id] ->
                            match storage node.Id with
                            | Some cell when cell.Initial = id -> retain cell; forward node.Id
                            | _ -> reject ()
                        | SemanticKind.Set(destination, value), _ ->
                            let cell = mutableCells.Value.Values |> Seq.tryFind (fun cell ->
                                cell.Writes |> List.contains (node.Id, destination, value))
                            match cell |> Option.bind (fun cell -> storage cell.Binding) with
                            | Some cell when id = value -> retain cell; forward cell.Binding
                            | Some cell when id = destination -> retain cell
                            | _ -> reject ()
                        | SemanticKind.EnvironmentWrite(_, slot, value), _ ->
                            match storage slot with
                            | Some cell when id = value && List.contains (node.Id, node.Id, value) cell.Writes ->
                                retain cell; forward cell.Binding
                            | _ -> reject ()
                        | SemanticKind.Binding(_, false, _, None), _ when node.Children = [id] -> forward node.Id
                        | SemanticKind.TypeAnnotation(value, _), _ when value = id -> forward node.Id
                        | SemanticKind.EagerExpr value, _ when value = id && ExplicitDemand.operand graph node.Id = Some id -> forward node.Id
                        | SemanticKind.Sequential values, _ -> if List.tryLast values = Some id then forward node.Id
                        | SemanticKind.IfThenElse(_, yes, no), (EdgeRole.ThenBranch | EdgeRole.ElseBranch)
                            when id = yes || no = Some id -> forward node.Id
                        | SemanticKind.Match(_, cases), _ when cases |> List.exists (fun branch -> branch.Body = id) -> forward node.Id
                        | SemanticKind.CaseElimination(_, cases), _ when cases |> List.exists (fun branch -> branch.Body = id) -> forward node.Id
                        | SemanticKind.RecordExpr _, _
                        | SemanticKind.TupleExpr _, _
                        | SemanticKind.UnionCase _, _
                        | SemanticKind.DUConstruct _, _ ->
                            // Construction is a use of the value, not an
                            // invocation. Follow its exact typed slots from
                            // the same origin census; unknown storage cannot
                            // certify the complete incoming family.
                            match resolution.Aggregates.TryFind node.Id with
                            | Some aggregate when aggregate.UnknownOrigins.IsEmpty &&
                                                  not aggregate.Alternatives.IsEmpty &&
                                                  (aggregate.Alternatives |> List.forall (fun alternative ->
                                                      alternative.Slots |> List.forall (fun slot -> slot.UnknownOrigins.IsEmpty))) &&
                                                  (aggregate.Alternatives |> List.exists (fun alternative ->
                                                      alternative.Construction = node.Id &&
                                                      (alternative.Slots |> List.exists (fun slot ->
                                                          slot.Values |> List.exists seen.Contains)))) ->
                                for KeyValue(source, inputs) in aggregate.Dependencies do
                                    proof <- { proof with Participants = Set.union proof.Participants (Set.ofList (source :: inputs)) }
                                forward node.Id
                            | _ -> reject ()
                        | (SemanticKind.FieldGet _ | SemanticKind.TupleGet _ | SemanticKind.DUEliminate _), _ ->
                            match AggregateProjections.read resolution node.Id with
                            | Some projection when projection.Aggregate = id ->
                                proof <- { proof with Participants = Set.union proof.Participants projection.Participants }
                                if projection.Inputs |> List.exists seen.Contains then forward node.Id
                            | _ ->
                                match AggregateProjections.tryTerminal resolution node.Id with
                                | Some(aggregate, participants) when aggregate = id ->
                                    proof <- { proof with Participants = Set.union proof.Participants participants }
                                | _ -> reject ()
                        | SemanticKind.DUGetTag(subject, _), EdgeRole.Subject when subject = id ->
                            proof <- { proof with Participants = Set.add node.Id proof.Participants }
                        | SemanticKind.Lambda(parameters, _, _, _, _), EdgeRole.Parameter
                            when parameters |> List.exists (fun (_, _, formal) -> formal = id) -> ()
                        | SemanticKind.ClosureValue(code, _), EdgeRole.Body when code = id -> forward node.Id
                        | SemanticKind.LazyValue(code, _), EdgeRole.Body when code = id ->
                            match lazyThunk code with
                            | Some lazyProof when lazyProof.Scope = LazyValues.IngressScope.WholeCurrentGraph && lazyProof.Formations.Contains node.Id ->
                                proof <-
                                    { proof with
                                        Participants = Set.union proof.Participants lazyProof.Participants
                                        UsedLazyForces = Set.union proof.UsedLazyForces lazyProof.UsedLazyForces }
                            | _ -> reject ()
                        | SemanticKind.EnvironmentReference value, EdgeRole.Subject when value = id ->
                            // Only the proven environment actual of an exact call
                            // can consume this projection as part of the value.
                            let consumers = getUses node.Id
                            if consumers.IsEmpty || consumers |> List.exists (fun useSite ->
                                useSite.Role <> EdgeRole.Argument || complete useSite.Target |> Option.isNone ||
                                environmentCalls.Value.TryFind useSite.Target <> Some(useSite.Ordinal, node.Id)) then reject ()
                        | SemanticKind.Application(callee, _), EdgeRole.Callee when callee = id ->
                            match complete node.Id, activation node.Id with
                            | Some call, Some caller ->
                                proof <-
                                    { proof with
                                        Callers = Set.add caller proof.Callers
                                        Calls = (call.Targets |> List.map (row node.Id)) @ proof.Calls }
                                if Some caller <> entry then dependency caller
                            | _ -> reject ()
                        | SemanticKind.Application(callee, [argument]), EdgeRole.Argument
                            when edge.Ordinal = 0 && argument = id && discards node callee argument ->
                            // The resolved primitive evaluates and discards
                            // this value; it never invokes the stored code.
                            proof <- { proof with Participants = Set.union proof.Participants (Set.ofList [callee; node.Id]) }
                        | SemanticKind.Application(_, arguments), EdgeRole.Argument
                            when List.tryItem edge.Ordinal arguments = Some id ->
                            match complete node.Id with
                            | Some call ->
                                for target in call.Targets do
                                    match List.tryItem edge.Ordinal target.Parameters with
                                    | Some (_, _, formal) ->
                                        match scopedDeclarations.Value.Participants.TryFind formal with
                                        | Some participants ->
                                            // A declared synchronous callback is activated
                                            // inside this exact invocation's lifetime. Its
                                            // native/library body need not contain a source
                                            // Invoke node. Keep that activation dependency
                                            // distinct from an invented callback argument list.
                                            match activation node.Id with
                                            | Some caller ->
                                                proof <-
                                                    { proof with
                                                        Callers = Set.add caller proof.Callers
                                                        Participants = Set.union proof.Participants (Set.add node.Id participants)
                                                        Calls = row node.Id target :: proof.Calls }
                                                if Some caller <> entry then dependency caller
                                            | None -> reject ()
                                        | None -> dependency target.Lambda; forward formal
                                    | None -> reject ()
                            | None -> reject ()
                        | SemanticKind.Lambda(_, body, _, _, _), EdgeRole.Body when body = id ->
                            dependency node.Id
                            let callers = invocations node.Id
                            // The complete enclosing family owns whether this
                            // returned value can be formed. No observed calls
                            // is admissible only with that dependency's full
                            // census; active ingress still requires connection
                            // to the program entry below.
                            for site, call in callers do
                                if not call.Complete || call.Unknown then reject () else forward site
                        | _ -> reject ()
                    | _ -> reject ()
                // Source captures are independent uses even when the value has
                // no structural edge into the nested deferred body yet.
                for node, capture in captureUses.TryFind id |> Option.defaultValue [] do
                    match node.Kind with
                    | SemanticKind.Lambda _ when not capture.IsMutable -> dependency node.Id
                    | SemanticKind.Lambda _ when storage id |> Option.exists (fun cell -> cell.Captures.Contains node.Id) ->
                        dependency node.Id
                    | _ -> reject ()
                follow next seen
        follow [implementation] Set.empty
        proof
    let candidates = Dictionary<NodeId, Closed>()
    let candidate id =
        match candidates.TryGetValue id with
        | true, value -> Some value
        | _ ->
            match nodes.TryFind id with
            | Some { Kind = SemanticKind.Lambda _ } ->
                let value = classify id
                candidates.Add(id, value)
                Some value
            | _ -> None
    let familyCache = Dictionary<NodeId, (Set<NodeId> * Set<NodeId>) option>()
    let findFamily implementation =
        match entry with
        | None -> None
        | Some root ->
            let rec collect pending seen valid =
                match pending with
                | [] -> if valid then Some seen else None
                | id :: rest when id = root || Set.contains id seen -> collect rest seen valid
                | id :: rest ->
                    match candidate id with
                    | Some candidate -> collect (Set.toList candidate.Dependencies @ rest) (Set.add id seen) (valid && candidate.Valid)
                    | None -> None
            collect [implementation] Set.empty true |> Option.map (fun required ->
                let rec connect reached =
                    let next = required |> Set.fold (fun reached id ->
                        if not (Set.intersect candidates[id].Callers reached).IsEmpty then Set.add id reached else reached) reached
                    if next = reached then reached else connect next
                required, connect (Set.singleton root))
    let family implementation =
        match familyCache.TryGetValue implementation with
        | true, value -> value
        | _ ->
            let value = findFamily implementation
            familyCache.Add(implementation, value)
            value
    let closed implementation =
        family implementation |> Option.bind (fun (required, reached) ->
            if Set.isSubset required reached then Some required else None)
    let empty = { Entry = entry; Roots = graph.DeclarationRoots; Formals = Set.empty; Implementations = Set.empty; Participants = Set.empty; UsedLazyForces = Set.empty; Uses = Map.empty; Calls = [] }
    let merge left right =
        { left with Formals = Set.union left.Formals right.Formals
                    Implementations = Set.union left.Implementations right.Implementations
                    Participants = Set.union left.Participants right.Participants
                    UsedLazyForces = Set.union left.UsedLazyForces right.UsedLazyForces
                    Calls = List.distinct (left.Calls @ right.Calls) }
    let continuationRows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ContinuationSlotAccess) |> List.groupBy _.Target |> Map.ofList
    let originalRows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ContinuationValue) |> List.groupBy _.Target |> Map.ofList
    let checkedInstance = SchemeInstances.reader graph
    let rec originalIdentity seen id =
        if Set.contains id seen then None else
        match graph.Nodes.TryFind id with
        | None | Some { Kind = SemanticKind.Binding(_, true, _, _) } -> None
        | Some node ->
            let next =
                match checkedInstance id, node.Kind, node.Children with
                | Some instance, _, _ -> Some instance.Declaration
                | _, SemanticKind.Binding(_, false, _, _), [value]
                | _, SemanticKind.VarRef(_, Some value), _ | _, SemanticKind.TypeAnnotation(value, _), _ -> Some value
                | _, SemanticKind.EagerExpr value, [child]
                    when value = child && ExplicitDemand.operand graph id = Some value -> Some value
                | _, SemanticKind.Sequential values, children when values = children -> List.tryLast values
                | _ -> None
            match next with
            | None -> Some(id, Set.singleton id)
            | Some value when (checkedInstance id |> Option.exists (fun instance -> instance.Declaration = value)) ||
                              (graph.Nodes.TryFind value |> Option.exists (fun child -> applySubst child.Type = applySubst node.Type)) ->
                originalIdentity (Set.add id seen) value |> Option.map (fun (source, participants) -> source, Set.add id participants)
            | _ -> None
    // One complete storage census serves read occurrences and the synthetic
    // control slots. A row enumerating writers is checked against these uses.
    let storageCensuses = Dictionary<NodeId * NodeId * NodeId * NodeId, (Set<NodeId> * Set<NodeId * NodeId>) option>()
    let storageCensus generator formal root slot =
        let key = generator, formal, root, slot
        match storageCensuses.TryGetValue key with
        | true, value -> value
        | _ ->
            let validated =
                match nodes.TryFind root with
                | None -> None
                | Some storage ->
                    // Reject opaque users and borrowed access to this slot even
                    // when no additional direct FrameWrite is visible.
                    let rec visit seen pending writers =
                        match pending with
                        | [] -> Some(seen, writers)
                        | current :: rest when Set.contains current seen -> visit seen rest writers
                        | current :: rest ->
                            let seen = Set.add current seen
                            let step found (edge: Hyperedge) =
                                found |> Option.bind (fun (aliases, writers) ->
                                    let declared = getUses current |> List.exists (fun expected -> edgeKey expected = edgeKey edge)
                                    match nodes.TryFind edge.Target with
                                    | Some target when declared ->
                                        let sameType = applySubst target.Type = applySubst storage.Type
                                        let here = activation target.Id = Some generator
                                        match target.Kind, edge.Class, edge.Role with
                                        | SemanticKind.VarRef(_, Some actual), EdgeClass.Reference, EdgeRole.Definition
                                            when actual = current && sameType && here -> Some(target.Id :: aliases, writers)
                                        | SemanticKind.Binding(_, false, _, None), EdgeClass.Structural, _
                                            when target.Children = [current] && sameType && here -> Some(target.Id :: aliases, writers)
                                        | SemanticKind.TypeAnnotation(actual, _), EdgeClass.Structural, _
                                            when actual = current && sameType && here -> Some(target.Id :: aliases, writers)
                                        | SemanticKind.EagerExpr actual, EdgeClass.Structural, EdgeRole.Subject
                                            when actual = current && sameType && here && ExplicitDemand.operand graph target.Id = Some current ->
                                            Some(target.Id :: aliases, writers)
                                        | SemanticKind.Lambda(parameters, _, _, _, _), EdgeClass.Structural, EdgeRole.Parameter
                                            when target.Id = generator && current = formal && parameters |> List.exists (fun (_, _, parameter) -> parameter = current) -> Some(aliases, writers)
                                        | SemanticKind.Sequential values, EdgeClass.Structural, _
                                            when here && List.contains current values && List.tryLast values <> Some current -> Some(aliases, writers)
                                        | SemanticKind.FrameRead(actual, _), EdgeClass.Structural, EdgeRole.Subject
                                            when actual = current && here -> Some(aliases, writers)
                                        | SemanticKind.FrameBorrow(actual, other), EdgeClass.Structural, EdgeRole.Subject
                                            when actual = current && other <> slot && here -> Some(aliases, writers)
                                        | SemanticKind.FrameWrite(actual, written, value), EdgeClass.Structural, EdgeRole.Subject
                                            when actual = current && here && applySubst target.Type = Types.unitType ->
                                            Some(aliases, if written = slot then Set.add (target.Id, value) writers else writers)
                                        | _ -> None
                                    | _ -> None)
                            observedUses current |> List.fold step (Some(rest, writers))
                            |> Option.bind (fun (next, writes) -> visit seen next writes)
                    visit Set.empty [root] Set.empty
            storageCensuses.Add(key, validated)
            validated
    let controlProtocols = Dictionary<NodeId, ControlInputs.Protocol option>()
    let controlProtocol owner =
        match controlProtocols.TryGetValue owner with
        | true, value -> value
        | _ ->
            let value = ControlInputs.forOwner graph owner
            controlProtocols.Add(owner, value)
            value
    let sequenceInitializers = Dictionary<NodeId, (NodeId * NodeId) list option>()
    let captureInitializers (sequence: SemanticNode) =
        match sequenceInitializers.TryGetValue sequence.Id with
        | true, value -> value
        | _ ->
            let value = ClosureEnvironments.sequenceInitializers graph sequence
            sequenceInitializers.Add(sequence.Id, value)
            value
    let logicalCellBorrows = Dictionary<NodeId, Set<NodeId> option>()
    let logicalCellBorrowClosed cell =
        match logicalCellBorrows.TryGetValue cell with
        | true, value -> value
        | _ ->
            let rec aliases seen pending =
                match pending with
                | [] -> Some seen
                | current :: rest when Set.contains current seen -> aliases seen rest
                | current :: rest ->
                    observedUses current |> List.fold (fun found edge ->
                        found |> Option.bind (fun pending ->
                            let declared = getUses current |> List.exists (fun expected -> edgeKey expected = edgeKey edge)
                            match nodes.TryFind edge.Target with
                            | Some target when declared ->
                                let sameType = applySubst target.Type = applySubst nodes[cell].Type
                                match target.Kind, target.Children with
                                | SemanticKind.VarRef(_, Some actual), _
                                | SemanticKind.TypeAnnotation(actual, _), _ when actual = current && sameType -> Some(target.Id :: pending)
                                | SemanticKind.Binding(_, false, _, _), [actual] when actual = current && sameType -> Some(target.Id :: pending)
                                | SemanticKind.EagerExpr actual, _ when actual = current && sameType &&
                                    ExplicitDemand.operand graph target.Id = Some current -> Some(target.Id :: pending)
                                | SemanticKind.VarRef(_, Some actual), _
                                | SemanticKind.TypeAnnotation(actual, _), _
                                | SemanticKind.EagerExpr actual, _ when actual = current -> None
                                | SemanticKind.Binding(_, false, _, _), [actual] when actual = current -> None
                                | _ when Borrows.takesAddress ((=) current) ((=) current) target -> None
                                | _ -> Some pending
                            | _ -> None)) (Some rest)
                    |> Option.bind (aliases (Set.add current seen))
            let validated = aliases Set.empty [cell] |> Option.bind (fun sourceAliases ->
                let dangerous = nodes.Values |> Seq.exists (Borrows.takesAddress sourceAliases.Contains sourceAliases.Contains)
                if dangerous then None else
                let borrows = nodes.Values |> Seq.choose (fun node ->
                    Borrows.trySlot node |> Option.bind (fun (slot, kind) ->
                        if sourceAliases.Contains slot then Some(node, kind) else None)) |> Seq.toList
                borrows |> List.fold (fun proof (borrow, kind) ->
                    proof |> Option.bind (fun participants ->
                        match kind with
                        | Borrows.SlotBorrow.Frame | Borrows.SlotBorrow.Lazy -> None
                        | Borrows.SlotBorrow.Environment ->
                            // Only the existing complete sequence-formation
                            // contract can consume this writable borrow. Any
                            // ordinary/raw use would expose an additional writer.
                            let typed = applySubst borrow.Type = NativeType.TByref(applySubst nodes[cell].Type, ByrefKind.InOut)
                            if not typed || not (observedUses borrow.Id).IsEmpty ||
                               (captureUses.TryFind borrow.Id |> Option.exists (not << List.isEmpty)) then None else
                            let consumers = graph.Edges |> List.filter (fun edge ->
                                match edge.Role, edge.Sources with
                                | EdgeRole.SequenceCaptureInitializer true, [slot; value] -> slot = cell && value = borrow.Id
                                | _ -> false)
                            if consumers.IsEmpty then None else
                            consumers |> List.fold (fun found edge ->
                                found |> Option.bind (fun support ->
                                    match nodes.TryFind edge.Target with
                                    | Some ({ Kind = SemanticKind.SeqExpr(_, captures) } as sequence)
                                        when captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some cell) ->
                                        captureInitializers sequence |> Option.bind (fun values ->
                                            if values |> List.filter (fun (slot, _) -> slot = cell) <> [cell, borrow.Id] then None else
                                            Some(support |> Set.add edge.Target |> Set.add borrow.Id))
                                    | _ -> None)) (Some participants))) (Some sourceAliases))
            logicalCellBorrows.Add(cell, validated)
            validated
    // The scalar cell's identity is separate from immutable capture values and
    // from callable identity. Its constructor must preserve this exact mutable
    // binding, directly or through the checked environment-borrow contract.
    let sharedCapture owner slot =
        match nodes.TryFind owner, nodes.TryFind slot with
        | Some ({ Kind = SemanticKind.SeqExpr(generator, captures); Type = NativeType.TSeq element } as sequence),
          Some ({ Kind = SemanticKind.Binding(_, true, _, _); Children = [initializer] } as source)
            when Types.isIntegerType (applySubst source.Type) ->
            match nodes.TryFind generator, graph.Nodes.TryFind initializer with
            | Some { Kind = SemanticKind.Lambda([_, environmentType, formal], _, [], _, LambdaContext.SeqGenerator) },
              Some initial when applySubst initial.Type = applySubst source.Type &&
                                applySubst environmentType = NativeType.TSeqEnumerator(applySubst element) ->
                match nodes.TryFind formal,
                      captures |> List.filter (fun capture -> capture.SourceNodeId = Some slot),
                      captureInitializers sequence with
                | Some { Kind = SemanticKind.PatternBinding _; Type = formalType }, [capture], Some values
                    when capture.IsMutable && applySubst capture.Type = applySubst source.Type &&
                         applySubst formalType = applySubst environmentType &&
                         values.Length = captures.Length &&
                         (captures |> List.choose _.SourceNodeId |> Set.ofList).Count = captures.Length &&
                         (values |> List.map fst |> Set.ofList).Count = values.Length ->
                    match values |> List.filter (fun (source, _) -> source = slot) with
                    | [_, value] ->
                        let identity =
                            if value = slot then Some Set.empty else
                            match graph.Nodes.TryFind value with
                            | Some { Kind = SemanticKind.EnvironmentBorrow(environment, actual); Type = borrowType }
                                when actual = slot && applySubst borrowType = NativeType.TByref(applySubst source.Type, ByrefKind.InOut) ->
                                // sequenceInitializers already checks the exact
                                // closure formal and mutable capture incidence.
                                Some(Set.ofList [value; environment])
                            | _ -> None
                        identity |> Option.bind (fun borrowed ->
                          logicalCellBorrowClosed slot |> Option.map (fun cellSupport ->
                            let formation = graph.Edges |> List.filter (fun edge ->
                                edge.Target = owner &&
                                (match edge.Role with
                                 | EdgeRole.SequenceCaptureFormation | EdgeRole.SequenceCaptureInitializer _ -> true
                                 | _ -> false))
                            let formationNodes = formation |> List.collect (fun edge -> edge.Target :: edge.Sources)
                            let environments = formation |> List.collect (fun edge ->
                                match edge.Role, edge.Sources with
                                | EdgeRole.SequenceCaptureFormation, closure :: _ ->
                                    match graph.Nodes.TryFind closure with
                                    | Some { Kind = SemanticKind.ClosureValue(_, environment) } ->
                                        match graph.Nodes.TryFind environment with
                                        | Some { Kind = SemanticKind.EnvironmentCreate(_, initializers) } ->
                                            environment :: (initializers |> List.collect (fun (source, value) -> [source; value]))
                                        | _ -> [environment]
                                    | _ -> []
                                | _ -> [])
                            let participants = Set.unionMany [cellSupport; borrowed; Set.ofList (
                                [owner; generator; formal; slot; initializer; value] @ formationNodes @ environments @
                                (values |> List.collect (fun (source, value) -> [source; value])))]
                            generator, formal, participants))
                    | _ -> None
                | _ -> None
            | _ -> None
        | _ -> None
    let slotAccesses = Dictionary<NodeId * NodeId, StorageAccess option>()
    let slotAccess owner slot =
        let key = owner, slot
        match slotAccesses.TryGetValue key with
        | true, value -> value
        | _ ->
            let validated =
                match controlProtocol owner, graph.Nodes.TryFind slot with
                | Some protocol, Some source when slot = protocol.StateSlot || Some slot = protocol.CurrentSlot ->
                    match storageCensus protocol.Generator protocol.Formal protocol.Formal slot with
                    | Some(aliases, actual) ->
                        let inputs =
                            if slot = protocol.StateSlot then protocol.StateWrites
                            else protocol.Cuts |> List.map (fun cut -> cut.Writer, cut.Value)
                        let typed = inputs |> List.forall (fun (_, value) ->
                            nodes.TryFind value |> Option.exists (fun node -> applySubst node.Type = applySubst source.Type))
                        if not typed || inputs.Length <> (Set.ofList inputs).Count ||
                           (inputs |> List.map fst |> Set.ofList).Count <> inputs.Length || Set.ofList inputs <> actual then None else
                        let initial = Set.unionMany [aliases; protocol.Participants; Set.ofList [owner; slot; protocol.Generator; protocol.Formal]]
                        let participants =
                            inputs |> List.fold (fun participants (writer, value) ->
                                participants |> Set.add writer |> Set.add value) initial
                        Some { Source = slot; Inputs = inputs; SharedCell = None
                               InitialState = if slot = protocol.StateSlot then Some(protocol.InitialEntry, 0I) else None
                               Participants = participants }
                    | None -> None
                | _ ->
                    sharedCapture owner slot |> Option.bind (fun (generator, formal, formation) ->
                        storageCensus generator formal formal slot |> Option.bind (fun (aliases, writers) ->
                            let inputs = Set.toList writers
                            let typed = inputs |> List.forall (fun (_, value) ->
                                nodes.TryFind value |> Option.exists (fun node -> applySubst node.Type = applySubst nodes[slot].Type))
                            if not typed then None else
                            let participants = inputs |> List.fold (fun participants (writer, value) ->
                                participants |> Set.add writer |> Set.add value) (Set.union aliases formation)
                            Some { Source = slot; Inputs = inputs; SharedCell = Some slot
                                   InitialState = None; Participants = participants }))
            slotAccesses.Add(key, validated)
            validated
    // A retained source name is insufficient after continuation realization:
    // validate all actual writes and every raw storage use in this graph
    // revision. Storage range inputs and callable identity share this census,
    // while callable identity additionally checks each writer's correspondence.
    // No final placement/codata is needed for either reading.
    let continuationStorage id =
        match nodes.TryFind id, continuationRows.TryFind id, originalRows.TryFind id with
        | Some { Kind = SemanticKind.FrameRead(frame, slot); Type = valueType },
          Some [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = owner :: generator :: root :: source :: declaredWriters }],
          Some [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [original] }]
            when slot = source && original = source && activation id = Some generator ->
            match nodes.TryFind owner, nodes.TryFind generator, graph.Nodes.TryFind source, nodes.TryFind root with
            | Some ({ Kind = SemanticKind.SeqExpr(actual, captured); Type = NativeType.TSeq element } as sequence),
              Some { Kind = SemanticKind.Lambda([_, environmentType, formal], _, [], _, LambdaContext.SeqGenerator) },
              Some original, Some storage when actual = generator && applySubst valueType = applySubst original.Type
                                             && applySubst environmentType = NativeType.TSeqEnumerator(applySubst element) ->
                let rec actualStorage seen id =
                    if Set.contains id seen then None else
                    match nodes.TryFind id with
                    | Some node when applySubst node.Type = applySubst storage.Type ->
                        if id = root then Some(Set.singleton id) else
                        let seen = Set.add id seen
                        match node.Kind, node.Children with
                        | SemanticKind.VarRef(_, Some value), _ | SemanticKind.TypeAnnotation(value, _), _
                        | SemanticKind.Binding(_, false, _, _), [value] -> actualStorage seen value |> Option.map (Set.add id)
                        | SemanticKind.EagerExpr value, _ when ExplicitDemand.operand graph id = Some value ->
                            actualStorage seen value |> Option.map (Set.add id)
                        | _ -> None
                    | _ -> None
                let storagePath = actualStorage Set.empty frame
                if storagePath.IsNone then None else
                let rec writerPairs parts =
                    match parts with
                    | [] -> Some []
                    | writer :: value :: rest -> writerPairs rest |> Option.map (fun pairs -> (writer, value) :: pairs)
                    | _ -> None
                let storageUses = storageCensus generator formal root slot
                let control = if root = formal then slotAccess owner slot else None
                let selected =
                    match storage.Kind with
                    | SemanticKind.PatternBinding _ when root = formal && applySubst storage.Type = applySubst environmentType ->
                        match captured |> List.filter (fun capture -> capture.SourceNodeId = Some slot) with
                        | [capture] when not capture.IsMutable && applySubst capture.Type = applySubst valueType ->
                            captureInitializers sequence |> Option.bind (fun initializers ->
                                match initializers |> List.filter (fun (source, _) -> source = slot) with
                                | [_, value] when graph.Nodes.TryFind value |> Option.exists (fun value -> applySubst value.Type = applySubst valueType) -> Some(value, true)
                                | _ -> None)
                        | [capture] when capture.IsMutable && applySubst capture.Type = applySubst valueType ->
                            control |> Option.bind (fun proof ->
                                if proof.SharedCell = Some slot then Some(slot, false) else None)
                        | [] ->
                            match control with
                            | Some _ -> Some(slot, false)
                            | None ->
                                graph.Edges |> List.tryPick (fun edge ->
                                    match edge.Class, edge.Role, edge.Sources with
                                    | EdgeClass.Suspension, EdgeRole.SuspensionLiveAcross, actualOwner :: actualGenerator :: _
                                        when edge.Target = slot && actualOwner = owner && actualGenerator = generator -> Some(slot, false)
                                    | _ -> None)
                        | _ -> None
                    | SemanticKind.ContinuationStorage actualOwner when actualOwner = owner && activation root = Some generator
                                                                 && applySubst storage.Type = Types.mkArrayType Types.uint8Type -> Some(slot, false)
                    | _ -> None
                match selected, writerPairs declaredWriters, storageUses with
                | Some(selected, immutableCapture), Some declared, Some(aliases, actual)
                    when Set.count (Set.ofList declared) = declared.Length
                         && (declared |> List.map fst |> Set.ofList |> Set.count) = declared.Length
                         && Set.ofList declared = actual
                         && (if immutableCapture then actual.IsEmpty else control.IsSome || not actual.IsEmpty) ->
                    let writes = Set.toList actual
                    let typed = writes |> List.forall (fun (_, value) ->
                        nodes.TryFind value |> Option.exists (fun node -> applySubst node.Type = applySubst valueType))
                    if not typed then None else
                    let inputs = if immutableCapture then [owner, selected] else writes
                    let initial = Set.union aliases (Set.ofList [id; owner; generator; formal; root; slot; selected])
                    let initial = control |> Option.map (fun proof -> Set.union proof.Participants initial) |> Option.defaultValue initial
                    let participants =
                        writes |> List.fold (fun participants (writer, value) ->
                            participants |> Set.add writer |> Set.add value) initial
                    Some(({ Source = selected; Inputs = inputs; SharedCell = control |> Option.bind _.SharedCell
                            InitialState = control |> Option.bind _.InitialState
                            Participants = participants }: StorageAccess), immutableCapture)
                | _ -> None
            | _ -> None
        | _ -> None
    let storageAccesses = Dictionary<NodeId, (StorageAccess * bool) option>()
    let storageAccess id =
        match storageAccesses.TryGetValue id with
        | true, value -> value
        | _ ->
            let value = continuationStorage id
            storageAccesses.Add(id, value)
            value
    let rec continuationSource pending id =
        if Set.contains id pending then None else
        let pending = Set.add id pending
        storageAccess id |> Option.bind (fun (storage, immutableCapture) ->
            if storage.SharedCell.IsSome then None else
            let proofs =
                if immutableCapture then [] else
                storage.Inputs |> List.map (fun (writer, value) ->
                    corresponds pending Set.empty storage.Source value |> Option.map (Set.add writer))
            if proofs |> List.exists Option.isNone then None else
            let participants = proofs |> List.choose (fun proof -> proof) |> List.fold Set.union storage.Participants
            Some(storage.Source, participants))
    and corresponds pending seen expected actual =
        if Set.contains (expected, actual) seen then None else
        let seen = Set.add (expected, actual) seen
        let add = Option.map (Set.add expected >> Set.add actual)
        match graph.Nodes.TryFind expected, nodes.TryFind actual with
        | Some source, Some value when applySubst source.Type = applySubst value.Type ->
            if expected = actual then Some(Set.singleton actual) else
            match source.Kind, source.Children, value.Kind, value.Children with
            | _, _, SemanticKind.FrameRead _, _ ->
                continuationSource pending actual |> Option.bind (fun (original, participants) ->
                    match originalIdentity Set.empty expected, originalIdentity Set.empty original with
                    | Some(left, before), Some(right, after) when left = right -> Some(Set.unionMany [participants; before; after])
                    | _ -> None) |> add
            | SemanticKind.Binding(_, false, _, _), [child], _, _
            | SemanticKind.VarRef(_, Some child), _, _, _
            | SemanticKind.TypeAnnotation(child, _), _, _, _ -> corresponds pending seen child actual |> add
            | _, _, SemanticKind.Binding(_, false, _, _), [child]
            | _, _, SemanticKind.VarRef(_, Some child), _
            | _, _, SemanticKind.TypeAnnotation(child, _), _ -> corresponds pending seen expected child |> add
            | _ ->
                // A cloned callable-producing expression may have rewritten
                // structural operands, but its operation and every operand
                // must still correspond to the exact retained expression.
                match originalRows.TryFind actual with
                | Some [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [original] }] when original = expected ->
                    let dependencies node =
                        let derived = kindEdges node.Id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                        (if derived.IsEmpty then node.Children else derived) |> List.distinct
                    let before, after = dependencies source, dependencies value
                    if before.Length <> after.Length then None else
                    let pairs = List.zip before after
                    let replacement = Map.ofList pairs
                    if Clef.Compiler.Nanopass.FoldIn.remapKindReferences replacement source.Kind <> value.Kind then None else
                    pairs |> List.fold (fun proof (source, value) ->
                        match proof, corresponds pending seen source value with
                        | Some prior, Some current -> Some(Set.union prior current)
                        | _ -> None) (Some(Set.ofList [expected; actual]))
                | _ -> None
        | _ -> None
    let rec occurrence retained seen id =
        if Set.contains id seen then Some(empty, Set.empty) else
        let seen = Set.add id seen
        let all inputs =
            inputs |> List.fold (fun found input ->
                match found, occurrence retained seen input with
                | Some(proof, leaves), Some(more, extra) -> Some(merge proof more, Set.union leaves extra)
                | _ -> None) (Some(empty, Set.empty))
        let result =
            match (if retained then graph.Nodes.TryFind id else nodes.TryFind id) with
            | Some { Kind = SemanticKind.Lambda _ | SemanticKind.ClosureValue _ } -> Some(empty, Set.singleton id)
            | Some { Kind = SemanticKind.VarRef(_, Some _) } when promotedReferences.Contains id ->
                sourceDeclaration id |> Option.bind (fun declaration -> all [declaration])
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] }
            | Some { Kind = SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _) } -> all [value]
            | Some { Kind = SemanticKind.EagerExpr value } when ExplicitDemand.operand graph id = Some value -> all [value]
            | Some { Kind = SemanticKind.Sequential values } -> List.tryLast values |> Option.bind (fun value -> all [value])
            | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } -> all [yes; no]
            | Some { Kind = SemanticKind.Match(_, cases) } -> all (cases |> List.map _.Body)
            | Some { Kind = SemanticKind.CaseElimination(_, cases) } -> all (cases |> List.map _.Body)
            | Some { Kind = SemanticKind.EnvironmentRead(environment, slot) } -> capturedValue environment slot |> Option.bind (fun value -> all [value])
            | Some { Kind = SemanticKind.FieldGet _ | SemanticKind.TupleGet _ | SemanticKind.DUEliminate _ } ->
                Clef.Compiler.Baker.Ingredients.CallableAggregateProjections.read resolution id
                |> Option.bind (fun reading ->
                    all reading.Inputs |> Option.map (fun (proof, leaves) ->
                        { proof with Participants = Set.union proof.Participants reading.Participants }, leaves))
            | Some { Kind = SemanticKind.FrameRead _ } ->
                continuationSource Set.empty id |> Option.bind (fun (source, participants) ->
                    occurrence true seen source |> Option.map (fun (proof, leaves) ->
                        { proof with Participants = Set.union proof.Participants participants }, leaves))
            | Some { Kind = SemanticKind.Application(callee, _) } ->
                complete id |> Option.bind (fun call -> all (callee :: (call.Targets |> List.map _.Body)))
            | Some { Kind = SemanticKind.PatternBinding _ } ->
                owners.TryFind id |> Option.bind (fun owner ->
                    closed owner |> Option.bind (fun required ->
                        let supplied = resolution.ParameterInputs.TryFind id |> Option.defaultValue []
                        let rows = supplied |> List.map (fun (site, actual) ->
                            complete site |> Option.bind (fun call ->
                                let matches = call.Targets |> List.filter (fun target ->
                                    target.Parameters.Length = target.Arguments.Length &&
                                    List.zip target.Parameters target.Arguments |> List.exists (fun ((_, _, formal), argument) -> formal = id && argument = actual))
                                if matches.IsEmpty then None else Some(matches |> List.map (row site))))
                        if supplied.IsEmpty || rows |> List.exists Option.isNone then None else
                        all (supplied |> List.map snd) |> Option.map (fun (proof, leaves) ->
                            let participantSet = required |> Set.fold (fun found code -> Set.union found candidates[code].Participants) proof.Participants
                            let lazyForces = required |> Set.fold (fun found code -> Set.union found candidates[code].UsedLazyForces) proof.UsedLazyForces
                            { proof with Formals = Set.add id proof.Formals; Implementations = Set.union required proof.Implementations
                                         Participants = participantSet
                                         UsedLazyForces = lazyForces
                                         Calls = List.distinct (proof.Calls @ (rows |> List.choose (fun value -> value) |> List.concat)
                                                               @ (required |> Set.toList |> List.collect (fun code -> candidates[code].Calls))) }, leaves)))
            | _ -> None
        result |> Option.map (fun (proof, leaves) -> { proof with Participants = Set.add id proof.Participants }, leaves)
    let evidence = nodes |> Map.toList |> List.choose (fun (id, node) ->
        match applySubst node.Type with
        | NativeType.TFun _ ->
            occurrence false Set.empty id |> Option.bind (fun (proof, leaves) ->
                if leaves.IsEmpty then None else
                Some(id, { proof with Uses = proof.Participants |> Set.toList |> List.map (fun participant -> participant, observedUses participant) |> Map.ofList }))
        | _ -> None) |> Map.ofList
    let accesses = Dictionary<NodeId, Access option>()
    let access id =
        match accesses.TryGetValue id with
        | true, value -> value
        | _ ->
            let value = continuationSource Set.empty id |> Option.map (fun (source, participants) ->
                { Source = source; Participants = Set.add id participants })
            accesses.Add(id, value)
            value
    let retained = evidence |> Map.toList |> List.choose (fun (id, _) ->
        match nodes[id].Kind with
        | SemanticKind.FrameRead _ ->
            access id |> Option.bind (fun current ->
                occurrence true Set.empty current.Source |> Option.map (fun (proof, _) ->
                    current.Source, { proof with Participants = Set.union proof.Participants current.Participants }))
        | _ -> None) |> Map.ofList
    let familyEvidence required =
        let participants = required |> Set.fold (fun found code -> Set.union found candidates[code].Participants) Set.empty
        let lazyForces = required |> Set.fold (fun found code -> Set.union found candidates[code].UsedLazyForces) Set.empty
        { empty with Implementations = required; Participants = participants
                     UsedLazyForces = lazyForces
                     Calls = required |> Set.toList |> List.collect (fun code -> candidates[code].Calls) |> List.distinct
                     Uses = participants |> Set.toList |> List.map (fun id -> id, observedUses id) |> Map.ofList }
    let closedImplementation implementation = closed implementation |> Option.map familyEvidence
    { Evidence = evidence; RetainedEvidence = retained; Access = access
      StorageAccess = fun id -> storageAccess id |> Option.map fst
      SlotAccess = slotAccess
      ValueIdentity = fun id ->
          originalIdentity Set.empty id |> Option.map (fun (source, participants) ->
              { Source = source; Participants = participants })
      ClosedImplementation = closedImplementation
      Family = fun implementation ->
          family implementation |> Option.map (fun (required, reached) ->
              { Evidence = familyEvidence required; Activated = reached })
      ExecutionOwner = activation
      Correspondence = fun source current -> corresponds Set.empty Set.empty source current }

let analyze graph = analyzeWith graph (CallableOrigins.resolve graph)
let tryEvidence reading occurrence = reading.Evidence.TryFind occurrence
/// Complete implementation ingress, unlike a code-value occurrence's identity.
let tryClosedImplementation reading implementation = reading.ClosedImplementation implementation
/// Reuses the ingress owner's caller closure; consumers supply their own
/// activation or execution-count obligations without another use census.
let tryFamily reading implementation = reading.Family implementation
/// Lexical execution ownership is not an assertion that the owner runs.
let tryExecutionOwner reading occurrence = reading.ExecutionOwner occurrence

/// Share the complete scalar/descriptor ingress decision with source recipes.
/// ParameterInputs is only a census; it becomes authority after the owning
/// implementation is closed and every actual occupies its exact formal slot.
let closedFormalInputs (graph: SemanticGraph) (resolution: CallableOrigins.Resolution) (reading: Reading) =
    let owners =
        graph.Nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.Lambda(parameters,_,_,_,_) -> parameters |> List.map (fun (_,_,formal) -> formal,node.Id)
            | _ -> [])
        |> Seq.groupBy fst |> Seq.choose (fun (formal, rows) ->
            match rows |> Seq.map snd |> Seq.distinct |> Seq.toList with
            | [owner] -> Some(formal,owner)
            | _ -> None) |> Map.ofSeq
    fun formal ->
        match resolution.ParameterInputs.TryFind formal, owners.TryFind formal |> Option.bind (tryClosedImplementation reading) with
        | Some inputs, Some proof when not inputs.IsEmpty ->
            let exact = proof.Calls |> List.collect (fun call ->
                if call.Parameters.Length <> call.Arguments.Length then [] else
                List.zip call.Parameters call.Arguments |> List.choose (fun (parameter,actual) ->
                    if parameter = formal then Some(call.Site,actual) else None)) |> Set.ofList
            if Set.ofList inputs = exact then
                let participants = inputs |> List.fold (fun participants (site,actual) ->
                    participants |> Set.add site |> Set.add actual) (proof.Participants |> Set.add formal)
                Some { Inputs = inputs; Closure = proof; Participants = participants }
            else None
        | _ -> None
/// Retained logical values are readable only through a validated current access;
/// they remain absent from executable occurrence admission.
let tryRetainedEvidence reading occurrence = reading.RetainedEvidence.TryFind occurrence
let tryAccess reading occurrence = reading.Access occurrence
/// Immutable aliases preserve one actual formation frontier. Calls, formals,
/// captured reads and frame reads remain distinct value instances; this never
/// follows a call result into its shared code/environment template.
let tryValueIdentity reading occurrence = reading.ValueIdentity occurrence
/// Complete current scalar storage inputs, without asserting callable identity.
let tryStorageAccess reading occurrence = reading.StorageAccess occurrence
/// Current control slot inputs under the checked cut/resume and storage census.
let trySlotAccess reading owner slot = reading.SlotAccess owner slot
let tryCorrespondence reading source current = reading.Correspondence source current
let allowsOccurrence reading occurrence = reading.Evidence.ContainsKey occurrence

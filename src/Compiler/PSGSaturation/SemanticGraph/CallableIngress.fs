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

type Call = { Site: NodeId; Implementation: NodeId; Parameters: NodeId list; Arguments: NodeId list }
type Evidence = {
    Entry: NodeId option
    Roots: (NodeId * DeclRoot) list
    Formals: Set<NodeId>
    Implementations: Set<NodeId>
    Participants: Set<NodeId>
    Uses: Map<NodeId, Hyperedge list>
    Calls: Call list
}
type Access = { Source: NodeId; Participants: Set<NodeId> }
type Reading = private {
    Evidence: Map<NodeId, Evidence>
    RetainedEvidence: Map<NodeId, Evidence>
    Access: NodeId -> Access option
    Correspondence: NodeId -> NodeId -> Set<NodeId> option
    ClosedImplementation: NodeId -> Evidence option
}
type private Closed = { Dependencies: Set<NodeId>; Callers: Set<NodeId>; Participants: Set<NodeId>; Calls: Call list; Valid: bool }

let analyzeWith (graph: SemanticGraph) (resolution: CallableOrigins.Resolution) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let initialization = ProgramInitialization.read graph
    let entry = initialization |> Option.map _.EntryLambda
    let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
    let edgeKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let grouped rows =
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
    let emptyClosed = { Dependencies = Set.empty; Callers = Set.empty; Participants = Set.empty; Calls = []; Valid = true }
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
                match nodes.TryFind id with
                | Some { Kind = SemanticKind.Binding(_, true, _, _) | SemanticKind.Binding(_, _, _, Some _) } -> reject ()
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
                            let selected = values |> List.filter (fun (_, value, mutableCell) -> value = id && not mutableCell)
                            if selected.IsEmpty then reject () else
                            match nodes.TryFind owner with
                            | Some { Kind = SemanticKind.ClosureValue(code, _) } ->
                                dependency code
                                for slot, _, _ in selected do capturedReads owner slot |> List.iter forward
                            | _ -> reject ()
                        | None -> reject ()
                    | Some node, EdgeClass.Structural, _ when declared ->
                        match node.Kind, edge.Role with
                        | SemanticKind.Binding(_, false, _, None), _ when node.Children = [id] -> forward node.Id
                        | SemanticKind.TypeAnnotation(value, _), _ when value = id -> forward node.Id
                        | SemanticKind.EagerExpr value, _ when value = id && ExplicitDemand.operand graph node.Id = Some id -> forward node.Id
                        | SemanticKind.Sequential values, _ -> if List.tryLast values = Some id then forward node.Id
                        | SemanticKind.IfThenElse(_, yes, no), (EdgeRole.ThenBranch | EdgeRole.ElseBranch)
                            when id = yes || no = Some id -> forward node.Id
                        | SemanticKind.Match(_, cases), _ when cases |> List.exists (fun branch -> branch.Body = id) -> forward node.Id
                        | SemanticKind.CaseElimination(_, cases), _ when cases |> List.exists (fun branch -> branch.Body = id) -> forward node.Id
                        | SemanticKind.Lambda(parameters, _, _, _, _), EdgeRole.Parameter
                            when parameters |> List.exists (fun (_, _, formal) -> formal = id) -> ()
                        | SemanticKind.ClosureValue(code, _), EdgeRole.Body when code = id -> forward node.Id
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
                            if callers.IsEmpty then reject ()
                            for site, call in callers do
                                if not call.Complete || call.Unknown then reject () else forward site
                        | _ -> reject ()
                    | _ -> reject ()
                // Source captures are independent uses even when the value has
                // no structural edge into the nested deferred body yet.
                for node, capture in captureUses.TryFind id |> Option.defaultValue [] do
                    match node.Kind with
                    | SemanticKind.Lambda _ when not capture.IsMutable -> dependency node.Id
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
    let closedCache = Dictionary<NodeId, Set<NodeId> option>()
    let findClosed implementation =
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
            collect [implementation] Set.empty true |> Option.bind (fun required ->
                let rec connect reached =
                    let next = required |> Set.fold (fun reached id ->
                        if not (Set.intersect candidates[id].Callers reached).IsEmpty then Set.add id reached else reached) reached
                    if next = reached then reached else connect next
                let reached = connect (Set.singleton root)
                if Set.isSubset required reached then Some required else None)
    let closed implementation =
        match closedCache.TryGetValue implementation with
        | true, value -> value
        | _ ->
            let value = findClosed implementation
            closedCache.Add(implementation, value)
            value
    let empty = { Entry = entry; Roots = graph.DeclarationRoots; Formals = Set.empty; Implementations = Set.empty; Participants = Set.empty; Uses = Map.empty; Calls = [] }
    let merge left right =
        { left with Formals = Set.union left.Formals right.Formals
                    Implementations = Set.union left.Implementations right.Implementations
                    Participants = Set.union left.Participants right.Participants
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
                | _ -> None
            match next with
            | None -> Some(id, Set.singleton id)
            | Some value when (checkedInstance id |> Option.exists (fun instance -> instance.Declaration = value)) ||
                              (graph.Nodes.TryFind value |> Option.exists (fun child -> applySubst child.Type = applySubst node.Type)) ->
                originalIdentity (Set.add id seen) value |> Option.map (fun (source, participants) -> source, Set.add id participants)
            | _ -> None
    // A retained source name is insufficient after continuation realization:
    // validate all actual writes and every raw storage use in this graph
    // revision. No final placement/codata is needed for this source identity.
    let rec continuationSource pending id =
        if Set.contains id pending then None else
        let pending = Set.add id pending
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
                // Following every use of the exact root also rejects aliases
                // passed to unknown code, cell assignments and borrowed access
                // to this callable slot. Such uses could invalidate its writer
                // census even when no new direct FrameWrite is visible.
                let rec storageUses seen pendingUses writers =
                    match pendingUses with
                    | [] -> Some(seen, writers)
                    | current :: rest when Set.contains current seen -> storageUses seen rest writers
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
                        |> Option.bind (fun (next, writes) -> storageUses seen next writes)
                let storageUses = storageUses Set.empty [root] Set.empty
                let selected =
                    match storage.Kind with
                    | SemanticKind.PatternBinding _ when root = formal && applySubst storage.Type = applySubst environmentType ->
                        match captured |> List.filter (fun capture -> capture.SourceNodeId = Some slot) with
                        | [capture] when not capture.IsMutable && applySubst capture.Type = applySubst valueType ->
                            ClosureEnvironments.sequenceInitializers graph sequence |> Option.bind (fun initializers ->
                                match initializers |> List.filter (fun (source, _) -> source = slot) with
                                | [_, value] when graph.Nodes.TryFind value |> Option.exists (fun value -> applySubst value.Type = applySubst valueType) -> Some(value, true)
                                | _ -> None)
                        | [] ->
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
                         && (if immutableCapture then actual.IsEmpty else not actual.IsEmpty) ->
                    let proofs =
                        actual |> Set.toList |> List.map (fun (writer, value) ->
                            match nodes.TryFind value with
                            | Some node when applySubst node.Type = applySubst valueType ->
                                corresponds pending Set.empty selected value |> Option.map (Set.add writer)
                            | _ -> None)
                    if proofs |> List.exists Option.isNone then None else
                    let participants = proofs |> List.choose (fun value -> value) |> List.fold Set.union aliases
                    Some(selected, Set.union participants (Set.ofList [owner; generator; formal; slot; selected]))
                | _ -> None
            | _ -> None
        | _ -> None
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
                            { proof with Formals = Set.add id proof.Formals; Implementations = Set.union required proof.Implementations
                                         Participants = participantSet
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
    let closedImplementation implementation =
        closed implementation |> Option.map (fun required ->
            let participants = required |> Set.fold (fun found code -> Set.union found candidates[code].Participants) Set.empty
            { empty with Implementations = required; Participants = participants
                         Calls = required |> Set.toList |> List.collect (fun code -> candidates[code].Calls) |> List.distinct
                         Uses = participants |> Set.toList |> List.map (fun id -> id, observedUses id) |> Map.ofList })
    { Evidence = evidence; RetainedEvidence = retained; Access = access
      ClosedImplementation = closedImplementation
      Correspondence = fun source current -> corresponds Set.empty Set.empty source current }

let analyze graph = analyzeWith graph (CallableOrigins.resolve graph)
let tryEvidence reading occurrence = reading.Evidence.TryFind occurrence
/// Complete implementation ingress, unlike a code-value occurrence's identity.
let tryClosedImplementation reading implementation = reading.ClosedImplementation implementation
/// Retained logical values are readable only through a validated current access;
/// they remain absent from executable occurrence admission.
let tryRetainedEvidence reading occurrence = reading.RetainedEvidence.TryFind occurrence
let tryAccess reading occurrence = reading.Access occurrence
let tryCorrespondence reading source current = reading.Correspondence source current
let allowsOccurrence reading occurrence = reading.Evidence.ContainsKey occurrence

// SPDX-License-Identifier: MIT
/// Complete ordinary call paths under the explicit program entry activation.
/// Deferred callers remain dependencies for the owning residence proof. This
/// establishes directional stack coverage, never static lifetime or escape.
module Clef.Compiler.PSGSaturation.SemanticGraph.ProgramActivation

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
module Incidence = Clef.Compiler.Baker.Ingredients.Closures
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module Initialization = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization

type private Call = { Site: NodeId; Callee: NodeId; Caller: NodeId option }
/// `Premises` are the scoped parameters, with their declarations, that account
/// for an argument use: recorded provenance, not an established invocation.
type private Candidate = { Aliases: NodeId list; Calls: Call list; Supports: NodeId list; Premises: NodeId list }
/// `Accounted` holds every ordinary implementation whose uses are all accounted for,
/// applied in source or not; `Candidates` is its subset with complete applications,
/// the shape coverage walks.
type Reading = private { Entry: NodeId option; Candidates: Map<NodeId, Candidate>; Accounted: Map<NodeId, Candidate>; Ordinary: Set<NodeId>; Deferred: Set<NodeId> }
type Coverage = { Dependencies: NodeId list; Evidence: Hyperedge list }

/// Classify every use of each known code value. A missing invocation path,
/// opaque reference, partial call, returned value or stored mutable alias is
/// a refusal, not permission derived from the function's lexical location.
let analyze (graph: SemanticGraph) : Reading =
    match Initialization.read graph with
    | None -> { Entry = None; Candidates = Map.empty; Accounted = Map.empty; Ordinary = Set.empty; Deferred = Set.empty }
    | Some entry ->
        let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
        let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
        let uses =
            incidence |> List.filter Hyperedge.isStructural
            |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
            |> List.groupBy fst |> Map.ofList |> Map.map (fun _ rows -> rows |> List.map snd)
        let activation id =
            let rec walk seen pending found missing =
                match pending with
                | [] -> if not missing && Set.count found = 1 then Some(Set.minElement found) else None
                | current :: rest when Set.contains current seen -> walk seen rest found missing
                | current :: rest ->
                    let seen = Set.add current seen
                    match nodes.TryFind current with
                    | Some { Kind = SemanticKind.Lambda _ } -> walk seen rest (Set.add current found) missing
                    | _ ->
                        match uses.TryFind current with
                        | Some parents when not parents.IsEmpty -> walk seen ((parents |> List.map _.Target) @ rest) found missing
                        | _ -> walk seen rest found true
            walk Set.empty [id] Set.empty false
        let resolved = CallableOrigins.resolve graph
        let scoped = lazy (ScopedCallbacks.read graph)
        let declared = lazy (ScopedDeclarations.read graph)
        let implementation = Environments.tryImplementation graph
        let identity id =
            implementation id
            |> Option.orElseWith (fun () -> resolved.Lambdas.TryFind id)
        let environmentCalls = Environments.callEnvironments graph
        let closureImplementations =
            nodes.Values |> Seq.choose (fun node ->
                match node.Kind with SemanticKind.ClosureValue(implementation, _) -> Some implementation | _ -> None) |> Set.ofSeq
        let ordinary =
            nodes |> Map.toList |> List.choose (fun (id, node) ->
                match node.Kind with
                | SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure)
                    when not parameters.IsEmpty && nodes.ContainsKey body &&
                         (parameters |> List.forall (fun (_, _, formal) -> nodes.ContainsKey formal)) -> Some(id, parameters.Length)
                | _ -> None)
        // The formals a complete call supplies at one argument position: a direct declaration's
        // own formals (a declared boundary's call need not appear among resolved calls: its body
        // is a native intrinsic), else every resolved target's. Only when each of them is a scoped
        // parameter is the argument invoked within the callee's own activation.
        let scopedFormalsAt callee (arguments: NodeId list) ordinal application =
            let rec declaration seen id =
                if Set.contains id seen then None else
                match nodes.TryFind id with
                | Some { Kind = SemanticKind.Lambda _ } -> Some id
                | Some { Kind = SemanticKind.VarRef(_, Some other) | SemanticKind.TypeAnnotation(other, _) } -> declaration (Set.add id seen) other
                | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> declaration (Set.add id seen) value
                | _ -> None
            let direct =
                identity callee |> Option.orElseWith (fun () -> declaration Set.empty callee) |> Option.bind (fun lambda ->
                    match nodes.TryFind lambda with
                    | Some { Kind = SemanticKind.Lambda(formals, _, _, _, _) } when arguments.Length = max 1 formals.Length ->
                        List.tryItem ordinal formals |> Option.map (fun (_, _, formal) -> [formal])
                    | _ -> None)
            let viaCalls () =
                resolved.Calls.TryFind application |> Option.bind (fun call ->
                    if not call.Complete || call.Targets.IsEmpty then None else
                    let formals = call.Targets |> List.map (fun target -> List.tryItem ordinal target.Parameters |> Option.map (fun (_, _, formal) -> formal))
                    if formals |> List.exists Option.isNone then None else Some(List.choose id formals))
            direct |> Option.orElseWith viaCalls
            |> Option.filter (fun formals -> not formals.IsEmpty && formals |> List.forall scoped.Value.Parameters.Contains)
        let accounted =
            ordinary |> List.choose (fun (implementation, arity) ->
                let aliases = nodes |> Map.toList |> List.choose (fun (id, node) ->
                    match applySubst node.Type with
                    | NativeType.TFun _ when identity id = Some implementation -> Some id
                    | _ -> None)
                let aliasSet = Set.ofList aliases
                // Projecting a closure's environment authorizes only its exact
                // actual position in a complete call, not a callable alias or
                // any other use of the environment view.
                let completeEnvironmentProjection projection =
                    let capturesValue value (node: SemanticNode) =
                        let captured =
                            match node.Kind with
                            | SemanticKind.SeqExpr(_, captures)
                            | SemanticKind.Lambda(_, _, captures, _, _)
                            | SemanticKind.LazyExpr(_, captures) -> captures
                            | _ -> []
                        captured |> List.exists (fun capture -> capture.SourceNodeId = Some value)
                    let rec follow seen value =
                        if Set.contains value seen || nodes.Values |> Seq.exists (capturesValue value) then None else
                        let seen = Set.add value seen
                        let references = nodes.Values |> Seq.choose (fun node ->
                            match node.Kind with SemanticKind.VarRef(_, Some source) when source = value -> Some node.Id | _ -> None) |> Seq.toList
                        let opaqueReference = graph.Edges |> List.exists (fun edge ->
                            if edge.Class <> EdgeClass.Reference || not (List.contains value edge.Sources) then false else
                            match nodes.TryFind edge.Target with
                            | Some { Kind = SemanticKind.VarRef(_, Some source) }
                                when edge.Role = EdgeRole.Definition && source = value && edge.Sources = [value] -> false
                            | None when graph.Nodes.ContainsKey edge.Target -> false
                            | _ -> true)
                        if opaqueReference then None else
                        let consumers = uses.TryFind value |> Option.defaultValue []
                        let readings = consumers |> List.map (fun edge ->
                            match nodes[edge.Target].Kind, edge.Role with
                            | SemanticKind.Binding(_, false, _, _), _ when nodes[edge.Target].Children = [value] -> follow seen edge.Target
                            | SemanticKind.TypeAnnotation _, _ -> follow seen edge.Target
                            | SemanticKind.Sequential expressions, _ ->
                                if List.tryLast expressions = Some value then follow seen edge.Target else Some 0
                            | SemanticKind.Application(callee, _), EdgeRole.Argument
                                when identity callee = Some implementation &&
                                     environmentCalls.TryFind edge.Target = Some(edge.Ordinal, value) -> Some 1
                            | _ -> None)
                        let readings = readings @ (references |> List.map (follow seen))
                        if readings.IsEmpty || readings |> List.exists Option.isNone then None
                        else readings |> List.choose id |> List.sum |> Some
                    follow Set.empty projection |> Option.exists (fun calls -> calls > 0)
                let mutable closed =
                    not (graph.DeclarationRoots |> List.exists (fun (root, _) -> aliasSet.Contains root)) &&
                    not (aliases |> List.exists (fun id ->
                        match nodes[id].Kind with SemanticKind.Binding(_, _, _, Some _) -> true | _ -> false))
                let mutable calls = []
                let mutable supports = []
                let mutable premises = []
                for alias in aliases do
                    for edge in uses.TryFind alias |> Option.defaultValue [] do
                        let target = nodes[edge.Target]
                        match target.Kind, edge.Role with
                        | SemanticKind.Binding(_, false, _, _), _
                        | SemanticKind.TypeAnnotation _, _ when aliasSet.Contains target.Id -> ()
                        | SemanticKind.Sequential values, _ when List.tryLast values <> Some alias || aliasSet.Contains target.Id -> ()
                        | SemanticKind.IfThenElse _, (EdgeRole.ThenBranch | EdgeRole.ElseBranch) when aliasSet.Contains target.Id -> ()
                        | SemanticKind.Lambda(_, body, [], _, LambdaContext.RegularClosure), EdgeRole.Body
                            when body = alias &&
                                 (resolved.Calls.Values |> Seq.exists (fun call ->
                                     call.Complete && call.Targets |> List.exists (fun callee ->
                                         callee.Lambda = target.Id && aliasSet.Contains callee.Body))) ->
                            // A returned value has no lexical lifetime. Its
                            // producing function must itself have complete uses;
                            // environment storage is proved separately.
                            supports <- target.Id :: supports
                        | SemanticKind.ClosureValue(code, _), EdgeRole.Body when code = implementation && alias = implementation -> ()
                        | SemanticKind.EnvironmentReference source, EdgeRole.Subject
                            when source = alias && completeEnvironmentProjection target.Id -> ()
                        | SemanticKind.Application(callee, arguments), EdgeRole.Callee
                            when callee = alias && arguments.Length = arity &&
                                 (resolved.Calls.TryFind target.Id |> Option.exists (fun call ->
                                     call.Complete && not call.Targets.IsEmpty &&
                                     call.Targets |> List.forall (fun callee -> callee.Lambda = implementation))) &&
                                 (not (closureImplementations.Contains implementation) || environmentCalls.ContainsKey target.Id) ->
                            calls <- { Site = target.Id; Callee = callee; Caller = activation target.Id } :: calls
                        | SemanticKind.Lambda(parameters, _, _, _, _), _
                            when parameters |> List.exists (fun (_, _, formal) -> formal = alias) && scoped.Value.Parameters.Contains alias ->
                            // The alias is a scoped formal that receives this implementation: the
                            // boundary invokes it only within its own activation (declared, or
                            // inferred by ScopedCallbacks), and the formal's own uses inside that
                            // body are aliases walked here. The formal's place in its lambda is
                            // not a use of the implementation. An unscoped formal stays an
                            // unaccounted use: residence consumers of coverage must not widen.
                            ()
                        | SemanticKind.Application(callee, arguments), EdgeRole.Argument
                            when (scopedFormalsAt callee arguments edge.Ordinal target.Id).IsSome ->
                            // A scoped parameter, declared by the boundary or inferred, is invoked
                            // only within the callee's own activation (Platform Bindings,
                            // ScopedCallbackDescriptor): the argument runs as part of this call,
                            // so the call site bounds it. The parameter and its declaration are
                            // recorded premises of that account, not an established invocation.
                            let formals = (scopedFormalsAt callee arguments edge.Ordinal target.Id).Value
                            let declarations = formals |> List.collect (fun formal ->
                                declared.Value.Participants.TryFind formal |> Option.map Set.toList |> Option.defaultValue [])
                            calls <- { Site = target.Id; Callee = callee; Caller = activation target.Id } :: calls
                            premises <- formals @ declarations @ premises
                        | SemanticKind.Application _, EdgeRole.Argument ->
                            match resolved.Calls.TryFind target.Id with
                            | Some call when call.Complete && not call.Targets.IsEmpty &&
                                             (call.Targets |> List.forall (fun callee ->
                                                 List.tryItem edge.Ordinal callee.Parameters
                                                 |> Option.exists (fun (_, _, formal) -> aliasSet.Contains formal))) ->
                                supports <- (call.Targets |> List.map _.Lambda) @ supports
                            | _ -> closed <- false
                        | _ -> closed <- false
                // Capture metadata is an independent value use, not a structural
                // edge. Only the existing known immutable sequence capture path
                // may defer a call; its residence is proved by the sequence owner.
                for node in nodes.Values do
                    let reject captures =
                        if captures |> List.exists (fun capture -> capture.SourceNodeId |> Option.exists aliasSet.Contains) then closed <- false
                    match node.Kind with
                    | SemanticKind.SeqExpr(_, captures) ->
                        for capture in captures do
                            match capture.SourceNodeId with
                            | Some source when aliasSet.Contains source ->
                                if capture.IsMutable ||
                                   (Environments.tryKnown graph source |> Option.forall (fun known -> known.Implementation <> implementation)) then closed <- false
                            | _ -> ()
                    | SemanticKind.Lambda(_, _, captures, _, LambdaContext.SeqGenerator) ->
                        let owners = nodes.Values |> Seq.choose (fun owner ->
                            match owner.Kind with SemanticKind.SeqExpr(generator, held) when generator = node.Id -> Some held | _ -> None) |> Seq.toList
                        match owners with
                        | [held] ->
                            for capture in captures do
                                if capture.SourceNodeId |> Option.exists aliasSet.Contains then
                                    if not (held |> List.exists (fun original -> original.SourceNodeId = capture.SourceNodeId && original.IsMutable = capture.IsMutable)) then closed <- false
                        | _ -> reject captures
                    | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.LazyExpr(_, captures) -> reject captures
                    | _ -> ()
                for edge in graph.Edges do
                    if edge.Class = EdgeClass.Reference && (edge.Sources |> List.exists aliasSet.Contains) then
                        match nodes.TryFind edge.Target with
                        | Some { Kind = SemanticKind.VarRef(_, Some source) } when edge.Role = EdgeRole.Definition && edge.Sources = [source] -> ()
                        | Some { Kind = SemanticKind.ModuleDef(_, members) } when edge.Role = EdgeRole.Member &&
                            (List.tryItem edge.Ordinal members |> Option.exists (fun source -> edge.Sources = [source])) -> ()
                        | Some { Kind = SemanticKind.EnvironmentCreate(owner, initializers) }
                            when edge.Role = EdgeRole.EnvironmentInitializer &&
                                 (List.tryItem edge.Ordinal initializers |> Option.exists (fun (slot, value) ->
                                     edge.Sources = [value] &&
                                     graph.Edges |> List.exists (fun capture ->
                                         capture.Class = EdgeClass.Provenance && capture.Role = EdgeRole.EnvironmentCapture false &&
                                         capture.Target = edge.Target && capture.Sources = [owner; slot; value]))) ->
                            match nodes.TryFind owner with
                            | Some { Kind = SemanticKind.ClosureValue(code, environment) } when environment = edge.Target ->
                                supports <- code :: supports
                            | _ -> closed <- false
                        | Some _ -> closed <- false
                        | None when not (graph.Nodes.ContainsKey edge.Target) -> closed <- false
                        | None -> ()
                if closed && (calls |> List.forall (fun call -> call.Caller.IsSome)) then
                    Some(implementation, { Aliases = aliases; Calls = calls |> List.distinctBy _.Site; Supports = List.distinct supports; Premises = List.distinct premises })
                else None)
        let candidates = accounted |> List.filter (fun (_, candidate) -> not candidate.Calls.IsEmpty) |> Map.ofList
        let deferred = nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) -> Some id | _ -> None) |> Set.ofList
        { Entry = Some entry.EntryLambda; Candidates = candidates; Accounted = Map.ofList accounted
          Ordinary = ordinary |> List.map fst |> Set.ofList; Deferred = deferred }

/// How an ordinary implementation is reached, for a consumer that bounds its phase
/// when coverage is incomplete: the sites and supports to bound in turn, and the
/// premises the account relies on (scoped parameters and their declarations), which
/// the consumer records so an accepted proof names the library facts it rests on.
/// `Some ([], premises)`: every use is accounted for and none applies it in source,
/// so it runs only where it is handed on, after its formation. `None`: some use is
/// unaccounted for.
let invocations (reading: Reading) (implementation: NodeId) : (NodeId list * NodeId list) option =
    reading.Accounted.TryFind implementation
    |> Option.map (fun candidate ->
        (candidate.Calls |> List.map _.Site) @ candidate.Supports |> List.distinct, candidate.Premises)

/// Every incoming call must lead back to the supplied covering activation or to an
/// explicit deferred owner that the caller must prove covered. Closed recursive
/// groups are accepted only with such an external root; self-cycles prove nothing.
let coverage (reading: Reading) covering actual : Coverage option =
    if reading.Entry.IsNone || not (reading.Ordinary.Contains covering) || reading.Deferred.Contains actual then None else
    let rec visit seen pending groups dependencies rooted =
        match pending with
        | [] ->
            let rec reachable reached =
                let next = groups |> List.fold (fun reached (implementation, candidate: Candidate) ->
                    if candidate.Calls |> List.exists (fun call -> reached |> Set.contains call.Caller.Value) then Set.add implementation reached
                    else reached) reached
                if next = reached then reached else reachable next
            let reached = reachable (Set.add covering dependencies)
            if not rooted || (groups |> List.exists (fun (implementation, _) -> not (reached.Contains implementation))) then None else
            let evidence = groups |> List.collect (fun (implementation, candidate: Candidate) ->
                let callEdges = candidate.Calls |> List.map (fun call ->
                    { Sources = [covering; call.Caller.Value; call.Callee; implementation]
                      Target = call.Site; Class = EdgeClass.Provenance; Role = EdgeRole.ProgramActivationCall; Ordinal = 0 })
                { Sources = covering :: (candidate.Aliases @ candidate.Supports @ (candidate.Calls |> List.map _.Site) @ candidate.Premises) |> List.distinct
                  Target = implementation; Class = EdgeClass.Provenance; Role = EdgeRole.ProgramActivationCoverage; Ordinal = 0 } :: callEdges)
            Some { Dependencies = Set.toList dependencies; Evidence = evidence }
        | current :: rest when current = covering -> visit seen rest groups dependencies true
        | current :: rest when reading.Deferred.Contains current -> visit seen rest groups (Set.add current dependencies) true
        | current :: rest when Set.contains current seen -> visit seen rest groups dependencies rooted
        | current :: rest ->
            match reading.Candidates.TryFind current with
            | None -> None
            | Some candidate ->
                visit (Set.add current seen) (candidate.Supports @ (candidate.Calls |> List.map (fun call -> call.Caller.Value)) @ rest)
                    ((current, candidate) :: groups) dependencies rooted
    visit Set.empty [actual] [] Set.empty false

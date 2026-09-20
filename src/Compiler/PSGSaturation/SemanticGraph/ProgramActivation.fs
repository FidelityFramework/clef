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
type private Candidate = { Aliases: NodeId list; Calls: Call list }
type Reading = private { Entry: NodeId option; Candidates: Map<NodeId, Candidate>; Deferred: Set<NodeId> }
type Coverage = { Dependencies: NodeId list; Evidence: Hyperedge list }

/// Classify every use of each known code value. A missing invocation path,
/// opaque reference, partial call, returned value or stored mutable alias is
/// a refusal, not permission derived from the function's lexical location.
let analyze (graph: SemanticGraph) : Reading =
    match Initialization.read graph with
    | None -> { Entry = None; Candidates = Map.empty; Deferred = Set.empty }
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
        let identity = Environments.tryImplementation graph
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
        let candidates =
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
                    let consumers = uses.TryFind projection |> Option.defaultValue []
                    let capturesProjection (node: SemanticNode) =
                        let captured =
                            match node.Kind with
                            | SemanticKind.SeqExpr(_, captures)
                            | SemanticKind.Lambda(_, _, captures, _, _)
                            | SemanticKind.LazyExpr(_, captures) -> captures
                            | _ -> []
                        captured |> List.exists (fun capture -> capture.SourceNodeId = Some projection)
                    not consumers.IsEmpty &&
                    (consumers |> List.forall (fun edge ->
                        match nodes[edge.Target].Kind, edge.Role with
                        | SemanticKind.Application(callee, _), EdgeRole.Argument ->
                            identity callee = Some implementation &&
                            environmentCalls.TryFind edge.Target = Some(edge.Ordinal, projection)
                        | _ -> false)) &&
                    not (nodes.Values |> Seq.exists capturesProjection) &&
                    not (graph.Edges |> List.exists (fun edge ->
                        edge.Class = EdgeClass.Reference && List.contains projection edge.Sources &&
                        (nodes.ContainsKey edge.Target || not (graph.Nodes.ContainsKey edge.Target))))
                let mutable closed =
                    not (graph.DeclarationRoots |> List.exists (fun (root, _) -> aliasSet.Contains root)) &&
                    not (aliases |> List.exists (fun id ->
                        match nodes[id].Kind with SemanticKind.Binding(_, _, _, Some _) -> true | _ -> false))
                let mutable calls = []
                for alias in aliases do
                    for edge in uses.TryFind alias |> Option.defaultValue [] do
                        let target = nodes[edge.Target]
                        match target.Kind, edge.Role with
                        | SemanticKind.Binding(_, false, _, _), _
                        | SemanticKind.TypeAnnotation _, _ when aliasSet.Contains target.Id -> ()
                        | SemanticKind.Sequential values, _ when List.tryLast values <> Some alias || aliasSet.Contains target.Id -> ()
                        | SemanticKind.IfThenElse _, (EdgeRole.ThenBranch | EdgeRole.ElseBranch) when aliasSet.Contains target.Id -> ()
                        | SemanticKind.ClosureValue(code, _), EdgeRole.Body when code = implementation && alias = implementation -> ()
                        | SemanticKind.EnvironmentReference source, EdgeRole.Subject
                            when source = alias && completeEnvironmentProjection target.Id -> ()
                        | SemanticKind.Application(callee, arguments), EdgeRole.Callee
                            when callee = alias && arguments.Length = arity &&
                                 (not (closureImplementations.Contains implementation) || environmentCalls.ContainsKey target.Id) ->
                            calls <- { Site = target.Id; Callee = callee; Caller = activation target.Id } :: calls
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
                        | Some _ -> closed <- false
                        | None when not (graph.Nodes.ContainsKey edge.Target) -> closed <- false
                        | None -> ()
                if closed && not calls.IsEmpty && (calls |> List.forall (fun call -> call.Caller.IsSome)) then
                    Some(implementation, { Aliases = aliases; Calls = calls |> List.distinctBy _.Site })
                else None)
            |> Map.ofList
        let deferred = nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) -> Some id | _ -> None) |> Set.ofList
        { Entry = Some entry.EntryLambda; Candidates = candidates; Deferred = deferred }

/// Every incoming call must lead back to the covering program entry or to an
/// explicit deferred owner that the caller must prove covered. Closed recursive
/// groups are accepted only with such an external root; self-cycles prove nothing.
let coverage (reading: Reading) covering actual : Coverage option =
    if reading.Entry <> Some covering || reading.Deferred.Contains actual then None else
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
                { Sources = covering :: (candidate.Aliases @ (candidate.Calls |> List.map _.Site)) |> List.distinct
                  Target = implementation; Class = EdgeClass.Provenance; Role = EdgeRole.ProgramActivationCoverage; Ordinal = 0 } :: callEdges)
            Some { Dependencies = Set.toList dependencies; Evidence = evidence }
        | current :: rest when current = covering -> visit seen rest groups dependencies true
        | current :: rest when reading.Deferred.Contains current -> visit seen rest groups (Set.add current dependencies) true
        | current :: rest when Set.contains current seen -> visit seen rest groups dependencies rooted
        | current :: rest ->
            match reading.Candidates.TryFind current with
            | None -> None
            | Some candidate ->
                visit (Set.add current seen) ((candidate.Calls |> List.map (fun call -> call.Caller.Value)) @ rest)
                    ((current, candidate) :: groups) dependencies rooted
    visit Set.empty [actual] [] Set.empty false

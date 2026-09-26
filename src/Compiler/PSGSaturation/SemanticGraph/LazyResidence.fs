// SPDX-License-Identifier: MIT
/// Complete-use residence for canonical explicit lazy environments. Preparing
/// a destination does not prove its lifetime: exact calls, aliases, force uses,
/// and retained cells are rechecked against the current graph here.
module Clef.Compiler.PSGSaturation.SemanticGraph.LazyResidence

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Closures
module Lazy = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues

type Residual = { Site: NodeId; Participants: NodeId list; Reason: string }
type Reading = {
    Sites: Map<NodeId, EscapeKind>
    Destinations: Map<NodeId, NodeId>
    Evidence: Hyperedge list
    Residuals: Residual list
}

type private Destination = {
    Factory: NodeId
    Constructor: NodeId
    Formation: NodeId
    Formal: NodeId
    FinalPath: NodeId list
    Calls: (NodeId * NodeId * NodeId) list // invocation, allocation, actual destination
}

let analyze (graph: SemanticGraph) : Reading =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let memoization = Lazy.settle graph
    let callable = lazy (CallableOrigins.resolve graph)
    let activations = lazy (ProgramActivation.analyze graph)
    let incidence = nodes.Values |> Seq.collect structuralIncidence |> Seq.toList
    let structural = incidence |> List.filter Hyperedge.isStructural
    let users source = structural |> List.filter (fun edge -> List.contains source edge.Sources)
    let parents = structural |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge.Target))
                  |> List.groupBy fst |> List.map (fun (source, pairs) -> source, pairs |> List.map snd |> List.distinct) |> Map.ofList
    let activation id =
        let rec walk seen pending found missing =
            match pending with
            | [] -> if missing then None else match Set.toList found with [owner] -> Some owner | _ -> None
            | id :: rest when Set.contains id seen -> walk seen rest found missing
            | id :: rest ->
                let seen = Set.add id seen
                match nodes.TryFind id with
                | Some { Kind = SemanticKind.Lambda _ } -> walk seen rest (Set.add id found) missing
                | _ ->
                    match parents.TryFind id with
                    | Some enclosing when not enclosing.IsEmpty -> walk seen (enclosing @ rest) found missing
                    | _ -> walk seen rest found true
        walk Set.empty [id] Set.empty false
    let rec coveredFrom covering seen actual =
        if covering = actual then true
        elif Set.contains actual seen then false
        else
            ProgramActivation.coverage activations.Value covering actual
            |> Option.exists (fun coverage ->
                coverage.Dependencies |> List.forall (coveredFrom covering (Set.add actual seen)))
    let covered covering actual = coveredFrom covering Set.empty actual
    let rec withinInitialization seen target id =
        if id = target then true
        elif Set.contains id seen then false
        else
            match nodes.TryFind id with
            | Some { Kind = SemanticKind.Lambda _ } -> false
            | _ -> parents.TryFind id |> Option.defaultValue [] |> List.exists (withinInitialization (Set.add id seen) target)
    let programSlots site =
        ProgramInitialization.read graph |> Option.map (fun plan ->
            plan.Initializers |> List.filter (fun row ->
                plan.ValueBindings.Contains row.Binding && withinInitialization Set.empty row.Initializer site)) |> Option.defaultValue []
    let rec repeated seen id =
        if Set.contains id seen then false else
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Lambda _ } -> false
        | Some { Kind = SemanticKind.WhileLoop _ | SemanticKind.ForLoop _ | SemanticKind.ForEach _ } -> true
        | _ -> parents.TryFind id |> Option.defaultValue [] |> List.exists (repeated (Set.add id seen))
    let rec allocation seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.LazyAllocate _; Type = ty } when applySubst ty = Lazy.environmentType -> Some id
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _); Type = ty }
            when applySubst ty = Lazy.environmentType -> allocation seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [source]; Type = ty }
            when applySubst ty = Lazy.environmentType -> allocation seen source
        | Some { Kind = SemanticKind.EagerExpr source }
            when ExplicitDemand.operand graph id = Some source -> allocation seen source
        | _ -> None
    let rec finalValue seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.LazyValue(_, environment) } -> Some(id, environment, [id])
        | Some { Kind = SemanticKind.Sequential values } ->
            List.tryLast values |> Option.bind (finalValue seen) |> Option.map (fun (owner, environment, path) -> owner, environment, id :: path)
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } ->
            finalValue seen value |> Option.map (fun (owner, environment, path) -> owner, environment, id :: path)
        | Some { Kind = SemanticKind.EagerExpr value }
            when ExplicitDemand.operand graph id = Some value ->
            finalValue seen value |> Option.map (fun (owner, environment, path) -> owner, environment, id :: path)
        | _ -> None
    let rec uniqueFinal seen factory body id =
        if Set.contains id seen then false else
        let seen = Set.add id seen
        match users id with
        | [edge] when id = body -> edge.Target = factory && edge.Role = EdgeRole.Body
        | [edge] ->
            match nodes.TryFind edge.Target with
            | Some { Kind = SemanticKind.LazyValue(_, environment) } when environment = id -> uniqueFinal seen factory body edge.Target
            | Some { Kind = SemanticKind.Sequential values } when List.tryLast values = Some id -> uniqueFinal seen factory body edge.Target
            | Some { Kind = SemanticKind.TypeAnnotation(value, _) } when value = id -> uniqueFinal seen factory body edge.Target
            | Some { Kind = SemanticKind.EagerExpr value }
                when value = id && ExplicitDemand.operand graph edge.Target = Some value -> uniqueFinal seen factory body edge.Target
            | _ -> false
        | _ -> false
    let destinations =
        graph.Edges
        |> List.filter (fun edge -> edge.Role = EdgeRole.LazyResultDestination)
        |> List.groupBy _.Target
        |> List.choose (fun (constructor, rows) ->
            match rows with
            | [{ Class = EdgeClass.Provenance; Sources = [factory; owner; formal]; Ordinal = 0 }] ->
                let result =
                    nodes.TryFind factory |> Option.bind (fun node ->
                        match node.Kind with SemanticKind.Lambda(_, body, _, _, _) -> finalValue Set.empty body | _ -> None)
                match memoization.Instances.TryFind owner, nodes.TryFind factory, result with
                | Some contract, Some { Kind = SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure) },
                  Some(actualOwner, actualConstructor, path)
                    when contract.Environment = constructor && actualOwner = owner && actualConstructor = constructor &&
                         uniqueFinal Set.empty factory body constructor ->
                    let ordinal = parameters |> List.tryFindIndex (fun (_, ty, id) -> id = formal && applySubst ty = Lazy.environmentType)
                    let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyResultCall && List.tryItem 1 edge.Sources = Some constructor)
                    let supplied = rows |> List.map (fun edge ->
                        match edge.Class, edge.Sources, ordinal, nodes.TryFind edge.Target, callable.Value.Calls.TryFind edge.Target with
                        | EdgeClass.Provenance, [actualFactory; actualConstructor; actualFormal; storage; actual], Some ordinal,
                          Some { Kind = SemanticKind.Application(_, arguments) }, Some { Targets = [target]; Unknown = false; Complete = true }
                            when edge.Ordinal = 0 && actualFactory = factory && actualConstructor = constructor && actualFormal = formal &&
                                 target.Lambda = factory && arguments.Length = parameters.Length && List.tryItem ordinal arguments = Some actual &&
                                 allocation Set.empty actual = Some storage &&
                                 (nodes.TryFind formal |> Option.exists (fun node ->
                                     match node.Kind with SemanticKind.PatternBinding _ -> applySubst node.Type = Lazy.environmentType | _ -> false)) &&
                                 (nodes.TryFind storage |> Option.exists (fun node -> node.Kind = SemanticKind.LazyAllocate owner && applySubst node.Type = Lazy.environmentType)) ->
                            Some(edge.Target, storage, actual)
                        | _ -> None)
                    let allCalls = callable.Value.Calls |> Map.toList |> List.choose (fun (id, call) ->
                        if call.Targets |> List.exists (fun target -> target.Lambda = factory) then Some id else None) |> Set.ofList
                    let claimed = rows |> List.map _.Target |> Set.ofList
                    let allocations = supplied |> List.choose id |> List.map (fun (_, storage, _) -> storage) |> Set.ofList
                    if not supplied.IsEmpty && List.forall Option.isSome supplied && claimed.Count = rows.Length &&
                       allocations.Count = rows.Length && claimed = allCalls then
                        Some(constructor, { Factory = factory; Constructor = constructor; Formation = owner; Formal = formal
                                            FinalPath = path; Calls = List.choose id supplied })
                    else None
                | _ -> None
            | _ -> None)
        |> Map.ofList
    let destinationCalls = destinations.Values |> Seq.collect (fun destination ->
        destination.Calls |> List.map (fun (call, storage, actual) -> call, (destination, storage, actual))) |> Map.ofSeq
    let destinationAllocations = destinationCalls |> Map.toList |> List.map (fun (call, (destination, storage, actual)) -> storage, (destination, call, actual)) |> Map.ofList
    let references = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Reference)
                     |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
                     |> List.groupBy fst |> List.map (fun (id, uses) -> id, uses |> List.map snd) |> Map.ofList
    let protocols = memoization.Forces.Values |> Seq.toList
    let calls = protocols |> List.map _.Invocation |> Set.ofList
    let accesses = protocols |> List.collect (fun proof -> [proof.Condition; proof.CachedRead; proof.ResultStore; proof.Publication]) |> Set.ofList
    let pending site participants reason = Error { Site = site; Participants = participants; Reason = reason }
    let combine left right = left |> Result.bind (fun first -> right () |> Result.map (fun second -> first @ second))
    let scope site covering consumer =
        match activation consumer with
        | Some actual when covered covering actual -> Ok [consumer; actual]
        | _ -> pending site [consumer] "A lazy value use crosses an unproved or ambiguous activation."
    let rec bounded site covering seen value =
        if Set.contains value seen then pending site [value] "Lazy value flow is recursive without a rooted covering use proof." else
        let seen = Set.add value seen
        let follow next = combine (scope site covering next) (fun () -> bounded site covering seen next)
        let structuralProof = users value |> List.fold (fun proof edge -> combine proof (fun () ->
            match nodes[edge.Target].Kind, edge.Role with
            | SemanticKind.Binding(_, false, _, _), _ | SemanticKind.TypeAnnotation _, _ -> follow edge.Target
            | SemanticKind.EagerExpr operand, _
                when operand = value && ExplicitDemand.operand graph edge.Target = Some value -> follow edge.Target
            | SemanticKind.LazyValue(_, environment), _ when value = environment -> follow edge.Target
            | SemanticKind.LazyEnvironmentReference _, _ -> follow edge.Target
            | SemanticKind.Sequential actions, _ ->
                if List.tryLast actions = Some value then follow edge.Target else scope site covering edge.Target
            | SemanticKind.IfThenElse _, (EdgeRole.ThenBranch | EdgeRole.ElseBranch) -> follow edge.Target
            | SemanticKind.LazyRead _, EdgeRole.Subject | SemanticKind.LazyWrite _, EdgeRole.Subject
                when accesses.Contains edge.Target -> scope site covering edge.Target
            | SemanticKind.Application _, EdgeRole.Argument when calls.Contains edge.Target -> scope site covering edge.Target
            | SemanticKind.Application _, EdgeRole.Argument ->
                match destinationCalls.TryFind edge.Target with
                | Some(_, storage, actual) when value = actual && storage = site -> follow edge.Target
                | _ -> pending site [edge.Target] "A lazy operand has no complete admitted force or destination use."
            | SemanticKind.Lambda _, EdgeRole.Parameter -> scope site covering edge.Target
            | _ -> pending site [edge.Target] "A lazy value is returned, retained, or consumed outside its proved use set.")) (Ok [])
        let referenceProof () = references.TryFind value |> Option.defaultValue [] |> List.fold (fun proof edge ->
            combine proof (fun () ->
                match nodes.TryFind edge.Target with
                | Some { Kind = SemanticKind.VarRef(_, Some actual) } when actual = value && edge.Sources = [value] && edge.Role = EdgeRole.Definition -> follow edge.Target
                | Some { Kind = SemanticKind.ModuleDef(_, members) }
                    when edge.Role = EdgeRole.Member && List.tryItem edge.Ordinal members = Some value -> Ok []
                | None when graph.Nodes.ContainsKey edge.Target -> Ok []
                | _ -> pending site [edge.Target] "An independent lazy reference is not covered by the storage use proof.")) (Ok [])
        combine structuralProof referenceProof
    let isScalar ty =
        match Types.tryGetNTUKind (applySubst ty) with
        | Some (NTUKind.NTUint _ | NTUKind.NTUuint _ | NTUKind.NTUfloat _ | NTUKind.NTUposit _ | NTUKind.NTUbool | NTUKind.NTUchar | NTUKind.NTUunit) -> true
        | _ -> false
    let isString ty = Types.tryGetNTUKind (applySubst ty) = Some NTUKind.NTUstring
    let retainedString (contract: Lazy.Instance) value =
        StaticStringLayout.retainedViews graph (fun node ->
            match node.Kind with
            | SemanticKind.LazyRead(environment, slot) ->
                Lazy.captureEnvironment graph contract environment |> Option.bind (fun path ->
                    contract.Captured |> List.tryPick (fun (source, initializer, mutableCell) ->
                        if source = slot && not mutableCell then Some(slot :: path, [initializer]) else None))
            | _ -> None
        ) value
    let residuals = ResizeArray<Residual>()
    let evidence = ResizeArray<Hyperedge>()
    let mutable sites = Map.empty
    for node in nodes.Values do
        let owner =
            match node.Kind with
            | SemanticKind.LazyEnvironment(owner, _) when not (destinations.ContainsKey node.Id) -> Some owner
            | SemanticKind.LazyAllocate owner -> Some owner
            | _ -> None
        match owner with
        | None -> ()
        | Some owner ->
            let proof =
                match memoization.Instances.TryFind owner, activation node.Id with
                | Some contract, Some covering when memoization.Residuals.IsEmpty &&
                    (match node.Kind with SemanticKind.LazyEnvironment _ -> contract.Environment = node.Id | _ -> true) ->
                    let destinationProof =
                        match node.Kind with
                        | SemanticKind.LazyAllocate _ when not (destinationAllocations.ContainsKey node.Id) ->
                            pending node.Id [owner] "The lazy result allocation has no exact complete-call destination relation."
                        | _ -> Ok []
                    let captures () = contract.Captured |> List.fold (fun proof (slot, value, mutableCell) ->
                        combine proof (fun () ->
                            if mutableCell then
                                match activation slot with
                                | Some cellActivation when covered cellActivation covering ->
                                    bounded node.Id cellActivation Set.empty node.Id
                                | _ -> pending node.Id [slot; value] "The original mutable capture cell does not cover every lazy instance use."
                            elif isScalar nodes[slot].Type then Ok [slot; value]
                            elif isString nodes[slot].Type then
                                match retainedString contract value with
                                | Some backing -> Ok(slot :: backing)
                                | None -> pending node.Id [slot; value] "The retained string capture has no current immutable program-storage proof."
                            else pending node.Id [slot; value] "A retained lazy capture requires complete backing-storage coverage.")) (Ok [])
                    let resultCoverage () =
                        if isScalar contract.ElementType then Ok []
                        elif isString contract.ElementType then
                            match retainedString contract contract.ThunkBody with
                            | Some backing -> Ok(contract.Cached :: backing)
                            | None -> pending node.Id [contract.Cached; contract.ThunkBody] "The cached string result has no current immutable program-storage proof."
                        else pending node.Id [contract.Cached; contract.ThunkBody] "A cached view or callable requires a result-storage lifetime protocol."
                    let authority =
                        match programSlots node.Id with
                        | [] -> Ok(EscapeKind.StackScoped, [])
                        | [row] ->
                            match ProgramInitialization.tryValueAuthority graph row.Binding with
                            | Some authority -> Ok(EscapeKind.StaticLifetime, row.Binding :: authority.Evidence.Sources)
                            | None -> pending node.Id [row.Binding] "Program-lifetime lazy caching requires declared writable storage authority."
                        | rows -> pending node.Id (rows |> List.map _.Binding) "A lazy allocation belongs to ambiguous program initializers."
                    if repeated Set.empty node.Id then
                        pending node.Id [] "Repeated lazy allocation requires a bounded activation region or proved storage reuse."
                    else
                        authority |> Result.bind (fun (residence, authority) ->
                            combine destinationProof (fun () ->
                                combine (resultCoverage ()) (fun () ->
                                    combine (captures ()) (fun () -> bounded node.Id covering Set.empty node.Id)))
                            |> Result.map (fun dependencies -> covering, residence, authority @ dependencies))
                | _ -> pending node.Id [owner] "Lazy formation, force protocol, or activation is unresolved."
            match proof with
            | Error reason -> residuals.Add reason
            | Ok(covering, residence, dependencies) ->
                sites <- sites.Add(node.Id, residence)
                let destination = destinationAllocations.TryFind node.Id |> Option.map (fun (destination, call, actual) ->
                    [destination.Factory; destination.Constructor; destination.Formal; call; actual] @ destination.FinalPath) |> Option.defaultValue []
                let captureUses = memoization.CaptureUses.TryFind owner |> Option.defaultValue []
                let participants = node.Id :: covering :: (destination @ dependencies @ captureUses) |> List.distinct
                evidence.Add { Class = EdgeClass.Provenance; Role = EdgeRole.LazyResidence; Sources = participants; Target = owner; Ordinal = 0 }
    { Sites = sites; Destinations = destinations |> Map.map (fun _ destination -> destination.Formal)
      Evidence = List.ofSeq evidence; Residuals = List.ofSeq residuals }

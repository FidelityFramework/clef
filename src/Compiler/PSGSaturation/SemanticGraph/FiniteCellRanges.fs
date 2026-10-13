// SPDX-License-Identifier: MIT
/// Finite ordinary activations bound affine updates to program and local cells.
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
module Borrows = Clef.Compiler.Baker.Ingredients.SourceStorageBorrows

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
    let ingress = CallableIngress.analyzeWith graph calls
    let sequencePulls =
        lazy
            (Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.currentPulls graph
             |> List.map (fun pull -> pull.Loop, pull)
             |> Map.ofList)

    let generatorInstructions = lazy (
        Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.currentInstructionExecutions graph
        |> List.collect (fun proof ->
            proof.LocalInitializers |> Set.toList |> List.collect (fun cell ->
                let writes = nodes.Values |> Seq.choose (fun node ->
                    match node.Kind with
                    | SemanticKind.Set(target, _) ->
                        match nodes.TryFind target with
                        | Some { Kind = SemanticKind.VarRef(_, Some actual) } when actual = cell -> Some node.Id
                        | _ -> None
                    | _ -> None) |> Seq.toList
                (cell :: writes) |> List.choose (fun id ->
                    proof.MaximumVisits.TryFind id |> Option.map (fun visits -> id, (visits, proof.Participants)))))
        |> List.groupBy fst |> List.choose (fun (id, claims) ->
            match claims with [_, evidence] -> Some(id, evidence) | _ -> None) |> Map.ofList)

    let complete site implementation =
        calls.Calls.TryFind site |> Option.filter (fun call ->
            valid site && call.Complete && not call.Unknown && not call.Targets.IsEmpty &&
            (call.Targets |> List.exists (fun target -> target.Lambda = implementation)) &&
            call.Targets |> List.forall (fun target ->
                valid target.Lambda && valid target.Body &&
                target.Parameters.Length = target.Arguments.Length &&
                List.zip target.Parameters target.Arguments |> List.forall (fun ((_, ty, formal), actual) ->
                    same formal actual && applySubst nodes[formal].Type = applySubst ty)))
    // Zero belongs to the ordinary demand owner's current inactivity proof,
    // never to an empty observed invocation list or closure retention alone.
    let inactivity = lazy (OrdinaryDemand.analyze graph).Inactivity
    let closedCache = System.Collections.Generic.Dictionary<NodeId, (NodeId list * Set<NodeId>) option>()
    let closedCalls implementation =
        match closedCache.TryGetValue implementation with
        | true, result -> result
        | _ ->
            // The ingress owner supplies the complete incoming-use census.
            // This owner still proves finite execution; closure membership is
            // neither an invocation count nor an excuse to ignore recursion.
            let result =
                CallableIngress.tryFamily ingress implementation
                |> Option.bind (fun family ->
                    let sites =
                        family.Evidence.Calls
                        |> List.filter (fun call -> call.Implementation = implementation)
                        |> List.map _.Site
                        |> List.distinct

                    if sites |> List.exists (fun site -> complete site implementation |> Option.isNone) then
                        None
                    elif not (family.Activated.Contains implementation) then
                        inactivity.Value.TryFind implementation
                        |> Option.bind (fun proof ->
                            let currentCalls =
                                nodes.Values
                                |> Seq.choose (fun node ->
                                    match node.Kind with
                                    | SemanticKind.Application _ when
                                        CallableIngress.tryExecutionOwner ingress node.Id = Some implementation
                                        ->
                                        Some node.Id
                                    | _ -> None)
                                |> Set.ofSeq

                            if not (Set.isSubset currentCalls proof.Calls) then
                                None
                            else
                                Some(
                                    [],
                                    Set.unionMany
                                        [
                                            family.Evidence.Participants
                                            OrdinaryDemand.inactivityParticipants proof
                                            proof.Excluded
                                            proof.Calls
                                            Set.ofList (proof.Implementation :: proof.Body :: proof.Parameters)
                                        ]
                                ))
                    elif sites.IsEmpty then
                        None
                    else
                        Some(sites, family.Evidence.Participants))

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
        let incoming () =
            let inputs = parents id

            if inputs.IsEmpty then
                None
            else
                inputs
                |> List.fold
                    (fun total edge ->
                        let contribution =
                            match nodes[edge.Target].Kind with
                            | SemanticKind.WhileLoop(guard, body) ->
                                sequencePulls.Value.TryFind edge.Target
                                |> Option.bind (fun pull ->
                                    let repetitions =
                                        if edge.Role = EdgeRole.Body && body = id && pull.Body = body then
                                            Some pull.Pulls.MaximumPulls
                                        elif edge.Role = EdgeRole.Guard && guard = id && pull.Guard = guard then
                                            Some(pull.Pulls.MaximumPulls + 1I)
                                        else
                                            None

                                    repetitions
                                    |> Option.bind (fun repetitions ->
                                        count seen edge.Target
                                        |> Option.map (fun (bound, required) ->
                                            repetitions * bound, Set.union required (Set.ofList pull.Participants))))
                            | _ -> count seen edge.Target

                        match total, contribution with
                        | Some(bound, required), Some(more, dependencies) -> Some(bound + more, Set.union required dependencies)
                        | _ -> None)
                    (Some(0I, Set.singleton id))

        if generatorInstructions.Value.ContainsKey id then generatorInstructions.Value.TryFind id
        elif id = startup.EntryLambda then
            if entryUncalled then Some(1I, startupParticipants) else None
        else
            match nodes[id].Kind with
            | SemanticKind.Lambda(_, _, _, _, LambdaContext.RegularClosure) ->
                closedCalls id |> Option.bind (fun (sites, dependencies) ->
                    sum sites |> Option.map (fun (bound, required) -> bound, Set.union dependencies required))
            | SemanticKind.WhileLoop _ ->
                sequencePulls.Value.TryFind id |> Option.bind (fun pull ->
                    if CallableIngress.tryExecutionOwner ingress id <> Some pull.Owner then None else
                    incoming () |> Option.map (fun (bound, required) ->
                        bound, Set.union required (Set.ofList pull.Participants)))
            | SemanticKind.Lambda _ | SemanticKind.ForLoop _
            | SemanticKind.ForEach _ | SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ -> None
            | _ -> incoming ()
    let environmentOrigins = lazy (ClosureEnvironments.origins graph)
    let environmentCalls = lazy (ClosureEnvironments.callEnvironments graph)
    let captureCache = System.Collections.Generic.Dictionary<NodeId * NodeId, (NodeId * Set<NodeId>) option>()
    let capture cell owner =
        let key = cell, owner
        match captureCache.TryGetValue key with
        | true, result -> result
        | _ ->
            let result =
                match nodes.TryFind owner with
                | Some { Kind = SemanticKind.Lambda(_, _, captures, _, LambdaContext.RegularClosure) } when valid owner ->
                    match captures |> List.filter (fun capture -> capture.SourceNodeId = Some cell) with
                    | [capture] when capture.IsMutable && applySubst capture.Type = applySubst nodes[cell].Type ->
                        closedCalls owner |> Option.map (fun (_, required) -> owner, Set.add cell required)
                    | _ -> None
                | Some { Kind = SemanticKind.ClosureValue(implementation, environment) }
                    when valid owner && valid implementation && valid environment ->
                    match ClosureEnvironments.capturedInitializers graph owner with
                    | Some initializers when (initializers |> List.filter (fun (slot, _, _) -> slot = cell)) = [cell, cell, true] ->
                        let formals = graph.Edges |> List.filter (fun edge ->
                            edge.Role = EdgeRole.EnvironmentFormal && edge.Sources = [owner; implementation])
                        match formals, closedCalls implementation with
                        | [formal], Some(sites, required) when valid formal.Target &&
                            environmentOrigins.Value.TryFind formal.Target = Some owner &&
                            (sites |> List.forall (fun site ->
                                environmentCalls.Value.TryFind site |> Option.exists (fun (_, actual) ->
                                    environmentOrigins.Value.TryFind actual = Some owner))) ->
                            let formation = initializers |> List.collect (fun (slot, value, _) -> [slot; value])
                            Some(implementation, Set.union required (Set.ofList (owner :: implementation :: environment :: formal.Target :: formation)))
                        | _ -> None
                    | _ -> None
                | _ -> None
            captureCache[key] <- result
            result
    // Environment identity comes from the closure owner. Here the finite
    // writer proof additionally requires the actual access to be in that code
    // body, through its exact formal. Arbitrary environment aliases and writable
    // borrows remain outside this bounded ordinary-activation rule.
    let environmentAccess cell (node: SemanticNode) =
        let environment =
            match node.Kind with
            | SemanticKind.EnvironmentRead(environment, slot)
            | SemanticKind.EnvironmentWrite(environment, slot, _) when slot = cell -> Some environment
            | _ -> None
        environment |> Option.bind (fun environment ->
            if not (valid node.Id && valid environment) then None else
            let formal =
                match nodes[environment].Kind with
                | SemanticKind.VarRef(_, Some formal) | SemanticKind.EnvironmentReference formal -> Some formal
                | _ -> None
            match formal, environmentOrigins.Value.TryFind environment with
            | Some formal, Some owner when valid formal &&
                applySubst nodes[environment].Type = ClosureEnvironments.environmentType ->
                capture cell owner |> Option.bind (fun (implementation, required) ->
                    let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EnvironmentFormal && edge.Target = formal)
                    match rows with
                    | [{ Class = EdgeClass.Provenance; Sources = [actualOwner; actualImplementation] }]
                        when actualOwner = owner && actualImplementation = implementation &&
                             CallableIngress.tryExecutionOwner ingress node.Id = Some implementation ->
                        Some(owner, Set.union required (Set.ofList [node.Id; environment; formal]))
                    | _ -> None)
            | _ -> None)
    let captureSupport cell =
        nodes.Values |> Seq.fold (fun accumulated node ->
            let next =
                match node.Kind with
                | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures)
                | SemanticKind.LazyExpr(_, captures) when captures |> List.exists (fun capture -> capture.SourceNodeId = Some cell) ->
                    capture cell node.Id |> Option.map snd
                | SemanticKind.EnvironmentCreate(owner, initializers) when initializers |> List.exists (fun (slot, value) -> slot = cell || value = cell) ->
                    capture cell owner |> Option.map snd
                | SemanticKind.EnvironmentRead(_, slot) | SemanticKind.EnvironmentWrite(_, slot, _) when slot = cell ->
                    environmentAccess cell node |> Option.map snd
                | SemanticKind.EnvironmentBorrow(_, slot) | SemanticKind.FrameRead(_, slot)
                | SemanticKind.FrameBorrow(_, slot) | SemanticKind.FrameWrite(_, slot, _)
                | SemanticKind.LazyRead(_, slot) | SemanticKind.LazyBorrow(_, slot)
                | SemanticKind.LazyWrite(_, slot, _) when slot = cell -> None
                | _ -> Some Set.empty
            match accumulated, next with
            | Some prior, Some required -> Some(Set.union prior required)
            | _ -> None) (Some Set.empty)
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
    let readCell cell id =
        same cell id &&
        (match nodes[id].Kind with
         | SemanticKind.VarRef(_, Some source) -> source = cell
         | SemanticKind.EnvironmentRead _ -> environmentAccess cell nodes[id] |> Option.isSome
         | _ -> false)
    // One magnitude interpreter owns constants and affine returns. The finite
    // worklist substitutes exact source actuals; neither graph rewriting nor
    // compiler/pass re-entry is involved. Path cycles and recursive calls refuse.
    let magnitude cell expected (initialSeen: Set<NodeId>) root =
        if not (valid root) || applySubst nodes[root].Type <> expected then
            None
        else
            let externalImplementations =
                (Clef.Compiler.Baker.Recipes.BoundaryDeclarations.elaborate graph).NewEdges
                |> List.choose (fun edge ->
                    match edge.Role with
                    | EdgeRole.BoundaryDeclaration declaration -> Some declaration.Implementation
                    | _ -> None)
                |> Set.ofList
            let emptyFacts: Map<NodeId * Map<NodeId, NodeId> * Set<NodeId>, (bigint * bigint * Set<NodeId>) option> =
                Map.empty

            let emptyEquations
                : Map<
                      NodeId * Map<NodeId, NodeId> * Set<NodeId>,
                      (NodeId * Map<NodeId, NodeId> * Set<NodeId>) list *
                      ((bigint * bigint * Set<NodeId>) list -> (bigint * bigint * Set<NodeId>) option)
                   > =
                Map.empty

            let first = root, Map.empty, Set.empty
            let initial = [ first, false, Set.empty ], emptyFacts, emptyEquations

            let join support values =
                Some(
                    values |> List.map (fun (a, _, _) -> a) |> List.fold max 0I,
                    values |> List.map (fun (_, b, _) -> b) |> List.fold max 0I,
                    Set.unionMany (support :: (values |> List.map (fun (_, _, p) -> p)))
                )

            let step
                (
                    pending,
                    facts: Map<NodeId * Map<NodeId, NodeId> * Set<NodeId>, (bigint * bigint * Set<NodeId>) option>,
                    equations:
                        Map<
                            NodeId * Map<NodeId, NodeId> * Set<NodeId>,
                            (NodeId * Map<NodeId, NodeId> * Set<NodeId>) list *
                            ((bigint * bigint * Set<NodeId>) list -> (bigint * bigint * Set<NodeId>) option)
                         >
                ) =
                match pending with
                | [] -> None
                | (((id, environment, callPath) as term), ready, (path: Set<NodeId * Map<NodeId, NodeId> * Set<NodeId>>)) :: rest ->
                    let next =
                        if facts.ContainsKey term then
                            rest, facts, equations
                        else if ready then
                            let dependencies, combine = equations[term]
                            let values = dependencies |> List.map (fun dependency -> facts[dependency])

                            let fact =
                                if values |> List.exists Option.isNone then
                                    None
                                else
                                    combine (List.choose (fun value -> value) values)

                            rest, facts.Add(term, fact), equations
                        elif initialSeen.Contains id || path.Contains term || not (valid id) then
                            rest, facts.Add(term, None), equations
                        else
                            let support = Set.singleton id

                            let forward source =
                                if valid source && same id source then
                                    Some([ source, environment, callPath ], fun values -> join support values)
                                else
                                    None

                            let decomposition =
                                if cell |> Option.exists (fun cell -> readCell cell id) then
                                    Some([], fun _ -> Some(1I, 0I, Set.ofList [ cell.Value; id ]))
                                else
                                    match nodes[id].Kind with
                                    | SemanticKind.Literal(NativeLiteral.Int(value, _)) ->
                                        Some([], fun _ -> Some(0I, abs (bigint value), support))
                                    | SemanticKind.Literal(NativeLiteral.UInt(value, _)) ->
                                        Some([], fun _ -> Some(0I, bigint value, support))
                                    | SemanticKind.VarRef(_, Some source) -> forward source
                                    | SemanticKind.Binding(_, false, false, None) when nodes[id].Children.Length = 1 ->
                                        forward nodes[id].Children.Head
                                    | SemanticKind.TypeAnnotation(source, declared) when applySubst declared = applySubst nodes[id].Type ->
                                        forward source
                                    | SemanticKind.EagerExpr source when ExplicitDemand.operand graph id = Some source -> forward source
                                    | SemanticKind.Sequential values when not values.IsEmpty && (values |> List.forall valid) ->
                                        forward (List.last values)
                                    | SemanticKind.PatternBinding _ ->
                                        match environment.TryFind id with
                                        | Some actual -> forward actual
                                        | None ->
                                            formalOwners.TryFind id
                                            |> Option.bind (fun owner ->
                                                closedCalls owner
                                                |> Option.bind (fun (sites, required) ->
                                                    let actuals =
                                                        sites
                                                        |> List.map (fun site ->
                                                            complete site owner
                                                            |> Option.bind (fun call ->
                                                                call.Targets
                                                                |> List.filter (fun target -> target.Lambda = owner)
                                                                |> List.collect (fun (target: CallableOrigins.CallTarget) ->
                                                                    List.zip target.Parameters target.Arguments
                                                                    |> List.choose (fun ((_, _, formal), actual) ->
                                                                        if formal = id then Some actual else None))
                                                                |> List.distinct
                                                                |> function
                                                                    | [ actual ] when valid actual && same id actual -> Some actual
                                                                    | _ -> None))

                                                    if actuals |> List.exists Option.isNone then
                                                        None
                                                    else
                                                        Some(
                                                            List.choose (fun value -> value) actuals
                                                            |> List.map (fun actual -> actual, environment, callPath),
                                                            join (Set.add id required)
                                                        )))
                                    | SemanticKind.Application _ ->
                                        match operator id with
                                        | Some(("op_Addition" | "op_Subtraction"), callee, left, right) ->
                                            Some(
                                                [ left, environment, callPath; right, environment, callPath ],
                                                function
                                                | [ a, b, p; c, d, q ] ->
                                                    Some(a + c, b + d, Set.unionMany [ support; Set.singleton callee; p; q ])
                                                | _ -> None
                                            )
                                        | Some("op_Multiply", callee, left, right) ->
                                            Some(
                                                [ left, environment, callPath; right, environment, callPath ],
                                                function
                                                | [ a, b, p; c, d, q ] ->
                                                    let scalar source =
                                                        match applySubst nodes[source].Type with
                                                        | NativeType.TNum(_, dimension) ->
                                                            dimension = Dimension.one
                                                            && Types.tryGetNTUKind nodes[source].Type =
                                                                Types.tryGetNTUKind nodes[id].Type
                                                        | _ -> false

                                                    let required = Set.unionMany [ support; Set.singleton callee; p; q ]

                                                    if c = 0I && scalar right then Some(a * d, b * d, required)
                                                    elif a = 0I && scalar left then Some(c * b, d * b, required)
                                                    else None
                                                | _ -> None
                                            )
                                        | _ ->
                                            calls.Calls.TryFind id
                                            |> Option.bind (fun call ->
                                                if not call.Complete || call.Unknown || call.Targets.IsEmpty then
                                                    None
                                                else
                                                    let targets =
                                                        call.Targets
                                                        |> List.map (fun target ->
                                                            match nodes.TryFind target.Lambda with
                                                            | Some {
                                                                       Kind = SemanticKind.Lambda(parameters,
                                                                                                  body,
                                                                                                  [],
                                                                                                  _,
                                                                                                  LambdaContext.RegularClosure)
                                                                   } when
                                                                parameters = target.Parameters
                                                                && parameters.Length = target.Arguments.Length
                                                                && not (callPath.Contains target.Lambda)
                                                                && not (externalImplementations.Contains target.Lambda)
                                                                && valid target.Lambda
                                                                && valid body
                                                                && same id body
                                                                && List.forall2
                                                                    (fun (_, ty, _) actual ->
                                                                        valid actual && applySubst ty = applySubst nodes[actual].Type)
                                                                    parameters
                                                                    target.Arguments
                                                                ->
                                                                let substituted =
                                                                    List.zip parameters target.Arguments
                                                                    |> List.fold
                                                                        (fun found ((_, _, formal), actual) ->
                                                                            Map.add formal actual found)
                                                                        environment

                                                                Some(
                                                                    (body, substituted, Set.add target.Lambda callPath),
                                                                    Set.ofList (
                                                                        target.Lambda :: body :: target.Arguments
                                                                        @ (parameters |> List.map (fun (_, _, formal) -> formal))
                                                                    )
                                                                )
                                                            | _ -> None)

                                                    if targets |> List.exists Option.isNone then
                                                        None
                                                    else
                                                        let targets = List.choose (fun value -> value) targets

                                                        Some(
                                                            List.map fst targets,
                                                            join (Set.unionMany (support :: (targets |> List.map snd)))
                                                        ))
                                    | _ -> None

                            match decomposition with
                            | None -> rest, facts.Add(term, None), equations
                            | Some(dependencies, combine) ->
                                let nextPending =
                                    (dependencies
                                     |> List.map (fun dependency -> dependency, false, Set.add term path))
                                    @ ((term, true, path) :: rest)

                                nextPending, facts, equations.Add(term, (dependencies, combine))

                    Some(next, next)

            let _, facts, _ =
                Seq.unfold step initial |> Seq.tryLast |> Option.defaultValue initial

            facts[first]

    let constant seen expected id =
        magnitude None expected seen id
        |> Option.bind (fun (scale, value, required) -> if scale = 0I then Some(value, required) else None)

    let affine cell seen id =
        magnitude (Some cell) (applySubst nodes[cell].Type) seen id
    // A local declaration must initialize before every use in its one lexical
    // sequence. Inspect all actual containment paths, not the advisory Parent
    // field. A captured body's access is ordered by its exact formation, never
    // by the rewritten implementation's declaration or advisory parent.
    let localInitialization cell =
        match parents cell with
        | [declaration] when valid declaration.Target ->
            match nodes[declaration.Target].Kind, count Set.empty cell with
            | SemanticKind.Sequential values, Some(activations, activationSources)
                when activations > 0I && declaration.Role = EdgeRole.Element &&
                     List.tryItem declaration.Ordinal values = Some cell ->
                let rec after seen id =
                    if Set.contains id seen || not (valid id) then None else
                    let seen = Set.add id seen
                    let incoming = parents id
                    if incoming.IsEmpty then None else
                    incoming |> List.fold (fun state edge ->
                        let next =
                            if not (valid edge.Target) then None
                            elif edge.Target = declaration.Target then
                                if edge.Role = EdgeRole.Element && edge.Ordinal > declaration.Ordinal &&
                                   List.tryItem edge.Ordinal values = Some id then Some(Set.ofList [id; edge.Target]) else None
                            else
                                match nodes[edge.Target].Kind with
                                | SemanticKind.Lambda _ ->
                                    let formations = nodes.Values |> Seq.choose (fun node ->
                                        capture cell node.Id |> Option.bind (fun (implementation, _) ->
                                            if implementation = edge.Target then Some node.Id else None)) |> Seq.toList
                                    match formations with
                                    | [formation] -> after seen formation |> Option.map (Set.add id)
                                    | _ -> None
                                | SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ -> None
                                | _ -> after seen edge.Target |> Option.map (Set.add id)
                        match state, next with
                        | Some prior, Some required -> Some(Set.union prior required)
                        | _ -> None) (Some Set.empty)
                uses.TryFind cell |> Option.defaultValue [] |> List.fold (fun state edge ->
                    let next =
                        if key edge = key declaration then Some(Set.ofList [cell; declaration.Target]) else
                        match nodes.TryFind edge.Target, edge.Class, edge.Role with
                        | Some { Kind = SemanticKind.VarRef(_, Some source) }, EdgeClass.Reference, EdgeRole.Definition
                            when source = cell && same cell edge.Target -> after Set.empty edge.Target
                        | Some { Kind = SemanticKind.EnvironmentCreate(owner, _) }, EdgeClass.Reference, _ ->
                            capture cell owner |> Option.bind (fun (_, required) ->
                                after Set.empty owner |> Option.map (Set.union required))
                        | _ -> None
                    match state, next with
                    | Some prior, Some required -> Some(Set.union prior required)
                    | _ -> None) (Some activationSources)
                |> Option.bind (fun ordered ->
                    // Source captures are formation uses even before their
                    // environment incidence is realized. A dormant body does
                    // not authorize forming a view before the cell exists.
                    nodes.Values |> Seq.fold (fun state formation ->
                        let captured =
                            match formation.Kind with
                            | SemanticKind.Lambda(_, _, captures, _, _) ->
                                captures |> List.exists (fun capture -> capture.SourceNodeId = Some cell)
                            | _ -> false
                        if not captured then state else
                        match state, after Set.empty formation.Id with
                        | Some prior, Some required -> Some(Set.union prior required)
                        | _ -> None) (Some ordered))
            | _ -> None
        | _ -> None
    nodes.Keys |> Seq.toList |> List.choose (fun cell ->
        match nodes.TryFind cell with
        | Some node when valid cell && Types.isIntegerType node.Type ->
            match node.Kind, node.Children with
            | SemanticKind.Binding(_, true, false, None), [initializer] ->
                let initialization =
                    if startup.ValueBindings.Contains cell then Some startupParticipants
                    else localInitialization cell
                let captureParticipants = captureSupport cell
                let dangerous = nodes.Values |> Seq.exists (fun useNode ->
                    match useNode.Kind with
                    | SemanticKind.VarRef(_, Some source) when source = cell -> not (same cell useNode.Id)
                    | _ -> Borrows.takesAddress (readCell cell) ((=) cell) useNode)
                let invalidUses =
                    uses.TryFind cell |> Option.defaultValue [] |> List.exists (fun edge -> not (valid edge.Target)) ||
                    (graph.Edges |> List.exists (fun edge ->
                        (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) &&
                        List.contains cell edge.Sources && nodes.ContainsKey edge.Target && not (valid edge.Target)))
                let writes = nodes.Values |> Seq.choose (fun store ->
                    match store.Kind with
                    | SemanticKind.Set(target, value) when readCell cell target -> Some(store.Id, target, value)
                    | SemanticKind.EnvironmentWrite(environment, slot, value) when slot = cell -> Some(store.Id, environment, value)
                    | _ -> None) |> Seq.toList
                if initialization.IsNone || captureParticipants.IsNone || dangerous || invalidUses || writes.IsEmpty then None else
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
                               Participants = Set.unionMany (startupParticipants :: initialization.Value :: captureParticipants.Value :: initialDependencies :: (contributions |> List.map snd)) }
            | _ -> None
        | _ -> None)

/// A resident arithmetic certificate remains tied to its source transition,
/// complete call ingress, startup authority, every writer and activation path.
let private settleCore (bounds: Bound list) (graph: SemanticGraph) =
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

let settle bounds graph =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> settleCore bounds graph)


/// Re-establish the complete current finite-cell certificate/row inventory in
/// Baker before another owner may retain held ranges. This invokes source
/// recognition, so publication must not call it.
let private evidenceMatches (bounds: Bound list) (graph: SemanticGraph) =
    let obligations =
        graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind = "finite-cell-effects" -> Some(id, info)
            | _ -> None)
    let sameRows expected actual =
        let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
        (expected |> List.map key |> List.sort) = (actual |> List.map key |> List.sort)
    let expectedRangeRows =
        bounds |> List.collect (fun bound ->
            let sources = Set.toList bound.Participants
            bound.Cell :: (bound.Writes |> List.map _.Value)
            |> List.map (fun target ->
                { Class = EdgeClass.Range; Role = EdgeRole.FiniteCellRange; Ordinal = 0
                  Sources = sources; Target = target }))
    bounds.Length = obligations.Length &&
    sameRows expectedRangeRows (graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.FiniteCellRange)) &&
    (bounds |> List.forall (fun bound ->
        let name = sprintf "finite_cell_%d" (NodeId.value bound.Cell)
        match obligations |> List.filter (fun (_, info) -> info.Id = name) with
        | [id, info] when info.Logic = "QF_LIA" && info.Body = ObligationBody.FiniteLinearRecurrence bound.Certificate ->
            let expected : Hyperedge =
                { Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = 0
                  Sources = Set.toList bound.Participants; Target = id }
            sameRows [expected] (graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = id))
        | _ -> false))

let evidenceCurrent (graph: SemanticGraph) = evidenceMatches (recognize graph) graph

type RepresentationChange = {
    Bound: Bound
    PreviousParticipants: Set<NodeId>
    Obligation: NodeId
}

let private representationInventory (graph: SemanticGraph) =
    let proofs = graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Obligation info when info.Kind = "finite-cell-effects" -> Some(id, info)
        | _ -> None)
    let ids = proofs |> List.map fst |> Set.ofList
    let rows =
        graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.FiniteCellRange ||
            (edge.Role = EdgeRole.Constrains && ids.Contains edge.Target))
        |> List.map (fun edge -> edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target)
        |> List.sort
    proofs, rows

/// Recognize current transitions without held ranges. A new dependency set
/// earns renewal only with the original inventory intact and the same complete
/// writer/activation certificate. The owning nanopass performs any settlement.
let tryRepresentationRenewal (before: SemanticGraph) (graph: SemanticGraph) =
    let previousBounds = recognize before
    let inventory = representationInventory before
    if previousBounds.IsEmpty || not (evidenceMatches previousBounds before) ||
       inventory <> representationInventory graph then None
    else
        let current = recognize graph
        let recurrence (bound: Bound) = bound.Cell, bound.Writes, bound.Certificate
        if (previousBounds |> List.map recurrence) <> (current |> List.map recurrence) then None
        else
            let proofs, _ = inventory
            let previous = previousBounds |> List.map (fun bound -> bound.Cell, bound) |> Map.ofList
            let changed = current |> List.choose (fun bound ->
                let old = previous[bound.Cell]
                if old.Participants = bound.Participants then None
                else
                    let name = sprintf "finite_cell_%d" (NodeId.value bound.Cell)
                    let obligation = proofs |> List.find (fun (_, info) -> info.Id = name) |> fst
                    Some { Bound = bound; PreviousParticipants = old.Participants; Obligation = obligation })
            if changed.IsEmpty then None else Some changed

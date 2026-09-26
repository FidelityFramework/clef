// SPDX-License-Identifier: MIT
/// Prove bounded residence for exact sequence allocation sites. Containment
/// comes from canonical structural incidence; value flow follows resolved
/// references. An unproved escape never selects a heap or static fallback.
module Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

[<RequireQualifiedAccess>]
type ResidualReason =
    | MissingActivation
    | AmbiguousActivation of NodeId list
    | DeferredActivation of NodeId
    | ReturnsFrom of NodeId
    | StoredAt of NodeId
    | UnsupportedConsumer of NodeId
    | CrossesActivation of NodeId
    | FactoryResult of NodeId
    | UnknownInputRegion of NodeId
    | InvalidResultDestination of NodeId
    | MissingResultCapture of NodeId * NodeId
    | RecursiveValueFlow of NodeId

type Unresolved = { Site: NodeId; Reason: ResidualReason }
type Reading = {
    Sites: Map<NodeId, EscapeKind>
    Regions: Map<NodeId, NodeId>
    Evidence: Hyperedge list
    Unresolved: Unresolved list
}

type private Use =
    | Alias of NodeId
    | Consumed of NodeId
    | Invocation of call: NodeId * participants: NodeId list
    | Captured of owner: NodeId * generator: NodeId * declaration: NodeId
    | Argument of call: NodeId * actual: NodeId * targets: (NodeId * NodeId) list
    | EnvironmentCaptured of environment: NodeId * slot: NodeId * value: NodeId
    | ResultDestination of NodeId
    | Refused of ResidualReason

type private PreparedResult = {
    Constructor: NodeId
    Implementation: NodeId
    Formal: NodeId
    FinalPath: NodeId list
    Calls: (NodeId * NodeId * NodeId) list // call, actual destination, allocation
}

let private analyzeCore allowGenerators environmentSites (graph: SemanticGraph) (destinations: Map<NodeId, NodeId>) (factoryCalls: Map<NodeId, NodeId>) : Reading =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let edges node =
        let derived = kindEdges node.Id node.Kind
        let contained = derived |> List.filter Hyperedge.isStructural |> List.collect _.Sources |> Set.ofList
        derived @ (node.Children |> List.filter (fun id -> not (contained.Contains id))
                   |> List.mapi (fun ordinal id -> Hyperedge.edge1 EdgeClass.Structural EdgeRole.Attached ordinal id node.Id))
    let incidence = nodes.Values |> Seq.collect edges |> Seq.toList
    let parents =
        incidence |> List.filter Hyperedge.isStructural
        |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge.Target))
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ pairs -> pairs |> List.map snd |> List.distinct)
    let activation id =
        let rec walk seen pending found missing =
            match pending with
            | [] -> found, missing
            | current :: rest when Set.contains current seen -> walk seen rest found missing
            | current :: rest ->
                let seen = Set.add current seen
                match nodes.TryFind current with
                | Some { Kind = SemanticKind.Lambda _ } -> walk seen rest (Set.add current found) missing
                | Some { Kind = SemanticKind.ModuleDef _ } -> walk seen rest found true
                | _ ->
                    match parents.TryFind current with
                    | Some enclosing when not enclosing.IsEmpty -> walk seen (enclosing @ rest) found missing
                    | _ -> walk seen rest found true
        let found, missing = walk Set.empty [id] Set.empty false
        match Set.toList found with
        | [owner] when not missing ->
            match nodes[owner].Kind with
            | SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) when allowGenerators -> Ok owner
            | SemanticKind.Lambda(_, _, _, _, (LambdaContext.SeqGenerator | LambdaContext.LazyThunk)) ->
                Error (ResidualReason.DeferredActivation owner)
            | _ -> Ok owner
        | [] -> Error ResidualReason.MissingActivation
        | owners -> Error (ResidualReason.AmbiguousActivation owners)
    let rec intrinsic seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Intrinsic info } -> Some info
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> intrinsic seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> intrinsic seen value
        | _ -> None
    let getEnumerator node =
        match node.Kind with
        | SemanticKind.Application(callee, [input]) ->
            match intrinsic Set.empty callee with
            | Some { Module = IntrinsicModule.Seq; Operation = "getEnumerator" } -> Some input
            | _ -> None
        | _ -> None
    let environmentArguments = ClosureEnvironments.callEnvironments graph
    let knownCallable = ClosureEnvironments.tryKnown graph
    let implementation = ClosureEnvironments.tryImplementation graph
    let environmentOwner = ClosureEnvironments.tryEnvironmentOwner graph
    let programActivations = lazy (ProgramActivation.analyze graph)
    let callableOrigins = lazy (CallableOrigins.resolve graph)
    let invocationParticipants call callee arguments =
        callableOrigins.Value.Calls.TryFind call |> Option.bind (fun resolved ->
            if not resolved.Complete || resolved.Targets.IsEmpty then None else
            let targets = resolved.Targets |> List.map (fun target ->
                let formals = target.Parameters |> List.map (fun (_, _, formal) -> formal)
                let resident = target.Lambda :: target.Body :: (formals @ arguments)
                let typesAgree =
                    target.Parameters.Length = arguments.Length &&
                    List.forall2 (fun (_, ty, formal) actual ->
                        match nodes.TryFind formal, nodes.TryFind actual with
                        | Some { Kind = SemanticKind.PatternBinding _; Type = declared }, Some argument ->
                            applySubst declared = applySubst ty && applySubst argument.Type = applySubst ty
                        | _ -> false) target.Parameters arguments
                if target.Arguments = arguments && typesAgree &&
                   resident |> List.forall nodes.ContainsKey then Some resident else None)
            if targets |> List.forall Option.isSome then
                Some(callee :: (List.choose id targets |> List.concat) |> List.distinct)
            else None)
    let argumentTargets call ordinal =
        callableOrigins.Value.Calls.TryFind call |> Option.bind (fun resolved ->
            if not resolved.Complete || resolved.Targets.IsEmpty then None else
            let targets = resolved.Targets |> List.map (fun target ->
                List.tryItem ordinal target.Parameters |> Option.map (fun (_, _, formal) -> formal, target.Lambda))
            if targets |> List.forall Option.isSome then Some(List.choose id targets |> List.distinct) else None)
    let formalInputs formal =
        callableOrigins.Value.ParameterInputs.TryFind formal |> Option.bind (fun inputs ->
            let actuals = inputs |> List.map (fun (call, actual) ->
                match nodes.TryFind call with
                | Some { Kind = SemanticKind.Application(_, arguments) } ->
                    arguments |> List.indexed |> List.tryPick (fun (ordinal, argument) ->
                        if argument <> actual then None else
                        argumentTargets call ordinal |> Option.bind (fun targets ->
                            if targets |> List.exists (fun (parameter, _) -> parameter = formal) then Some(call, actual) else None))
                | _ -> None)
            if not actuals.IsEmpty && actuals |> List.forall Option.isSome then Some(List.choose id actuals |> List.distinct) else None)
    // The initializer and its immutable capture relation jointly identify the
    // retained view. A slot declaration alone cannot supply the runtime value.
    let immutableInitializer environment slot value =
        match nodes.TryFind environment with
        | Some { Kind = SemanticKind.EnvironmentCreate(owner, _) } ->
            ClosureEnvironments.capturedInitializers graph owner
            |> Option.exists (List.contains (slot, value, false))
        | _ -> false
    let capturedValue = ClosureEnvironments.tryCapturedValue graph
    let rec storageSource seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.ContinuationAllocate _ | SemanticKind.EnvironmentAllocate _ } -> Some id
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> storageSource seen source
        | Some { Kind = SemanticKind.EagerExpr source } when ExplicitDemand.operand graph id = Some source -> storageSource seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> storageSource seen value
        | _ -> None
    let rec finalPath seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.SeqExpr _ } -> Some [id]
        | Some { Kind = SemanticKind.ClosureValue(_, environment) } -> Some [id; environment]
        | Some { Kind = SemanticKind.Sequential values } ->
            List.tryLast values |> Option.bind (finalPath seen) |> Option.map (fun path -> id :: path)
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } -> finalPath seen value |> Option.map (fun path -> id :: path)
        | Some { Kind = SemanticKind.EagerExpr value } when ExplicitDemand.operand graph id = Some value ->
            finalPath seen value |> Option.map (fun path -> id :: path)
        | _ -> None
    let finalConstructor seen id = finalPath seen id |> Option.bind List.tryLast
    let rec uniqueFinal seen factory body id =
        if Set.contains id seen then false else
        let seen = Set.add id seen
        let consumers = incidence |> List.filter (fun edge -> Hyperedge.isStructural edge && List.contains id edge.Sources)
        match consumers with
        | [edge] when id = body -> edge.Target = factory && edge.Role = EdgeRole.Body
        | [edge] ->
            match nodes.TryFind edge.Target with
            | Some { Kind = SemanticKind.ClosureValue(_, environment) } when environment = id -> uniqueFinal seen factory body edge.Target
            | Some { Kind = SemanticKind.Sequential values } when List.tryLast values = Some id -> uniqueFinal seen factory body edge.Target
            | Some { Kind = SemanticKind.TypeAnnotation(value, _) } when value = id -> uniqueFinal seen factory body edge.Target
            | Some { Kind = SemanticKind.EagerExpr value } when value = id && ExplicitDemand.operand graph edge.Target = Some id ->
                uniqueFinal seen factory body edge.Target
            | _ -> false
        | _ -> false
    let prepareResult constructor formal expectedCalls =
        if not (nodes.ContainsKey constructor) then None else
        match activation constructor with
        | Error _ -> None
        | Ok factory ->
            match nodes[factory].Kind with
            | SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure)
                when finalConstructor Set.empty body = Some constructor && uniqueFinal Set.empty factory body constructor ->
                let ordinal = parameters |> List.tryFindIndex (fun (_, _, parameter) -> parameter = formal)
                let calls = expectedCalls |> List.map (fun (call, allocation, expectedActual) ->
                    match ordinal, nodes.TryFind call, callableOrigins.Value.Calls.TryFind call, nodes.TryFind allocation with
                    | Some ordinal, Some { Kind = SemanticKind.Application(_, arguments) },
                      Some { Targets = [target]; Unknown = false; Complete = true }, Some allocationNode
                        when target.Lambda = factory && arguments.Length = parameters.Length ->
                        let matches =
                            match allocationNode.Kind, nodes[constructor].Kind with
                            | SemanticKind.ContinuationAllocate owner, SemanticKind.SeqExpr _ -> owner = constructor
                            | SemanticKind.EnvironmentAllocate owner, SemanticKind.EnvironmentCreate(actual, _) -> owner = actual
                            | _ -> false
                        let actual = arguments[ordinal]
                        let _, formalType, _ = parameters[ordinal]
                        let sameStorageType =
                            [Some allocationNode; nodes.TryFind formal; nodes.TryFind actual; nodes.TryFind constructor]
                            |> List.forall (Option.exists (fun node -> applySubst node.Type = applySubst formalType))
                        if matches && storageSource Set.empty actual = Some allocation &&
                           sameStorageType &&
                           (expectedActual |> Option.forall ((=) actual)) then Some(call, actual, allocation) else None
                    | _ -> None)
                let allCalls = nodes.Values |> Seq.choose (fun node ->
                    match node.Kind with
                    | SemanticKind.Application(callee, _) when implementation callee = Some factory ||
                        (callableOrigins.Value.Calls.TryFind node.Id |> Option.exists (fun call ->
                            call.Targets |> List.exists (fun target -> target.Lambda = factory))) -> Some node.Id
                    | _ -> None) |> Set.ofSeq
                let supplied = expectedCalls |> List.map (fun (call, _, _) -> call) |> Set.ofList
                if calls.IsEmpty || calls.Length <> supplied.Count || allCalls <> supplied ||
                   not (List.forall Option.isSome calls) then None
                else Some { Constructor = constructor; Implementation = factory; Formal = formal
                            FinalPath = finalPath Set.empty body |> Option.defaultValue []; Calls = List.choose id calls }
            | _ -> None
    // Preparation is a requirement, not lifetime evidence. Recheck its actual
    // signature, constructor, allocation and complete call set before using it.
    let sequenceResults = destinations |> Map.toList |> List.choose (fun (constructor, formal) ->
        let calls = factoryCalls |> Map.toList |> List.choose (fun (call, allocation) ->
            match nodes.TryFind allocation with
            | Some { Kind = SemanticKind.ContinuationAllocate owner } when owner = constructor -> Some(call, allocation, None)
            | _ -> None)
        prepareResult constructor formal calls |> Option.map (fun result -> constructor, result))
    let environmentResults = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EnvironmentResultDestination)
                             |> List.groupBy _.Target |> List.choose (fun (constructor, rows) ->
        match rows with
        | [{ Class = EdgeClass.Provenance; Sources = [factory; owner; formal] }] ->
            match nodes.TryFind constructor, nodes.TryFind owner with
            | Some { Kind = SemanticKind.EnvironmentCreate(actual, _) },
              Some { Kind = SemanticKind.ClosureValue(_, environment) } when actual = owner && environment = constructor ->
                let rows = graph.Edges |> List.filter (fun edge ->
                    edge.Role = EdgeRole.EnvironmentResultCall && List.tryItem 1 edge.Sources = Some constructor)
                let calls = rows |> List.map (fun edge ->
                    match edge.Class, edge.Sources with
                    | EdgeClass.Provenance, [actualFactory; actualConstructor; actualFormal; allocation; actual]
                        when actualFactory = factory && actualConstructor = constructor && actualFormal = formal -> Some(edge.Target, allocation, Some actual)
                    | _ -> None)
                if calls |> List.forall Option.isSome then
                    prepareResult constructor formal (List.choose id calls)
                    |> Option.filter (fun result -> result.Implementation = factory)
                    |> Option.map (fun result -> constructor, result)
                else None
            | _ -> None
        | _ -> None)
    let results = Map.ofList (sequenceResults @ environmentResults)
    let resultAllocations = results.Values |> Seq.collect (fun result -> result.Calls |> List.map (fun (call, actual, allocation) -> allocation, (result, call, actual))) |> Map.ofSeq
    let resultCalls = results.Values |> Seq.collect (fun result -> result.Calls |> List.map (fun (call, actual, allocation) -> call, (actual, allocation))) |> Map.ofSeq
    let factoryCalls = resultCalls |> Map.map (fun _ (_, allocation) -> allocation)
    let sites = nodes |> Map.filter (fun _ node ->
        if environmentSites then
            match node.Kind with
            | SemanticKind.EnvironmentCreate _ -> not (results.ContainsKey node.Id)
            | SemanticKind.EnvironmentAllocate _ -> true
            | _ -> false
        else
            match node.Kind with
            | SemanticKind.SeqExpr _ -> not (results.ContainsKey node.Id)
            | SemanticKind.ContinuationAllocate _ -> true
            | _ -> getEnumerator node |> Option.isSome)
    // A generator's repeated capture metadata describes the same constructor,
    // not a second owner. Missing/shared ownership never acquires a borrow.
    let generatorOwners =
        nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with SemanticKind.SeqExpr(generator, _) -> Some(generator, id) | _ -> None)
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ pairs -> pairs |> List.map snd)
    let sequenceOwner generator =
        match generatorOwners.TryFind generator, nodes.TryFind generator with
        | Some [owner], Some { Kind = SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) } -> Some owner
        | _ -> None
    let captures owner =
        match nodes.TryFind owner with Some { Kind = SemanticKind.SeqExpr(_, captures) } -> captures | _ -> []
    let borrowable (capture: CaptureInfo) =
        not capture.IsMutable &&
        (match applySubst capture.Type with
         | NativeType.TSeq _ -> true
         // A sequence result may retain a callback whose backing environment
         // has other deferred uses. Those uses need the same joint proof even
         // when the sites being admitted in this reading are sequence frames.
         | NativeType.TFun _ -> capture.SourceNodeId |> Option.bind knownCallable |> Option.isSome
         | _ -> false)
    let rec sourceAllocations seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.SeqExpr _ | SemanticKind.EnvironmentCreate _ } ->
            match results.TryFind id with
            | Some result -> result.Calls |> List.map (fun (_, _, allocation) -> allocation) |> Set.ofList |> Some
            | None -> Some(Set.singleton id)
        | Some { Kind = SemanticKind.ContinuationAllocate _ | SemanticKind.EnvironmentAllocate _ } -> Some (Set.singleton id)
        | Some { Kind = SemanticKind.ClosureValue(_, environment) | SemanticKind.EnvironmentReference environment } -> sourceAllocations seen environment
        | Some { Kind = SemanticKind.Lambda(_, _, [], _, LambdaContext.RegularClosure) } -> Some Set.empty
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> sourceAllocations seen source
        | Some { Kind = SemanticKind.EagerExpr source } when ExplicitDemand.operand graph id = Some source -> sourceAllocations seen source
        | Some { Kind = SemanticKind.FrameRead(_, source) } -> sourceAllocations seen source
        | Some { Kind = SemanticKind.EnvironmentRead(environment, slot) } ->
            capturedValue environment slot |> Option.bind (sourceAllocations seen)
        | Some { Kind = SemanticKind.PatternBinding _ } ->
            formalInputs id |> Option.bind (fun inputs ->
                inputs |> List.fold (fun result (_, actual) -> Option.map2 Set.union result (sourceAllocations seen actual)) (Some Set.empty))
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> sourceAllocations seen value
        | Some { Kind = SemanticKind.Sequential values } -> List.tryLast values |> Option.bind (sourceAllocations seen)
        | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } ->
            Option.map2 Set.union (sourceAllocations seen yes) (sourceAllocations seen no)
        | Some { Kind = SemanticKind.Application _ } -> factoryCalls.TryFind id |> Option.bind (sourceAllocations seen)
        | _ -> None
    let mutable uses: Map<NodeId, Use list> = Map.empty
    let useValue source usage = uses <- uses.Add(source, usage :: (uses.TryFind source |> Option.defaultValue []))
    for node in nodes.Values do
        let structural = edges node |> List.filter Hyperedge.isStructural
        for edge in structural do
            for source in edge.Sources do
                let usage =
                    match node.Kind, edge.Role with
                    | SemanticKind.Binding(_, false, _, _), _ -> Alias node.Id
                    | SemanticKind.Binding _, _ -> Refused (ResidualReason.StoredAt node.Id)
                    | SemanticKind.TypeAnnotation _, _ -> Alias node.Id
                    | SemanticKind.EagerExpr value, _ when value = source && ExplicitDemand.operand graph node.Id = Some source -> Alias node.Id
                    | SemanticKind.ClosureValue(_, environment), _ when source = environment -> Alias node.Id
                    | SemanticKind.EnvironmentReference _, _ -> Alias node.Id
                    | SemanticKind.EnvironmentCreate(owner, initializers), EdgeRole.Attached ->
                        match initializers |> List.filter (snd >> (=) source) with
                        | [(slot, _)] when immutableInitializer node.Id slot source ->
                            match applySubst nodes[source].Type with
                            | NativeType.TSeq _ -> EnvironmentCaptured(node.Id, slot, source)
                            | NativeType.TFun _ when knownCallable source |> Option.isSome -> EnvironmentCaptured(node.Id, slot, source)
                            | _ -> Consumed node.Id
                        | [(slot, _)] when ClosureEnvironments.capturedInitializers graph owner |> Option.exists (List.contains (slot, source, true)) ->
                            Consumed node.Id
                        | _ -> Refused (ResidualReason.StoredAt node.Id)
                    | SemanticKind.Sequential values, _ ->
                        if List.tryLast values = Some source then Alias node.Id else Consumed node.Id
                    | SemanticKind.IfThenElse _, (EdgeRole.ThenBranch | EdgeRole.ElseBranch)
                    | SemanticKind.Match _, EdgeRole.CaseBody
                    | SemanticKind.CaseElimination _, EdgeRole.CaseBody
                    | SemanticKind.TryWith _, (EdgeRole.Body | EdgeRole.Handler)
                    | SemanticKind.TryFinally _, EdgeRole.Body -> Alias node.Id
                    | SemanticKind.TryFinally _, EdgeRole.Cleanup -> Consumed node.Id
                    | SemanticKind.Lambda _, EdgeRole.Parameter -> Consumed node.Id
                    | SemanticKind.Lambda _, EdgeRole.Body ->
                        match finalConstructor Set.empty source |> Option.bind (fun constructor -> results.TryFind constructor) with
                        | Some result when result.Implementation = node.Id -> ResultDestination result.Constructor
                        | _ -> Refused (ResidualReason.ReturnsFrom node.Id)
                    | SemanticKind.Application(callee, arguments), EdgeRole.Callee when source = callee ->
                        match invocationParticipants node.Id callee arguments with
                        | Some participants -> Invocation(node.Id, participants)
                        | None -> Refused (ResidualReason.UnsupportedConsumer node.Id)
                    | SemanticKind.Application _, EdgeRole.Argument
                        when resultCalls.TryFind node.Id |> Option.exists (fun (actual, allocation) ->
                            actual = source && storageSource Set.empty source = Some allocation) -> Alias node.Id
                    | SemanticKind.Application(callee, _), EdgeRole.Argument ->
                        match intrinsic Set.empty callee, edge.Ordinal with
                        | _, ordinal when environmentArguments.TryFind node.Id = Some(ordinal, source) -> Consumed node.Id
                        | Some { Module = IntrinsicModule.Seq; Operation = "getEnumerator" }, 0 -> Alias node.Id
                        | Some { Module = IntrinsicModule.SeqEnumerator; Operation = ("moveNext" | "current") }, 0
                        | Some { Module = IntrinsicModule.Operators; Operation = "ignore" }, _ -> Consumed node.Id
                        | _ ->
                            match nodes.TryFind source, argumentTargets node.Id edge.Ordinal with
                            | Some argument, Some targets when
                                (match applySubst argument.Type with
                                 | NativeType.TSeq _ -> true
                                 | NativeType.TFun _ -> knownCallable source |> Option.isSome
                                 | _ -> false) ->
                                Argument(node.Id, source, targets)
                            | _ -> Refused (ResidualReason.UnsupportedConsumer node.Id)
                    | SemanticKind.RecordExpr _, _ | SemanticKind.TupleExpr _, _ | SemanticKind.ArrayExpr _, _
                    | SemanticKind.ListExpr _, _ | SemanticKind.DUConstruct _, _ | SemanticKind.UnionCase _, _
                    | SemanticKind.Set _, _ | SemanticKind.FieldSet _, _ | SemanticKind.IndexSet _, _
                    | SemanticKind.FrameWrite _, _ -> Refused (ResidualReason.StoredAt node.Id)
                    | _ -> Refused (ResidualReason.UnsupportedConsumer node.Id)
                useValue source usage
        match node.Kind with
        | SemanticKind.EnvironmentCreate(_, initializers) ->
            for slot, source in initializers do
                let view =
                    match nodes.TryFind source with
                    | Some value ->
                        match applySubst value.Type with
                        | NativeType.TSeq _ -> true
                        | NativeType.TFun _ -> knownCallable source |> Option.isSome
                        | _ -> false
                    | None -> false
                let usage =
                    if allowGenerators && view && immutableInitializer node.Id slot source then
                        EnvironmentCaptured(node.Id, slot, source)
                    else Refused (ResidualReason.StoredAt node.Id)
                useValue source usage
        | SemanticKind.VarRef(_, Some source) -> useValue source (Alias node.Id)
        | SemanticKind.EnvironmentRead(environment, slot) ->
            capturedValue environment slot |> Option.iter (fun source -> useValue source (Alias node.Id))
        | SemanticKind.SeqExpr(generator, captured) ->
            for capture in captured do
                capture.SourceNodeId |> Option.iter (fun source ->
                    let usage =
                        if allowGenerators && borrowable capture && sequenceOwner generator = Some node.Id then
                            Captured(node.Id, generator, source)
                        else Refused (ResidualReason.StoredAt node.Id)
                    useValue source usage)
        | SemanticKind.Lambda(_, _, captured, _, LambdaContext.SeqGenerator) ->
            for capture in captured do
                capture.SourceNodeId |> Option.iter (fun source ->
                    let duplicate = sequenceOwner node.Id |> Option.exists (fun owner ->
                        captures owner |> List.exists (fun original ->
                            original.SourceNodeId = Some source && original.IsMutable = capture.IsMutable))
                    if not duplicate then useValue source (Refused (ResidualReason.StoredAt node.Id)))
        | SemanticKind.Lambda(_, _, captured, _, _) | SemanticKind.LazyExpr(_, captured) ->
            for capture in captured do
                capture.SourceNodeId |> Option.iter (fun source -> useValue source (Refused (ResidualReason.StoredAt node.Id)))
        | _ -> ()
    let combine left right = left |> Result.bind (fun first -> right () |> Result.map (fun second -> first @ second))
    do
        // Independent reference incidence is not erased by structural recipes.
        // Unknown consumers prevent a complete-use environment residence proof.
        for edge in graph.Edges do
            if edge.Class = EdgeClass.Reference then
                match nodes.TryFind edge.Target with
                | Some { Kind = SemanticKind.VarRef(_, Some source) }
                    when edge.Role = EdgeRole.Definition && edge.Sources = [source] -> ()
                | Some { Kind = SemanticKind.EnvironmentCreate(_, initializers) }
                    when edge.Role = EdgeRole.EnvironmentInitializer &&
                         (List.tryItem edge.Ordinal initializers |> Option.exists (fun (_, value) -> edge.Sources = [value])) -> ()
                | Some { Kind = SemanticKind.ModuleDef(_, members) }
                    when edge.Role = EdgeRole.Member &&
                         (List.tryItem edge.Ordinal members |> Option.exists (fun source -> edge.Sources = [source])) -> ()
                | Some _ ->
                    for source in edge.Sources do useValue source (Refused(ResidualReason.UnsupportedConsumer edge.Target))
                | None when not (graph.Nodes.ContainsKey edge.Target) ->
                    for source in edge.Sources do useValue source (Refused(ResidualReason.UnsupportedConsumer edge.Target))
                | None -> ()
    // Coverage follows complete value use, not lexical nesting. Each crossed
    // deferred activation must have exactly one constructor whose own complete
    // use is bounded in an already covered activation.
    let rec activationCovered covering proving actual =
        if actual = covering then Ok []
        elif ProgramActivation.coverage programActivations.Value covering actual |> Option.isSome then
            let coverage = ProgramActivation.coverage programActivations.Value covering actual |> Option.get
            if Set.contains actual proving then Error (ResidualReason.RecursiveValueFlow actual)
            else
                coverage.Dependencies |> List.fold (fun proof dependency ->
                    combine proof (fun () -> activationCovered covering (Set.add actual proving) dependency)) (Ok coverage.Evidence)
        elif not allowGenerators then Error (ResidualReason.CrossesActivation actual)
        else
            match sequenceOwner actual with
            | Some constructor when not (Set.contains constructor proving) ->
                activation constructor |> Result.bind (fun enclosing ->
                    combine (activationCovered covering (Set.add constructor proving) enclosing) (fun () ->
                        let region = if results.ContainsKey constructor then covering else enclosing
                        bounded constructor region (Set.add constructor proving) Set.empty constructor))
            | _ -> Error (ResidualReason.CrossesActivation actual)
    and borrow allocation covering proving constructor generator declaration =
        let selected = captures constructor |> List.exists (fun capture ->
            capture.SourceNodeId = Some declaration && borrowable capture)
        let knownSource = sourceAllocations Set.empty declaration |> Option.exists (Set.contains allocation)
        if not selected || not knownSource || sequenceOwner generator <> Some constructor then
            Error (ResidualReason.UnknownInputRegion declaration)
        elif Set.contains constructor proving then Error (ResidualReason.RecursiveValueFlow constructor)
        else
            activation constructor |> Result.bind (fun enclosing ->
                let proving = Set.add constructor proving
                combine (activationCovered covering proving enclosing) (fun () ->
                    let region = if results.ContainsKey constructor then covering else enclosing
                    bounded constructor region proving Set.empty constructor)
                |> Result.map (fun evidence ->
                    { Class = EdgeClass.Provenance; Role = EdgeRole.SequenceTemplateBorrow
                      Sources = [allocation; covering; declaration; generator]; Target = constructor; Ordinal = 0 } :: evidence))
    and scopeUse allocation covering proving id =
        activation id |> Result.bind (fun actual ->
            if actual = covering then Ok []
            elif ProgramActivation.coverage programActivations.Value covering actual |> Option.isSome then
                activationCovered covering proving actual
            elif not allowGenerators then Error (ResidualReason.CrossesActivation id)
            else
                match sequenceOwner actual with
                | Some constructor ->
                    let declarations =
                        captures constructor
                        |> List.choose (fun capture ->
                            match capture.SourceNodeId with
                            | Some declaration when borrowable capture && (sourceAllocations Set.empty declaration |> Option.exists (Set.contains allocation)) -> Some declaration
                            | _ -> None)
                        |> List.distinct
                    match declarations with
                    | [] -> Error (ResidualReason.CrossesActivation id)
                    | _ -> declarations |> List.fold (fun result declaration ->
                        combine result (fun () -> borrow allocation covering proving constructor actual declaration)) (Ok [])
                | None -> Error (ResidualReason.CrossesActivation id))
    and argumentBorrow allocation covering proving seen call actual targets =
        combine (scopeUse allocation covering proving call) (fun () ->
            targets |> List.fold (fun proof (formal, implementation) ->
                combine proof (fun () ->
                    combine (activationCovered covering proving implementation) (fun () ->
                        bounded allocation covering proving seen formal)
                    |> Result.map (fun evidence ->
                        { Class = EdgeClass.Provenance; Role = EdgeRole.SequenceInputBorrow
                          Sources = [allocation; covering; actual; formal; implementation]; Target = call; Ordinal = 0 } :: evidence))) (Ok []))
    and environmentBorrow allocation covering proving environment slot value =
        if not (immutableInitializer environment slot value) ||
           not (sourceAllocations Set.empty value |> Option.exists (Set.contains allocation)) then
            Error (ResidualReason.UnknownInputRegion value)
        elif Set.contains environment proving then Error (ResidualReason.RecursiveValueFlow environment)
        else
            activation environment |> Result.bind (fun enclosing ->
                let proving = Set.add environment proving
                combine (activationCovered covering proving enclosing) (fun () ->
                    bounded environment covering proving Set.empty environment))
    and resultBorrow covering proving seen constructor =
        match results.TryFind constructor with
        | None -> Error (ResidualReason.InvalidResultDestination constructor)
        | Some result ->
            result.Calls |> List.fold (fun proof (call, _, allocation) ->
                combine proof (fun () ->
                    combine (scopeUse allocation covering proving call) (fun () ->
                        bounded allocation covering (Set.add constructor proving) seen allocation))) (Ok [])
    and bounded allocation covering proving seen id =
        if Set.contains id seen then Error (ResidualReason.RecursiveValueFlow id) else
        let seen = Set.add id seen
        uses.TryFind id |> Option.defaultValue []
        |> List.fold (fun result usage -> combine result (fun () ->
            match usage with
            | Refused reason -> Error reason
            | Captured(constructor, generator, declaration) -> borrow allocation covering proving constructor generator declaration
            | Argument(call, actual, targets) -> argumentBorrow allocation covering proving seen call actual targets
            | EnvironmentCaptured(environment, slot, value) -> environmentBorrow allocation covering proving environment slot value
            | ResultDestination constructor -> resultBorrow covering proving seen constructor
            | Invocation(call, participants) ->
                scopeUse allocation covering proving call |> Result.map (fun evidence ->
                    { Class = EdgeClass.Provenance; Role = EdgeRole.CallableInvocationBorrow
                      Sources = List.distinct (allocation :: covering :: participants)
                      Target = call; Ordinal = 0 } :: evidence)
            | Consumed consumer -> scopeUse allocation covering proving consumer
            | Alias other -> combine (scopeUse allocation covering proving other) (fun () -> bounded allocation covering proving seen other))) (Ok [])
    // The iterator's input must have a source allocation, with complete bounded
    // use and an exact capture relation when it crosses a generator boundary.
    // Factory/opaque inputs retain their residual unless preparation supplied
    // the exact caller-owned allocation identity.
    let rec inputRegion owner useSite seen id =
        if Set.contains id seen then Error (ResidualReason.RecursiveValueFlow id) else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.SeqExpr _ } when results.ContainsKey id ->
            results[id].Calls |> List.fold (fun proof (_, _, allocation) ->
                combine proof (fun () -> inputRegion owner useSite seen allocation)) (Ok [])
        | Some { Kind = SemanticKind.SeqExpr _ | SemanticKind.ContinuationAllocate _ } ->
            activation id |> Result.bind (fun sourceActivation ->
                if sourceActivation = owner then Ok []
                else combine (scopeUse id sourceActivation (Set.singleton id) useSite) (fun () ->
                    bounded id sourceActivation (Set.singleton id) Set.empty id))
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> inputRegion owner useSite seen source
        | Some { Kind = SemanticKind.EagerExpr source } when ExplicitDemand.operand graph id = Some source -> inputRegion owner useSite seen source
        | Some { Kind = SemanticKind.FrameRead(_, source) } -> inputRegion owner useSite seen source
        | Some { Kind = SemanticKind.EnvironmentRead(environment, slot) } ->
            match capturedValue environment slot with
            | Some value -> inputRegion owner useSite seen value
            | None -> Error (ResidualReason.UnknownInputRegion id)
        | Some { Kind = SemanticKind.PatternBinding _ } ->
            match formalInputs id with
            | Some inputs ->
                inputs |> List.fold (fun proof (_, actual) -> combine proof (fun () -> inputRegion owner useSite seen actual)) (Ok [])
            | None -> Error (ResidualReason.UnknownInputRegion id)
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> inputRegion owner useSite seen value
        | Some { Kind = SemanticKind.Sequential values } ->
            match List.tryLast values with Some last -> inputRegion owner useSite seen last | None -> Error (ResidualReason.UnknownInputRegion id)
        | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } ->
            combine (inputRegion owner useSite seen yes) (fun () -> inputRegion owner useSite seen no)
        | Some { Kind = SemanticKind.Application _ } ->
            match factoryCalls.TryFind id with
            | Some allocation -> inputRegion owner useSite seen allocation
            | None -> Error (ResidualReason.FactoryResult id)
        | _ -> Error (ResidualReason.UnknownInputRegion id)
    let rec actualValue (result: PreparedResult) call seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        let parameters = match nodes[result.Implementation].Kind with SemanticKind.Lambda(parameters, _, _, _, _) -> parameters | _ -> []
        let arguments = match nodes[call].Kind with SemanticKind.Application(_, arguments) -> arguments | _ -> []
        match parameters |> List.tryFindIndex (fun (_, _, formal) -> formal = id) with
        | Some ordinal -> List.tryItem ordinal arguments
        | None ->
            match nodes.TryFind id with
            | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> actualValue result call seen source
            | Some { Kind = SemanticKind.EagerExpr source } when ExplicitDemand.operand graph id = Some source -> actualValue result call seen source
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> actualValue result call seen value
            | Some { Kind = SemanticKind.EnvironmentRead(environment, slot) } ->
                actualValue result call seen environment |> Option.bind (fun actual -> capturedValue actual slot)
            | Some { Kind = SemanticKind.EnvironmentBorrow(environment, slot) } ->
                actualValue result call seen environment |> Option.bind environmentOwner
                |> Option.bind (ClosureEnvironments.capturedInitializers graph)
                |> Option.bind (List.tryPick (fun (source, value, mutableCell) -> if source = slot && mutableCell then Some value else None))
            | Some _ -> Some id
            | None -> None
    let rec inputFormal seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.PatternBinding _ } -> Some id
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> inputFormal seen source
        | Some { Kind = SemanticKind.EagerExpr source } when ExplicitDemand.operand graph id = Some source -> inputFormal seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> inputFormal seen value
        | Some { Kind = SemanticKind.EnvironmentRead(environment, _) } -> inputFormal seen environment
        | _ -> None
    let retainedView site owner slot value =
        match sourceAllocations Set.empty value with
        | None -> Error (ResidualReason.UnknownInputRegion value)
        | Some allocations ->
            allocations |> Set.fold (fun proof allocation ->
                combine proof (fun () ->
                    activation allocation |> Result.bind (fun sourceOwner ->
                        combine (scopeUse allocation sourceOwner (Set.singleton allocation) site) (fun () ->
                            combine (bounded allocation sourceOwner (Set.singleton allocation) Set.empty allocation) (fun () ->
                                bounded site sourceOwner (Set.singleton site) Set.empty site))
                        |> Result.map (fun evidence ->
                            let edge =
                                match nodes[owner].Kind with
                                | SemanticKind.SeqExpr(generator, _) ->
                                    { Class = EdgeClass.Provenance; Role = EdgeRole.SequenceTemplateBorrow
                                      Sources = [allocation; sourceOwner; slot; generator]; Target = owner; Ordinal = 0 }
                                | _ ->
                                    { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentResidence
                                      Sources = [site; sourceOwner; allocation; slot; value]; Target = owner; Ordinal = 0 }
                            edge :: evidence)))) (Ok [])
    let resultInputs site result call destination =
        match nodes[result.Constructor].Kind with
        | SemanticKind.EnvironmentCreate(owner, _) ->
            match ClosureEnvironments.capturedInitializers graph owner with
            | None -> Error (ResidualReason.UnknownInputRegion result.Constructor)
            | Some initializers ->
                initializers |> List.fold (fun proof (slot, value, mutableCell) ->
                    combine proof (fun () ->
                        match actualValue result call Set.empty value with
                        | None -> Error (ResidualReason.UnknownInputRegion value)
                        | Some actual when mutableCell ->
                            activation actual |> Result.bind (fun sourceOwner ->
                                combine (scopeUse actual sourceOwner (Set.singleton site) site) (fun () ->
                                    bounded site sourceOwner (Set.singleton site) Set.empty site))
                        | Some actual ->
                            match applySubst nodes[value].Type with
                            | NativeType.TSeq _ | NativeType.TFun _ -> retainedView site owner slot actual
                            | _ -> Ok [])) (Ok [])
        | SemanticKind.SeqExpr(_, captured) ->
            match ClosureEnvironments.sequenceInitializers graph nodes[result.Constructor] with
            | None -> Error (ResidualReason.UnknownInputRegion result.Constructor)
            | Some initializers ->
                captured |> List.fold (fun proof capture ->
                    let view = not capture.IsMutable && (match applySubst capture.Type with NativeType.TSeq _ | NativeType.TFun _ -> true | _ -> false)
                    if not view then proof else
                    combine proof (fun () ->
                        match capture.SourceNodeId |> Option.bind (fun slot -> initializers |> List.tryFind (fst >> (=) slot)) with
                        | None -> Error (ResidualReason.UnknownInputRegion result.Constructor)
                        | Some(slot, initializer) ->
                            let requirements = graph.Edges |> List.filter (fun edge ->
                                edge.Role = EdgeRole.SequenceResultCapture && edge.Target = result.Constructor &&
                                List.tryHead edge.Sources = Some slot && List.tryItem 4 edge.Sources = Some call)
                            match requirements, inputFormal Set.empty initializer, nodes[call].Kind, nodes[result.Implementation].Kind with
                            | [{ Class = EdgeClass.Provenance; Sources = [actualSlot; actualInitializer; factory; formal; actualCall; actual; actualDestination; allocation]; Ordinal = ordinal }],
                              Some expectedFormal, SemanticKind.Application(_, arguments), SemanticKind.Lambda(parameters, _, _, _, _)
                                when actualSlot = slot && actualInitializer = initializer && factory = result.Implementation &&
                                     formal = expectedFormal && actualCall = call && actualDestination = destination && allocation = site &&
                                     List.tryItem ordinal arguments = Some actual &&
                                     (List.tryItem ordinal parameters |> Option.exists (fun (_, _, parameter) -> parameter = formal)) ->
                                match actualValue result call Set.empty initializer with
                                | Some value -> retainedView site result.Constructor slot value
                                | None -> Error (ResidualReason.UnknownInputRegion initializer)
                            | _ -> Error (ResidualReason.MissingResultCapture(result.Constructor, slot)))) (Ok [])
        | _ -> Error (ResidualReason.InvalidResultDestination result.Constructor)
    sites |> Map.fold (fun result id node ->
        let proof = activation id |> Result.bind (fun owner ->
            let capturedInputs =
                match node.Kind with
                | SemanticKind.EnvironmentAllocate _ ->
                    match resultAllocations.TryFind id with
                    | Some(prepared, call, destination) -> resultInputs id prepared call destination
                    | None -> Error (ResidualReason.InvalidResultDestination id)
                | SemanticKind.ContinuationAllocate _ ->
                    match resultAllocations.TryFind id with
                    | Some(prepared, call, destination) -> resultInputs id prepared call destination
                    | None -> Error (ResidualReason.InvalidResultDestination id)
                | SemanticKind.EnvironmentCreate(layout, _) ->
                    match ClosureEnvironments.capturedInitializers graph layout with
                    | None -> Error (ResidualReason.UnknownInputRegion id)
                    | Some initializers ->
                        initializers |> List.fold (fun proof (slot, value, mutableCell) ->
                            combine proof (fun () ->
                                if mutableCell then
                                    activation slot |> Result.bind (fun cellOwner ->
                                        activationCovered cellOwner (Set.singleton id) owner)
                                else
                                    match applySubst nodes[value].Type with
                                    | NativeType.TSeq _ | NativeType.TFun _ ->
                                        match sourceAllocations Set.empty value with
                                        | None -> Error (ResidualReason.UnknownInputRegion value)
                                        | Some allocations ->
                                            allocations |> Set.fold (fun evidence allocation ->
                                                combine evidence (fun () ->
                                                    activation allocation |> Result.bind (fun sourceOwner ->
                                                        combine (activationCovered sourceOwner (Set.singleton id) owner) (fun () ->
                                                            bounded id sourceOwner (Set.singleton id) Set.empty id)
                                                        |> Result.map (fun evidence ->
                                                            { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentResidence
                                                              Sources = [id; owner; allocation; sourceOwner; slot; value]
                                                              Target = layout; Ordinal = 0 } :: evidence)))) (Ok [])
                                    | _ -> Ok [])) (Ok [])
                | _ -> Ok []
            combine (combine capturedInputs (fun () ->
                        match getEnumerator node with Some input -> inputRegion owner id Set.empty input | None -> Ok []))
                (fun () -> bounded id owner (Set.singleton id) Set.empty id)
            |> Result.map (fun evidence -> owner, evidence))
        match proof with
        | Ok(owner, evidence) ->
            let evidence =
                match node.Kind with
                | SemanticKind.EnvironmentAllocate layout ->
                    let prepared, call, destination = resultAllocations[id]
                    let initializers = ClosureEnvironments.capturedInitializers graph layout |> Option.defaultValue []
                    { Sources = List.distinct ((id :: owner :: prepared.Constructor :: call :: destination :: prepared.FinalPath) @
                                    (initializers |> List.collect (fun (slot, value, _) -> [slot; value])))
                      Target = layout; Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentResidence; Ordinal = 0 } :: evidence
                | SemanticKind.EnvironmentCreate(layout, initializers) ->
                    let values = nodes |> Map.toList |> List.choose (fun (value, _) ->
                        if sourceAllocations Set.empty value |> Option.exists (Set.contains id) then Some value else None)
                    { Sources = List.distinct (id :: owner :: (initializers |> List.collect (fun (slot, value) -> [slot; value])) @ values)
                      Target = layout; Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentResidence; Ordinal = 0 } :: evidence
                | _ -> evidence
            let result = { result with Evidence = evidence @ result.Evidence }
            match nodes[owner].Kind with
            | SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) -> { result with Regions = result.Regions.Add(id, owner) }
            | _ -> { result with Sites = result.Sites.Add(id, EscapeKind.StackScoped) }
        | Error reason -> { result with Unresolved = { Site = id; Reason = reason } :: result.Unresolved })
        { Sites = Map.empty; Regions = Map.empty; Evidence = []; Unresolved = [] }
    |> fun result ->
        { result with
            Unresolved = List.rev result.Unresolved
            Evidence = result.Evidence |> List.distinctBy (fun edge -> edge.Class, edge.Role, edge.Sources, edge.Target, edge.Ordinal) }

/// Scope-only form retains the original conservative admission boundary.
let analyze graph = analyzeCore false false graph Map.empty Map.empty

/// Destination-backed constructors do not allocate in the factory activation.
let analyzePrepared graph destinations factoryCalls = analyzeCore false false graph destinations factoryCalls

/// Generator-local values whose complete use stays within that generator can
/// be assigned subregions of its frame. This returns a requirement, not a
/// selected offset or permission to use activation-local stack storage.
let analyzeWithRegions graph destinations factoryCalls = analyzeCore true false graph destinations factoryCalls

/// The same complete-use covering proof for known callable environments.
/// Generator-local results are requirements for owned regions, not permission
/// to allocate backing storage in a single MoveNext activation.
let analyzeEnvironments graph = analyzeCore true true graph Map.empty Map.empty

/// Environment placement sees the same prepared sequence destinations without
/// forcing unfinished codata. Both result protocols still require final proof.
let analyzeEnvironmentsPrepared graph destinations factoryCalls = analyzeCore true true graph destinations factoryCalls

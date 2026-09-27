// SPDX-License-Identifier: MIT
/// Source settlement for the callable witness contract. All discovery and
/// premise checking runs here, before publication; emission reads sealed rows.
module Clef.Compiler.PSGSaturation.SemanticGraph.CallableEmission

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let private choose chooser values =
    values |> Map.toSeq |> Seq.choose (fun (key, value) -> chooser key value |> Option.map (fun selected -> key, selected)) |> Map.ofSeq

let private bindingName (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Binding(name, _, _, _) ->
        match node.Parent |> Option.bind graph.Nodes.TryFind with
        | Some { Kind = SemanticKind.ModuleDef(moduleName, _) } -> Some(CallableSymbolName.ModuleBinding(moduleName, name))
        | _ when node.Parent.IsSome -> Some(CallableSymbolName.LocalBinding(node.Id, name))
        | _ -> Some(CallableSymbolName.RootBinding name)
    | _ -> None

let private declarations (graph: SemanticGraph) =
    let mutable symbols = graph.Nodes |> choose (fun _ node -> bindingName graph node)
    let mutable declarations = Map.empty
    for node in graph.Nodes.Values do
        match node.Kind with
        | SemanticKind.Lambda(parameters, body, captures, _, context) ->
            let anonymous =
                graph.Codata.Value.Closures.ContainsKey node.Id &&
                ([ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
                 |> List.exists (fun key -> node.Metadata.TryFind key = Some(MetadataValue.Bool true)))
            let name =
                if anonymous then CallableSymbolName.Anonymous node.Id
                else node.Parent |> Option.bind symbols.TryFind |> Option.defaultValue (CallableSymbolName.Anonymous node.Id)
            symbols <- symbols.Add(node.Id, name)
            let participants = Set.ofList (node.Id :: body :: ((parameters |> List.map (fun (_, _, id) -> id)) @ Option.toList node.Parent @ (captures |> List.choose _.SourceNodeId)))
            declarations <- declarations.Add(node.Id,
                { Lookup = node.Id; Implementation = node.Id; Parameters = parameters; Result = body
                  Context = context; Captures = captures; Name = name; Parent = node.Parent; Participants = participants })
        | _ -> ()
    let rec code seen id =
        if Set.contains id seen then None else
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Lambda _ } -> declarations.TryFind id |> Option.map (fun declaration -> declaration, Set.singleton id)
        | Some { Kind = SemanticKind.TypeAnnotation(inner, declared); Type = ty; Children = [child] }
            when inner = child && applySubst ty = applySubst declared ->
            code (Set.add id seen) inner |> Option.map (fun (declaration, path) -> declaration, Set.add id path)
        | _ -> None
    for node in graph.Nodes.Values do
        match node.Kind, node.Children with
        | SemanticKind.Binding(_, false, _, _), [child] ->
            match code Set.empty child, symbols.TryFind node.Id with
            | Some(declaration, path), Some name when declaration.Captures.IsEmpty ->
                declarations <- declarations.Add(node.Id,
                    { declaration with Lookup = node.Id; Name = name; Parent = node.Parent
                                       Participants = Set.union declaration.Participants (Set.add node.Id path) })
            | _ -> ()
        | _ -> ()
    symbols, declarations

/// Validate the held codata against the current source snapshot once. Missing
/// optional rows remain absent; a consumer requiring one must report the source
/// settlement gap. A stale held row is never converted to an admitted empty row.
let projectWithDemand (graph: SemanticGraph) (ordinary: OrdinaryDemandProjection) : Result<CallableEmissionProjection, WitnessProjectionFailure list> =
    let codata = graph.Codata.Value
    let errors = ResizeArray<WitnessProjectionFailure>()
    let sameRows name current held =
        let keys = Set.union (current |> Map.keys |> Set.ofSeq) (held |> Map.keys |> Set.ofSeq)
        for id in keys do
            if Map.tryFind id current <> Map.tryFind id held then
                errors.Add({ Occurrence = Some id; Participants = Set.singleton id
                             Reason = $"{name} at {NodeId.value id} is missing or does not match its current source participants." })
    let origins = ClosureEnvironments.origins graph
    let known = ClosureEnvironments.knownCallables graph
    let carriers, _ = CallableCarriers.settle { Layouts = codata.EnvironmentLayouts; Origins = origins; Known = known } graph
    let storage = MutableCallableStorage.settle carriers codata.EnvironmentLayouts graph
    let flows, _ = CallableFlows.settle
                        { Carriers = carriers; Joins = storage.Joins; Layouts = codata.EnvironmentLayouts
                          SequenceFlows = codata.SequenceFlows; SequenceFamilies = codata.SequenceFamilies } graph
    sameRows "Callable carrier" carriers codata.CallableCarriers
    sameRows "Callable join" storage.Joins codata.CallableJoins
    sameRows "Callable flow" flows codata.CallableFlows
    sameRows "Mutable callable storage" storage.Storage codata.MutableCallableStorage
    if errors.Count > 0 then Result.Error(List.ofSeq errors) else
    let shapes = graph.Nodes |> Map.map (fun _ node -> CallableCarriers.valueShape graph node)
    let signatureData =
        codata.CallableCarriers.Values |> Seq.groupBy _.Implementation |> Seq.map (fun (implementation, values) ->
            let carrier = Seq.head values
            let participants = carrier.Result :: (carrier.Parameters |> List.map (fun (_, _, id) -> id))
            implementation, participants |> List.filter (CallableInstantiations.allowsSignatureData graph carrier) |> Set.ofList)
        |> Map.ofSeq
    let resolution = CallableOrigins.resolve graph
    let ingress = CallableIngress.analyzeWith graph resolution
    let instance = CallableInstantiations.readerWith graph resolution ingress
    let instances =
        codata.CallableCarriers |> choose (fun occurrence carrier ->
            graph.Nodes.TryFind carrier.Implementation |> Option.bind (fun implementation ->
                instance carrier.Implementation (CallableCarriers.sourceType implementation) occurrence))
    let instantiatedTransports =
        instances |> Map.map (fun _ destination ->
            destination.ValuePath |> Set.filter (fun source ->
                instances.TryFind source |> Option.exists (fun original -> original.Template = destination.Template)))
    let directTransports =
        graph.Nodes |> choose (fun destination node ->
            let source =
                match node.Kind, node.Children with
                | SemanticKind.Binding(_, false, _, _), [source]
                | SemanticKind.VarRef(_, Some source), [] -> Some source
                | SemanticKind.TypeAnnotation(source, declared), [child]
                    when child = source && applySubst declared = applySubst node.Type -> Some source
                | SemanticKind.Sequential values, children when values = children -> List.tryLast values
                | SemanticKind.EagerExpr source, [child] when source = child && ExplicitDemand.operand graph destination = Some source -> Some source
                | _ -> None
            let actual = source |> Option.filter (fun source ->
                shapes.TryFind source = Some(CallableValueShape.Callable source) &&
                shapes.TryFind destination = Some(CallableValueShape.Callable destination) &&
                applySubst (CallableCarriers.sourceType graph.Nodes[source]) = applySubst (CallableCarriers.sourceType node)) |> Option.toList |> Set.ofList
            let admitted = Set.union actual (instantiatedTransports.TryFind destination |> Option.defaultValue Set.empty)
            if admitted.IsEmpty then None else Some admitted)
    // An already witnessed occurrence preserves itself. Transparent result
    // wrappers preserve the exact value on their selected source path, not an
    // arbitrary occurrence with the same implementation/environment schema.
    let callableOccurrences =
        Set.unionMany [codata.CallableCarriers |> Map.keys |> Set.ofSeq
                       codata.CallableJoins |> Map.keys |> Set.ofSeq
                       codata.CallableFlows |> Map.keys |> Set.ofSeq]
    let transportPath destination =
        // Instance paths may already contain their transitive ancestors. A
        // shared worklist visits each participant once, including on diamonds.
        let rec collect seen pending =
            match pending with
            | [] -> seen
            | current :: remaining when Set.contains current seen -> collect seen remaining
            | current :: remaining ->
                let direct = directTransports.TryFind current |> Option.defaultValue Set.empty
                collect (Set.add current seen) (Set.toList direct @ remaining)
        collect Set.empty [destination]
    let transports =
        callableOccurrences |> Seq.map (fun destination -> destination, transportPath destination) |> Map.ofSeq
    let callInstance = CallableInstantiations.callReader graph
    let calls =
        resolution.Calls |> choose (fun site call ->
            match call.Complete, call.Unknown, call.Targets with
            | true, false, [target] ->
                match graph.Nodes.TryFind target.Lambda, graph.Nodes.TryFind site with
                | Some { Kind = SemanticKind.Lambda(parameters, body, [], _, _) },
                  Some { Kind = SemanticKind.Application(callee, arguments); Children = children }
                    when children = callee :: arguments && arguments = target.Arguments && parameters.Length = arguments.Length ->
                    if parameters |> List.exists (fun (_, ty, _) -> not (freeMeasureVars ty).IsEmpty) then
                        match callInstance site target.Lambda with
                        | Some proof ->
                            Some { Site = site; Implementation = proof.Implementation; Parameters = proof.Parameters
                                   Arguments = proof.Arguments; Result = proof.Result; SignatureData = proof.SignatureData
                                   Participants = proof.Participants }
                        | None ->
                            errors.Add { Occurrence = Some site
                                         Participants = Set.ofList (site :: callee :: target.Lambda :: arguments)
                                         Reason = $"Baker callable instantiation did not settle a dimensional call instance for call site {NodeId.value site}: callee {NodeId.value target.Lambda} has measure-polymorphic formals and no checked scheme instance was proved along its actual callee/environment path." }
                            None
                    else
                        Some { Site = site; Implementation = target.Lambda; Parameters = parameters; Arguments = arguments
                               Result = body; SignatureData = Set.empty
                               Participants = Set.ofList (site :: callee :: target.Lambda :: body :: (arguments @ (parameters |> List.map (fun (_, _, id) -> id)))) }
                | _ -> None
            | _ -> None)
    let symbols, declarations = declarations graph
    let rec directCallee seen id =
        if Set.contains id seen then None else
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } when declarations.ContainsKey binding -> Some binding
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _); Children = [child] } when inner = child -> directCallee (Set.add id seen) inner
        | Some { Kind = SemanticKind.Lambda(_, _, [], _, LambdaContext.LazyThunk) } when declarations.ContainsKey id -> Some id
        | _ -> None
    let directCallees = graph.Nodes |> choose (fun id _ -> directCallee Set.empty id)
    let foreignCalls =
        graph.Edges |> List.choose (fun edge ->
            match edge.Role with EdgeRole.BoundaryCall call -> Some call.Site | _ -> None) |> Set.ofList
    let mutableRetentions =
        codata.MutableCallableStorage.Values |> Seq.collect _.Alternatives |> Seq.distinct |> Seq.filter (fun id ->
            codata.CallableCarriers.TryFind id |> Option.exists (fun carrier ->
                carrier.Environment |> Option.forall (fun environment ->
                    match graph.Nodes.TryFind environment.Owner with
                    | Some { Kind = SemanticKind.ClosureValue(_, allocation) } when not (codata.EnvironmentDestinations.ContainsKey allocation) ->
                        codata.Escapes.TryFind allocation = Some EscapeKind.StaticLifetime
                    | _ -> false))) |> Set.ofSeq
    let intrinsicAliases =
        let rec intrinsic seen id =
            if Set.contains id seen then false else
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.Intrinsic _ } -> true
            | Some { Kind = SemanticKind.TypeAnnotation(inner, _); Children = [child] } when inner = child ->
                intrinsic (Set.add id seen) inner
            | _ -> false
        graph.Nodes.Keys |> Seq.filter (intrinsic Set.empty) |> Set.ofSeq
    let programInstances =
        match ProgramInitialization.read graph with
        | None -> Map.empty
        | Some plan ->
            plan.ValueBindings |> Set.toList |> List.choose (fun binding ->
                Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.programInstance graph binding
                |> Option.map (fun value -> binding, { Carrier = value.Carrier; Allocation = value.Allocation; Participants = value.Participants }))
            |> Map.ofList
    let callbacks = CallbackDeclarations.read graph
    let voidCallbacks = callbacks.Callbacks |> List.filter _.ReturnsVoid |> List.map _.Lambda |> Set.ofList
    let voidPointers =
        codata.FunctionPointers.Values |> Seq.choose (function FunctionPointerPlan.Invoke(pointer, _, _, _) -> Some pointer | _ -> None)
        |> Seq.filter (fun pointer -> CallbackDeclarations.forPointer graph pointer |> Option.exists _.ReturnsVoid) |> Set.ofSeq
    let nativeEntries =
        codata.FunctionPointers.Values |> Seq.choose (function
            | FunctionPointerPlan.Address(symbol, implementation) -> Some(implementation, symbol)
            | _ -> None) |> Map.ofSeq
    let functionBindings =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind, node.Children |> List.tryHead |> Option.bind graph.Nodes.TryFind with
            | SemanticKind.Binding _, Some { Kind = SemanticKind.Lambda _ } -> Some node.Id
            | _ -> None) |> Set.ofSeq
    let definitionOnlyBindings =
        functionBindings |> Set.filter (fun id ->
            match graph.Nodes[id].Kind, graph.Nodes[id].Children with
            | SemanticKind.Binding(_, false, _, _), [child] -> not (codata.Closures.ContainsKey child)
            | _ -> false)
    let definitionOnlyLambdas =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind, node.Parent with
            | SemanticKind.Lambda(_, _, [], _, LambdaContext.LazyThunk), _ when not (codata.Closures.ContainsKey node.Id) ->
                if codata.LazyLayouts.Values |> Seq.exists (fun layout ->
                    layout.Thunk = node.Id && Clef.Compiler.Nanopass.LazyRuntime.validate graph layout) then Some node.Id else None
            | SemanticKind.Lambda(_, _, [], _, _), Some binding when definitionOnlyBindings.Contains binding && graph.Nodes[binding].Children = [node.Id] -> Some node.Id
            | _ -> None) |> Set.ofSeq
    let takesEnvironment =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Lambda(_, _, captures, _, _) when not captures.IsEmpty || node.Metadata.TryFind ClosureMetadata.RequiresClosurePair = Some(MetadataValue.Bool true) -> Some node.Id
            | _ -> None) |> Set.ofSeq
    let rec callableComponents seen occurrence =
        if Set.contains occurrence seen then None else
        let seen = Set.add occurrence seen
        match codata.CallableCarriers.TryFind occurrence, codata.CallableJoins.TryFind occurrence, codata.CallableFlows.TryFind occurrence with
        | Some carrier, None, None -> Some(if carrier.Environment.IsSome then 2 else 1)
        | None, Some joined, None -> alternativeComponents seen joined.Alternatives
        | None, None, Some flow -> alternativeComponents seen flow.Alternatives
        | _ -> None
    and alternativeComponents seen alternatives =
        match alternatives |> List.map (callableComponents seen) |> List.distinct with
        | [Some count] -> Some count
        | _ -> None
    let arguments =
        graph.Nodes |> choose (fun implementation node ->
            match node.Kind with
            | SemanticKind.Lambda(parameters, _, _, _, _) ->
                let omitted = ordinary.Parameters.TryFind implementation |> Option.defaultValue Set.empty
                let components =
                    parameters |> List.map (fun (_, _, formal) ->
                        let count =
                            if omitted.Contains formal then Some 0 else
                            match shapes.TryFind formal with
                            | Some(CallableValueShape.Data _) -> Some 1
                            | Some(CallableValueShape.Sequence _ | CallableValueShape.Lazy _) -> Some 2
                            | Some(CallableValueShape.Callable occurrence) -> callableComponents Set.empty occurrence
                            | None -> None
                        formal, count)
                if components |> List.exists (snd >> Option.isNone) then
                    if node.IsReachable then
                        errors.Add { Occurrence = Some implementation
                                     Participants = declarations[implementation].Participants
                                     Reason = "Callable declaration lacks a settled physical component convention for every logical formal." }
                    None
                else
                // A materialized environment is already an explicit formal.
                // Only the older placed closure convention adds a hidden prefix.
                let prefix = if codata.Closures.ContainsKey implementation then 1 else 0
                components |> List.mapFold (fun ordinal (formal, count) ->
                    let count = Option.get count
                    (formal, List.init count ((+) ordinal)), ordinal + count) prefix
                |> fst |> Map.ofList |> Some
            | _ -> None)
    let rec aliasTarget seen id =
        if Set.contains id seen then Result.Error seen else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.PatternBinding _; Children = child :: _ } when graph.Nodes.ContainsKey child -> aliasTarget seen child
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = child :: _ }
            when not (ProgramInitialization.isSlotBinding graph id) && graph.Nodes.ContainsKey child -> aliasTarget seen child
        | _ -> Result.Ok(id, seen)
    let aliases =
        graph.Nodes |> choose (fun id _ ->
            match aliasTarget Set.empty id with
            | Result.Ok value -> Some value
            | Result.Error participants ->
                errors.Add { Occurrence = Some id; Participants = participants; Reason = "SSA source aliases contain a cycle rather than one declared value identity." }
                None)
    let aliasTargets = aliases |> Map.map (fun _ (target, _) -> target)
    let unitNodes =
        graph.Nodes.Values |> Seq.filter (fun node ->
            match applySubst node.Type with NativeType.TApp({ NTUKind = Some NTUKind.NTUunit }, []) -> true | _ -> false) |> Seq.map _.Id |> Set.ofSeq
    let closedData =
        graph.Nodes.Values |> Seq.filter (fun node ->
            not (hasUnboundVars node.Type) && (freeMeasureVars node.Type).IsEmpty &&
            (match applySubst node.Type with NativeType.TFun _ | NativeType.TForall _ -> false | _ -> true)) |> Seq.map _.Id |> Set.ofSeq
    let demandCallSupports =
        ordinary.Calls |> Map.toSeq |> Seq.groupBy (fun (_, call) -> call.Implementation)
        |> Seq.map (fun (implementation, calls) ->
            implementation, calls |> Seq.collect (fun (site, call) -> site :: call.Actuals) |> Set.ofSeq)
        |> Map.ofSeq
    let supports =
        [ yield! declarations |> Map.toSeq |> Seq.map (fun (id, declaration) -> id, declaration.Participants)
          yield! calls |> Map.toSeq |> Seq.map (fun (id, call) -> id, call.Participants)
          yield! instances |> Map.toSeq |> Seq.map (fun (id, instance) -> id, instance.Participants)
          yield! transports |> Map.toSeq |> Seq.map (fun (id, sources) -> id, Set.add id sources)
          yield! programInstances |> Map.toSeq |> Seq.map (fun (id, instance) -> id, instance.Participants)
          yield! aliases |> Map.toSeq |> Seq.map (fun (id, (_, path)) -> id, path)
          yield! arguments |> Map.toSeq |> Seq.map (fun (implementation, formals) ->
              let components =
                  formals.Keys |> Seq.collect (fun formal ->
                      match codata.CallableCarriers.TryFind formal, codata.CallableJoins.TryFind formal, codata.CallableFlows.TryFind formal with
                      | Some carrier, _, _ -> [carrier.Implementation; carrier.Result] @ (carrier.Environment |> Option.map (fun env -> [env.Owner; env.Formal]) |> Option.defaultValue [])
                      | _, Some joined, _ -> joined.Storage :: joined.Read :: joined.Alternatives
                      | _, _, Some flow -> flow.Alternatives @ (flow.Dependencies |> Map.toSeq |> Seq.collect (fun (id, dependencies) -> id :: dependencies) |> Seq.toList)
                      | _ -> []) |> Set.ofSeq
              let demand = demandCallSupports.TryFind implementation |> Option.defaultValue Set.empty
              implementation, Set.unionMany [declarations[implementation].Participants; components; demand])
          yield! Set.unionMany [functionBindings; definitionOnlyBindings; definitionOnlyLambdas; takesEnvironment]
                 |> Set.toSeq |> Seq.map (fun id ->
                     let node = graph.Nodes[id]
                     id, Set.ofList (id :: (node.Children @ Option.toList node.Parent))) ]
        |> List.groupBy fst |> List.map (fun (id, values) -> id, values |> List.map snd |> Set.unionMany) |> Map.ofList
    if errors.Count > 0 then Result.Error(List.ofSeq errors) else
    Result.Ok {
        Carriers = codata.CallableCarriers; Joins = codata.CallableJoins; Flows = codata.CallableFlows
        MutableStorage = codata.MutableCallableStorage; ValueShapes = shapes; SignatureData = signatureData
        Calls = calls; Transports = transports; Declarations = declarations; Symbols = symbols
        IntrinsicAliases = intrinsicAliases; ProgramInstances = programInstances
        DirectCallees = directCallees; ForeignCalls = foreignCalls; MutableRetentions = mutableRetentions
        VoidCallbacks = voidCallbacks; VoidPointers = voidPointers; NativeEntries = nativeEntries; Supports = supports
        FunctionBindings = functionBindings; DefinitionOnlyBindings = definitionOnlyBindings; DefinitionOnlyLambdas = definitionOnlyLambdas
        Arguments = arguments; AliasTargets = aliasTargets; TakesEnvironment = takesEnvironment; UnitNodes = unitNodes; ClosedData = closedData
    }

/// Direct source callers validate demand before constructing the dependent
/// calling convention. Aggregate publication shares its already validated row.
let project graph = OrdinaryDemand.projectValidated graph |> Result.bind (projectWithDemand graph)

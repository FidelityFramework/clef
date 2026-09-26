// SPDX-License-Identifier: MIT
/// Provide caller storage for a closed materialized callable factory. This
/// prepares an explicit destination; residence still has to prove each capture
/// and every use of each distinct allocation before native admission.
module Clef.Compiler.Nanopass.EnvironmentFactoryResults

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.Nanopass.Recipe
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module Incidence = Clef.Compiler.Baker.Ingredients.Closures
module ExplicitDemand = Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand

let prepare (graph: SemanticGraph) (curry: CurryInfo) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let rec finalClosure seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.ClosureValue(_, environment) } -> Some(id, environment)
        | Some { Kind = SemanticKind.Sequential values } -> List.tryLast values |> Option.bind (finalClosure seen)
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } -> finalClosure seen value
        | Some { Kind = SemanticKind.EagerExpr value } when ExplicitDemand.operand graph id = Some value ->
            finalClosure seen value
        | _ -> None
    let resolved = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
    // Recover a named implementation through immutable value transport while
    // retaining the original callee expression. A stored application result
    // is a distinct formation frontier and is not flattened here.
    let rec functionReference seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } ->
            match nodes.TryFind value with
            | Some { Kind = SemanticKind.Lambda _ } -> Some(id, Set.empty)
            | _ -> functionReference seen value |> Option.map (fun (binding, path) -> binding, Set.add id path)
        | Some { Kind = SemanticKind.VarRef(_, Some value) }
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } ->
            functionReference seen value |> Option.map (fun (binding, path) -> binding, Set.add id path)
        | Some { Kind = SemanticKind.Sequential values } ->
            List.tryLast values |> Option.bind (functionReference seen)
            |> Option.map (fun (binding, path) -> binding, Set.add id path)
        | Some { Kind = SemanticKind.EagerExpr value } when ExplicitDemand.operand graph id = Some value ->
            functionReference seen value |> Option.map (fun (binding, path) -> binding, Set.add id path)
        | _ -> None
    let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
    let users id = incidence |> List.filter (fun edge -> Hyperedge.isStructural edge && List.contains id edge.Sources)
    let plans = nodes.Values |> Seq.choose (fun binding ->
        match binding.Kind, binding.Children with
        | SemanticKind.Binding(_, false, _, _), [implementation] ->
            match nodes.TryFind implementation with
            | Some ({ Kind = SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure) } as lambda)
                when [ClosureMetadata.RequiresClosurePair; ClosureMetadata.LambdaExpression]
                     |> List.forall (fun key -> lambda.Metadata.TryFind key <> Some(MetadataValue.Bool true)) ->
                finalClosure Set.empty body |> Option.bind (fun (owner, constructor) ->
                    let refs = nodes.Values |> Seq.choose (fun node ->
                        match node.Kind with SemanticKind.VarRef(_, Some definition) when definition = binding.Id -> Some node.Id | _ -> None) |> Set.ofSeq
                    let calls = nodes.Values |> Seq.choose (fun node ->
                        match node.Kind, resolved.Calls.TryFind node.Id with
                        | SemanticKind.Application(callee, arguments), Some { Targets = [target]; Unknown = false; Complete = true }
                            when target.Lambda = implementation && arguments.Length = parameters.Length ->
                            functionReference Set.empty callee |> Option.bind (fun (definition, path) ->
                                if definition = binding.Id then Some(node, callee, arguments, path) else None)
                        | _ -> None) |> Seq.toList
                    let callIds = calls |> List.map (fun (node, _, _, _) -> node.Id) |> Set.ofList
                    let rec closedValue seen id =
                        if Set.contains id seen then false else
                        let seen = Set.add id seen
                        let directUses = users id |> List.forall (fun edge ->
                            match nodes[edge.Target].Kind with
                            | SemanticKind.Application _ -> edge.Role = EdgeRole.Callee && callIds.Contains edge.Target
                            | SemanticKind.Binding(_, false, _, _) | SemanticKind.TypeAnnotation _ -> closedValue seen edge.Target
                            | SemanticKind.EagerExpr value when value = id && ExplicitDemand.operand graph edge.Target = Some id ->
                                closedValue seen edge.Target
                            | SemanticKind.Sequential values -> List.tryLast values <> Some id || closedValue seen edge.Target
                            | _ -> false)
                        let references = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Reference && List.contains id edge.Sources)
                        let referenceUses = references |> List.forall (fun edge ->
                            match nodes.TryFind edge.Target with
                            | Some { Kind = SemanticKind.VarRef(_, Some source) } when source = id -> closedValue seen edge.Target
                            | None -> true
                            | _ -> false)
                        let captured = nodes.Values |> Seq.exists (fun node ->
                            let captures =
                                match node.Kind with
                                | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures)
                                | SemanticKind.LazyExpr(_, captures) -> captures
                                | _ -> []
                            captures |> List.exists (fun capture -> capture.SourceNodeId = Some id))
                        directUses && referenceUses && not captured
                    let closed = not calls.IsEmpty && (refs |> Set.forall (closedValue Set.empty))
                    // One final formation per invocation, with no sharing into
                    // a prefix/branch or another activation of the same body.
                    let rec unique seen id =
                        if Set.contains id seen then false
                        elif id = body then users id |> List.forall (fun edge -> edge.Target = implementation)
                        else
                            match users id with
                            | [edge] ->
                                match nodes[edge.Target].Kind with
                                | SemanticKind.Sequential values when List.tryLast values = Some id -> unique (Set.add id seen) edge.Target
                                | SemanticKind.TypeAnnotation(value, _) when value = id -> unique (Set.add id seen) edge.Target
                                | SemanticKind.EagerExpr value when value = id && ExplicitDemand.operand graph edge.Target = Some id ->
                                    unique (Set.add id seen) edge.Target
                                | _ -> false
                            | _ -> false
                    if closed && unique Set.empty owner then Some(binding, lambda, owner, constructor, calls) else None)
            | _ -> None
        | _ -> None) |> Seq.toList
    let mutable changed = Set.empty
    let mutable edges = []
    let mutable updatedCurry = curry
    let fresh (source: SemanticNode) kind ty children =
        { source with Id = NodeId.fresh(); Kind = kind; Type = ty; Children = children; Parent = None
                      Metadata = Map.empty; ValueRange = None; IsReachable = true }
        |> markBaker "Closure.factoryResult" (NodeId.value source.Id)
    let signature (source: SemanticNode) ty kind children =
        let metadata =
            if source.Metadata.ContainsKey ClosureMetadata.SourceSignature then source.Metadata
            else source.Metadata.Add(ClosureMetadata.SourceSignature, MetadataValue.Type source.Type)
        { source with Type = ty; Kind = kind; Children = children; Metadata = metadata }
    let recipes = plans |> List.map (fun (binding, lambda, owner, constructor, calls) ->
        let generated = ResizeArray<SemanticNode>()
        let add node = generated.Add node; node
        let ty = Environments.environmentType
        let formal = fresh lambda (SemanticKind.PatternBinding "__environment_result") ty [] |> add
        let parameters, body, captures, enclosing, context =
            match lambda.Kind with SemanticKind.Lambda(a,b,c,d,e) -> a,b,c,d,e | _ -> failwith "Expected settled factory"
        // Closure invocation keeps the environment first (closure spec §6.1).
        // The internal result destination follows it, before source arguments.
        let hasEnvironment =
            match parameters with
            | (_, formalType, first) :: _ when formalType = Environments.environmentType ->
                graph.Edges |> List.exists (fun edge ->
                    edge.Role = EdgeRole.EnvironmentFormal && edge.Target = first && List.tryLast edge.Sources = Some lambda.Id)
            | _ -> false
        let ordinal = if hasEnvironment then 1 else 0
        let parameters = List.take ordinal parameters @ [("__environment_result", ty, formal.Id)] @ List.skip ordinal parameters
        let rec insert index = function
            | NativeType.TForall(parameters, body) -> NativeType.TForall(parameters, insert index body)
            | body when index = 0 -> NativeType.TFun(ty, body)
            | NativeType.TFun(domain, result) -> NativeType.TFun(domain, insert (index - 1) result)
            | _ -> invalidOp "A factory destination must occur at a settled parameter boundary"
        let insertDestination = insert ordinal
        let factoryType = insertDestination binding.Type
        signature lambda (insertDestination lambda.Type) (SemanticKind.Lambda(parameters, body, captures, enclosing, context))
            ((parameters |> List.map (fun (_, _, id) -> id)) @ [body]) |> add |> ignore
        signature binding factoryType binding.Kind binding.Children |> add |> ignore
        edges <- { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentResultDestination
                   Sources = [lambda.Id; owner; formal.Id]; Target = constructor; Ordinal = 0 } :: edges
        for call, callee, arguments, path in calls do
            let allocation = fresh call (SemanticKind.EnvironmentAllocate owner) ty [] |> add
            let name = sprintf "__environment_destination_%d" (NodeId.value call.Id)
            let stored = fresh call (SemanticKind.Binding(name, false, false, None)) ty [allocation.Id] |> add
            let destination = fresh call (SemanticKind.VarRef(name, Some stored.Id)) ty [] |> add
            for id in path do
                let source = nodes[id]
                let kind =
                    match source.Kind with
                    | SemanticKind.TypeAnnotation(inner, _) -> SemanticKind.TypeAnnotation(inner, factoryType)
                    | _ -> source.Kind
                signature source factoryType kind source.Children |> add |> ignore
            // This representation boundary only provides result storage.
            // Ordinary actuals retain their existing demand/effect frontiers;
            // copying them into a prefix would force previously deferred work.
            let arguments = List.take ordinal arguments @ [destination.Id] @ List.skip ordinal arguments
            let invocation = { fresh call (SemanticKind.Application(callee, arguments)) call.Type (callee :: arguments) with ValueRange = call.ValueRange } |> add
            let ordered = [stored.Id; invocation.Id]
            { call with Kind = SemanticKind.Sequential ordered; Children = ordered } |> add |> ignore
            edges <- { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentResultCall
                       Sources = [lambda.Id; constructor; formal.Id; allocation.Id; destination.Id]
                       Target = invocation.Id; Ordinal = 0 } :: edges
            updatedCurry <- { updatedCurry with SaturatedCalls = updatedCurry.SaturatedCalls.Remove(call.Id).Add(invocation.Id, { TargetBindingId = binding.Id; AllArgNodes = arguments }) }
        let emitted = generated |> Seq.map (fun node -> node.Id, node) |> Map.ofSeq |> Map.values |> Seq.toList
        changed <- Set.union changed (emitted |> List.map _.Id |> Set.ofList)
        { OriginalNodeId = binding.Id; NewNodes = emitted; ReplacementRootId = binding.Id
          ElaborationKind = "Baker"; ElaborationSource = "Closure.factoryResult"; NewEdges = [] })
    if recipes.IsEmpty then graph, curry else
    let byId = recipes |> List.map (fun recipe -> recipe.OriginalNodeId, recipe) |> Map.ofList
    let folded = FanOut.fanOut "EnvironmentFactoryResults" (fun node -> byId.ContainsKey node.Id)
                    (fun node _ -> RecipeCreated byId[node.Id]) graph
                 |> fun recipes -> FoldIn.foldIn recipes graph
    let updated = { folded with FieldRanges = graph.FieldRanges; ElementRanges = graph.ElementRanges
                                Layouts = graph.Layouts; StaticStringPool = graph.StaticStringPool; Escaping = graph.Escaping
                                Codata = lazy { graph.Codata.Value with Curry = updatedCurry }
                                Edges = (folded.Edges |> List.filter (fun edge ->
                                    not (changed.Contains edge.Target &&
                                        (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference || edge.Class = EdgeClass.Evaluation))))
                                        @ edges @ (changed |> Set.toList |> List.collect (fun id -> Incidence.structuralIncidence folded.Nodes[id])) }
    updated, updatedCurry

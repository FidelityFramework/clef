// SPDX-License-Identifier: MIT
/// Closed, direct sequence factories receive one caller-owned result destination.
/// This is a representation preparation after Curry/range settlement. It does
/// not prove the caller's allocation lifetime or invent an allocation region.
module Clef.Compiler.Nanopass.SequenceFactoryResults

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.Nanopass.Recipe
module Incidence = Clef.Compiler.Baker.Ingredients.Closures
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module Residence = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence

type Residual = { Factory: NodeId; Reason: string }
type Preparation = {
    Graph: SemanticGraph
    Curry: CurryInfo
    Destinations: Map<NodeId, NodeId>
    AllocationOrigins: Map<NodeId, NodeId>
    FactoryCalls: Map<NodeId, NodeId>
    Unresolved: Residual list
}

type private Call = {
    Site: SemanticNode
    Callee: NodeId
    Arguments: NodeId list
    Spine: Set<NodeId>
    CalleeNodes: Set<NodeId>
}

type private Plan = {
    Binding: SemanticNode
    Lambda: SemanticNode
    Owner: SemanticNode
    Calls: Call list
    Borrows: Hyperedge list
    ResultPath: NodeId list
}

let prepare (graph: SemanticGraph) (curry: CurryInfo) : Preparation =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let known, _ = Origins.settle graph curry
    let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
    let users = incidence |> List.filter Hyperedge.isStructural
                |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
                |> List.groupBy fst |> Map.ofList |> Map.map (fun _ pairs -> List.map snd pairs)
    let enclosingFunctions source =
        let rec walk seen pending scopes =
            match pending with
            | [] -> scopes
            | id :: rest when Set.contains id seen -> walk seen rest scopes
            | id :: rest ->
                let seen = Set.add id seen
                match nodes.TryFind id with
                | Some { Kind = SemanticKind.Lambda _ } -> walk seen rest (Set.add id scopes)
                | _ ->
                    let parents = users.TryFind id |> Option.defaultValue [] |> List.map _.Target
                    walk seen (parents @ rest) scopes
        walk Set.empty [source] Set.empty
    let requiresStorageLifetime (capture: CaptureInfo) =
        capture.IsMutable ||
        match Types.tryGetNTUKind (applySubst capture.Type) with
        | Some (NTUKind.NTUint _ | NTUKind.NTUuint _ | NTUKind.NTUfloat _ | NTUKind.NTUposit _
              | NTUKind.NTUbool | NTUKind.NTUchar | NTUKind.NTUunit | NTUKind.NTUsize | NTUKind.NTUdiff) -> false
        | _ -> true
    let environmentResidence = lazy (Residence.analyzeEnvironments graph)
    let environmentArguments = Environments.callEnvironments graph
    let captureBorrow lambda (owner: SemanticNode) (call: Call) (capture: CaptureInfo) =
        let formation = graph.Edges |> List.filter (fun edge -> edge.Target = owner.Id && edge.Role = EdgeRole.SequenceCaptureFormation)
        match formation, capture.SourceNodeId, Environments.sequenceInitializers graph owner with
        | [{ Class = EdgeClass.Provenance; Sources = [closure; implementation; formal] }], Some slot, Some initializers
            when implementation = lambda && capture.IsMutable ->
            let access = initializers |> List.tryFind (fst >> (=) slot) |> Option.map snd
            match access, graph.Nodes.TryFind closure, environmentArguments.TryFind call.Site.Id with
            | Some initializer, Some { Kind = SemanticKind.ClosureValue(code, environment) }, Some(_, actual)
                when code = lambda && Environments.tryEnvironmentOwner graph actual = Some closure &&
                     not ((enclosingFunctions slot).Contains lambda) ->
                let reading = environmentResidence.Value
                let evidence = reading.Evidence |> List.filter (fun edge ->
                    edge.Role = EdgeRole.EnvironmentResidence && edge.Target = closure &&
                    List.contains environment edge.Sources && List.contains slot edge.Sources)
                match evidence, Set.toList (enclosingFunctions call.Site.Id) with
                | [proof], [activation] when reading.Sites.ContainsKey environment ->
                    let covering = proof.Sources |> List.tryItem 1
                    let covered =
                        covering = Some activation ||
                        (reading.Evidence |> List.exists (fun edge ->
                            edge.Role = EdgeRole.SequenceTemplateBorrow &&
                            (match edge.Sources with
                             | [allocation; scope; _; generator] -> allocation = environment && Some scope = covering && generator = activation
                             | _ -> false)))
                    if covered then
                        Some { Sources = proof.Sources @ [formal; slot; initializer; lambda; call.Site.Id; actual; activation]
                               Target = owner.Id; Class = EdgeClass.Provenance; Role = EdgeRole.SequenceEnvironmentBorrow; Ordinal = 0 }
                    else None
                | _ -> None
            | _ -> None
        | _ -> None
    let captureResidual lambda (owner: SemanticNode) calls =
        match owner.Kind with
        | SemanticKind.SeqExpr(_, captures) ->
            captures |> List.tryFind (fun capture ->
                requiresStorageLifetime capture &&
                not (calls |> List.forall (fun call -> captureBorrow lambda owner call capture |> Option.isSome))) |> Option.map (fun capture ->
                let local = capture.SourceNodeId |> Option.exists (fun source -> (enclosingFunctions source).Contains lambda)
                if local then
                    sprintf "Factory-local capture '%s' refers to storage in the returning activation; a covering caller/program region is not established." capture.Name
                else
                    sprintf "Reference capture '%s' has no established storage region covering the caller-owned result." capture.Name)
        | _ -> None
    let rec resultType ty =
        match applySubst ty with
        | NativeType.TForall(_, body) | NativeType.TFun(_, body) -> resultType body
        | result -> result
    let rec functionReference seen id =
        if Set.contains id seen then None else
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } -> Some(binding, Set.singleton id)
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } ->
            functionReference (Set.add id seen) inner |> Option.map (fun (binding, refs) -> binding, Set.add id refs)
        | _ -> None
    // An unstored application chain has one eager frontier. A stored partial
    // has an earlier frontier and must not move its operands into each use.
    let rec callSpine seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Application(callee, arguments) } ->
            match functionReference Set.empty callee with
            | Some(binding, refs) -> Some(binding, callee, arguments, Set.singleton id, refs)
            | None ->
                callSpine seen callee |> Option.map (fun (binding, baseCallee, earlier, spine, refs) ->
                    binding, baseCallee, earlier @ arguments, Set.add id spine, refs)
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } ->
            callSpine seen inner |> Option.map (fun (binding, callee, arguments, spine, refs) ->
                binding, callee, arguments, Set.add id spine, refs)
        | _ -> None
    let allCalls = nodes.Values |> Seq.choose (fun node ->
        match node.Kind, applySubst node.Type with
        | SemanticKind.Application _, NativeType.TSeq _ ->
            callSpine Set.empty node.Id |> Option.map (fun (binding, callee, arguments, spine, refs) ->
                binding, { Site = node; Callee = callee; Arguments = arguments; Spine = spine; CalleeNodes = refs })
        | _ -> None) |> Seq.toList
    let mutable unresolved = []
    let refuse binding reason = unresolved <- { Factory = binding; Reason = reason } :: unresolved
    let plans = nodes.Values |> Seq.choose (fun binding ->
        match binding.Kind, binding.Children with
        | SemanticKind.Binding(_, false, _, _), [lambdaId]
            when binding.Metadata.TryFind ElaborationMetadata.For <> Some (MetadataValue.String "Seq.factoryResult") ->
            match nodes.TryFind lambdaId with
            | Some ({ Kind = SemanticKind.Lambda(parameters, body, captures, _, LambdaContext.RegularClosure) } as lambda) ->
                match resultType lambda.Type with
                | NativeType.TSeq _ ->
                    let calls = allCalls |> List.choose (fun (target, call) -> if target = binding.Id then Some call else None)
                    let rec finalExpression seen id =
                        if Set.contains id seen then None else
                        match nodes.TryFind id with
                        | Some { Kind = SemanticKind.SeqExpr _ } -> Some [id]
                        | Some { Kind = SemanticKind.Sequential values } ->
                            List.tryLast values |> Option.bind (finalExpression (Set.add id seen)) |> Option.map (fun path -> id :: path)
                        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } ->
                            finalExpression (Set.add id seen) value |> Option.map (fun path -> id :: path)
                        | _ -> None
                    let finalPath = finalExpression Set.empty body
                    let owner = finalPath |> Option.bind List.tryLast |> Option.bind nodes.TryFind |> Option.filter (fun node ->
                        match node.Kind with SemanticKind.SeqExpr _ -> known.TryFind body = Some node.Id | _ -> false)
                    let refs = nodes.Values |> Seq.choose (fun node ->
                        match node.Kind with SemanticKind.VarRef(_, Some target) when target = binding.Id -> Some node.Id | _ -> None) |> Set.ofSeq
                    let usedCallees = calls |> List.map _.CalleeNodes |> Set.unionMany
                    let usedSpine = calls |> List.map _.Spine |> Set.unionMany
                    let permittedUse edge =
                        (edge.Role = EdgeRole.Callee && usedSpine.Contains edge.Target)
                        || (edge.Role = EdgeRole.Operand && (usedCallees.Contains edge.Target || usedSpine.Contains edge.Target))
                    let isClosed =
                        not calls.IsEmpty && Set.isSubset refs usedCallees
                        && (Set.union usedCallees (usedSpine |> Set.filter (fun id -> calls |> List.forall (fun call -> call.Site.Id <> id)))
                            |> Set.forall (fun id -> users.TryFind id |> Option.defaultValue [] |> List.forall permittedUse))
                        && not (nodes.Values |> Seq.exists (fun node ->
                            let held = match node.Kind with
                                       | SemanticKind.Lambda(_, _, values, _, _) | SemanticKind.SeqExpr(_, values) | SemanticKind.LazyExpr(_, values) -> values
                                       | _ -> []
                            held |> List.exists (fun capture -> capture.SourceNodeId = Some binding.Id)))
                    let named =
                        captures.IsEmpty
                        && ([ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
                            |> List.forall (fun key -> lambda.Metadata.TryFind key <> Some (MetadataValue.Bool true)))
                    let storedPartial = curry.PartialApplications |> Map.exists (fun id partial ->
                        partial.TargetBindingId = binding.Id && not (usedSpine.Contains id))
                    if not named then refuse binding.Id "Factory requires a named direct callable with settled capture formals."; None
                    elif storedPartial then refuse binding.Id "Stored partial application requires its earlier eager snapshot frontier."; None
                    elif not isClosed then refuse binding.Id "Factory uses are not a closed set of direct complete application chains."; None
                    elif calls |> List.exists (fun call -> call.Arguments.Length <> parameters.Length) then
                        refuse binding.Id "Factory call arity does not match the settled complete formal list."; None
                    else
                        match owner with
                        | Some owner when not (hasUnboundVars owner.Type) && (freeMeasureVars owner.Type |> List.isEmpty) ->
                            // The final constructor must occur only once in this
                            // body; sharing it with an earlier prefix or another
                            // activation would reuse one destination for instances.
                            let containing = users.TryFind owner.Id |> Option.defaultValue []
                            let rec uniqueFinal seen id =
                                if Set.contains id seen then false
                                elif id = body then
                                    users.TryFind id |> Option.defaultValue [] |> List.forall (fun edge -> edge.Target = lambda.Id)
                                else
                                    match users.TryFind id |> Option.defaultValue [] with
                                    | [edge] ->
                                        match nodes[edge.Target].Kind with
                                        | SemanticKind.Sequential values when List.tryLast values = Some id -> uniqueFinal (Set.add id seen) edge.Target
                                        | SemanticKind.TypeAnnotation(value, _) when value = id -> uniqueFinal (Set.add id seen) edge.Target
                                        | _ -> false
                                    | _ -> false
                            match captureResidual lambda.Id owner calls with
                            | Some reason -> refuse binding.Id reason; None
                            | None when uniqueFinal Set.empty owner.Id && not containing.IsEmpty ->
                                let borrowed = match owner.Kind with SemanticKind.SeqExpr(_, captures) -> captures |> List.filter requiresStorageLifetime | _ -> []
                                let borrows = calls |> List.collect (fun call -> borrowed |> List.choose (captureBorrow lambda.Id owner call))
                                Some { Binding = binding; Lambda = lambda; Owner = owner; Calls = calls; Borrows = borrows
                                       ResultPath = lambda.Id :: finalPath.Value }
                            | None -> refuse binding.Id "Result constructor is shared or repeated outside its single final position."; None
                        | _ -> refuse binding.Id "Factory requires one concrete, uniquely known final SeqExpr constructor."; None
                | _ -> None
            | _ -> None
        | _ -> None) |> Seq.toList
    let mutable destinations, allocationOrigins, factoryCalls = Map.empty, Map.empty, Map.empty
    let mutable changed, retired = Set.empty, Set.empty
    let mutable extraEdges = []
    let mutable updatedCurry = curry
    let mutable meets = graph.Codata.Value.Meets
    let fresh (source: SemanticNode) kind ty children range =
        { source with Id = NodeId.fresh(); Kind = kind; Type = ty; Children = children; Parent = None
                      Metadata = Map.empty; IsReachable = true; EmissionStrategy = EmissionStrategy.Inline; ValueRange = range }
        |> markBaker "Seq.factoryResult" (NodeId.value source.Id)
    let signature (source: SemanticNode) ty kind children =
        let metadata =
            if source.Metadata.ContainsKey ClosureMetadata.SourceSignature then source.Metadata
            else source.Metadata.Add(ClosureMetadata.SourceSignature, MetadataValue.Type source.Type)
        { source with Type = ty; Kind = kind; Children = children; Metadata = metadata }
        |> markBaker "Seq.factoryResult" (NodeId.value source.Id)
    let recipes = plans |> List.map (fun plan ->
        let generated = ResizeArray<SemanticNode>()
        let add node = generated.Add node; node
        let destinationType = applySubst plan.Owner.Type
        let destination = fresh plan.Lambda (SemanticKind.PatternBinding "__sequence_result") destinationType [] None |> add
        destinations <- destinations.Add(plan.Owner.Id, destination.Id)
        let rec prepend ty =
            match ty with
            | NativeType.TForall(parameters, body) -> NativeType.TForall(parameters, prepend body)
            | _ -> NativeType.TFun(destinationType, ty)
        let factoryType = prepend plan.Binding.Type
        let parameters, body, captures, enclosing, context =
            match plan.Lambda.Kind with SemanticKind.Lambda(a,b,c,d,e) -> a,b,c,d,e | _ -> failwith "Expected factory Lambda"
        let parameters = ("__sequence_result", destinationType, destination.Id) :: parameters
        signature plan.Lambda (prepend plan.Lambda.Type) (SemanticKind.Lambda(parameters, body, captures, enclosing, context))
            ((parameters |> List.map (fun (_,_,id) -> id)) @ [body]) |> add |> ignore
        signature plan.Binding factoryType plan.Binding.Kind plan.Binding.Children |> add |> ignore
        extraEdges <- { Sources = plan.ResultPath; Target = destination.Id
                        Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0 } :: extraEdges
        for call in plan.Calls do
            let snapshots = call.Arguments |> List.mapi (fun index argument ->
                let value = nodes[argument]
                let name = sprintf "__sequence_argument_%d_%d" (NodeId.value call.Site.Id) index
                let binding = fresh value (SemanticKind.Binding(name, false, false, None)) value.Type [argument] value.ValueRange |> add
                let reference = fresh value (SemanticKind.VarRef(name, Some binding.Id)) value.Type [] value.ValueRange |> add
                binding.Id, reference.Id)
            let allocation = fresh call.Site (SemanticKind.ContinuationAllocate plan.Owner.Id) destinationType [] None |> add
            allocationOrigins <- allocationOrigins.Add(allocation.Id, plan.Owner.Id)
            let allocationName = sprintf "__sequence_destination_%d" (NodeId.value call.Site.Id)
            let allocationBinding = fresh call.Site (SemanticKind.Binding(allocationName, false, false, None)) destinationType [allocation.Id] None |> add
            let destinationActual = fresh call.Site (SemanticKind.VarRef(allocationName, Some allocationBinding.Id)) destinationType [] None |> add
            let callee = nodes[call.Callee]
            for calleeId in call.CalleeNodes do
                let source = nodes[calleeId]
                let kind = match source.Kind with SemanticKind.TypeAnnotation(inner, _) -> SemanticKind.TypeAnnotation(inner, factoryType) | _ -> source.Kind
                signature source factoryType kind source.Children |> add |> ignore
            let arguments = destinationActual.Id :: (snapshots |> List.map snd)
            let actual = fresh call.Site (SemanticKind.Application(callee.Id, arguments)) call.Site.Type (callee.Id :: arguments) call.Site.ValueRange |> add
            for proof in plan.Borrows do
                if List.contains call.Site.Id proof.Sources then
                    extraEdges <- { proof with Sources = proof.Sources @ plan.ResultPath @ [destination.Id; allocation.Id; destinationActual.Id; actual.Id] } :: extraEdges
            factoryCalls <- factoryCalls.Add(actual.Id, allocation.Id)
            let sequence = (snapshots |> List.map fst) @ [allocationBinding.Id; actual.Id]
            { call.Site with Kind = SemanticKind.Sequential sequence; Children = sequence }
            |> markBaker "Seq.factoryResult" (NodeId.value call.Site.Id) |> add |> ignore
            let obsolete = call.Spine.Remove call.Site.Id
            for id in obsolete do { nodes[id] with IsReachable = false } |> add |> ignore
            retired <- Set.union retired obsolete
            let rewrittenMeets =
                List.zip call.Arguments (snapshots |> List.map snd) |> List.collect (fun (original, replacement) ->
                    call.Spine |> Set.toList |> List.collect (fun id -> meets.TryFind id |> Option.defaultValue [])
                    |> List.filter (fun meet -> meet.Operand = original)
                    |> List.map (fun meet -> { meet with Consumer = actual.Id; Operand = replacement }))
            for id in call.Spine do meets <- meets.Remove id
            if not rewrittenMeets.IsEmpty then meets <- meets.Add(actual.Id, rewrittenMeets)
            let removedPartials = updatedCurry.PartialApplications |> Map.filter (fun id _ -> call.Spine.Contains id)
            let removedArguments = removedPartials.Values |> Seq.collect _.SuppliedArgNodes |> Set.ofSeq
            updatedCurry <-
                { updatedCurry with
                    PartialApplications = updatedCurry.PartialApplications |> Map.filter (fun id _ -> not (call.Spine.Contains id))
                    SaturatedCalls = (updatedCurry.SaturatedCalls |> Map.filter (fun id _ -> not (call.Spine.Contains id))).Add(actual.Id, { TargetBindingId = plan.Binding.Id; AllArgNodes = arguments })
                    DeferredArgNodes = Set.difference updatedCurry.DeferredArgNodes removedArguments }
            for node in generated do
                if node.Id <> call.Site.Id && node.Range = call.Site.Range then
                    extraEdges <- { Sources = [call.Site.Id; plan.Binding.Id; plan.Owner.Id]; Target = node.Id
                                    Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0 } :: extraEdges
        let emitted = generated |> Seq.map (fun node -> node.Id, node) |> Map.ofSeq |> Map.values |> Seq.toList
        changed <- Set.union changed (emitted |> List.map _.Id |> Set.ofList)
        { OriginalNodeId = plan.Binding.Id; NewNodes = emitted; ReplacementRootId = plan.Binding.Id
          ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Seq.factoryResult" })
    let recipeMap = recipes |> List.map (fun recipe -> recipe.OriginalNodeId, recipe) |> Map.ofList
    let folded =
        if recipeMap.IsEmpty then graph
        else
            FanOut.fanOut "SequenceFactoryResults" (fun node -> recipeMap.ContainsKey node.Id)
                (fun node _ -> RecipeCreated recipeMap[node.Id]) graph
            |> fun recipes -> FoldIn.foldIn recipes graph
    let updated =
        { folded with
            FieldRanges = graph.FieldRanges; ElementRanges = graph.ElementRanges; Layouts = graph.Layouts
            StaticStringPool = graph.StaticStringPool; Escaping = graph.Escaping
            Codata = lazy { graph.Codata.Value with Curry = updatedCurry; Meets = meets }
            Edges =
                (folded.Edges |> List.filter (fun edge ->
                    // Changed local evaluation contracts require regeneration;
                    // retaining the old call contract on a block would lie.
                    not (changed.Contains edge.Target && (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference || edge.Class = EdgeClass.Evaluation))))
                @ extraEdges
                @ (changed |> Set.toList |> List.filter (fun id -> not (retired.Contains id))
                   |> List.collect (fun id -> Incidence.structuralIncidence folded.Nodes[id])) }
    { Graph = updated; Curry = updatedCurry; Destinations = destinations; AllocationOrigins = allocationOrigins
      FactoryCalls = factoryCalls; Unresolved = List.rev unresolved }

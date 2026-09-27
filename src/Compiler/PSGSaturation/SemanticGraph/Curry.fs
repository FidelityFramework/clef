// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Curry: the normalisation of curried lambda chains and the record of partial applications.
///
/// A chain `Lambda(a) -> Lambda(b) -> body` becomes one `Lambda(a, b) -> body`; the absorbed
/// inner lambdas are marked unreachable and their parameters and the innermost body reparented.
/// Over the flattened graph, an under-saturated call of a flattened function is a partial
/// application, the binding that holds it is a partial-application binding, and a call through
/// that binding that completes the argument list is a saturated call. Runs at the end of
/// saturation, after the range pass and placement have read the graph in its curried form (the
/// order Composer's former pass kept); the result is carried as `Codata.Curry`.
/// A source function expression or an already-settled closure pair is a value boundary,
/// not another formal parameter group. Its lambda, captures and result type remain intact.
module Clef.Compiler.PSGSaturation.SemanticGraph.Curry

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

/// Reuse the distinction recorded during elaboration and read by closure placement.
/// In particular, `fun () -> value` retains its unit formal and is a returned
/// function value; absorbing it would silently change its parent's result to the payload.
let private isFunctionValue (node: SemanticNode) : bool =
    [ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
    |> List.exists (fun key -> Map.tryFind key node.Metadata = Some (MetadataValue.Bool true))

/// The parameters of a chain of nested lambdas, its innermost body, and the lambdas absorbed.
let rec private chain (graph: SemanticGraph) (nodeId: NodeId) : (string * NativeType * NodeId) list * NodeId * NodeId list =
    match SemanticGraph.tryGetNode nodeId graph with
    | Some ({ Kind = SemanticKind.Lambda (parameters, bodyId, _, _, _) } as node) when node.IsReachable && not (isFunctionValue node) ->
        let (deeper, innermost, absorbed) = chain graph bodyId
        (parameters @ deeper, innermost, nodeId :: absorbed)
    | _ -> ([], nodeId, [])

/// Flatten every reachable curried chain. Returns the graph and the absorbed lambdas.
let private flatten (graph: SemanticGraph) : SemanticGraph * Set<NodeId> =
    let mutable nodes = graph.Nodes
    let mutable absorbedSet = Set.empty
    for kvp in graph.Nodes do
        let node = kvp.Value
        if node.IsReachable && not (Set.contains node.Id absorbedSet) then
            match node.Kind with
            | SemanticKind.Lambda (outerParams, bodyId, captures, enclosing, context) ->
                match SemanticGraph.tryGetNode bodyId graph with
                | Some ({ Kind = SemanticKind.Lambda _ } as bodyNode) when bodyNode.IsReachable && not (isFunctionValue bodyNode) ->
                    let (innerParams, innermost, absorbed) = chain graph bodyId
                    let allParams = outerParams @ innerParams
                    let flattened =
                        { node with
                            Kind = SemanticKind.Lambda (allParams, innermost, captures, enclosing, context)
                            Children = (allParams |> List.map (fun (_, _, id) -> id)) @ [ innermost ] }
                    nodes <- Map.add node.Id flattened nodes
                    for absId in absorbed do
                        match Map.tryFind absId nodes with
                        | Some abs ->
                            nodes <- Map.add absId { abs with IsReachable = false } nodes
                            absorbedSet <- Set.add absId absorbedSet
                        | None -> ()
                    for (_, _, paramId) in innerParams do
                        match Map.tryFind paramId nodes with
                        | Some p -> nodes <- Map.add paramId { p with Parent = Some node.Id } nodes
                        | None -> ()
                    match Map.tryFind innermost nodes with
                    | Some b -> nodes <- Map.add innermost { b with Parent = Some node.Id } nodes
                    | None -> ()
                | _ -> ()
            | _ -> ()
    ({ graph with Nodes = nodes }, absorbedSet)

/// The reachable Lambda a function binding holds.
let private lambdaOfBinding (graph: SemanticGraph) (bindingId: NodeId) : NodeId option =
    match SemanticGraph.tryGetNode bindingId graph with
    | Some ({ Kind = SemanticKind.Binding _ } as binding) ->
        binding.Children |> List.tryHead |> Option.bind (fun childId ->
            match SemanticGraph.tryGetNode childId graph with
            | Some ({ Kind = SemanticKind.Lambda _ } as l) when l.IsReachable -> Some childId
            | _ -> None)
    | _ -> None

let private parameterCount (graph: SemanticGraph) (lambdaId: NodeId) : int option =
    match SemanticGraph.tryGetNode lambdaId graph with
    | Some { Kind = SemanticKind.Lambda (parameters, _, _, _, _) } -> Some parameters.Length
    | _ -> None

let private analyze (graph: SemanticGraph) (absorbed: Set<NodeId>) : CurryInfo =
    let reachable = graph.Nodes |> Map.toList |> List.map snd |> List.filter (fun n -> n.IsReachable)
    // under-saturated calls of a flattened function, and the bindings that hold them
    let partials, partialBindings =
        reachable
        |> List.fold (fun (partials: Map<NodeId, PartialApplication>, bindings: Set<NodeId>) node ->
            match node.Kind with
            | SemanticKind.Application (funcId, args) ->
                match SemanticGraph.tryGetNode funcId graph with
                | Some { Kind = SemanticKind.VarRef (_, Some bindingId) } ->
                    match lambdaOfBinding graph bindingId |> Option.bind (parameterCount graph) with
                    | Some total when total > args.Length ->
                        let partials' = Map.add node.Id ({ TargetBindingId = bindingId; SuppliedArgNodes = args; TotalParams = total } : PartialApplication) partials
                        let bindings' =
                            match node.Parent |> Option.bind (fun p -> SemanticGraph.tryGetNode p graph) with
                            | Some { Kind = SemanticKind.Binding _; Id = parentId } -> Set.add parentId bindings
                            | _ -> bindings
                        (partials', bindings')
                    | _ -> (partials, bindings)
                | _ -> (partials, bindings)
            | _ -> (partials, bindings)) (Map.empty, Set.empty)
    // calls through a partial-application binding that complete the argument list
    let saturated =
        reachable
        |> List.fold (fun (acc: Map<NodeId, SaturatedCall>) node ->
            match node.Kind with
            | SemanticKind.Application (funcId, args) ->
                match SemanticGraph.tryGetNode funcId graph with
                | Some { Kind = SemanticKind.VarRef (_, Some bindingId) } when Set.contains bindingId partialBindings ->
                    let partial =
                        SemanticGraph.tryGetNode bindingId graph
                        |> Option.bind (fun b -> List.tryHead b.Children)
                        |> Option.bind (fun appId -> Map.tryFind appId partials)
                    match partial with
                    | Some p when p.SuppliedArgNodes.Length + args.Length = p.TotalParams ->
                        Map.add node.Id ({ TargetBindingId = p.TargetBindingId; AllArgNodes = p.SuppliedArgNodes @ args } : SaturatedCall) acc
                    | _ -> acc
                | _ -> acc
            | _ -> acc) Map.empty
    { PartialApplications = partials
      SaturatedCalls = saturated
      PartialAppBindings = partialBindings
      AbsorbedLambdas = absorbed }

/// Flatten the graph's curried chains and record its partial applications.
let normalize (graph: SemanticGraph) : SemanticGraph * CurryInfo =
    let (flattened, absorbed) = flatten graph
    (flattened, analyze flattened absorbed)

/// A completed partial application keeps its saved and current argument
/// occurrences in one declared boundary. Validate the held owner facts against
/// the actual immutable binding chain before publication names that boundary.
let completedCalls (graph: SemanticGraph) (held: CurryInfo) (resolution: CallableOrigins.Resolution) =
    let current = analyze graph held.AbsorbedLambdas
    let errors = ResizeArray<WitnessProjectionFailure>()
    let refuse site participants =
        errors.Add { Occurrence = Some site; Participants = participants
                     Reason = "Completed partial application lacks its exact source declaration, immutable saved arguments and current invocation correspondence." }
    for KeyValue(site, saturated) in current.SaturatedCalls do
        if not (held.SaturatedCalls.ContainsKey site) then
            refuse site (Set.ofList(site :: saturated.TargetBindingId :: saturated.AllArgNodes))
    let calls = held.SaturatedCalls |> Map.fold (fun calls site saturated ->
        let participants = Set.ofList(site :: saturated.TargetBindingId :: saturated.AllArgNodes)
        let boundary =
            match graph.Nodes.TryFind site, current.SaturatedCalls.TryFind site, resolution.Calls.TryFind site with
            | Some { Kind = SemanticKind.Application(callee, arguments); Children = children }, None,
              Some { Complete = true; Unknown = false; Targets = [target] }
                when children = callee :: arguments && arguments = saturated.AllArgNodes && target.Arguments = arguments &&
                     target.Parameters.Length = arguments.Length ->
                // Factory-result recipes already made their hidden destination
                // an actual operand. Their complete invocation shares this
                // codata table but is not an immutable partial-binding chain.
                match graph.Nodes.TryFind saturated.TargetBindingId, graph.Nodes.TryFind target.Lambda with
                | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [implementation] },
                  Some { Kind = SemanticKind.Lambda(parameters, body, [], _, _) }
                    when implementation = target.Lambda && parameters = target.Parameters && body = target.Body ->
                    let complete = Set.union participants (Set.ofList(callee :: implementation :: body :: (parameters |> List.map (fun (_, _, id) -> id))))
                    Some { Site = site; Implementation = implementation; Parameters = parameters
                           Arguments = arguments; Result = body; SignatureData = Set.empty; Participants = complete }
                | _ -> None
            | Some { Kind = SemanticKind.Application(callee, arguments); Children = children }, Some actual,
              Some { Complete = true; Unknown = false; Targets = [target] }
                when actual = saturated && children = callee :: arguments ->
                match graph.Nodes.TryFind callee with
                | Some { Kind = SemanticKind.VarRef(_, Some binding) } ->
                    match graph.Nodes.TryFind binding with
                    | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [partialSite] }
                        when held.PartialAppBindings.Contains binding && current.PartialAppBindings.Contains binding ->
                        match graph.Nodes.TryFind partialSite, held.PartialApplications.TryFind partialSite,
                              current.PartialApplications.TryFind partialSite with
                        | Some { Kind = SemanticKind.Application(originalCallee, supplied); Children = partialChildren },
                          Some partial, Some expected
                            when partial = expected && partialChildren = originalCallee :: supplied &&
                                 partial.SuppliedArgNodes = supplied && partial.TargetBindingId = saturated.TargetBindingId &&
                                 supplied @ arguments = saturated.AllArgNodes ->
                            match graph.Nodes.TryFind saturated.TargetBindingId, graph.Nodes.TryFind originalCallee with
                            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [implementation] },
                              Some { Kind = SemanticKind.VarRef(_, Some declaration) } when declaration = saturated.TargetBindingId ->
                                match graph.Nodes.TryFind implementation with
                                | Some { Kind = SemanticKind.Lambda(parameters, body, [], _, _) }
                                    when target.Lambda = implementation && target.Body = body && target.Arguments = arguments &&
                                         parameters.Length = partial.TotalParams && parameters.Length = saturated.AllArgNodes.Length &&
                                         target.Parameters = List.skip supplied.Length parameters ->
                                    let complete = Set.union participants (Set.ofList(callee :: binding :: partialSite :: originalCallee :: implementation :: body :: (parameters |> List.map (fun (_, _, id) -> id))))
                                    Some { Site = site; Implementation = implementation; Parameters = parameters
                                           Arguments = saturated.AllArgNodes; Result = body; SignatureData = Set.empty
                                           Participants = complete }
                                | _ -> None
                            | _ -> None
                        | _ -> None
                    | _ -> None
                | _ -> None
            | _ -> None
        match boundary with
        | Some proof -> Map.add site proof calls
        | None -> refuse site participants; calls) Map.empty
    calls, List.ofSeq errors

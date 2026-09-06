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
module Clef.Compiler.PSGSaturation.SemanticGraph.Curry

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

/// The parameters of a chain of nested lambdas, its innermost body, and the lambdas absorbed.
let rec private chain (graph: SemanticGraph) (nodeId: NodeId) : (string * NativeType * NodeId) list * NodeId * NodeId list =
    match SemanticGraph.tryGetNode nodeId graph with
    | Some ({ Kind = SemanticKind.Lambda (parameters, bodyId, _, _, _) } as node) when node.IsReachable ->
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
                | Some ({ Kind = SemanticKind.Lambda _ } as bodyNode) when bodyNode.IsReachable ->
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
    let deferred = partials |> Map.fold (fun acc _ p -> p.SuppliedArgNodes |> List.fold (fun s a -> Set.add a s) acc) Set.empty
    { PartialApplications = partials
      SaturatedCalls = saturated
      PartialAppBindings = partialBindings
      AbsorbedLambdas = absorbed
      DeferredArgNodes = deferred }

/// Flatten the graph's curried chains and record its partial applications.
let normalize (graph: SemanticGraph) : SemanticGraph * CurryInfo =
    let (flattened, absorbed) = flatten graph
    (flattened, analyze flattened absorbed)

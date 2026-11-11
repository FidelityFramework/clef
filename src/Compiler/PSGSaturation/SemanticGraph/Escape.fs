// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Escape: the lifetime of every allocating site (a union construction, a record construction, a
/// string-returning call, a closure with captures), as the four-point lattice of
/// closure-representation.md §3.3. Computed once over the saturated graph and carried as
/// `Codata.Escapes`; the allocation site's witness reads its placement here and decides nothing.
module Clef.Compiler.PSGSaturation.SemanticGraph.Escape

open System.Collections.Generic
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

[<RequireQualifiedAccess>]
type private SiteKind =
    | Union
    | Record
    | StringCall
    | Closure

/// Whether a value is the last expression of its function, or referenced by it.
let private isReturned (graph: SemanticGraph) (valueId: NodeId) (scopeId: NodeId) : bool =
    match SemanticGraph.tryGetNode scopeId graph |> Option.bind (fun s -> List.tryLast s.Children) with
    | None -> false
    | Some lastId ->
        lastId = valueId ||
        (match SemanticGraph.tryGetNode lastId graph with
         | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> defId = valueId
         | _ -> false)

/// Whether a value transitively contributes to its function's return, through branches and blocks.
let rec private isTransitivelyReturned (graph: SemanticGraph) (valueId: NodeId) (scopeId: NodeId) : bool =
    isReturned graph valueId scopeId ||
    (match SemanticGraph.tryGetNode valueId graph |> Option.bind (fun n -> n.Parent) with
     | Some parentId -> isTransitivelyReturned graph parentId scopeId
     | None -> false)

let private isString (ty: NativeType) : bool =
    match ty with
    | NativeType.TApp (tycon, _) -> tycon.NTUKind = Some NTUKind.NTUstring
    | _ -> false

/// The escape kind of every allocating site in the graph.
let analyze (graph: SemanticGraph) : Map<NodeId, EscapeKind> =
    let varRefsByDef = Dictionary<NodeId, ResizeArray<NodeId>>()
    let bindingByFirstChild = Dictionary<NodeId, NodeId>()
    let siteList = ResizeArray<struct(NodeId * SiteKind)>()

    for kvp in graph.Nodes do
        let id = kvp.Key
        let node = kvp.Value
        match node.Kind with
        | SemanticKind.VarRef (_, Some defId) ->
            match varRefsByDef.TryGetValue(defId) with
            | true, list -> list.Add(id)
            | false, _ ->
                let list = ResizeArray<NodeId>(4)
                list.Add(id)
                varRefsByDef.[defId] <- list
        | SemanticKind.Binding _ ->
            match node.Children with
            | valueChild :: _ ->
                if not (bindingByFirstChild.ContainsKey(valueChild)) then
                    bindingByFirstChild.[valueChild] <- id
            | [] -> ()
        | SemanticKind.DUConstruct _ ->
            siteList.Add(struct(id, SiteKind.Union))
        | SemanticKind.RecordExpr _ ->
            siteList.Add(struct(id, SiteKind.Record))
        | SemanticKind.Application _ when isString node.Type ->
            siteList.Add(struct(id, SiteKind.StringCall))
        | SemanticKind.Lambda (_, _, captures, _, _)
            when not captures.IsEmpty ||
                 (node.Metadata |> Map.tryFind ClosureMetadata.RequiresClosurePair = Some (MetadataValue.Bool true)) ->
            siteList.Add(struct(id, SiteKind.Closure))
        | _ -> ()

    if siteList.Count = 0 then
        Map.empty
    else
        let enclosingCache = Dictionary<NodeId, NodeId option>()
        let rec enclosingFunction (nodeId: NodeId) : NodeId option =
            match enclosingCache.TryGetValue(nodeId) with
            | true, cached -> cached
            | false, _ ->
                let result =
                    match SemanticGraph.tryGetNode nodeId graph with
                    | None -> None
                    | Some node ->
                        match node.Kind with
                        | SemanticKind.Lambda _ | SemanticKind.Binding _ -> Some nodeId
                        | _ -> node.Parent |> Option.bind enclosingFunction
                enclosingCache.[nodeId] <- result
                result

        let escapesScope (scopeId: NodeId) (valueId: NodeId) : bool =
            match varRefsByDef.TryGetValue(valueId) with
            | false, _ -> false
            | true, refs ->
                let mutable found = false
                let mutable i = 0
                while i < refs.Count && not found do
                    match enclosingFunction refs.[i] with
                    | None -> found <- true
                    | Some useScope -> if useScope <> scopeId then found <- true
                    i <- i + 1
                found

        let stackLambdas = lazy ((ScopedCallbacks.read graph).StackLambdas)

        let escapeOf (siteId: NodeId) (kind: SiteKind) : EscapeKind =
            match kind with
            // a closure's environment is part of the pair it returns: structurally escaping
            | SiteKind.Closure when Set.contains siteId stackLambdas.Value -> EscapeKind.StackScoped
            | SiteKind.Closure -> EscapeKind.EscapesViaReturn
            | _ ->
                // a union or record construction is the value; a string-returning call is traced through
                // the binding that holds it
                let valueId =
                    match kind with
                    | SiteKind.StringCall ->
                        match bindingByFirstChild.TryGetValue(siteId) with
                        | true, bId -> bId
                        | false, _ -> siteId
                    | _ -> siteId
                match enclosingFunction valueId with
                | None -> EscapeKind.StaticLifetime
                | Some scopeId ->
                    if escapesScope scopeId valueId then EscapeKind.EscapesViaReturn
                    elif isTransitivelyReturned graph valueId scopeId then EscapeKind.EscapesViaReturn
                    else EscapeKind.StackScoped

        let mutable result = Map.empty
        for i = 0 to siteList.Count - 1 do
            let struct(siteId, kind) = siteList.[i]
            result <- Map.add siteId (escapeOf siteId kind) result
        result

/// Whether no lambda encloses a node: it belongs to the program, not to an activation.
let rec private outsideEveryLambda (graph: SemanticGraph) (nodeId: NodeId) : bool =
    match SemanticGraph.tryGetNode nodeId graph with
    | None -> false
    | Some node ->
        match node.Kind with
        | SemanticKind.Lambda _ -> false
        | _ -> node.Parent |> Option.forall (outsideEveryLambda graph)

/// The activation containing a node starts at its parent, including when the node
/// itself is a lambda used as the value of a write.
let enclosingLambda (graph: SemanticGraph) (nodeId: NodeId) : NodeId option =
    let rec find id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.Lambda _ } -> Some id
        | Some node -> node.Parent |> Option.bind find
        | None -> None
    SemanticGraph.tryGetNode nodeId graph |> Option.bind (fun node -> node.Parent) |> Option.bind find

/// Module cells live for the program; local cells need complete same-activation
/// access and no captured or borrowed cell before their stack residence is published.
let mutableCellResidences (graph: SemanticGraph) (storage: Map<NodeId, MutableCallableStorage>) : Map<NodeId, EscapeKind> =
    storage
    |> Map.toSeq
    |> Seq.choose (fun (_, row) ->
        match SemanticGraph.tryGetNode row.Binding graph with
        | Some { Kind = SemanticKind.Binding(_, true, _, _) } ->
            match enclosingLambda graph row.Binding with
            | None when outsideEveryLambda graph row.Binding -> Some(row.Binding, EscapeKind.StaticLifetime)
            | Some owner ->
                let inActivation id = enclosingLambda graph id = Some owner
                let writeInActivation (write: MutableCallableWrite) =
                    inActivation write.Site && inActivation write.Destination && inActivation write.Value
                if writeInActivation row.Initializer && List.forall writeInActivation row.Writes &&
                   Set.forall inActivation row.Reads && row.Captures.IsEmpty && row.Borrows.IsEmpty then
                    Some(row.Binding, EscapeKind.StackScoped)
                else None
            | None -> None
        | _ -> None)
    |> Map.ofSeq

/// Use the source census even when physical settlement rejected a cell: a
/// rejected row must not hide an access crossing the activation boundary.
[<RequireQualifiedAccess>]
type MutableCellActivationFailure =
    | Read
    | Write
    | Unsettled of string

let mutableCellActivationFailures (graph: SemanticGraph)
        (residuals: MutableCallableStorage.Residual list) =
    let _, _, accesses = MutableCallableStorage.sourceCensusesWithAccesses graph
    let failures =
        accesses |> Map.toList |> List.choose (fun (binding, cell) ->
            enclosingLambda graph binding |> Option.bind (fun owner ->
                let outside id = enclosingLambda graph id <> Some owner
                let write =
                    (binding, binding, cell.Initial) :: cell.Writes
                    |> List.tryPick (fun (site, destination, value) ->
                        if outside site || outside destination || outside value then Some(site, MutableCellActivationFailure.Write) else None)
                let read = cell.Reads |> Set.toList |> List.tryFind outside |> Option.map (fun id -> id, MutableCellActivationFailure.Read)
                let captured =
                    Set.union cell.Captures cell.Borrows |> Set.toList |> List.tryHead
                    |> Option.map (fun id -> id, MutableCellActivationFailure.Read)
                write |> Option.orElseWith (fun () -> read) |> Option.orElseWith (fun () -> captured)
                |> Option.map (fun (site, access) -> binding, site, access)))
    let failedBindings = failures |> List.map (fun (binding, _, _) -> binding) |> Set.ofList
    let unresolved =
        residuals |> List.choose (fun pending ->
            if failedBindings.Contains pending.Binding || (enclosingLambda graph pending.Binding).IsNone then None
            else Some(pending.Binding, pending.Binding, MutableCellActivationFailure.Unsettled pending.Reason))
        |> List.distinct
    failures @ unresolved

// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Escape: the lifetime of every allocating site (a union construction, a record construction, a
/// string-returning call, a closure with captures), as the four-point lattice of
/// closure-representation.md §3.3. Computed once over the saturated graph and carried as
/// `Codata.Escapes`; the allocation site's witness reads its placement here and decides nothing.
module Clef.Compiler.PSGSaturation.SemanticGraph.Escape

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

[<RequireQualifiedAccess>]
type private SiteKind =
    | Union
    | Record
    | StringCall
    | Closure

/// The enclosing function scope of a node: the nearest Lambda, or a top-level Binding.
let rec private enclosingFunction (graph: SemanticGraph) (nodeId: NodeId) : NodeId option =
    match SemanticGraph.tryGetNode nodeId graph with
    | None -> None
    | Some node ->
        match node.Kind with
        | SemanticKind.Lambda _ | SemanticKind.Binding _ -> Some nodeId
        | _ -> node.Parent |> Option.bind (enclosingFunction graph)

/// Whether a value is referenced from outside its defining scope.
let private escapesScope (graph: SemanticGraph) (scopeId: NodeId) (valueId: NodeId) : bool =
    graph.Nodes
    |> Seq.exists (fun kvp ->
        match kvp.Value.Kind with
        | SemanticKind.VarRef (_, Some defId) when defId = valueId ->
            match enclosingFunction graph kvp.Key with
            | None -> true
            | Some useScope -> useScope <> scopeId
        | _ -> false)

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

let private sites (graph: SemanticGraph) : (NodeId * SiteKind) list =
    graph.Nodes
    |> Seq.choose (fun kvp ->
        match kvp.Value.Kind with
        | SemanticKind.DUConstruct _ -> Some (kvp.Key, SiteKind.Union)
        | SemanticKind.RecordExpr _ -> Some (kvp.Key, SiteKind.Record)
        | SemanticKind.Application _ when isString kvp.Value.Type -> Some (kvp.Key, SiteKind.StringCall)
        | SemanticKind.Lambda (_, _, captures, _, _)
            when not captures.IsEmpty ||
                 (kvp.Value.Metadata |> Map.tryFind ClosureMetadata.RequiresClosurePair = Some (MetadataValue.Bool true)) ->
            Some (kvp.Key, SiteKind.Closure)
        | _ -> None)
    |> Seq.toList

let private escapeOf (graph: SemanticGraph) (siteId: NodeId) (kind: SiteKind) : EscapeKind =
    match kind with
    // a closure's environment is part of the pair it returns: structurally escaping
    | SiteKind.Closure when ScopedCallbacks.isStackLambda graph siteId -> EscapeKind.StackScoped
    | SiteKind.Closure -> EscapeKind.EscapesViaReturn
    | _ ->
        // a union or record construction is the value; a string-returning call is traced through
        // the binding that holds it
        let valueId =
            match kind with
            | SiteKind.StringCall ->
                graph.Nodes
                |> Seq.tryPick (fun kvp ->
                    match kvp.Value.Kind, kvp.Value.Children with
                    | SemanticKind.Binding _, valueChild :: _ when valueChild = siteId -> Some kvp.Key
                    | _ -> None)
                |> Option.defaultValue siteId
            | _ -> siteId
        match enclosingFunction graph valueId with
        | None -> EscapeKind.StaticLifetime
        | Some scopeId ->
            if escapesScope graph scopeId valueId then EscapeKind.EscapesViaReturn
            elif isTransitivelyReturned graph valueId scopeId then EscapeKind.EscapesViaReturn
            else EscapeKind.StackScoped

/// The escape kind of every allocating site in the graph.
let analyze (graph: SemanticGraph) : Map<NodeId, EscapeKind> =
    sites graph
    |> List.map (fun (siteId, kind) -> siteId, escapeOf graph siteId kind)
    |> Map.ofList

/// Whether no lambda encloses a node: it belongs to the program, not to an activation.
let rec private outsideEveryLambda (graph: SemanticGraph) (nodeId: NodeId) : bool =
    match SemanticGraph.tryGetNode nodeId graph with
    | None -> false
    | Some node ->
        match node.Kind with
        | SemanticKind.Lambda _ -> false
        | _ -> node.Parent |> Option.forall (outsideEveryLambda graph)

/// The residence of each published mutable callable cell whose binding no lambda encloses:
/// a module-level cell lives as long as the program (Farscape #109). A cell inside an
/// activation receives no residence here; its stack lifetime needs its own activation
/// proof (Farscape #107), so it stays unpublished rather than assumed.
let mutableCellResidences (graph: SemanticGraph) (storage: Map<NodeId, MutableCallableStorage>) : Map<NodeId, EscapeKind> =
    storage
    |> Map.toSeq
    |> Seq.choose (fun (_, row) ->
        match SemanticGraph.tryGetNode row.Binding graph with
        | Some { Kind = SemanticKind.Binding(_, true, _, _) } when outsideEveryLambda graph row.Binding ->
            Some(row.Binding, EscapeKind.StaticLifetime)
        | _ -> None)
    |> Map.ofSeq

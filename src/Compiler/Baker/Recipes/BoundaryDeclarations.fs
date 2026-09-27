// SPDX-License-Identifier: MIT
/// First stage of the boundary owner: declaration identity before ordinary demand.
module Clef.Compiler.Baker.Recipes.BoundaryDeclarations

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations

let isExternal (node: SemanticNode) =
    node.Metadata.ContainsKey "FidelityExtern.Library" || node.Metadata.ContainsKey "FidelityExtern.Symbol"

let bindingPath (graph: SemanticGraph) binding =
    let rec follow seen id =
        if Set.contains id seen then Error "The external declaration path is cyclic." else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [child] } ->
            follow seen child |> Result.map (fun (path, formals, body) -> id :: path, formals, body)
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _); Children = [child] } when inner = child ->
            follow seen inner |> Result.map (fun (path, formals, body) -> id :: path, formals, body)
        | Some { Kind = SemanticKind.Lambda(formals, body, captures, _, _) } when captures.IsEmpty -> Ok ([id], formals, body)
        | _ -> Error "The external declaration must retain a capture-free source function and its exact structural path."
    follow Set.empty binding

/// This is the only boundary callee identity walk. Other domains consume rows.
let target (graph: SemanticGraph) id =
    let rec follow seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some ({ Kind = SemanticKind.Binding(_, false, _, _); Children = [child] } as node) when not (isExternal node) ->
            match graph.Nodes.TryFind child |> Option.map _.Kind with
            | Some (SemanticKind.VarRef _ | SemanticKind.TypeAnnotation _ | SemanticKind.Intrinsic _) -> follow seen child
            | _ -> Some (node, seen)
        | Some ({ Kind = SemanticKind.Binding _ } as node)
        | Some ({ Kind = SemanticKind.Intrinsic _ } as node) -> Some (node, seen)
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _); Children = [child] } when inner = child -> follow seen inner
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } -> follow seen binding
        | _ -> None
    follow Set.empty id

let row (declaration: BoundaryDeclaration) =
    { Class = EdgeClass.Boundary; Role = EdgeRole.BoundaryDeclaration declaration; Ordinal = 0
      Sources = declaration.Path @ declaration.Formals @ [declaration.Body]; Target = declaration.Binding }

let elaborate (graph: SemanticGraph) =
    graph.Nodes |> Map.fold (fun enrichment _ node ->
        if not (isExternal node) then enrichment else
        match bindingPath graph node.Id with
        | Error _ -> enrichment // Late admission retains the located failure.
        | Ok (path, formals, body) ->
            let declaration = { Binding = node.Id; Path = path; Implementation = List.last path
                                Formals = formals |> List.map (fun (_, _, formal) -> formal); Body = body }
            { enrichment with NewEdges = enrichment.NewEdges @ [row declaration] }) Enrichment.empty

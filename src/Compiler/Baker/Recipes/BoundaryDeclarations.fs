// SPDX-License-Identifier: MIT
/// First stage of the boundary owner: declaration identity before ordinary demand.
module Clef.Compiler.Baker.Recipes.BoundaryDeclarations

open Clef.Compiler.NativeTypedTree.NativeTypes
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

/// Both direct declarations and imported-entry transport use this one source
/// identity walk. Transport finds a formation; it establishes no ABI or loading.
type private TargetPurpose =
    | Declaration
    | Entry

let private targetWith purpose (graph: SemanticGraph) id =
    let rec follow seen id =
        if Set.contains id seen then
            None
        else
            let seen = Set.add id seen

            match graph.Nodes.TryFind id with
            | Some({
                       Kind = SemanticKind.Binding(_, false, _, _)
                       Children = [ child ]
                   } as node) when not (isExternal node) ->
                match purpose, graph.Nodes.TryFind child |> Option.map _.Kind with
                | Entry, Some _ -> follow seen child
                | Declaration, Some(SemanticKind.VarRef _ | SemanticKind.TypeAnnotation _ | SemanticKind.Intrinsic _) -> follow seen child
                | _ -> Some(node, seen)
            | Some({ Kind = SemanticKind.Binding _ } as node)
            | Some({ Kind = SemanticKind.Intrinsic _ } as node) -> Some(node, seen)
            | Some {
                       Kind = SemanticKind.TypeAnnotation(inner, _)
                       Children = [ child ]
                   } when inner = child -> follow seen inner
            | Some {
                       Kind = SemanticKind.VarRef(_, Some binding)
                   } -> follow seen binding
            | Some({ Kind = SemanticKind.Application _ } as node) when purpose = Entry -> Some(node, seen)
            | _ -> None

    follow Set.empty id

/// This is the only boundary callee identity walk. Other domains consume rows.
let target graph id = targetWith Declaration graph id

type EntrySource =
    {
        Formation: NodeId
        Operand: NodeId
        Declaration: NodeId
        Transport: Set<NodeId>
    }

/// Current immutable transport to an actual ofExtern formation. The declared
/// binding is retained exactly; a coincidentally equal symbol is not a target.
let entryFormation graph occurrence =
    match targetWith Entry graph occurrence with
    | Some(({
                Kind = SemanticKind.Application(callee, [ operand ])
            } as formation),
           transport) ->
        match target graph callee, target graph operand with
        | Some({
                   Kind = SemanticKind.Intrinsic {
                                                     Module = IntrinsicModule.FnPtr
                                                     Operation = "ofExtern"
                                                 }
               },
               intrinsicPath),
          Some(declaration, declarationPath) when isExternal declaration ->
            Some
                {
                    Formation = formation.Id
                    Operand = operand
                    Declaration = declaration.Id
                    Transport = Set.unionMany [ transport; intrinsicPath; declarationPath ]
                }
        | _ -> None
    | _ -> None

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

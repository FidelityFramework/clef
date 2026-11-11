// SPDX-License-Identifier: MIT
/// First stage of the boundary owner: declaration identity before ordinary demand.
module Clef.Compiler.Baker.Recipes.BoundaryDeclarations

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
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

let isOptionalTagProjection (node: SemanticNode) =
    node.Metadata.ContainsKey "Baker.BoundaryOptionalTagProjection"

let elaborateOptionalTagProjections (graph: SemanticGraph) : SemanticGraph =
    let reading = Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read graph
    let conditionalByCall =
        reading.OptionalReceiving
        |> List.groupBy (fun row -> row.Call, row.Invocation.Parameter, row.Operand)
        |> List.choose (fun ((callId, parameter, operand), rows) ->
            match rows with
            | [first; second] when Set.ofList [first.CaseOrdinal; second.CaseOrdinal] = Set.ofList [0; 1] ->
                Some(callId, parameter, operand)
            | _ -> None)
        |> List.sortBy (fun (callId, parameter, _) -> NodeId.value callId, parameter)
        |> List.groupBy (fun (callId, _, _) -> callId)
        |> Map.ofList
    let existingProjections =
        graph.Nodes.Values
        |> Seq.choose (fun node ->
            match
                node.Kind,
                node.Metadata.TryFind "Baker.BoundaryOptionalTagProjection",
                node.Metadata.TryFind "Baker.BoundaryOptionalTagParameter"
            with
            | SemanticKind.DUGetTag(target, _),
              Some(MetadataValue.NodeIdList [callId; actual]),
              Some(MetadataValue.Int parameter)
                when target = actual ->
                Some((callId, parameter, actual), node)
            | _ -> None)
        |> Map.ofSeq
    Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () ->
        let enrichId = freshId ()
        let retainedIds, nodes, updatedCalls =
            conditionalByCall
            |> Map.fold (fun (retainedIds, (nodes: Map<NodeId, SemanticNode>), updatedCalls) callId items ->
                match nodes.TryFind callId with
                | Some({ Kind = SemanticKind.Application(callee, args) } as callNode) ->
                    let baseChildren =
                        callNode.Children
                        |> List.filter (fun child -> not (nodes.TryFind child |> Option.exists isOptionalTagProjection))
                    if baseChildren <> callee :: args then
                        retainedIds, nodes, updatedCalls
                    else
                        let projectionIds, retainedIds, nodes =
                            items
                            |> List.fold (fun (projIds, (retainedIds: Set<NodeId>), (nodes: Map<NodeId, SemanticNode>)) (_, parameter, operand) ->
                                match nodes.TryFind operand with
                                | None -> projIds, retainedIds, nodes
                                | Some actualNode ->
                                    let tagNode =
                                        match existingProjections.TryFind(callId, parameter, operand) with
                                        | Some existing ->
                                            let unchangedKind =
                                                match existing.Kind with
                                                | SemanticKind.DUGetTag(target, targetType) ->
                                                    target = operand
                                                    && Clef.Compiler.NativeTypedTree.TypeIdentities.ofType targetType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType actualNode.Type
                                                | _ -> false
                                            if unchangedKind
                                               && existing.Parent = Some callId
                                               && existing.ArenaAffinity = callNode.ArenaAffinity
                                               && existing.IsReachable = callNode.IsReachable
                                               && existing.ValueRange = Some(ValueRange.Bounded(0I, 1I)) then
                                                existing
                                            else
                                                { existing with
                                                    Kind = SemanticKind.DUGetTag(operand, actualNode.Type)
                                                    Parent = Some callId
                                                    ArenaAffinity = callNode.ArenaAffinity
                                                    IsReachable = callNode.IsReachable
                                                    ValueRange = Some(ValueRange.Bounded(0I, 1I)) }
                                        | None ->
                                            let baseMeta =
                                                Map.ofList
                                                    [ "Baker.BoundaryOptionalTagProjection", MetadataValue.NodeIdList [callId; operand]
                                                      "Baker.BoundaryOptionalTagParameter", MetadataValue.Int parameter
                                                      "Baker.SourceNode", MetadataValue.NodeId operand ]
                                            let meta =
                                                match callNode.Metadata.TryFind "Source.ObligationSite" with
                                                | Some(MetadataValue.String site) ->
                                                    baseMeta.Add("Source.ObligationSite", MetadataValue.String($"{site}/optionalTag/{parameter}"))
                                                | _ -> baseMeta
                                            { Id = NodeId.fresh ()
                                              Kind = SemanticKind.DUGetTag(operand, actualNode.Type)
                                              Range = { actualNode.Range with End = actualNode.Range.Start }
                                              Type = Types.intType
                                              SRTPResolution = None
                                              ArenaAffinity = callNode.ArenaAffinity
                                              LayoutHint = None
                                              Children = [operand]
                                              Parent = Some callId
                                              Metadata = meta
                                              IsReachable = callNode.IsReachable
                                              EmissionStrategy = EmissionStrategy.Inline
                                              ValueRange = Some(ValueRange.Bounded(0I, 1I)) }
                                            |> markBaker "Boundary.optionalTag" enrichId
                                    projIds @ [tagNode.Id], Set.add tagNode.Id retainedIds, nodes.Add(tagNode.Id, tagNode))
                                ([], retainedIds, nodes)
                        let children = baseChildren @ projectionIds
                        let updatedCall = if callNode.Children = children then callNode else { callNode with Children = children }
                        retainedIds, nodes.Add(callId, updatedCall), Set.add callId updatedCalls
                | _ -> retainedIds, nodes, updatedCalls)
                (Set.empty, graph.Nodes, Set.empty)
        let retiredIds =
            graph.Nodes
            |> Map.fold (fun retired id node ->
                if isOptionalTagProjection node && not (retainedIds.Contains id) then Set.add id retired else retired)
                Set.empty
        let nodes, strippedCalls =
            if retiredIds.IsEmpty then nodes, Set.empty
            else
                nodes
                |> Map.fold (fun ((acc: Map<NodeId, SemanticNode>), stripped) id node ->
                    if retiredIds.Contains id then acc, stripped
                    elif node.Children |> List.exists retiredIds.Contains then
                        let updated = { node with Children = node.Children |> List.filter (retiredIds.Contains >> not) }
                        acc.Add(id, updated), Set.add id stripped
                    else acc.Add(id, node), stripped)
                    (Map.empty, Set.empty)
        let affectedCalls = Set.union updatedCalls strippedCalls
        if affectedCalls.IsEmpty && retiredIds.IsEmpty && retainedIds.IsEmpty then
            graph
        else
            let keepEdge (edge: Hyperedge) =
                if retiredIds.Contains edge.Target || (edge.Sources |> List.exists retiredIds.Contains) then false
                elif retainedIds.Contains edge.Target && edge.Class = EdgeClass.Structural then false
                elif affectedCalls.Contains edge.Target && edge.Class = EdgeClass.Structural && edge.Role = EdgeRole.Attached && (edge.Sources |> List.exists retainedIds.Contains) then false
                else true
            let baseEdges = graph.Edges |> List.filter keepEdge
            let projectionEdges =
                retainedIds
                |> Set.toList
                |> List.collect (fun id -> Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence nodes[id])
            let attachedEdges =
                affectedCalls
                |> Set.toList
                |> List.collect (fun callId ->
                    match nodes.TryFind callId with
                    | Some callNode ->
                        Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence callNode
                        |> List.filter (fun edge -> edge.Role = EdgeRole.Attached && (edge.Sources |> List.exists retainedIds.Contains))
                    | None -> [])
            let edgeKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
            let existingManaged = graph.Edges |> List.filter (keepEdge >> not) |> List.map edgeKey
            let desiredManaged = (projectionEdges @ attachedEdges) |> List.map edgeKey
            let unchangedNodes =
                nodes.Count = graph.Nodes.Count
                && (nodes |> Map.forall (fun id node -> graph.Nodes.TryFind id |> Option.exists (fun original -> obj.ReferenceEquals(node, original))))
            if unchangedNodes && existingManaged = desiredManaged then
                graph
            else
                let newEdges = baseEdges @ projectionEdges @ attachedEdges
                { graph with Nodes = nodes; Edges = newEdges } |> Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.invalidateWitness)

let elaborate (graph: SemanticGraph) =
    graph.Nodes |> Map.fold (fun enrichment _ node ->
        if not (isExternal node) then enrichment else
        match bindingPath graph node.Id with
        | Error _ -> enrichment // Late admission retains the located failure.
        | Ok (path, formals, body) ->
            let declaration = { Binding = node.Id; Path = path; Implementation = List.last path
                                Formals = formals |> List.map (fun (_, _, formal) -> formal); Body = body }
            { enrichment with NewEdges = enrichment.NewEdges @ [row declaration] }) Enrichment.empty

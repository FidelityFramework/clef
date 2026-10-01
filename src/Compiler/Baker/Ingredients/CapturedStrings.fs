// SPDX-License-Identifier: MIT
/// Exact immutable string reads through a scoped callable environment.
/// This is source provenance only: neither storage layout nor residence is inferred.
module Clef.Compiler.Baker.Ingredients.CapturedStrings

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module ExplicitDemand = Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand

/// The initializer remains an occurrence, not a declaration guessed from a slot.
/// Support is direct derivation/navigation evidence; boundary freshness also
/// requires the complete current node/relation/root source snapshot.
type Read = {
    Occurrence: NodeId
    Environment: NodeId
    Formal: NodeId
    Owner: NodeId
    Implementation: NodeId
    Constructor: NodeId
    Slot: NodeId
    Initializer: NodeId
    SourceReference: bool
    Support: NodeId list
}

let reader (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let sourceEdge (edge: Hyperedge) = edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Target, edge.Sources
    let agrees (node: SemanticNode) =
        let expected = Closures.structuralIncidence node |> List.filter sourceEdge |> List.map key
        let actual = graph.Edges |> List.filter (fun edge -> edge.Target = node.Id && sourceEdge edge) |> List.map key
        actual.Length = (List.distinct actual).Length && List.forall (fun edge -> List.contains edge expected) actual
    let parents =
        nodes.Values |> Seq.collect Closures.structuralIncidence
        |> Seq.filter Hyperedge.isStructural
        |> Seq.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge.Target))
        |> Seq.groupBy fst
        |> Seq.map (fun (source, edges) -> source, edges |> Seq.map snd |> Seq.distinct |> Seq.toList)
        |> Map.ofSeq
    let rec formalPath seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        let follow source = formalPath seen source |> Option.map (fun (formal, path) -> formal, id :: path)
        match nodes.TryFind id with
        | Some node when applySubst node.Type = Environments.environmentType && agrees node ->
            match node.Kind with
            | SemanticKind.PatternBinding _ when node.Children.IsEmpty -> Some(id, [id])
            | SemanticKind.VarRef(_, Some source) when node.Children.IsEmpty -> follow source
            | SemanticKind.TypeAnnotation(source, declared)
                when applySubst declared = Environments.environmentType && node.Children = [source] -> follow source
            | SemanticKind.Binding(_, false, _, _) when node.Children.Length = 1 -> follow node.Children.Head
            | SemanticKind.EagerExpr source when ExplicitDemand.operand graph id = Some source -> follow source
            | _ -> None
        | _ -> None
    let rec scopePath owner seen id =
        if Set.contains id seen then None else
        match nodes.TryFind id with
        | Some node when agrees node ->
            if id = owner then Some [id] else
            match node.Kind, parents.TryFind id with
            | SemanticKind.Lambda _, _ -> None
            | _, Some enclosing when not enclosing.IsEmpty ->
                enclosing |> List.fold (fun proof parent ->
                    Option.map2 (@) proof (scopePath owner (Set.add id seen) parent)) (Some [id])
            | _ -> None
        | _ -> None
    // A generated forwarding read has no source-reference row. Its own exact
    // current constructor and immutable initializer row establish that case.
    // Absence of provenance on an ordinary expression is not permission to infer it.
    let forwardedEnvironment (read: SemanticNode) slot =
        nodes.Values |> Seq.choose (fun constructor ->
            match constructor.Kind with
            | SemanticKind.EnvironmentCreate(childOwner, initializers) when agrees constructor ->
                let matching = initializers |> List.indexed |> List.filter (fun (_, (actualSlot, value)) -> actualSlot = slot && value = read.Id)
                match matching, nodes.TryFind childOwner, Environments.capturedInitializers graph childOwner with
                | [(ordinal, _)], Some { Kind = SemanticKind.ClosureValue(_, actualConstructor) }, Some captures
                    when actualConstructor = constructor.Id && List.contains read.Id constructor.Children ->
                    match List.tryItem ordinal captures with
                    | Some(actualSlot, value, false) when actualSlot = slot && value = read.Id ->
                        Some [constructor.Id; childOwner; slot; read.Id]
                    | _ -> None
                | _ -> None
            | _ -> None)
        |> Seq.toList
    let forwardedSequence (read: SemanticNode) owner implementation formal slot =
        nodes.Values |> Seq.choose (fun sequence ->
            match sequence.Kind with
            | SemanticKind.SeqExpr(generator, captured) when sequence.Children = [generator] && agrees sequence ->
                let formations = graph.Edges |> List.filter (fun edge -> edge.Target = sequence.Id && edge.Role = EdgeRole.SequenceCaptureFormation)
                let rows = graph.Edges |> List.filter (fun edge ->
                    edge.Target = sequence.Id && match edge.Role with EdgeRole.SequenceCaptureInitializer _ -> true | _ -> false)
                match formations, Environments.sequenceInitializers graph sequence with
                | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [actualOwner; actualImplementation; actualFormal] }], Some values
                    when actualOwner = owner && actualImplementation = implementation && actualFormal = formal &&
                         rows.Length = captured.Length && values.Length = captured.Length ->
                    let complete =
                        List.zip captured values |> List.mapi (fun ordinal (capture, (source, value)) ->
                            match capture.SourceNodeId, rows |> List.filter (fun row -> row.Ordinal = ordinal) with
                            | Some actualSource, [{ Class = EdgeClass.Provenance; Role = EdgeRole.SequenceCaptureInitializer mutableCell; Sources = [actualSlot; actualValue] }]
                                when actualSource = source && actualSlot = source && actualValue = value && mutableCell = capture.IsMutable ->
                                match graph.Nodes.TryFind source, graph.Nodes.TryFind value with
                                | Some declaration, Some initializer when applySubst declaration.Type = applySubst capture.Type ->
                                    if source = value then agrees initializer else
                                    match initializer.Kind with
                                    | SemanticKind.EnvironmentRead(environment, held) when not mutableCell ->
                                        held = source && initializer.Children = [environment] && agrees initializer &&
                                        applySubst initializer.Type = applySubst capture.Type
                                    | SemanticKind.EnvironmentBorrow(environment, held) when mutableCell ->
                                        held = source && initializer.Children = [environment] && agrees initializer &&
                                        applySubst initializer.Type = NativeType.TByref(applySubst capture.Type, ByrefKind.InOut)
                                    | _ -> false
                                | _ -> false
                            | _ -> false)
                        |> List.forall id
                    let selected =
                        List.zip captured values |> List.filter (fun (capture, (source, value)) -> source = slot && value = read.Id && not capture.IsMutable)
                    if complete && selected.Length = 1 then
                        Some(sequence.Id :: generator :: owner :: implementation :: formal ::
                             (rows |> List.collect (fun row -> row.Target :: row.Sources)))
                    else None
                | _ -> None
            | _ -> None)
        |> Seq.toList
    let provenance (read: SemanticNode) owner implementation formal slot =
        let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.CaptureReferenceOrigin && edge.Target = read.Id)
        match rows with
        | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [actualOwner; declaration] }]
            when actualOwner = owner && declaration = slot -> Some(true, [owner; slot; read.Id])
        | [] ->
            match forwardedEnvironment read slot @ forwardedSequence read owner implementation formal slot with
            | [support] -> Some(false, support)
            | _ -> None
        | _ -> None
    fun occurrence ->
        match nodes.TryFind occurrence with
        | Some ({ Kind = SemanticKind.EnvironmentRead(environment, slot); Children = [actual] } as read)
            when actual = environment && Types.isStringType read.Type && agrees read ->
            formalPath Set.empty environment |> Option.bind (fun (formal, path) ->
                let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EnvironmentFormal && edge.Target = formal)
                match rows with
                | [({ Class = EdgeClass.Provenance; Sources = [owner; implementation]; Ordinal = 0 } as formalRow)]
                    when (graph.Edges |> List.filter (fun edge ->
                        edge.Role = EdgeRole.EnvironmentFormal &&
                        (match edge.Sources with actualOwner :: _ -> actualOwner = owner | _ -> false))
                        |> List.map key) = [key formalRow] ->
                    match nodes.TryFind owner, nodes.TryFind implementation, nodes.TryFind slot with
                    | Some ({ Kind = SemanticKind.ClosureValue(actualImplementation, constructor) } as closure),
                      Some ({ Kind = SemanticKind.Lambda(parameters, _, [], _, _) } as code), Some declaration
                        when actualImplementation = implementation && agrees closure && agrees code &&
                             closure.Children = [implementation; constructor] &&
                             applySubst declaration.Type = applySubst read.Type &&
                             (parameters |> List.filter (fun (_, _, id) -> id = formal)
                              |> function [(_, ty, _)] -> applySubst ty = Environments.environmentType | _ -> false) ->
                        match nodes.TryFind constructor, Environments.capturedInitializers graph owner,
                              scopePath implementation Set.empty read.Id, provenance read owner implementation formal slot with
                        | Some construction, Some captures, Some scope, Some(original, provenanceSupport) when agrees construction ->
                            match captures |> List.filter (fun (source, _, _) -> source = slot) with
                            | [(_, value, false)] ->
                                nodes.TryFind value |> Option.bind (fun initializer ->
                                    if applySubst initializer.Type <> applySubst read.Type then None else
                                    Some { Occurrence = occurrence; Environment = environment; Formal = formal
                                           Owner = owner; Implementation = implementation; Constructor = constructor
                                           Slot = slot; Initializer = value; SourceReference = original
                                           Support = read.Id :: environment :: owner :: implementation :: constructor :: slot :: value ::
                                                     (path @ scope @ provenanceSupport) |> List.distinct })
                            | _ -> None
                        | _ -> None
                    | _ -> None
                | _ -> None)
        | _ -> None

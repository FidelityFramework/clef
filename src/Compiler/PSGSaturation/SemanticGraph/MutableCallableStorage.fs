// SPDX-License-Identifier: MIT
/// Finite mutable callable storage is a source protocol, not a layout guessed
/// by Alex. A cell stores an alternative discriminator and, where present, the
/// actual environment descriptor. Reads dispatch to function values. No function
/// address is stored as data and no alternative supplies an exemplar identity.
module Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Residual = { Binding: NodeId; Participants: NodeId list; Reason: string }
type Settlement = {
    Storage: Map<NodeId, MutableCallableStorage>
    Joins: Map<NodeId, CallableJoin>
    Residuals: Residual list
}

/// Complete exact write boundaries are the first finite family. An opaque
/// write, an unproved borrow, or a different physical boundary remains owning
/// source work; its known neighbours cannot erase it from the cell's use set.
let settle (carriers: Map<NodeId, CallableCarrier>) (layouts: Map<NodeId, EnvironmentLayout>)
           (graph: SemanticGraph) : Settlement =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let mutable residuals = []
    let reject binding participants reason =
        residuals <- { Binding = binding; Participants = participants; Reason = reason } :: residuals
        None
    let rec target seen id =
        if Set.contains id seen then None else
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some declaration) } -> Some declaration
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> target (Set.add id seen) inner
        | _ -> None
    let environmentBytes (carrier: CallableCarrier) =
        match carrier.Environment with
        | None -> Some None
        | Some environment ->
            layouts.TryFind environment.Owner
            |> Option.filter (fun layout -> layout.Formal = environment.Formal &&
                                            layout.Implementation = carrier.Implementation && layout.Bytes > 0)
            |> Option.map (fun layout -> Some layout.Bytes)
    // Source component participants must agree before a common boundary is
    // proposed. Alex still checks the projected physical types at commitment.
    let rec sameShape seen left right =
        match left, right with
        | CallableValueShape.Data left, CallableValueShape.Data right ->
            match nodes.TryFind left, nodes.TryFind right with
            | Some left, Some right ->
                let sameRange =
                    match Types.tryGetNTUKind (applySubst left.Type) with
                    | Some (NTUKind.NTUint _ | NTUKind.NTUuint _) -> left.ValueRange = right.ValueRange
                    | _ -> true
                applySubst left.Type = applySubst right.Type && sameRange
            | _ -> false
        | CallableValueShape.Callable left, CallableValueShape.Callable right ->
            if Set.contains (left, right) seen then false else
            match carriers.TryFind left, carriers.TryFind right with
            | Some left, Some right -> sameBoundary (Set.add (left.Occurrence, right.Occurrence) seen) left right
            | _ -> false
        | _ -> false
    and sameBoundary seen (left: CallableCarrier) (right: CallableCarrier) =
        applySubst left.SourceType = applySubst right.SourceType &&
        environmentBytes left = environmentBytes right && (environmentBytes left).IsSome &&
        left.ParameterShapes.Length = right.ParameterShapes.Length &&
        List.forall2 (sameShape seen) left.ParameterShapes right.ParameterShapes &&
        sameShape seen left.ResultShape right.ResultShape

    let storage = nodes |> Map.toList |> List.choose (fun (binding, node) ->
        match node.Kind, applySubst node.Type, node.Children with
        | SemanticKind.Binding(_, true, _, _), NativeType.TFun _, [initial] ->
            let writes = nodes.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Set(destination, value) when target Set.empty destination = Some binding ->
                    Some(node.Id, destination, value)
                | SemanticKind.EnvironmentWrite(_, slot, value) when slot = binding ->
                    Some(node.Id, node.Id, value)
                | _ -> None) |> Seq.toList
            let targets = writes |> List.map (fun (_, destination, _) -> destination) |> Set.ofList
            let directReads =
                nodes.Values
                |> Seq.choose (fun node ->
                    match node.Kind with
                    | SemanticKind.VarRef(_, Some actual) when actual = binding && not (targets.Contains node.Id) -> Some node.Id
                    | SemanticKind.EnvironmentRead(_, slot) when slot = binding -> Some node.Id
                    | _ -> None)
                |> Set.ofSeq
            let borrows =
                nodes.Values
                |> Seq.choose (fun node ->
                    match node.Kind with
                    | SemanticKind.EnvironmentBorrow(_, slot) when slot = binding -> Some node.Id
                    | _ -> None)
                |> Set.ofSeq
            let environmentOwner = ClosureEnvironments.tryEnvironmentOwner graph
            let rec fromOriginalCell seen value =
                if value = binding then true
                elif Set.contains value seen then false
                else
                    match nodes.TryFind value with
                    | Some { Kind = SemanticKind.EnvironmentBorrow(environment, slot) } when slot = binding ->
                        environmentOwner environment
                        |> Option.bind (ClosureEnvironments.capturedInitializers graph)
                        |> Option.exists (List.exists (fun (source, initial, mutableCell) ->
                            source = binding && mutableCell && fromOriginalCell (Set.add value seen) initial))
                    | _ -> false
            let mutable invalidCapture = []
            let captures = nodes.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures)
                | SemanticKind.LazyExpr(_, captures) ->
                    let held = captures |> List.filter (fun capture -> capture.SourceNodeId = Some binding)
                    if held |> List.exists (fun capture ->
                        not capture.IsMutable || applySubst capture.Type <> applySubst graph.Nodes[binding].Type) then
                        invalidCapture <- node.Id :: invalidCapture
                    if held.IsEmpty then None else Some node.Id
                | SemanticKind.EnvironmentCreate(owner, initializers) ->
                    let held = initializers |> List.filter (fun (slot, value) -> slot = binding || value = binding || borrows.Contains value)
                    if held.IsEmpty then None else
                    match ClosureEnvironments.capturedInitializers graph owner with
                    | Some complete when held |> List.forall (fun (slot, value) ->
                        slot = binding && fromOriginalCell Set.empty value &&
                        List.contains (slot, value, true) complete) -> Some node.Id
                    | _ -> invalidCapture <- node.Id :: invalidCapture; Some node.Id
                | _ -> None) |> Set.ofSeq
            let validAccess id =
                let access = nodes[id]
                match access.Kind with
                | SemanticKind.EnvironmentRead(environment, slot) | SemanticKind.EnvironmentBorrow(environment, slot)
                | SemanticKind.EnvironmentWrite(environment, slot, _) ->
                    environmentOwner environment
                    |> Option.bind (ClosureEnvironments.capturedInitializers graph)
                    |> Option.exists (List.exists (fun (source, value, mutableCell) ->
                        source = slot && source = binding && mutableCell && fromOriginalCell Set.empty value))
                | _ -> true
            let invalidAccess = Set.unionMany [directReads; borrows; writes |> List.map (fun (site, _, _) -> site) |> Set.ofList]
                                |> Set.toList |> List.filter (validAccess >> not)
            let unsupportedUses = nodes.Values |> Seq.choose (fun consumer ->
                let mentions =
                    (kindEdges consumer.Id consumer.Kind |> List.exists (fun edge ->
                        (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) && List.contains binding edge.Sources)) ||
                    (match consumer.Kind with SemanticKind.Binding _ -> List.contains binding consumer.Children | _ -> false)
                if not mentions then None else
                match consumer.Kind with
                | SemanticKind.VarRef(_, Some actual) when actual = binding -> None
                | SemanticKind.EnvironmentCreate _ when captures.Contains consumer.Id -> None
                | SemanticKind.Sequential expressions when List.tryLast expressions <> Some binding -> None
                | _ -> Some consumer.Id) |> Seq.toList
            let opaqueReferences =
                graph.Edges |> List.choose (fun edge ->
                    if edge.Class <> EdgeClass.Reference || not (List.contains binding edge.Sources) then None
                    else
                        match nodes.TryFind edge.Target with
                        | Some { Kind = SemanticKind.VarRef(_, Some actual) }
                            when actual = binding && edge.Role = EdgeRole.Definition && edge.Sources = [binding] -> None
                        | Some { Kind = SemanticKind.EnvironmentCreate _ } when captures.Contains edge.Target -> None
                        | None when graph.Nodes.ContainsKey edge.Target -> None
                        | _ -> Some edge.Target)
            let unsupported = unsupportedUses @ opaqueReferences
            let values = initial :: (writes |> List.map (fun (_, _, value) -> value))
            let exact = values |> List.map (fun value -> carriers.TryFind value |> Option.filter (fun carrier ->
                carrier.Occurrence = value && applySubst carrier.SourceType = applySubst node.Type &&
                (nodes.TryFind value |> Option.exists (fun value ->
                    applySubst (CallableCarriers.sourceType value) = applySubst carrier.SourceType)) &&
                (nodes.TryFind carrier.Implementation |> Option.exists (fun code ->
                    match code.Kind with
                    | SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure) ->
                        parameters = carrier.Parameters && body = carrier.Result &&
                        (parameters |> List.map (fun (_, _, id) -> nodes.TryFind id |> Option.map (CallableCarriers.valueShape graph))) =
                            (carrier.ParameterShapes |> List.map Some) &&
                        (nodes.TryFind body |> Option.map (CallableCarriers.valueShape graph)) = Some carrier.ResultShape
                    | _ -> false))))
            if not invalidCapture.IsEmpty then reject binding invalidCapture "A mutable callable capture does not preserve the original shared cell and mutable mode."
            elif not invalidAccess.IsEmpty then reject binding invalidAccess "A mutable callable access lacks its exact captured-cell provenance."
            elif not unsupported.IsEmpty then reject binding unsupported "The mutable callable cell has an unaccounted storage or reference use."
            elif List.exists Option.isNone exact then
                reject binding (List.zip values exact |> List.choose (fun (id, carrier) -> if carrier.IsNone then Some id else None))
                    "Every mutable callable write requires its complete exact alternative; opaque or joined writes need further source dispatch settlement."
            else
                let exact = List.choose id exact
                let first = List.head exact
                if not (exact |> List.forall (sameBoundary Set.empty first)) then
                    reject binding values "Mutable callable alternatives require an admitted common parameter, result, and environment convention."
                else
                    let alternatives = values |> List.distinct
                    let alternative value = alternatives |> List.findIndex ((=) value)
                    let initialWrite = { Site = binding; Destination = binding; Value = initial; Alternative = alternative initial }
                    Some(binding,
                        { Binding = binding; SourceType = node.Type; Initializer = initialWrite
                          Writes = writes |> List.map (fun (site, target, value) ->
                            { Site = site; Destination = target; Value = value; Alternative = alternative value })
                          Reads = directReads; Alternatives = alternatives
                          AlternativeCarriers = alternatives |> List.map (fun id -> carriers[id])
                          EnvironmentBytes = environmentBytes first |> Option.get
                          Captures = captures; Borrows = borrows })
        | SemanticKind.Binding(_, true, _, _), NativeType.TFun _, _ ->
            reject binding node.Children "Mutable callable storage requires one exact initializer."
        | _ -> None) |> Map.ofList

    let mutable joins =
        storage |> Map.toList |> List.collect (fun (_, cell) ->
            cell.Reads |> Set.toList |> List.map (fun read ->
                read, { Occurrence = read; SourceType = cell.SourceType; Storage = cell.Binding
                        Read = read; Alternatives = cell.Alternatives })) |> Map.ofList
    let mutable changed = true
    while changed do
        changed <- false
        for KeyValue(id, node) in nodes do
            let source =
                match node.Kind, node.Children with
                | SemanticKind.Binding(_, false, _, _), [value] -> Some value
                | SemanticKind.VarRef(_, Some value), _ | SemanticKind.TypeAnnotation(value, _), _ -> Some value
                | SemanticKind.Sequential values, _ -> List.tryLast values
                | _ -> None
            match source |> Option.bind (fun source -> joins.TryFind source) with
            | Some source when not (joins.ContainsKey id) && applySubst node.Type = applySubst source.SourceType ->
                joins <- joins.Add(id, { source with Occurrence = id })
                changed <- true
            | _ -> ()
    { Storage = storage; Joins = joins; Residuals = List.rev residuals }

/// Revalidate the complete participant set when observing retained codata.
/// Added writes/borrows and changed signatures retract an earlier conclusion.
let validate (graph: SemanticGraph) (expected: MutableCallableStorage) =
    let codata = graph.Codata.Value
    let currentCarriers, _ = CallableCarriers.settle
                                { Layouts = codata.EnvironmentLayouts; Origins = ClosureEnvironments.origins graph
                                  Known = ClosureEnvironments.knownCallables graph } graph
    let actual = settle currentCarriers codata.EnvironmentLayouts graph
    actual.Storage.TryFind expected.Binding = Some expected

let validateJoin (graph: SemanticGraph) (expected: CallableJoin) =
    let actual = settle graph.Codata.Value.CallableCarriers graph.Codata.Value.EnvironmentLayouts graph
    actual.Joins.TryFind expected.Occurrence = Some expected &&
    (graph.Codata.Value.MutableCallableStorage.TryFind expected.Storage |> Option.exists (validate graph))

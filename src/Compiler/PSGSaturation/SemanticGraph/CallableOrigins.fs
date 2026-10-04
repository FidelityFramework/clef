// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Read actual callable boundaries from resident value flow. A function's type
/// supplies the types at a proved boundary; it never supplies the native arity.
module Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins

open System.Collections.Generic
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

/// One stage of an application whose complete argument list crosses a returned
/// function boundary. The arity is established from every possible callee.
type Stage = { Arguments: NodeId list; ResultType: NativeType }

/// A complete invocation at an actual callable boundary. Parameters already
/// supplied by an earlier partial application are represented by ParameterInputs.
type CallTarget = {
    Lambda: NodeId
    Parameters: (string * NativeType * NodeId) list
    Arguments: NodeId list
    Body: NodeId
}
type ResolvedCall = {
    Targets: CallTarget list
    Unknown: bool
    /// Every alternative is an exact complete invocation. Unknown alone does
    /// not imply this: a known partial origin deliberately is not opaque.
    Complete: bool
}
/// The first declared boundary, including known partial applications. Complete
/// CallTargets alone omit partials and cannot authorize all supplied actuals.
type FirstBoundaryTarget = {
    Lambda: NodeId
    Parameters: (string * NativeType * NodeId) list
    Offset: int
    Remaining: int
}
type FirstBoundary = {
    Callee: NodeId
    Targets: FirstBoundaryTarget list
    UnknownOrigins: Set<NodeId>
}
type Resolution = {
    Calls: Map<NodeId, ResolvedCall>
    /// Native entry invocations retain their own boundary. They are not
    /// ordinary closure calls or evidence for an ordinary calling convention.
    NativeCalls: Map<NodeId, ResolvedCall>
    ParameterInputs: Map<NodeId, (NodeId * NodeId) list>
    Lambdas: Map<NodeId, NodeId>
    FirstBoundaries: Map<NodeId, FirstBoundary>
    /// Final source observations; completeness is scoped by the owning Baker
    /// whole-revision authority, not by this map's direct participant IDs.
    Branches: Map<NodeId, CallableBranchObservation>
}

type private Origin = NodeId * int

// Negative offsets distinguish an opaque producer (-1) from a payload that
// the current typed constructor proves absent (-2). Empty alternatives flow
// internally so aliases cannot reseed them as unknown. They never supply a
// callable target, arity, environment, or published branch witness.
let private emptyOrigin id : Origin = id, -2
let private isEmptyOrigin (_, offset) = offset = -2
let private presentOrigins origins = origins |> Set.filter (isEmptyOrigin >> not)

type private GuardDecision =
    | AwaitOrigins
    | BothArms
    | OpaqueArms of NodeId
    | OneArm of CallableBranchObservation

type private Transport = ValidTransport | PendingTransport | UnsupportedTransport | MalformedTransport

let private sameType left right =
    Clef.Compiler.NativeTypedTree.TypeIdentities.ofType left =
        Clef.Compiler.NativeTypedTree.TypeIdentities.ofType right

/// This first case adapter covers the exact native Result declaration. Other
/// unions retain the existing conservative join until their owner is supported.
let private resultPayloads ty =
    match applySubst ty with
    | NativeType.TApp(constructor, [ok; error])
        when Clef.Compiler.NativeTypedTree.TypeIdentities.constructor constructor =
                 Clef.Compiler.NativeTypedTree.TypeIdentities.constructor
                     Clef.Compiler.NativeTypedTree.Expressions.Types.resultTycon -> Some ["Ok", ok; "Error", error]
    | _ -> None

/// Case identity comes from the exact native declarations, not a matching
/// name or discriminant. Unsupported unions retain conservative origins.
let private casePayloads ty =
    match resultPayloads ty with
    | Some cases -> Some(cases |> List.map (fun (name, payload) -> name, Some payload))
    | None ->
        match applySubst ty with
        | NativeType.TApp(constructor, [payload])
            when Clef.Compiler.NativeTypedTree.TypeIdentities.constructor constructor =
                     Clef.Compiler.NativeTypedTree.TypeIdentities.constructor Types.optionTyCon ->
            Some ["None", None; "Some", Some payload]
        | _ -> None

let private branchReaders (graph: SemanticGraph) (nodes: Map<NodeId, SemanticNode>) =
    let sourceEdge (edge: Hyperedge) = edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference
    let edgeKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let recorded =
        graph.Edges
        |> List.filter sourceEdge
        |> List.groupBy _.Target
        |> Map.ofList
    let agrees (node: SemanticNode) =
        let expected = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node |> List.filter sourceEdge
        let children = kindEdges node.Id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
        let childrenAgree =
            match node.Kind with
            | SemanticKind.Binding _ -> node.Children.Length = 1
            | SemanticKind.Intrinsic _ -> node.Children.IsEmpty
            | _ -> node.Children = children
        let actual = recorded.TryFind node.Id |> Option.defaultValue [] |> List.map edgeKey
        childrenAgree &&
        (expected |> List.collect _.Sources |> List.forall nodes.ContainsKey) &&
        actual.Length = (List.distinct actual).Length &&
        List.forall (fun row -> expected |> List.exists (fun edge -> edgeKey edge = row)) actual
    let caseAlternative unionType (origin, offset) =
        match casePayloads unionType, nodes.TryFind origin with
        | Some cases, Some node when offset = 0 && sameType node.Type unionType && agrees node ->
            let value =
                match node.Kind with
                | SemanticKind.DUConstruct(name, tag, payload, None)
                | SemanticKind.UnionCase(name, tag, payload) -> Some(name, tag, payload)
                | _ -> None
            value |> Option.bind (fun (name, tag, payload) ->
                let declared = if tag >= 0 && tag < cases.Length then List.tryItem tag cases else None
                match declared, payload with
                | Some(expectedName, None), None when name = expectedName ->
                    Some { Constructor = origin; Tag = tag; Payloads = [] }
                | Some(expectedName, Some expectedType), Some payload when name = expectedName ->
                    nodes.TryFind payload |> Option.bind (fun actual ->
                        if sameType actual.Type expectedType then
                            Some { Constructor = origin; Tag = tag; Payloads = [payload] }
                        else None)
                | _ -> None)
        | _ -> None
    let readGuard (choice: SemanticNode) =
        match choice.Kind with
        | SemanticKind.IfThenElse(guard, yes, Some no) when agrees choice ->
            match nodes.TryFind guard, nodes.TryFind yes, nodes.TryFind no with
            | Some condition, Some yesNode, Some noNode
                when sameType condition.Type Types.boolType && agrees condition &&
                     sameType yesNode.Type choice.Type && sameType noNode.Type choice.Type ->
                match condition.Kind with
                | SemanticKind.Application(operator, [tag; literal]) ->
                    match nodes.TryFind operator, nodes.TryFind tag, nodes.TryFind literal with
                    | Some operation, Some tagRead, Some expected
                        when agrees operation && agrees tagRead && agrees expected &&
                             sameType tagRead.Type Types.int8Type && sameType expected.Type Types.int8Type &&
                             sameType operation.Type
                                 (NativeType.TFun(Types.int8Type, NativeType.TFun(Types.int8Type, Types.boolType))) ->
                        match operation.Kind, tagRead.Kind, expected.Kind with
                        | SemanticKind.Intrinsic info, SemanticKind.DUGetTag(subject, unionType),
                          SemanticKind.Literal(NativeLiteral.Int(value, NTUKind.NTUint(NTUWidth.Fixed 8)))
                            when info.Module = IntrinsicModule.Operators && info.Operation = "op_Equality" &&
                                 info.Category = IntrinsicCategory.Comparison && (value = 0L || value = 1L) ->
                            match nodes.TryFind subject, resultPayloads unionType with
                            | Some source, Some _ when sameType source.Type unionType && agrees source ->
                                Some
                                    ({ Choice = choice.Id; Guard = guard; Operator = operator
                                       Comparison = CallableBranchComparison.Equal
                                       TagRead = tag; Subject = subject; Literal = literal; ExpectedTag = int value
                                       UnionType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType unionType
                                       TrueArm = yes; FalseArm = no; SelectedArm = yes
                                       Alternatives = []; Participants = [] }, unionType)
                            | _ -> None
                        | _ -> None
                    | _ -> None
                | _ -> None
            | _ -> None
        | _ -> None
    let guards =
        nodes |> Map.toList |> List.choose (fun (id, node) -> readGuard node |> Option.map (fun guard -> id, guard)) |> Map.ofList
    let combine statuses =
        if List.contains MalformedTransport statuses then MalformedTransport
        elif List.contains UnsupportedTransport statuses then UnsupportedTransport
        elif List.contains PendingTransport statuses then PendingTransport
        else ValidTransport
    // This is deliberately smaller than the general origin analysis. A final
    // branch may refine only paths whose current source transport is checked
    // here; unsupported paths retain the previous conservative join.
    let rec transport read seen expected id =
        if Set.contains id seen then UnsupportedTransport
        else
            let seen = Set.add id seen
            match nodes.TryFind id with
            | None -> MalformedTransport
            | Some node when not (agrees node) -> MalformedTransport
            | Some node when not (sameType node.Type expected) ->
                match applySubst node.Type, applySubst expected with
                | NativeType.TForall _, _ | _, NativeType.TForall _ -> UnsupportedTransport
                | _ -> MalformedTransport
            | Some node ->
                let follow child = transport read seen expected child
                match node.Kind with
                | SemanticKind.Binding(_, false, _, _) -> follow node.Children.Head
                | SemanticKind.VarRef(_, Some definition) -> follow definition
                | SemanticKind.TypeAnnotation(value, declared) ->
                    if sameType declared expected then follow value else MalformedTransport
                | SemanticKind.EagerExpr value ->
                    if ExplicitDemand.operand graph id = Some value then follow value else MalformedTransport
                | SemanticKind.Sequential values ->
                    values |> List.tryLast |> Option.map follow |> Option.defaultValue MalformedTransport
                | SemanticKind.IfThenElse(guard, yes, Some no) ->
                    match nodes.TryFind guard with
                    | Some guard when sameType guard.Type Types.boolType && agrees guard -> combine [follow yes; follow no]
                    | _ -> MalformedTransport
                | SemanticKind.DUConstruct _ | SemanticKind.UnionCase _ ->
                    if (caseAlternative expected (id, 0)).IsSome then ValidTransport else MalformedTransport
                | SemanticKind.Lambda(parameters, body, [], _, _) ->
                    match nodes.TryFind body with
                    | Some body ->
                        let signature = List.foldBack (fun (_, ty, _) rest -> NativeType.TFun(ty, rest)) parameters body.Type
                        if not (sameType signature node.Type) then MalformedTransport
                        else
                            parameters
                            |> List.map (fun (_, ty, formal) ->
                                match nodes.TryFind formal with
                                | Some ({ Kind = SemanticKind.PatternBinding _ } as value) when agrees value && sameType ty value.Type -> ValidTransport
                                | _ -> MalformedTransport)
                            |> combine
                    | None -> MalformedTransport
                | SemanticKind.Application(callee, arguments) ->
                    match nodes.TryFind callee with
                    | None -> MalformedTransport
                    | Some target ->
                        let boundary = transport read seen target.Type callee
                        let origins: Set<Origin> = read callee
                        // A supported factory can be discovered on a later
                        // origin pass. Joining both arms now would survive
                        // even after final evidence selects only one arm.
                        if origins.IsEmpty then combine [boundary; PendingTransport]
                        else
                            let returns =
                                origins |> Set.toList |> List.map (fun (origin, offset) ->
                                    match nodes.TryFind origin with
                                    | Some { Kind = SemanticKind.Lambda(parameters, body, [], _, _) }
                                        when offset = 0 && parameters.Length = arguments.Length ->
                                        let actuals =
                                            List.zip parameters arguments
                                            |> List.map (fun ((_, ty, _), actual) ->
                                                match nodes.TryFind actual with
                                                | Some value when sameType value.Type ty && agrees value -> ValidTransport
                                                | _ -> MalformedTransport)
                                        combine (follow body :: actuals)
                                    | _ -> UnsupportedTransport)
                            combine (boundary :: returns)
                | _ -> UnsupportedTransport
    let decide read (guard: CallableBranchObservation, unionType) =
        let origins: Set<Origin> = read guard.Subject
        if origins.IsEmpty then AwaitOrigins
        else
            let alternatives = origins |> Set.toList |> List.map (caseAlternative unionType)
            if List.exists Option.isNone alternatives then BothArms
            else
                let alternatives = List.choose id alternatives
                match transport read Set.empty unionType guard.Subject,
                      alternatives |> List.map (fun alternative -> alternative.Tag = guard.ExpectedTag) |> List.distinct with
                | MalformedTransport, _ -> OpaqueArms guard.Choice
                | PendingTransport, _ -> AwaitOrigins
                | ValidTransport, [selected] ->
                    let selectedArm = if selected then guard.TrueArm else guard.FalseArm
                    let participant role ordinal group node : Participant =
                        { Node = node; Role = role; Ordinal = ordinal; Group = group }
                    let participants =
                        [ participant ParticipantRole.BranchChoice 0 guard.Choice guard.Choice
                          participant ParticipantRole.BranchGuard 0 guard.Choice guard.Guard
                          participant ParticipantRole.BranchOperator 0 guard.Choice guard.Operator
                          participant ParticipantRole.BranchTagRead 0 guard.Choice guard.TagRead
                          participant ParticipantRole.BranchSubject 0 guard.Choice guard.Subject
                          participant ParticipantRole.BranchLiteral 0 guard.Choice guard.Literal
                          participant ParticipantRole.BranchTrueArm 0 guard.Choice guard.TrueArm
                          participant ParticipantRole.BranchFalseArm 0 guard.Choice guard.FalseArm
                          participant ParticipantRole.BranchSelectedArm 0 guard.Choice selectedArm ]
                        @ (alternatives
                           |> List.mapi (fun ordinal alternative ->
                               participant ParticipantRole.BranchConstructor ordinal guard.Choice alternative.Constructor
                               :: (alternative.Payloads
                                   |> List.mapi (fun position payload ->
                                       participant ParticipantRole.BranchPayload position alternative.Constructor payload)))
                           |> List.concat)
                    OneArm
                        { guard with
                            SelectedArm = selectedArm
                            Alternatives = alternatives; Participants = participants }
                | _ -> BothArms
    guards, decide, caseAlternative, agrees

let private isFunctionValue (node: SemanticNode) =
    [ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
    |> List.exists (fun key -> node.Metadata.TryFind key = Some (MetadataValue.Bool true))

/// Synthetic parameter tails belong to one declaration; a new function expression
/// in its body is a returned value, including a unit-parameter function.
let rec private shape (nodes: Map<NodeId, SemanticNode>) id =
    match nodes.TryFind id with
    | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } ->
        match nodes.TryFind body with
        | Some ({ Kind = SemanticKind.Lambda _ } as inner) when not (isFunctionValue inner) ->
            shape nodes body |> Option.map (fun (rest, result) -> parameters @ rest, result)
        | _ -> Some (parameters, body)
    | _ -> None

let private afterArguments count ty =
    let rec drop remaining ty =
        if remaining = 0 then Some ty
        else
            match applySubst ty with
            | NativeType.TFun (_, result) -> drop (remaining - 1) result
            | _ -> None
    drop count ty

let private nativeOperation (nodes: Map<NodeId, SemanticNode>) callee =
    let rec follow seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = operation } } -> Some operation
        | Some { Kind = SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _) } -> follow seen value
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> follow seen value
        | _ -> None
    follow Set.empty callee

/// A finite origin analysis over declaration, parameter, result and aggregate
/// edges. Unknown callable leaves remain explicit origins, preventing a known
/// candidate from silently standing in for an opaque alternative.
let private analyze branchSelections (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let sourceGuards, sourceDecision, caseAlternative, agrees = branchReaders graph nodes
    let guards, decideGuard =
        if branchSelections then sourceGuards, sourceDecision
        else Map.empty, (fun _ _ -> BothArms)
    let facts = Dictionary<NodeId, Set<Origin>>()
    let fields = Dictionary<NodeId * string, Set<Origin>>()
    let read id = match facts.TryGetValue id with true, values -> values | _ -> Set.empty
    let mutable changed = false
    let add id values =
        let old = read id
        let combined = Set.union old values
        if old <> combined then
            facts[id] <- combined
            changed <- true
    let union ids = ids |> Seq.map read |> Seq.fold Set.union Set.empty
    let shapes =
        nodes |> Map.toSeq |> Seq.choose (fun (id, _) -> shape nodes id |> Option.map (fun value -> id, value)) |> Map.ofSeq
    let captures =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources, nodes.TryFind edge.Target with
            | EdgeClass.Provenance, EdgeRole.EnvironmentCapture false, [owner; slot; value],
              Some { Kind = SemanticKind.EnvironmentCreate(actual, initializers) }
                when owner = actual && List.contains (slot, value) initializers -> Some((owner, slot), value)
            | _ -> None)
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ rows -> List.map snd rows)
    let environments =
      graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Sources with
        | EdgeClass.Provenance, EdgeRole.EnvironmentFormal, [owner; implementation] ->
            match nodes.TryFind owner, nodes.TryFind implementation with
            | Some { Kind = SemanticKind.ClosureValue(actual, environment) }, Some { Kind = SemanticKind.Lambda(parameters, _, _, _, _) }
                when actual = implementation && (parameters |> List.exists (fun (_, _, formal) -> formal = edge.Target)) ->
                match nodes.TryFind environment with
                | Some { Kind = SemanticKind.EnvironmentCreate(expected, _) } when expected = owner -> Some(edge.Target, (owner, implementation))
                | _ -> None
            | _ -> None
        | _ -> None) |> Map.ofList
    let rec environmentOwner seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match environments.TryFind id with
        | Some(owner, _) -> Some owner
        | None ->
            match nodes.TryFind id with
            | Some { Kind = SemanticKind.EnvironmentCreate(owner, _) } -> Some owner
            | Some { Kind = SemanticKind.ClosureValue _ } -> Some id
            | Some { Kind = SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _)
                           | SemanticKind.EnvironmentReference value } -> environmentOwner seen value
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> environmentOwner seen value
            | Some { Kind = SemanticKind.EagerExpr value } when ExplicitDemand.operand graph id = Some value -> environmentOwner seen value
            | Some { Kind = SemanticKind.Sequential values } -> List.tryLast values |> Option.bind (environmentOwner seen)
            | _ -> None
    let inputs = Dictionary<NodeId, Set<NodeId * NodeId>>()
    let supply call parameter argument =
        let old = match inputs.TryGetValue parameter with true, values -> values | _ -> Set.empty
        inputs[parameter] <- Set.add (call, argument) old

    for KeyValue(id, node) in nodes do
        match node.Kind with
        | SemanticKind.Lambda _ | SemanticKind.RecordExpr _ | SemanticKind.TupleExpr _
        | SemanticKind.DUConstruct _ | SemanticKind.UnionCase _ -> add id (Set.singleton (id, 0))
        | SemanticKind.Intrinsic _ | SemanticKind.PlatformBinding _ ->
            match applySubst node.Type with
            | NativeType.TFun _ -> add id (Set.singleton (id, 0))
            | _ -> ()
        | _ -> ()

    let rec invoke call seen (origins: Set<Origin>) (arguments: NodeId list) =
        origins |> Set.fold (fun results (id, offset) ->
            let key = id, offset, arguments.Length
            if isEmptyOrigin (id, offset) then Set.add (id, offset) results
            elif Set.contains key seen then results
            else
                match shapes.TryFind id with
                | Some (parameters, body) when offset >= 0 ->
                    let total = max 1 parameters.Length
                    let available = total - offset
                    let supplied = min available arguments.Length
                    parameters |> List.skip (min offset parameters.Length) |> List.truncate supplied
                    |> List.iteri (fun index (_, _, parameter) ->
                        supply call parameter arguments[index]
                        add parameter (read arguments[index]))
                    let produced =
                        if supplied < available then Set.singleton (id, offset + supplied)
                        elif arguments.Length = supplied then read body
                        else invoke call (Set.add key seen) (read body) (List.skip supplied arguments)
                    Set.union results produced
                | _ -> Set.add (id, -1) results) Set.empty

    changed <- true
    let mutable seedUnknown = true
    while changed || seedUnknown do
        if not changed then
            // A callable or aggregate with no resident producing edge is
            // opaque. Its projections must remain in later joins beside any
            // known candidate. Proved-empty alternatives carry their marker
            // through this pass instead of becoming opaque producing edges.
            seedUnknown <- false
            for KeyValue(id, node) in nodes do
                match applySubst node.Type with
                | NativeType.TFun _ | NativeType.TApp _ | NativeType.TTuple _
                | NativeType.TAnon _ | NativeType.TUnion _ when Set.isEmpty (read id) ->
                    add id (Set.singleton (id, -1))
                | _ -> ()
        changed <- false
        for KeyValue(id, node) in nodes do
            let values =
                match node.Kind with
                | SemanticKind.Binding _ -> union node.Children
                | SemanticKind.VarRef (_, Some definition) -> read definition
                | SemanticKind.TypeAnnotation (value, _) -> read value
                | SemanticKind.EagerExpr value when ExplicitDemand.operand graph id = Some value -> read value
                | SemanticKind.Sequential expressions -> expressions |> List.tryLast |> Option.map read |> Option.defaultValue Set.empty
                | SemanticKind.IfThenElse (_, yes, no) ->
                    match guards.TryFind id with
                    | Some guard ->
                        match decideGuard read guard with
                        | AwaitOrigins -> Set.empty
                        | OneArm observation -> read observation.SelectedArm
                        | BothArms -> union (yes :: Option.toList no)
                        | OpaqueArms origin -> Set.add (origin, -1) (union (yes :: Option.toList no))
                    | None -> union (yes :: Option.toList no)
                | SemanticKind.Match (_, cases) -> union (cases |> List.map (fun arm -> arm.Body))
                | SemanticKind.CaseElimination (_, arms) -> union (arms |> List.map (fun arm -> arm.Body))
                | SemanticKind.Application (callee, arguments) ->
                    match nativeOperation nodes callee, arguments with
                    | Some "ofFunction", [handler] -> read handler
                    | Some "invoke", pointer :: actuals -> invoke id Set.empty (read pointer) actuals
                    | _ -> invoke id Set.empty (read callee) arguments
                | SemanticKind.EnvironmentRead(environment, slot) ->
                    environmentOwner Set.empty environment
                    |> Option.bind (fun owner -> captures.TryFind (owner, slot))
                    |> Option.map union |> Option.defaultValue Set.empty
                | SemanticKind.ClosureValue(implementation, _) ->
                    // The pair closes over its explicitly declared environment
                    // formal. Rewritten direct calls still supply that formal.
                    let formal = graph.Edges |> List.tryPick (fun edge ->
                        if edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.EnvironmentFormal
                           && edge.Sources = [id; implementation] then Some edge.Target else None)
                    match shapes.TryFind implementation, formal with
                    | Some ((_, _, first) :: _, _), Some actual when first = actual -> Set.singleton(implementation, 1)
                    | _ -> Set.empty
                | SemanticKind.Set (target, value) ->
                    match nodes.TryFind target with
                    | Some { Kind = SemanticKind.VarRef (_, Some definition) } -> add definition (read value)
                    | Some { Kind = SemanticKind.Binding _ } -> add target (read value)
                    | _ -> ()
                    Set.empty
                | SemanticKind.DUEliminate (value, tag, name, payloadType) ->
                    read value |> Set.fold (fun values ((origin, _) as alternative) ->
                        let payload =
                            let cases = nodes.TryFind value |> Option.bind (fun source -> casePayloads source.Type)
                            match isEmptyOrigin alternative, cases with
                            | true, _ -> Set.singleton alternative
                            | false, Some cases ->
                                let declared = if tag >= 0 && tag < cases.Length then List.tryItem tag cases else None
                                match declared, caseAlternative nodes[value].Type alternative with
                                | Some(caseName, Some caseType), Some constructor
                                    when agrees node && name = caseName && sameType payloadType caseType && sameType node.Type caseType ->
                                    if constructor.Tag = tag then union constructor.Payloads
                                    else Set.singleton (emptyOrigin id)
                                // An invalid constructor does not disappear just
                                // because its advertised tag differs from this arm.
                                | _ -> Set.singleton (origin, -1)
                            | false, None ->
                                match nodes.TryFind origin with
                                | Some { Kind = SemanticKind.DUConstruct (_, actual, payload, _) }
                                | Some { Kind = SemanticKind.UnionCase (_, actual, payload) } ->
                                    if actual = tag then payload |> Option.map read |> Option.defaultValue Set.empty
                                    else Set.empty
                                | _ -> Set.singleton (origin, -1)
                        Set.union values payload) Set.empty
                | SemanticKind.TupleGet (value, index) ->
                    read value |> Set.fold (fun values ((origin, _) as alternative) ->
                        let element =
                            match isEmptyOrigin alternative, nodes.TryFind origin with
                            | true, _ -> Set.singleton alternative
                            | false, Some { Kind = SemanticKind.TupleExpr elements } ->
                                elements |> List.tryItem index |> Option.map read |> Option.defaultValue Set.empty
                            | _ -> Set.singleton (origin, -1)
                        Set.union values element) Set.empty
                | SemanticKind.FieldGet (value, name) ->
                    read value |> Set.fold (fun values ((origin, _) as alternative) ->
                        let initial =
                            match isEmptyOrigin alternative, nodes.TryFind origin with
                            | true, _ -> Set.singleton alternative
                            | false, Some { Kind = SemanticKind.RecordExpr (members, _) } -> members |> List.tryPick (fun (field, value) -> if field = name then Some (read value) else None) |> Option.defaultValue (Set.singleton (origin, -1))
                            | _ -> Set.singleton (origin, -1)
                        let assigned = match fields.TryGetValue ((origin, name)) with true, values -> values | _ -> Set.empty
                        Set.union values (Set.union initial assigned)) Set.empty
                | SemanticKind.FieldSet (value, name, assigned) ->
                    for origin, _ in presentOrigins (read value) do
                        let old = match fields.TryGetValue ((origin, name)) with true, values -> values | _ -> Set.empty
                        let combined = Set.union old (read assigned)
                        if old <> combined then
                            fields[(origin, name)] <- combined
                            changed <- true
                    Set.empty
                | _ -> Set.empty
            add id values

    // Only the final fixed point can author a branch observation. Transient
    // one-arm discoveries are not retained when later/opaque origins arrive.
    let branches =
        guards
        |> Map.toList
        |> List.choose (fun (id, guard) ->
            match decideGuard read guard with OneArm observation -> Some(id, observation) | _ -> None)
        |> Map.ofList
    nodes, shapes, (facts |> Seq.map (fun pair -> pair.Key, pair.Value) |> Map.ofSeq),
        (inputs |> Seq.map (fun pair -> pair.Key, Set.toList pair.Value) |> Map.ofSeq), branches

/// Share actual value-flow evidence with range and sequence analyses. Opaque
/// alternatives remain visible even when a known implementation also reaches
/// the call. This does not establish environment residence or native admission.
let private resolveWith branchSelections (graph: SemanticGraph) : Resolution =
    let nodes, shapes, facts, inputs, branches = analyze branchSelections graph
    let read id = facts.TryFind id |> Option.defaultValue Set.empty |> presentOrigins
    let provedEmpty id = facts.TryFind id |> Option.exists (fun origins -> not origins.IsEmpty && Set.forall isEmptyOrigin origins)
    let nativeCalls =
        nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with
            | SemanticKind.Application(callee, pointer :: arguments) when nativeOperation nodes callee = Some "invoke" ->
                let origins = read pointer
                let targets =
                    origins |> Set.toList |> List.choose (fun (lambda, offset) ->
                        match shapes.TryFind lambda with
                        | Some (parameters, body) when offset = 0 && parameters.Length = arguments.Length ->
                            Some { Lambda = lambda; Parameters = parameters; Arguments = arguments; Body = body }
                        | _ -> None)
                let complete =
                    not origins.IsEmpty &&
                    (origins |> Set.forall (fun (lambda, offset) ->
                        match shapes.TryFind lambda with
                        | Some (parameters, _) when offset = 0 -> parameters.Length = arguments.Length
                        | _ -> false))
                Some(id, { Targets = targets; Unknown = not complete && not (provedEmpty pointer); Complete = complete })
            | _ -> None)
        |> Map.ofList
    let calls = nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Application(callee, arguments) ->
            let origins = read callee
            let targets = origins |> Set.toList |> List.choose (fun (lambda, offset) ->
                match shapes.TryFind lambda with
                | Some (parameters, body) when offset >= 0 && max 1 parameters.Length - offset = arguments.Length ->
                    Some { Lambda = lambda; Parameters = parameters |> List.skip (min offset parameters.Length)
                           Arguments = arguments; Body = body }
                | _ -> None)
            let unknown = (origins.IsEmpty && not (provedEmpty callee)) || (origins |> Set.exists (fun (lambda, offset) ->
                match shapes.TryFind lambda with
                | Some (parameters, _) when offset >= 0 -> arguments.Length > max 1 parameters.Length - offset
                | _ -> true))
            let complete = not origins.IsEmpty && (origins |> Set.forall (fun (lambda, offset) ->
                match shapes.TryFind lambda with
                | Some (parameters, _) when offset >= 0 -> max 1 parameters.Length - offset = arguments.Length
                | _ -> false))
            Some(id, { Targets = targets; Unknown = unknown; Complete = complete })
        | _ -> None) |> Map.ofList
    let lambdas = facts |> Map.toList |> List.choose (fun (id, origins) ->
        match origins |> presentOrigins |> Set.toList with
        | [lambda, 0] when shapes.ContainsKey lambda -> Some(id, lambda)
        | _ -> None) |> Map.ofList
    let boundaries =
        nodes
        |> Map.toList
        |> List.choose (fun (id, node) ->
            match node.Kind with
            | SemanticKind.Application(callee, _) ->
                let origins = read callee
                let targets, unknown =
                    origins |> Set.fold (fun (targets, unknown) (lambda, offset) ->
                        match shapes.TryFind lambda with
                        | Some (parameters, _) when offset >= 0 && offset < (max 1 parameters.Length) ->
                            let target =
                                { Lambda = lambda; Parameters = parameters; Offset = offset
                                  Remaining = max 1 parameters.Length - offset }
                            target :: targets, unknown
                        | _ -> targets, Set.add lambda unknown) ([], Set.empty)
                let unknown = if origins.IsEmpty && not (provedEmpty callee) then Set.singleton callee else unknown
                Some(id, { Callee = callee; Targets = List.rev targets; UnknownOrigins = unknown })
            | _ -> None)
        |> Map.ofList
    { Calls = calls; NativeCalls = nativeCalls; ParameterInputs = inputs; Lambdas = lambdas; FirstBoundaries = boundaries; Branches = branches }

/// Early source analyses retain conservative joins. They do not yet own the
/// transfer of branch premises through their subsequent rewrites.
let resolve graph = resolveWith false graph

/// Opt-in final callable reading. The owning Baker settlement must retain and
/// validate its whole-revision branch authority before publication.
let resolveCallableBranches graph = resolveWith true graph

let resolveCalls graph = (resolve graph).Calls
let knownLambdas graph = (resolve graph).Lambdas

let applicationStages (graph: SemanticGraph) : Map<NodeId, Stage list> =
    let nodes, shapes, facts, _, _ = analyze false graph
    let read id = facts.TryFind id |> Option.defaultValue Set.empty |> presentOrigins

    let boundary origins =
        if Set.isEmpty origins then None
        else
            let counts = origins |> Set.toList |> List.map (fun (id, offset) ->
                if offset < 0 then None
                else shapes.TryFind id |> Option.map (fun (parameters, _) -> max 1 parameters.Length - offset))
            match List.distinct counts with
            | [Some count] when count > 0 -> Some count
            | _ -> None
    let returned origins =
        origins |> Set.fold (fun values (id, _) ->
            match shapes.TryFind id with
            | Some (_, body) -> Set.union values (read body)
            | None -> values) Set.empty
    let rec stages origins ty (arguments: NodeId list) =
        match boundary origins with
        | Some count when arguments.Length >= count ->
            afterArguments count ty |> Option.bind (fun resultType ->
                let stage = { Arguments = List.take count arguments; ResultType = resultType }
                if arguments.Length = count then Some [stage]
                else stages (returned origins) resultType (List.skip count arguments) |> Option.map (fun rest -> stage :: rest))
        | _ -> None
    nodes |> Map.toSeq |> Seq.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.Application (callee, arguments) ->
            stages (read callee) nodes[callee].Type arguments
            |> Option.bind (fun plan -> if plan.Length > 1 then Some (id, plan) else None)
        | _ -> None) |> Map.ofSeq

// SPDX-License-Identifier: MIT
/// Current scalar inputs after continuation realization. Retired source cuts
/// retain identities, while the numeric solver reads actual generated values.
/// Storage escape/write authority remains the shared CallableIngress census.
module Clef.Compiler.PSGSaturation.SemanticGraph.ContinuationCurrentInputs

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Incidence = Clef.Compiler.Baker.Ingredients.Closures

type Cut = {
    Yield: NodeId
    Payload: NodeId
    Writer: NodeId
    Value: NodeId
    State: int
    Action: NodeId
}
type Protocol = {
    Owner: NodeId
    Generator: NodeId
    Formal: NodeId
    StateSlot: NodeId
    CurrentSlot: NodeId option
    InitialEntry: NodeId
    Cuts: Cut list
    StateWrites: (NodeId * NodeId) list
    Participants: Set<NodeId>
}

let private single = function [value] -> Some value | _ -> None
let private sameType left right =
    Clef.Compiler.NativeTypedTree.TypeIdentities.ofType left =
        Clef.Compiler.NativeTypedTree.TypeIdentities.ofType right

let forOwner (graph: SemanticGraph) owner : Protocol option =
    let live id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
    let ownerRows role = graph.Edges |> List.filter (fun edge ->
        role edge.Role && List.tryHead edge.Sources = Some owner)
    let rows role target = graph.Edges |> List.filter (fun edge -> edge.Role = role && edge.Target = target)
    let suspension sources (edge: Hyperedge) =
        edge.Class = EdgeClass.Suspension && edge.Ordinal = 0 && edge.Sources = sources
    match live owner with
    | Some { Kind = SemanticKind.SeqExpr(generator, _); Type = NativeType.TSeq element } ->
        match live generator with
        | Some { Kind = SemanticKind.Lambda([_, environmentType, formal], body, [], _, LambdaContext.SeqGenerator) }
            when sameType environmentType (NativeType.TSeqEnumerator element) ->
            let rec descend seen pending =
                match pending with
                | [] -> Some seen
                | id :: rest when Set.contains id seen -> descend seen rest
                | id :: rest ->
                    match live id with
                    | None -> None
                    | Some { Kind = SemanticKind.Lambda _ } -> descend (Set.add id seen) rest
                    | Some node ->
                        let children = Incidence.structuralIncidence node |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                        let childShape =
                            match node.Kind with
                            | SemanticKind.Binding _ -> node.Children.Length = 1
                            // Kind-derived edges own operand roles and order.
                            // Their enumeration order can differ from Children
                            // (dispatch lists its default before its cases).
                            | _ -> List.sort node.Children = List.sort children
                        if not childShape then None else descend (Set.add id seen) (children @ rest)
            match descend Set.empty [body] with
            | None -> None
            | Some scope ->
                let rec environment seen id =
                    if Set.contains id seen then None
                    else
                        match live id with
                        | Some node when sameType node.Type environmentType ->
                            if id = formal then Some(Set.singleton id)
                            else
                                let seen = Set.add id seen
                                let follow value = environment seen value |> Option.map (Set.add id)
                                match node.Kind with
                                | SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _) -> follow value
                                | SemanticKind.Binding(_, false, _, _ ) when node.Children.Length = 1 -> follow node.Children.Head
                                | SemanticKind.EagerExpr value when ExplicitDemand.operand graph id = Some value -> follow value
                                | _ -> None
                        | _ -> None
                let literal id =
                    match live id with
                    | Some { Kind = SemanticKind.Literal(NativeLiteral.Int(value, _)) } -> Some(bigint value)
                    | Some { Kind = SemanticKind.Literal(NativeLiteral.UInt(value, _)) } -> Some(bigint value)
                    | _ -> None
                let resumes = ownerRows (function EdgeRole.SuspensionResume _ -> true | _ -> false)
                let completed = ownerRows ((=) EdgeRole.SuspensionCompleted)
                let initial = resumes |> List.filter (fun edge -> edge.Role = EdgeRole.SuspensionResume 0) |> single
                match initial, completed |> single with
                | Some initial, Some completed
                    when suspension [owner; generator] initial && scope.Contains initial.Target ->
                    match completed.Sources with
                    | [actualOwner; actualGenerator; stateSlot]
                        when actualOwner = owner && actualGenerator = generator && suspension completed.Sources completed && scope.Contains completed.Target ->
                        let entryDispatches = scope |> Set.toList |> List.choose (fun id ->
                            match live id with
                            | Some { Kind = SemanticKind.ContinuationDispatch(selector, cases, fallback) } when fallback = completed.Target ->
                                match live selector with
                                | Some { Kind = SemanticKind.FrameRead(frame, slot) }
                                    when slot = stateSlot && (environment Set.empty frame).IsSome -> Some(selector, cases)
                                | _ -> None
                            | _ -> None)
                        let cutRows = ownerRows (function EdgeRole.SuspensionCut _ -> true | _ -> false)
                        let delimiters = ownerRows ((=) EdgeRole.Delimiter)
                        let sourceCuts = cutRows |> List.map (fun edge ->
                            match edge.Role, edge.Sources, graph.Nodes.TryFind edge.Target with
                            | EdgeRole.SuspensionCut state, [actualOwner; actualGenerator; payload],
                              Some { Kind = SemanticKind.Yield actual }
                                when actualOwner = owner && actualGenerator = generator && actual = payload && state > 0 &&
                                     suspension edge.Sources edge &&
                                     (graph.Nodes.TryFind payload |> Option.exists (fun value -> sameType value.Type element)) ->
                                match delimiters |> List.filter (fun row -> row.Target = edge.Target) with
                                | [delimiter] when suspension [owner; generator] delimiter -> Some(edge.Target, payload, state)
                                | _ -> None
                            | _ -> None)
                        let cuts = List.choose id sourceCuts
                        let states = cuts |> List.map (fun (_, _, state) -> state)
                        let maximum = states |> List.fold max 0 |> bigint
                        let obligations = System.Collections.Generic.HashSet<NodeId>()
                        let obligation value participants =
                            let candidates = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Sources = participants)
                            match candidates with
                            | [{ Class = EdgeClass.Obligation; Ordinal = 0; Target = target }]
                                when (rows EdgeRole.Constrains target).Length = 1 ->
                                match graph.Nodes.TryFind target with
                                | Some { Kind = SemanticKind.Obligation info }
                                    when info.Kind = "continuation-state-range" && info.Logic = "QF_LIA" &&
                                         info.Body = ObligationBody.IntegerLiteralRange(value, -1I, maximum) ->
                                    obligations.Add target |> ignore
                                    true
                                | _ -> false
                            | _ -> false
                        let validResumes =
                            resumes |> List.forall (fun edge ->
                                match edge.Role with
                                | EdgeRole.SuspensionResume 0 -> suspension [owner; generator] edge
                                | EdgeRole.SuspensionResume state ->
                                    cuts |> List.exists (fun (sourceYield, _, expected) ->
                                        expected = state && suspension [owner; generator; sourceYield] edge && scope.Contains edge.Target)
                                | _ -> false)
                        let actionRows = ownerRows (function EdgeRole.SuspensionResumeAction _ -> true | _ -> false)
                        let actionDispatches = scope |> Set.toList |> List.choose (fun id ->
                            match live id with
                            | Some { Kind = SemanticKind.ContinuationDispatch(selector, cases, _) } ->
                                match live selector with
                                | Some { Kind = SemanticKind.VarRef _ } -> Some cases
                                | _ -> None
                            | _ -> None)
                        let validActions = actionRows |> List.forall (fun edge ->
                            match edge.Role with
                            | EdgeRole.SuspensionResumeAction state ->
                                match resumes |> List.filter (fun row -> row.Role = EdgeRole.SuspensionResume state) with
                                | [resume] ->
                                    let targetMatches =
                                        match live resume.Target, actionDispatches with
                                        | Some { Kind = SemanticKind.Sequential [setEntry; _] }, [cases] ->
                                            match live setEntry with
                                            | Some { Kind = SemanticKind.Set(_, value) } ->
                                                literal value |> Option.exists (fun label ->
                                                    cases |> List.exists (fun (actual, action) -> bigint actual = label && action = edge.Target))
                                            | _ -> false
                                        | _ -> false
                                    suspension ([owner; generator; resume.Target] @ (resume.Sources |> List.skip 2)) edge &&
                                    scope.Contains edge.Target && targetMatches
                                | _ -> false
                            | _ -> false)
                        let writes = scope |> Set.toList |> List.choose (fun id ->
                            match live id with
                            | Some { Kind = SemanticKind.FrameWrite(frame, slot, value); Type = ty }
                                when ty = Types.unitType && (environment Set.empty frame).IsSome -> Some(id, slot, value)
                            | _ -> None)
                        let stateWrites = writes |> List.choose (fun (writer, slot, value) -> if slot = stateSlot then Some(writer, value) else None)
                        let currentCuts = cuts |> List.map (fun (sourceYield, payload, state) ->
                            let writers = writes |> List.filter (fun (writer, _, _) ->
                                match rows EdgeRole.ContinuationValue writer with
                                | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [source] }] -> source = sourceYield
                                | _ -> false)
                            match writers with
                            | [writer, currentSlot, value] when currentSlot <> stateSlot ->
                                let typed = live value |> Option.exists (fun actual -> sameType actual.Type element)
                                let identity =
                                    if value = payload then true
                                    else
                                        match rows EdgeRole.ContinuationValue value with
                                        | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [source] }] -> source = payload
                                        | _ -> false
                                let actions = scope |> Set.toList |> List.choose (fun action ->
                                    match live action with
                                    | Some { Kind = SemanticKind.Sequential [actualWriter; stateWriter; _] } when actualWriter = writer ->
                                        stateWrites |> List.tryPick (fun (candidate, stateValue) ->
                                            if candidate = stateWriter && literal stateValue = Some(bigint state) then Some action else None)
                                    | _ -> None)
                                match actions with
                                | [action] when typed && identity -> Some(currentSlot, { Yield = sourceYield; Payload = payload; Writer = writer; Value = value; State = state; Action = action })
                                | _ -> None
                            | _ -> None)
                        let currentCuts = List.choose id currentCuts
                        let currentSlots = currentCuts |> List.map fst |> List.distinct
                        let resumeMap = resumes |> List.choose (fun edge ->
                            match edge.Role with EdgeRole.SuspensionResume state -> Some(state, edge.Target) | _ -> None) |> Map.ofList
                        let entryValid =
                            match entryDispatches with
                            | [_, cases] -> cases.Length = resumes.Length && Map.ofList cases = resumeMap
                            | _ -> false
                        let stateValid =
                            stateWrites.Length >= cuts.Length + 1 &&
                            (stateWrites |> List.forall (fun (writer, value) ->
                                (graph.Nodes.TryFind stateSlot |> Option.exists (fun slot ->
                                    match slot.Kind with
                                    | SemanticKind.PatternBinding _ -> live value |> Option.exists (fun actual -> sameType slot.Type actual.Type)
                                    | _ -> false)) &&
                                (literal value |> Option.exists (fun number ->
                                    (number = -1I || (states |> List.exists (fun state -> bigint state = number))) &&
                                    obligation number [owner; generator; stateSlot; writer; value]))))
                        let completionValid =
                            match actionDispatches with
                            | [cases] -> cases |> List.exists (fun (_, action) ->
                                match live action with
                                | Some { Kind = SemanticKind.Sequential [writer; _] } ->
                                    stateWrites |> List.exists (fun (actual, value) -> actual = writer && literal value = Some -1I)
                                | _ -> false)
                            | _ -> false
                        if cuts.Length <> sourceCuts.Length || cuts.Length <> delimiters.Length ||
                           (cuts |> List.map (fun (cut, _, _) -> cut) |> Set.ofList).Count <> cuts.Length ||
                           (Set.ofList states).Count <> states.Length || not validResumes ||
                           resumes.Length <> states.Length + 1 || not validActions || actionRows.Length <> resumes.Length ||
                           not entryValid || not stateValid || not completionValid || not (obligation 0I [owner; generator; stateSlot; initial.Target]) ||
                           currentCuts.Length <> cuts.Length then None
                        else
                            match currentSlots with
                            | [currentSlot] when graph.Nodes.TryFind currentSlot |> Option.exists (fun slot ->
                                match slot.Kind with SemanticKind.PatternBinding _ -> sameType slot.Type element | _ -> false) ->
                                let actual = writes |> List.choose (fun (writer, slot, value) -> if slot = currentSlot then Some(writer, value) else None) |> Set.ofList
                                let expected = currentCuts |> List.map (fun (_, cut) -> cut.Writer, cut.Value) |> Set.ofList
                                if actual <> expected || actual.Count <> cuts.Length then None else
                                let participants =
                                    scope |> Set.add owner |> Set.add generator |> Set.add formal |> Set.add stateSlot |> Set.add currentSlot
                                    |> Set.union (obligations |> Set.ofSeq)
                                    |> Set.union (cuts |> List.collect (fun (cut, payload, _) -> [cut; payload]) |> Set.ofList)
                                Some { Owner = owner; Generator = generator; Formal = formal; StateSlot = stateSlot; CurrentSlot = Some currentSlot
                                       InitialEntry = initial.Target; Cuts = List.map snd currentCuts; StateWrites = stateWrites; Participants = participants }
                            | [] when cuts.IsEmpty ->
                                let participants = scope |> Set.add owner |> Set.add generator |> Set.add formal |> Set.add stateSlot
                                                   |> Set.union (obligations |> Set.ofSeq)
                                Some { Owner = owner; Generator = generator; Formal = formal; StateSlot = stateSlot; CurrentSlot = None
                                       InitialEntry = initial.Target; Cuts = []; StateWrites = stateWrites; Participants = participants }
                            | _ -> None
                    | _ -> None
                | _ -> None
        | _ -> None
    | _ -> None

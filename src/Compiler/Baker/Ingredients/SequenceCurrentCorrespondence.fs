// SPDX-License-Identifier: MIT
/// Read a realized current operation through its exact guarded source prefix.
/// The finite PC graph checks a fresh successful pull in this activation; source
/// provenance alone cannot authorize a current moved ahead of that guard.
module Clef.Compiler.Baker.Ingredients.SequenceCurrentCorrespondence

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress
module Inputs = Clef.Compiler.PSGSaturation.SemanticGraph.ContinuationCurrentInputs
module Current = Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes

type Evidence = {
    Source: NodeId
    Current: NodeId
    Iterator: NodeId
    Participants: Set<NodeId>
}

[<RequireQualifiedAccess>]
type private Pull = Empty | Fresh | False | Guarded

let read (graph: SemanticGraph) (ingress: Ingress.Reading) : Evidence list =
    let lifted = graph.Edges |> List.filter (fun edge ->
        edge.Role = EdgeRole.IteratorCurrentAdmitted && edge.Sources.Length > 3)
    if lifted.IsEmpty then [] else
    let live id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
    let rows role target = graph.Edges |> List.filter (fun edge -> edge.Role = role && edge.Target = target)
    let originals = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ContinuationValue)
    let corresponds source actual = Ingress.tryCorrespondence ingress source actual
    let protocols =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.SeqExpr _ when node.IsReachable -> Inputs.forOwner graph node.Id
            | _ -> None) |> Seq.toList
    let descendants root =
        let rec visit seen = function
            | [] -> seen
            | id :: rest when Set.contains id seen -> visit seen rest
            | id :: rest ->
                match graph.Nodes.TryFind id with
                | None -> visit seen rest
                | Some node ->
                    let seen = Set.add id seen
                    let children =
                        match node.Kind with
                        | SemanticKind.Lambda _ | SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ -> []
                        | SemanticKind.VarRef(_, Some definition) -> [definition]
                        | _ -> Closures.structuralIncidence node |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                    visit seen (children @ rest)
        visit Set.empty [root]
    let literal id =
        match live id with
        | Some { Kind = SemanticKind.Literal(NativeLiteral.Int(value, _)) } -> Some(bigint value)
        | Some { Kind = SemanticKind.Literal(NativeLiteral.UInt(value, _)) } -> Some(bigint value)
        | _ -> None
    let operation operation id =
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Application(callee, [argument]); Children = children } when children = [callee; argument] ->
            match graph.Nodes.TryFind callee with
            | Some { Kind = SemanticKind.Intrinsic info } when info.Module = IntrinsicModule.SeqEnumerator && info.Operation = operation -> Some argument
            | _ -> None
        | _ -> None
    let guarded (protocol: Inputs.Protocol) guard current =
        let scope = protocol.Participants
        let dispatches = scope |> Set.toList |> List.choose (fun id ->
            match live id with
            | Some { Kind = SemanticKind.ContinuationDispatch(selector, cases, _) } ->
                match live selector with
                | Some { Kind = SemanticKind.VarRef(_, Some pc) } -> Some(pc, cases)
                | _ -> None
            | _ -> None)
        match dispatches with
        | [pc, cases] when not cases.IsEmpty && (cases |> List.map fst |> Set.ofList).Count = cases.Length ->
            let actions = Map.ofList cases
            let labels = actions.Keys |> Seq.map bigint |> Set.ofSeq
            let pcValid =
                match live pc with
                | Some { Kind = SemanticKind.Binding(_, true, false, None); Type = ty; Children = [initial] }
                    when ty = Types.nintType && (literal initial).IsSome ->
                    let references = graph.Nodes.Values |> Seq.filter (fun node ->
                        node.IsReachable &&
                        match node.Kind with SemanticKind.VarRef(_, Some source) -> source = pc | _ -> false) |> Seq.toList
                    let incidence = graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.collect Closures.structuralIncidence |> Seq.toList
                    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
                    let captured = graph.Nodes.Values |> Seq.exists (fun node ->
                        let captures =
                            match node.Kind with
                            | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures) | SemanticKind.LazyExpr(_, captures) -> captures
                            | _ -> []
                        node.IsReachable && (captures |> List.exists (fun capture ->
                            capture.SourceNodeId |> Option.exists (fun source -> source = pc || (references |> List.exists (fun node -> node.Id = source))))))
                    not captured && not references.IsEmpty && (references |> List.forall (fun reference ->
                        let uses = incidence |> List.filter (fun edge -> edge.Sources |> List.contains reference.Id)
                        let recorded = graph.Edges |> List.filter (fun edge ->
                            (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) && (edge.Sources |> List.contains reference.Id))
                        scope.Contains reference.Id && reference.Type = ty &&
                        (recorded |> List.forall (fun row -> uses |> List.exists (fun actual -> key actual = key row))) &&
                        match uses with
                        | [consumer] when scope.Contains consumer.Target ->
                            match live consumer.Target with
                            | Some { Kind = SemanticKind.Set(target, value) } -> target = reference.Id && (literal value |> Option.exists labels.Contains)
                            | Some { Kind = SemanticKind.ContinuationDispatch(selector, actual, _) } -> selector = reference.Id && actual = cases
                            | _ -> false
                        | _ -> false))
                | _ -> false
            let resumes = graph.Edges |> List.filter (fun edge ->
                match edge.Role with
                | EdgeRole.SuspensionResume _ -> edge.Class = EdgeClass.Suspension && List.tryHead edge.Sources = Some protocol.Owner
                | _ -> false)
            let entries = resumes |> List.map (fun resume ->
                match live resume.Target with
                | Some { Kind = SemanticKind.Sequential(setEntry :: _) } ->
                    match live setEntry with
                    | Some { Kind = SemanticKind.Set(target, value) } ->
                        match live target, literal value with
                        | Some { Kind = SemanticKind.VarRef(_, Some actual) }, Some label when actual = pc && labels.Contains label ->
                            cases |> List.tryPick (fun (key, _) -> if bigint key = label then Some key else None)
                        | _ -> None
                    | _ -> None
                | _ -> None)
            let pull, exhausted =
                match graph.Nodes.TryFind guard with
                | Some { Kind = SemanticKind.IfThenElse(_, pull, Some exhausted) } -> pull, Some exhausted
                | _ -> guard, None
            let actualPulls = originals |> List.choose (fun edge ->
                if edge.Sources = [pull] && scope.Contains edge.Target && (operation "moveNext" edge.Target).IsSome &&
                   (corresponds pull edge.Target).IsSome then Some edge.Target else None) |> Set.ofList
            let guardCondition id =
                match corresponds guard id with
                | Some _ -> true
                | None ->
                    // A conditional guard is copied from either the checked
                    // pull or its explicit false exhaustion branch. The shared
                    // storage census must account for every actual writer.
                    match exhausted, Ingress.tryStorageAccess ingress id with
                    | Some exhausted, Some access when access.Source = guard && not access.Inputs.IsEmpty ->
                        access.Inputs |> List.forall (fun (_, value) ->
                            (corresponds pull value).IsSome || (corresponds exhausted value).IsSome)
                    | _ -> false
            let falseGuard slot value =
                slot = guard && (exhausted |> Option.exists (fun source -> (corresponds source value).IsSome))
            let mutable observed = false
            let rec evaluate seen completed state jump id =
                // A block's produced value may also be a store operand. Reuse
                // that value only on this same action path; dispatching another
                // action starts a fresh evaluation, including loop iterations.
                if Set.contains id completed then Some [state, jump, completed]
                elif Set.contains id seen then None else
                match live id with
                | None -> None
                | Some node ->
                    let seen = Set.add id seen
                    let sequence ids =
                        ids |> List.fold (fun paths child ->
                            paths |> Option.bind (fun paths ->
                                paths |> List.fold (fun result (state, jump, completed) ->
                                    match result, evaluate seen completed state jump child with
                                    | Some before, Some after -> Some(before @ after)
                                    | _ -> None) (Some []))) (Some [state, jump, completed])
                    let result =
                      if id = current then
                        observed <- true
                        if state = Pull.Guarded then sequence node.Children |> Option.map (List.map (fun (_, jump, completed) -> Pull.Empty, jump, completed))
                        else None
                      elif actualPulls.Contains id then
                        sequence node.Children |> Option.map (List.map (fun (_, jump, completed) -> Pull.Fresh, jump, completed))
                      else
                        match node.Kind with
                        | SemanticKind.Lambda _ -> Some [state, jump, completed]
                        | SemanticKind.Sequential values -> sequence values
                        | SemanticKind.IfThenElse(condition, yes, no) ->
                            evaluate seen completed state jump condition |> Option.bind (fun paths ->
                                paths |> List.fold (fun result (state, jump, completed) ->
                                    let truth, falsity =
                                        if guardCondition condition then
                                            (if state = Pull.False then [] else [if state = Pull.Fresh then Pull.Guarded else Pull.Empty]), [Pull.Empty]
                                        else [state], [state]
                                    let branch states target =
                                        states |> List.fold (fun result state ->
                                            match result, target |> Option.map (evaluate seen completed state jump) |> Option.defaultValue (Some [state, jump, completed]) with
                                            | Some before, Some after -> Some(before @ after)
                                            | _ -> None) (Some [])
                                    match result, branch truth (Some yes), branch falsity no with
                                    | Some before, Some yes, Some no -> Some(before @ yes @ no)
                                    | _ -> None) (Some []))
                        | SemanticKind.Set(target, value) ->
                            match live target with
                            | Some { Kind = SemanticKind.VarRef(_, Some actual) } when actual = pc ->
                                literal value |> Option.bind (fun label ->
                                    cases |> List.tryPick (fun (key, _) -> if bigint key = label then Some [state, Some key, completed] else None))
                            | _ -> sequence node.Children
                        | SemanticKind.FrameWrite(_, slot, value) ->
                            sequence node.Children |> Option.map (List.map (fun (state, jump, completed) ->
                                (if falseGuard slot value then Pull.False else state), jump, completed))
                        | SemanticKind.WhileLoop _ | SemanticKind.ContinuationDispatch _ -> None
                        | SemanticKind.Application _ ->
                            // An unrelated invocation may advance or replace
                            // this iterator. It cannot carry a successful pull.
                            sequence node.Children |> Option.map (List.map (fun (_, jump, completed) -> Pull.Empty, jump, completed))
                        | _ -> sequence node.Children
                    result |> Option.map (List.map (fun (state, jump, completed) -> state, jump, Set.add id completed))
            if not pcValid || (entries |> List.exists Option.isNone) || actualPulls.IsEmpty then false else
            let mutable inputs = entries |> List.choose id |> List.distinct |> List.map (fun label -> label, Set.singleton Pull.Empty) |> Map.ofList
            let mutable pending = inputs.Keys |> Seq.toList
            let mutable valid = true
            while valid && not pending.IsEmpty do
                let label = pending.Head
                pending <- pending.Tail
                for state in inputs[label] do
                    match evaluate Set.empty Set.empty state None actions[label] with
                    | None -> valid <- false
                    | Some paths ->
                        for state, destination, _ in paths do
                            match destination with
                            | None -> ()
                            | Some next ->
                                let before = inputs.TryFind next |> Option.defaultValue Set.empty
                                let after = before.Add state
                                if before <> after then
                                    inputs <- inputs.Add(next, after)
                                    if not (List.contains next pending) then pending <- next :: pending
            valid && observed
        | _ -> false
    lifted |> List.choose (fun certificate ->
        match certificate.Class, certificate.Ordinal, certificate.Sources, live certificate.Target with
        | EdgeClass.Suspension, 0, [source; enumerator; guard; loop; iterator],
          Some { Kind = SemanticKind.Application(_, [actual]); Type = actualType } when actual = iterator && (operation "current" certificate.Target).IsSome ->
            match rows EdgeRole.IteratorCurrentAdmitted source, rows EdgeRole.IteratorCurrentAdmitted certificate.Target,
                  rows EdgeRole.ContinuationValue certificate.Target, graph.Nodes.TryFind source,
                  protocols |> List.filter (fun protocol -> protocol.Participants.Contains certificate.Target) with
            | [{ Class = EdgeClass.Suspension; Ordinal = 0; Sources = [actualEnumerator; actualGuard; actualLoop] }], [_],
              [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [original] }], Some originalNode, [protocol]
                when original = source && actualEnumerator = enumerator && actualGuard = guard && actualLoop = loop &&
                     applySubst originalNode.Type = applySubst actualType ->
                let support = descendants loop |> Set.union (descendants enumerator)
                let consumers = Current.structuralConsumersIncluding graph support
                match graph.Nodes.TryFind loop |> Option.bind (Current.forSupportedLoop graph consumers support), corresponds source certificate.Target with
                | Some original, Some correspondence when original.Target = source && original.Sources = [enumerator; guard; loop] &&
                                                        guarded protocol guard certificate.Target ->
                    Some { Source = source; Current = certificate.Target; Iterator = iterator
                           Participants = Set.unionMany [support; protocol.Participants; correspondence; Set.ofList certificate.Sources] }
                | _ -> None
            | _ -> None
        | _ -> None)

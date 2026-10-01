// SPDX-License-Identifier: MIT

/// Finite successful pulls and their additive consumers are separate premises.
/// This bounded source contract admits fresh local enumerators and acyclic
/// producer control, or a bounded product with one finite inner iterator; it
/// neither selects a carrier nor promises termination.
module Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Control = Clef.Compiler.Baker.Recipes.SequenceControlRecipes
module Evaluation = Clef.Compiler.Baker.Recipes.SequenceEvaluationRecipes
module Current = Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes
module Closures = Clef.Compiler.Baker.Ingredients.Closures
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins
module ExplicitDemand = Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand
module Loop = Clef.Compiler.Baker.Recipes.LoopRangeRecipes

type PullComposition = {
    ModelLabel: int
    SourceLabel: int
    RemainingPulls: bigint
    Origin: NodeId
    InnerProducer: NodeId
    Enumerator: NodeId
    Acquisition: NodeId
    Guard: NodeId
    Loop: NodeId
}

type Accumulation = {
    Owner: NodeId
    Producer: NodeId
    Generator: NodeId
    Input: NodeId
    Enumerator: NodeId
    Acquisition: NodeId
    Guard: NodeId
    Loop: NodeId
    Current: NodeId
    Cell: NodeId
    Initial: NodeId
    Delta: NodeId
    Update: NodeId
    Store: NodeId
    Pulls: FiniteSequencePullModel
    InnerPulls: FiniteSequencePullModel option
    Composition: PullComposition list
    Participants: NodeId list
}

let hasProof (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Obligation { Kind = "finite-sequence-pulls" | "sequence-inner-finite-pulls" | "sequence-additive-invariant" } -> true
    | _ -> false

let private edgeKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
let pullSources (item: Accumulation) =
    [item.Producer; item.Generator; item.Input; item.Enumerator; item.Acquisition; item.Guard; item.Loop] @ item.Participants
let accumulationSources (item: Accumulation) =
    [item.Owner; item.Loop; item.Initial; item.Store; item.Update; item.Delta; item.Current] @ item.Participants

/// Every successor is retained, including resumption after a suspension. Labels
/// are evaluation occurrences, never substitute graph node identities.
let private finiteModel entry (steps: Map<int, bool * bool * int list>) : FiniteSequencePullModel option =
    let rec visit path doneSteps label =
        if Set.contains label path then None
        else
            match Map.tryFind label doneSteps with
            | Some _ -> Some doneSteps
            | None ->
                match steps.TryFind label with
                | None -> None
                | Some(suspend, terminal, successors) ->
                    if terminal <> successors.IsEmpty then None
                    else
                        successors
                        |> List.fold (fun state target -> state |> Option.bind (fun facts -> visit (Set.add label path) facts target)) (Some doneSteps)
                        |> Option.map (fun facts ->
                            let weight = if suspend then 1I else 0I
                            let tail = successors |> List.map (fun target -> Map.find target facts) |> function [] -> 0I | values -> List.max values
                            Map.add label (weight + tail) facts)
    match visit Set.empty Map.empty entry with
    | Some remaining when remaining.Count = steps.Count ->
        Some { Entry = entry; MaximumPulls = remaining[entry]
               Steps = steps |> Map.toList |> List.map (fun (label, (suspend, _, successors)) ->
                   { Label = label; Suspend = suspend; Successors = successors; Remaining = remaining[label] }) }
    | _ -> None

let private resumesCurrent (control: Control.Control) =
    let cuts = control.Steps.Values |> Seq.choose (fun step ->
        match step.Instruction with
        | Control.Instruction.Suspend(_, state) ->
            match step.Successors with
            | [{ Target = next; Transfer = EvaluationTransfer.Resume }] -> Some(state, next)
            | _ -> Some(state, -1)
        | _ -> None) |> Seq.toList
    let resumes = (0, control.Entry) :: cuts
    resumes.Length = (Map.ofList resumes).Count && Map.ofList resumes = control.ResumeEntries &&
    (cuts |> List.forall (fun (state, next) -> state > 0 && next >= 0)) &&
    (control.Steps |> Map.forall (fun label step -> label = step.Label))

let finitePulls (control: Control.Control) : FiniteSequencePullModel option =
    if not (resumesCurrent control) then None
    else
        control.Steps |> Map.map (fun _ step ->
            (match step.Instruction with Control.Instruction.Suspend _ -> true | _ -> false),
            (match step.Instruction with Control.Instruction.Complete -> true | _ -> false),
            step.Successors |> List.map _.Target)
        |> finiteModel control.Entry

/// Kind and attached children agree; recorded incidence can repeat neither a
/// use nor a definition. Missing optional materialized incidence is canonical
/// from the source kind, while present incidence must match it exactly.
let private structural (graph: SemanticGraph) (node: SemanticNode) =
    let children =
        match node.Kind with
        | SemanticKind.Sequential ids | SemanticKind.TupleExpr ids -> Some ids
        | SemanticKind.Application(callee, arguments) -> Some(callee :: arguments)
        | SemanticKind.Set(target, value) -> Some [target; value]
        | SemanticKind.IfThenElse(guard, yes, no) -> Some([guard; yes] @ Option.toList no)
        | SemanticKind.WhileLoop(guard, body) -> Some [guard; body]
        | SemanticKind.TypeAnnotation(value, _) | SemanticKind.EagerExpr value | SemanticKind.Yield value
        | SemanticKind.EnvironmentReference value -> Some [value]
        | SemanticKind.Binding _ -> if node.Children.Length <= 1 then Some node.Children else None
        | SemanticKind.Intrinsic _ | SemanticKind.VarRef _ | SemanticKind.Literal _ | SemanticKind.PatternBinding _ -> Some []
        | _ -> None
    match children with
    | Some expected when expected = node.Children && (expected |> List.forall graph.Nodes.ContainsKey) ->
        let relevant (edge: Hyperedge) = edge.Class = EdgeClass.Structural || edge.Role = EdgeRole.Definition
        let canonical = Closures.structuralIncidence node |> List.filter relevant |> List.map edgeKey |> Set.ofList
        let resident = graph.Edges |> List.filter (fun edge -> edge.Target = node.Id && relevant edge) |> List.map edgeKey
        resident.Length = (Set.ofList resident).Count && List.forall canonical.Contains resident
    | _ -> false

let private sourceControlOnly graph producer =
    let expected = Evaluation.forOwner graph producer
    let actual = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Evaluation && List.tryHead edge.Sources = Some producer.Id)
    if List.sort (List.map edgeKey expected.NewEdges) <> List.sort (List.map edgeKey actual) then None
    else
        match Control.forOwner graph producer with
        | Error _ -> None
        | Ok control ->
            let sites = actual |> List.collect (fun edge -> edge.Target :: List.skip 1 edge.Sources) |> Set.ofList |> Set.remove control.Generator |> Set.remove producer.Id
            if sites |> Set.forall (fun id -> graph.Nodes.TryFind id |> Option.exists (fun node -> node.IsReachable && structural graph node)) then
                Some(control, sites)
            else None

/// Product states are proof labels, not source nodes or runtime unrolling. A
/// successful pull from the exact inner iterator consumes one admitted unit;
/// every other control alternative is retained. Keep compilation bounded too.
let private productPulls (control: Control.Control) guard loop maximum =
    let branch = control.Steps.Values |> Seq.filter (fun step ->
        step.Origin = loop && step.Port = EvaluationPort.OperandExit 0 &&
        step.Instruction = Control.Instruction.Branch guard) |> Seq.toList
    match branch with
    | [test] when resumesCurrent control && maximum >= 0I &&
                  (control.Steps.Values |> Seq.filter (fun step -> step.Instruction = Control.Instruction.Evaluate guard) |> Seq.length) = 1 &&
                  (test.Successors |> List.map _.Transfer |> List.sort) = [EvaluationTransfer.WhenTrue; EvaluationTransfer.WhenFalse] ->
        let maximumStates = 4096
        let rec expand pending labels steps =
            match pending with
            | [] -> Some(labels, steps)
            | ((label, budget) as state) :: rest ->
                match control.Steps.TryFind label with
                | None -> None
                | Some step ->
                    let next = step.Successors |> List.choose (fun arc ->
                        if label = test.Label && arc.Transfer = EvaluationTransfer.WhenTrue then
                            if budget = 0I then None else Some(arc.Target, budget - 1I)
                        else Some(arc.Target, budget))
                    let fresh = next |> List.distinct |> List.filter (fun key -> not (Map.containsKey key labels))
                    if Map.count labels + fresh.Length > maximumStates then None
                    else
                        let labels = fresh |> List.fold (fun mapping key -> Map.add key (Map.count mapping) mapping) labels
                        let modelLabel = Map.find state labels
                        let suspend = match step.Instruction with Control.Instruction.Suspend _ -> true | _ -> false
                        let terminal = match step.Instruction with Control.Instruction.Complete -> true | _ -> false
                        let steps = Map.add modelLabel (suspend, terminal, List.map (fun key -> Map.find key labels) next) steps
                        expand (rest @ fresh) labels steps
        match expand [control.Entry, maximum] (Map.ofList [((control.Entry, maximum), 0)]) Map.empty with
        | Some(labels, steps) ->
            finiteModel 0 steps |> Option.map (fun model ->
                model, labels |> Map.toList |> List.map (fun ((label, budget), product) -> product, label, budget) |> List.sortBy (fun (product, _, _) -> product))
        | None -> None
    | _ -> None

let private sourceControl (graph: SemanticGraph) producer =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let node id = nodes.TryFind id
    let valid id = node id |> Option.exists (structural graph)
    let same left right =
        match node left, node right with Some a, Some b -> applySubst a.Type = applySubst b.Type | _ -> false
    let reference id =
        match node id with
        | Some { Kind = SemanticKind.VarRef(_, Some target) } when valid id && same id target -> Some target
        | _ -> None
    let operation modl name id =
        match node id with
        | Some { Kind = SemanticKind.Application(callee, [argument]) } when valid id ->
            match node callee with
            | Some { Kind = SemanticKind.Intrinsic info } when info.Module = modl && info.Operation = name && valid callee -> Some argument
            | _ -> None
        | _ -> None
    let rec actions path id =
        if Set.contains id path then None
        else
            match node id with
            | Some { Kind = SemanticKind.Sequential children } when valid id ->
                children |> List.fold (fun acc child ->
                    match acc, actions (Set.add id path) child with Some left, Some right -> Some(left @ right) | _ -> None) (Some [])
            | Some _ -> Some [id]
            | _ -> None
    // No opaque origin is inferred away: this slice follows an immutable
    // source transport to the actual constructor, preserving each occurrence.
    let rec inputOrigin path id =
        if Set.contains id path then None
        else
            match node id with
            | Some ({ Kind = SemanticKind.SeqExpr _ } as source) -> Some(source, [id])
            | Some value when valid id ->
                let next =
                    match value.Kind with
                    | SemanticKind.VarRef(_, Some target) when same id target -> Some target
                    | SemanticKind.Binding(_, false, false, _) ->
                        match value.Children with [target] when same id target -> Some target | _ -> None
                    | SemanticKind.TypeAnnotation(target, _) when same id target -> Some target
                    | SemanticKind.EagerExpr target when same id target && ExplicitDemand.operand graph id = Some target -> Some target
                    | _ -> None
                next |> Option.bind (inputOrigin (Set.add id path)) |> Option.map (fun (source, rest) -> source, id :: rest)
            | _ -> None
    match sourceControlOnly graph producer with
    | None -> None
    | Some(control, sites) ->
        match finitePulls control with
        | Some bound -> Some(control, bound, sites, [], None)
        | None ->
            let consumers = Current.structuralConsumers graph
            let solely value owner = consumers.TryFind value = Some [owner]
            let captured enumerator =
                let ty = nodes[enumerator].Type |> applySubst
                nodes.Values |> Seq.exists (fun value ->
                    match value.Kind with
                    | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures) | SemanticKind.LazyExpr(_, captures) ->
                        captures |> List.exists (fun capture -> capture.SourceNodeId = Some enumerator || (capture.SourceNodeId.IsNone && applySubst capture.Type = ty))
                    | SemanticKind.EnvironmentRead(_, slot) | SemanticKind.EnvironmentBorrow(_, slot) | SemanticKind.EnvironmentWrite(_, slot, _)
                    | SemanticKind.FrameRead(_, slot) | SemanticKind.FrameBorrow(_, slot) | SemanticKind.FrameWrite(_, slot, _) | SemanticKind.CellAddress slot -> slot = enumerator
                    | SemanticKind.AddressOf(value, _) -> reference value = Some enumerator
                    | _ -> false)
            let shape =
                match node control.Generator with
                | Some { Kind = SemanticKind.Lambda(_, body, _, _, LambdaContext.SeqGenerator) } ->
                    match actions Set.empty body with
                    | Some [enumerator; loop] when solely enumerator body && solely loop body -> Some(body, enumerator, loop)
                    | _ -> None
                | _ -> None
            match shape with
            | Some(body, enumerator, loop) ->
                match node enumerator, node loop with
                | Some { Kind = SemanticKind.Binding(_, false, false, _); Children = [acquisition] },
                  Some ({ Kind = SemanticKind.WhileLoop(guard, _) } as loopNode)
                    when valid enumerator && valid loop && solely acquisition enumerator && not (captured enumerator) ->
                    match operation IntrinsicModule.Seq "getEnumerator" acquisition,
                          operation IntrinsicModule.SeqEnumerator "moveNext" guard,
                          Current.forLoop graph consumers loopNode with
                    | Some input, Some guardReference, Some admitted when admitted.Sources = [enumerator; guard; loop] && solely guardReference guard ->
                        match operation IntrinsicModule.SeqEnumerator "current" admitted.Target, inputOrigin Set.empty input with
                        | Some currentReference, Some(inner, originPath) when inner.Id <> producer.Id && solely currentReference admitted.Target ->
                            let references = nodes.Values |> Seq.choose (fun value -> if reference value.Id = Some enumerator then Some value.Id else None) |> Seq.toList
                            let incidence = nodes.Values |> Seq.collect Closures.structuralIncidence |> Seq.toList
                            let relevant edge =
                                (edge.Class = EdgeClass.Structural || edge.Role = EdgeRole.Definition) &&
                                (edge.Sources |> List.exists (fun id -> id = enumerator || id = guardReference || id = currentReference))
                            let canonical = incidence |> List.filter relevant |> List.map edgeKey |> Set.ofList
                            let recorded = graph.Edges |> List.filter relevant |> List.map edgeKey
                            let uses = incidence |> List.filter (fun edge -> edge.Sources |> List.contains enumerator)
                            let usesValid = uses |> List.forall (fun edge ->
                                (edge.Role = EdgeRole.Definition && List.contains edge.Target references) ||
                                (Hyperedge.isStructural edge && edge.Target = body))
                            if Set.ofList references <> Set.ofList [guardReference; currentReference] ||
                               reference guardReference <> Some enumerator || reference currentReference <> Some enumerator ||
                               recorded.Length <> (Set.ofList recorded).Count || not (List.forall canonical.Contains recorded) || not usesValid then None
                            else
                                match sourceControlOnly graph inner with
                                | Some(innerControl, innerSites) ->
                                    match finitePulls innerControl with
                                    | Some innerBound ->
                                        productPulls control guard loop innerBound.MaximumPulls |> Option.map (fun (bound, correspondence) ->
                                            let supports = Set.union sites innerSites |> Set.union (Set.ofList (body :: inner.Id :: innerControl.Generator :: originPath))
                                            let composition = correspondence |> List.map (fun (product, label, remaining) ->
                                                { ModelLabel = product; SourceLabel = label; RemainingPulls = remaining; Origin = control.Steps[label].Origin
                                                  InnerProducer = inner.Id; Enumerator = enumerator; Acquisition = acquisition; Guard = guard; Loop = loop })
                                            control, bound, supports, composition, Some innerBound)
                                    | _ -> None
                                | _ -> None
                        | _ -> None
                    | _ -> None
                | _ -> None
            | _ -> None

let recognize (graph: SemanticGraph) (inputs: Loop.Inputs) : Accumulation list =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let node id = nodes.TryFind id
    let same left right =
        match node left, node right with Some a, Some b -> applySubst a.Type = applySubst b.Type | _ -> false
    let valid id = node id |> Option.exists (structural graph)
    let consumers = Current.structuralConsumers graph
    let solely value owner = consumers.TryFind value = Some [owner]
    let incidence = nodes.Values |> Seq.collect Closures.structuralIncidence |> Seq.map edgeKey |> Set.ofSeq
    let recordedUsesAgree ids =
        let rows = graph.Edges |> List.filter (fun edge ->
            (edge.Class = EdgeClass.Structural || edge.Role = EdgeRole.Definition) &&
            (edge.Sources |> List.exists (fun id -> Set.contains id ids))) |> List.map edgeKey
        rows.Length = (Set.ofList rows).Count && List.forall incidence.Contains rows
    let rec uniqueWithin root seen id =
        if id = root then true
        elif Set.contains id seen then false
        else
            match consumers.TryFind id with
            | Some [parent] -> uniqueWithin root (Set.add id seen) parent
            | _ -> false
    let reference id =
        match node id with
        | Some { Kind = SemanticKind.VarRef(_, Some target) } when valid id && same id target -> Some target
        | _ -> None
    let operation modl name id =
        match node id with
        | Some { Kind = SemanticKind.Application(callee, [argument]) } when valid id ->
            match node callee with
            | Some { Kind = SemanticKind.Intrinsic info } when info.Module = modl && info.Operation = name && valid callee -> Some argument
            | _ -> None
        | _ -> None
    let rec actions path id =
        if Set.contains id path then None
        else
            match node id with
            | Some { Kind = SemanticKind.Sequential children } when valid id ->
                children |> List.fold (fun collected child ->
                    match collected, actions (Set.add id path) child with Some left, Some right -> Some(left @ right) | _ -> None) (Some [])
            | Some _ -> Some [id]
            | _ -> None
    let captured =
        nodes.Values |> Seq.collect (fun n ->
            match n.Kind with
            | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures) | SemanticKind.LazyExpr(_, captures) -> captures |> List.choose _.SourceNodeId
            | SemanticKind.EnvironmentRead(_, slot) | SemanticKind.EnvironmentBorrow(_, slot) | SemanticKind.EnvironmentWrite(_, slot, _)
            | SemanticKind.FrameRead(_, slot) | SemanticKind.FrameBorrow(_, slot) | SemanticKind.FrameWrite(_, slot, _) | SemanticKind.CellAddress slot -> [slot]
            | SemanticKind.AddressOf(value, _) -> reference value |> Option.toList
            | _ -> []) |> Set.ofSeq
    let unknownCapture id =
        match node id with
        | None -> true
        | Some value ->
            nodes.Values |> Seq.exists (fun item ->
                let captures = match item.Kind with
                               | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures) | SemanticKind.LazyExpr(_, captures) -> captures
                               | _ -> []
                captures |> List.exists (fun capture -> capture.SourceNodeId.IsNone && applySubst capture.Type = applySubst value.Type))
    let allStores cell =
        nodes.Values |> Seq.choose (fun n ->
            match n.Kind with SemanticKind.Set(target, value) when reference target = Some cell -> Some(n.Id, value) | _ -> None) |> Seq.toList
    let effectsDisjoint cell id =
        match inputs.Effects.TryFind id with Some(writes, false) -> not (writes.Contains cell) | _ -> false
    let _, origins = Origins.settle graph graph.Codata.Value.Curry
    let rec currentValue current path id =
        if id = current then Some [id]
        elif Set.contains id path || not (valid id) then None
        else
            let next =
                match node id with
                | Some { Kind = SemanticKind.VarRef(_, Some value) } when same id value -> Some value
                | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } when same id value -> Some value
                | Some { Kind = SemanticKind.TypeAnnotation(value, _) } when same id value -> Some value
                | Some { Kind = SemanticKind.EagerExpr value } when same id value && ExplicitDemand.operand graph id = Some value -> Some value
                | _ -> None
            next |> Option.bind (currentValue current (Set.add id path)) |> Option.map (fun rest -> id :: rest)
    let recognizeLoop owner ownerActions initialized loopId =
        match node loopId with
        | Some ({ Kind = SemanticKind.WhileLoop(guard, body) } as loop) when valid loopId ->
            match Current.forLoop graph consumers loop, operation IntrinsicModule.SeqEnumerator "moveNext" guard with
            | Some certificate, Some guardReference ->
                match certificate.Sources, node body with
                | [enumerator; actualGuard; actualLoop], Some { Kind = SemanticKind.Sequential [currentBinding; currentReference; action] }
                    when actualGuard = guard && actualLoop = loopId && valid body ->
                    let current = certificate.Target
                    match node enumerator, operation IntrinsicModule.SeqEnumerator "current" current, actions Set.empty action with
                    | Some { Kind = SemanticKind.Binding(_, false, false, _); Children = [acquisition] }, Some currentArgument, Some bodyActions
                        when valid enumerator && valid current && Set.contains enumerator initialized ->
                        match operation IntrinsicModule.Seq "getEnumerator" acquisition with
                        | Some input when solely acquisition enumerator && solely guardReference guard && solely currentArgument current &&
                                          reference guardReference = Some enumerator && reference currentArgument = Some enumerator ->
                            let references = nodes.Values |> Seq.choose (fun n -> if reference n.Id = Some enumerator then Some n.Id else None) |> Set.ofSeq
                            let uses = nodes.Values |> Seq.collect Closures.structuralIncidence |> Seq.filter (fun edge -> edge.Sources |> List.contains enumerator) |> Seq.toList
                            let permitted edge =
                                (edge.Role = EdgeRole.Definition && references.Contains edge.Target) ||
                                (Hyperedge.isStructural edge && consumers.TryFind enumerator = Some [edge.Target] && List.contains enumerator ownerActions)
                            let origin = origins.TryFind input |> Option.bind (fun alternatives ->
                                match Set.toList alternatives with [Origins.Origin.Known producer] -> node producer | _ -> None)
                            match origin with
                            | Some producer when references = Set.ofList [guardReference; currentArgument] && not (captured.Contains enumerator) && not (unknownCapture enumerator) &&
                                                 recordedUsesAgree (Set.ofList [enumerator; guardReference; currentArgument]) && (uses |> List.forall permitted) ->
                                match sourceControl graph producer with
                                // Empty-consumer elimination owns the zero-pull
                                // case; an unobservable current is no delta fact.
                                | Some(control, pulls, producerSites, composition, innerPulls) when pulls.MaximumPulls > 0I ->
                                    bodyActions |> List.choose (fun store ->
                                        match node store with
                                        | Some { Kind = SemanticKind.Set(target, update) } when valid store && uniqueWithin body Set.empty store && solely update store ->
                                            match reference target, inputs.Operators.TryFind update with
                                            | Some cell, Some("op_Addition", [left; right]) when valid update && not (captured.Contains cell) && not (unknownCapture cell) &&
                                                                                                              recordedUsesAgree (Set.ofList [store; update; cell]) && Set.contains cell initialized ->
                                                let delta = if reference left = Some cell then Some right elif reference right = Some cell then Some left else None
                                                match node cell, delta |> Option.bind (fun delta -> currentValue current Set.empty delta |> Option.map (fun path -> delta, path)) with
                                                | Some { Kind = SemanticKind.Binding(_, true, _, _); Children = [initial]; Type = ty }, Some(delta, deltaPath)
                                                    when Types.isIntegerType ty && valid cell && same cell initial && same cell delta && same cell update &&
                                                         (node initial |> Option.exists (fun node -> match node.Kind with SemanticKind.Literal(NativeLiteral.Int _ | NativeLiteral.UInt _) -> valid initial | _ -> false)) &&
                                                         allStores cell = [store, update] && inputs.Assignments.TryFind cell = Some [update] &&
                                                         (bodyActions |> List.forall (fun id -> id = store || effectsDisjoint cell id)) &&
                                                         (ownerActions |> List.forall (fun id -> id = loopId || id = cell || effectsDisjoint cell id)) &&
                                                         effectsDisjoint cell guard && effectsDisjoint cell acquisition && effectsDisjoint cell delta ->
                                                    let participants =
                                                        [owner; loopId; body; guard; guardReference; enumerator; acquisition; input; producer.Id; control.Generator;
                                                         current; currentBinding; currentReference; currentArgument; action; cell; initial; target; store; update; left; right]
                                                        @ ownerActions @ bodyActions @ deltaPath @ Set.toList producerSites
                                                        |> List.distinct
                                                    Some { Owner = owner; Producer = producer.Id; Generator = control.Generator; Input = input
                                                           Enumerator = enumerator; Acquisition = acquisition; Guard = guard; Loop = loopId; Current = current
                                                           Cell = cell; Initial = initial; Delta = delta; Update = update; Store = store; Pulls = pulls
                                                           InnerPulls = innerPulls; Composition = composition; Participants = participants }
                                                | _ -> None
                                            | _ -> None
                                        | _ -> None)
                                | _ -> []
                            | _ -> []
                        | _ -> []
                    | _ -> []
                | _ -> []
            | _ -> []
        | _ -> []
    nodes.Values |> Seq.collect (fun owner ->
        match owner.Kind with
        | SemanticKind.Lambda(_, body, _, _, context) when context <> LambdaContext.SeqGenerator ->
            match actions Set.empty body with
            | Some items when (items |> List.distinct).Length = items.Length ->
                items |> List.fold (fun (initialized, found) id ->
                    let next = recognizeLoop owner.Id items initialized id
                    let initialized = match node id with Some { Kind = SemanticKind.Binding _ } -> Set.add id initialized | _ -> initialized
                    initialized, found @ next) (Set.empty, []) |> snd
            | _ -> []
        | _ -> []) |> Seq.toList
    |> List.groupBy _.Loop
    |> List.collect (fun (_, items) -> match items with [item] -> [item] | _ -> [])

let saturate range (item: Accumulation) : AdditiveLoopInvariantModel option =
    match range item.Initial, range item.Delta with
    | ValueRange.Bounded(initialLo, initialHi), ValueRange.Bounded(deltaLo, deltaHi) ->
        let count = item.Pulls.MaximumPulls
        Some { MaximumIterations = count; InitialLower = initialLo; InitialUpper = initialHi
               DeltaLower = deltaLo; DeltaUpper = deltaHi
               Lower = initialLo + count * min 0I deltaLo; Upper = initialHi + count * max 0I deltaHi }
    | _ -> None

let relations (items: Accumulation list) = items |> List.collect (fun item ->
    [{ Class = EdgeClass.Range; Role = EdgeRole.SequencePullBound; Ordinal = 0; Sources = pullSources item; Target = item.Current }
     { Class = EdgeClass.Range; Role = EdgeRole.SequenceAccumulation; Ordinal = 0; Sources = accumulationSources item; Target = item.Cell }]
    @ (item.Composition |> List.map (fun step ->
        { Class = EdgeClass.Range; Role = EdgeRole.SequencePullComposition(step.SourceLabel, step.RemainingPulls); Ordinal = step.ModelLabel
          Sources = [item.Producer; step.InnerProducer; step.Enumerator; step.Acquisition; step.Guard; step.Loop; step.Origin]
          Target = item.Current })))

let isRelation (edge: Hyperedge) =
    match edge.Role with
    | EdgeRole.SequencePullBound | EdgeRole.SequenceAccumulation | EdgeRole.SequencePullComposition _ -> true
    | _ -> false

let obligations (graph: SemanticGraph) range (items: Accumulation list) =
    items |> List.mapi (fun index item ->
        match saturate range item with
        | None -> Enrichment.empty
        | Some invariant ->
            let subject = graph.Nodes[item.Cell]
            let make suffix kind statement body =
                let info = { Id = sprintf "sequence_%s_%d_%d" suffix (NodeId.value item.Loop) (NodeId.value item.Cell)
                             Kind = kind; Logic = "QF_LIA"; Statement = statement; Source = fmtRange subject.Range; Refs = []; Body = body }
                let proof = obligationNode subject index info
                { Enrichment.empty with NewNodes = [proof]; NewEdges = [constrains (item.Current :: item.Cell :: item.Participants |> List.distinct) proof] }
            let inner =
                match item.InnerPulls with
                | Some model -> make "inner_pulls" "sequence-inner-finite-pulls" "The complete acyclic inner source control supplies the initial budget of the fresh iterator product." (ObligationBody.FiniteSequencePull model)
                | None -> Enrichment.empty
            [make "pulls" "finite-sequence-pulls" "The complete source control or its source-validated finite iterator product bounds successful pulls of this fresh, unescaped iterator." (ObligationBody.FiniteSequencePull item.Pulls)
             make "additive" "sequence-additive-invariant" "The local additive update stays in the enclosure for every admitted successful pull." (ObligationBody.AdditiveLoopInvariant invariant)
             inner] |> Enrichment.concat)
    |> Enrichment.concat

type private ProofPair = {
    Item: Accumulation
    PullProof: SemanticNode
    PullInfo: ObligationInfo
    PullRow: Hyperedge
    Pulls: FiniteSequencePullModel
    Additive: NodeId
    Inner: NodeId option
}

/// A successful reader must account for every owning proof, not merely find a
/// usable finite proof among them. Both arithmetic propositions cite the same
/// exact current accumulation and agree on the retained successful-pull count.
let private proofPairs (graph: SemanticGraph) (items: Accumulation list) =
    let owned = graph.Nodes.Values |> Seq.filter hasProof |> Seq.toList
    let selected item kind =
        let expected = item.Current :: item.Cell :: item.Participants |> List.distinct
        owned |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind = kind && not node.IsReachable ->
                match graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = node.Id) with
                | [row] when row.Class = EdgeClass.Obligation && row.Ordinal = 0 && row.Sources = expected -> Some(node, info, row)
                | _ -> None
            | _ -> None)
    let range id = graph.Nodes.TryFind id |> Option.bind _.ValueRange |> Option.defaultValue ValueRange.Unbounded
    let enclosed lower upper id =
        match range id with
        | ValueRange.Bounded(lo, hi) -> lower <= lo && lo <= hi && hi <= upper
        | _ -> false
    let pairs = items |> List.map (fun item ->
        let inner =
            match item.InnerPulls, selected item "sequence-inner-finite-pulls" with
            | None, [] -> Some None
            | Some expected, [(proof, { Body = ObligationBody.FiniteSequencePull actual }, _)] when expected = actual -> Some(Some proof.Id)
            | _ -> None
        match selected item "finite-sequence-pulls", selected item "sequence-additive-invariant" with
        | [(pull, pullInfo, pullRow)], [(additive, additiveInfo, _)] ->
            match pullInfo.Body, additiveInfo.Body with
            | ObligationBody.FiniteSequencePull old, ObligationBody.AdditiveLoopInvariant invariant
                when item.Pulls.MaximumPulls <= old.MaximumPulls && invariant.MaximumIterations = old.MaximumPulls ->
                let retained = { item with Pulls = { item.Pulls with MaximumPulls = old.MaximumPulls } }
                match saturate range retained with
                | Some expected when expected = invariant &&
                                     enclosed invariant.DeltaLower invariant.DeltaUpper item.Current &&
                                     enclosed invariant.Lower invariant.Upper item.Cell &&
                                     enclosed invariant.Lower invariant.Upper item.Update && inner.IsSome ->
                    Some { Item = item; PullProof = pull; PullInfo = pullInfo; PullRow = pullRow; Pulls = old; Additive = additive.Id; Inner = Option.flatten inner }
                | _ -> None
            | _ -> None
        | _ -> None)
    let found = pairs |> List.choose id
    let ids = found |> List.collect (fun pair -> [pair.PullProof.Id; pair.Additive] @ Option.toList pair.Inner)
    if found.Length = items.Length && ids.Length = (Set.ofList ids).Count && Set.ofList ids = (owned |> List.map _.Id |> Set.ofList) then
        Some found
    else None

/// The representation recipe revalidates its current control before rewriting
/// the generator. The numeric envelope already used by range selection cannot
/// grow here; a changed producer requiring more pulls is an explicit refusal.
let handoff (graph: SemanticGraph) (controls: Map<NodeId, Control.Control>) (fresh: Accumulation list option) =
    let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequencePullBound)
    let invalid = rows |> List.tryFind (fun edge -> edge.Class <> EdgeClass.Range || edge.Ordinal <> 0)
    let repeated = rows |> List.groupBy _.Target |> List.tryFind (fun (_, rows) -> rows.Length <> 1)
    let incidenceAgrees =
        fresh |> Option.exists (fun items ->
            let expected = relations items |> List.map edgeKey |> List.sort
            let actual = graph.Edges |> List.filter isRelation |> List.map edgeKey |> List.sort
            actual = expected)
    let pairs = fresh |> Option.bind (proofPairs graph)
    let reject reason =
        let sites =
            (graph.Edges |> List.filter isRelation |> List.map _.Target) @
            (graph.Nodes.Values |> Seq.filter hasProof |> Seq.map _.Id |> Seq.toList)
            |> List.distinct
        graph, sites |> List.map (fun site -> site, reason)
    match invalid, repeated, incidenceAgrees, pairs with
    | Some row, _, _, _ -> graph, [row.Target, "The finite successful-pull relation has an invalid class or ordinal."]
    | _, Some(current, _), _, _ -> graph, [current, "The finite successful-pull relation duplicates one iterator occurrence."]
    | _, _, false, _ -> reject "The finite successful-pull source consumer, origin, write/effect or dependency incidence is no longer current."
    | _, _, _, None -> reject "The finite-pull/additive proof inventory, exact source support, count, or settled range enclosure is inconsistent."
    | None, None, true, Some pairs ->
        pairs |> List.fold (fun ((graph: SemanticGraph), failures) pair ->
            let item = pair.Item
            let fail reason = graph, (item.Current, reason) :: failures
            match controls.TryFind item.Producer, graph.Nodes.TryFind item.Producer with
            | Some control, Some owner when control.Generator = item.Generator ->
                match sourceControl graph owner with
                | Some(actual, current, participants, _, _) when actual = control && current.MaximumPulls <= pair.Pulls.MaximumPulls ->
                    let model = { current with MaximumPulls = pair.Pulls.MaximumPulls }
                    let proof = { pair.PullProof with Kind = SemanticKind.Obligation { pair.PullInfo with Body = ObligationBody.FiniteSequencePull model } }
                    let supports = List.distinct (pair.PullRow.Sources @ Set.toList participants)
                    let edges = graph.Edges |> List.map (fun edge ->
                        if edge.Target = proof.Id && edge.Class = EdgeClass.Obligation && edge.Role = EdgeRole.Constrains then { edge with Sources = supports }
                        else edge)
                    { graph with Nodes = graph.Nodes.Add(proof.Id, proof); Edges = edges }, failures
                | _ -> fail "The finite successful-pull envelope no longer covers the complete current source control."
            | _ -> fail "The finite successful-pull producer lacks its current owner and generator.") (graph, [])

/// Called only after SequenceContinuationEvidence accepts the generated machine.
/// Keep its complete representation/proof support on the source bound; this is
/// conservative dependency retention, not selective lifetime-proof reuse.
let retainMachineSupports owner supports (graph: SemanticGraph) =
    let currents = graph.Edges |> List.choose (fun edge ->
        match edge.Role, edge.Sources with
        | EdgeRole.SequencePullBound, actual :: _ when edge.Ordinal = 0 && actual = owner -> Some edge.Target
        | EdgeRole.SequencePullComposition _, outer :: inner :: _ when owner = outer || owner = inner -> Some edge.Target
        | _ -> None) |> Set.ofList
    let finite = graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with SemanticKind.Obligation { Kind = "finite-sequence-pulls" | "sequence-inner-finite-pulls" } -> Some id | _ -> None) |> Set.ofList
    let edges = graph.Edges |> List.map (fun edge ->
        if finite.Contains edge.Target && edge.Role = EdgeRole.Constrains && (edge.Sources |> List.exists currents.Contains) then
            { edge with Sources = List.distinct (edge.Sources @ supports) }
        else edge)
    { graph with Edges = edges }

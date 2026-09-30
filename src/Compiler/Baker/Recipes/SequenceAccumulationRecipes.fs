// SPDX-License-Identifier: MIT

/// Finite successful pulls and their additive consumers are separate premises.
/// This bounded source contract admits fresh local enumerators and acyclic
/// producer control; it neither selects a carrier nor promises termination.
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
    Participants: NodeId list
}

let hasProof (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Obligation { Kind = "finite-sequence-pulls" | "sequence-additive-invariant" } -> true
    | _ -> false

let private edgeKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
let pullSources (item: Accumulation) =
    [item.Producer; item.Generator; item.Input; item.Enumerator; item.Acquisition; item.Guard; item.Loop] @ item.Participants
let accumulationSources (item: Accumulation) =
    [item.Owner; item.Loop; item.Initial; item.Store; item.Update; item.Delta; item.Current] @ item.Participants

/// Every successor is retained, including resumption after a suspension. Labels
/// are evaluation occurrences, never substitute graph node identities.
let finitePulls (control: Control.Control) : FiniteSequencePullModel option =
    let rec visit path doneSteps label =
        if Set.contains label path then None
        else
            match Map.tryFind label doneSteps with
            | Some _ -> Some doneSteps
            | None ->
                match control.Steps.TryFind label with
                | None -> None
                | Some step when step.Label <> label -> None
                | Some step ->
                    let terminal = match step.Instruction with Control.Instruction.Complete -> true | _ -> false
                    if terminal <> step.Successors.IsEmpty then None
                    else
                        let successors = step.Successors |> List.map _.Target
                        successors
                        |> List.fold (fun state target -> state |> Option.bind (fun facts -> visit (Set.add label path) facts target)) (Some doneSteps)
                        |> Option.map (fun facts ->
                            let weight = match step.Instruction with Control.Instruction.Suspend _ -> 1I | _ -> 0I
                            let tail = successors |> List.map (fun target -> Map.find target facts) |> function [] -> 0I | values -> List.max values
                            Map.add label (weight + tail) facts)
    let cuts = control.Steps.Values |> Seq.choose (fun step ->
        match step.Instruction with
        | Control.Instruction.Suspend(_, state) ->
            match step.Successors with
            | [{ Target = next; Transfer = EvaluationTransfer.Resume }] -> Some(state, next)
            | _ -> Some(state, -1)
        | _ -> None) |> Seq.toList
    let resumes = (0, control.Entry) :: cuts
    if resumes.Length <> (Map.ofList resumes).Count || Map.ofList resumes <> control.ResumeEntries || (cuts |> List.exists (fun (state, next) -> state <= 0 || next < 0)) then None
    else
        match visit Set.empty Map.empty control.Entry with
        | Some remaining when remaining.Count = control.Steps.Count ->
            Some { Entry = control.Entry; MaximumPulls = remaining[control.Entry]
                   Steps = control.Steps |> Map.toList |> List.map (fun (label, step) ->
                       { Label = label; Suspend = (match step.Instruction with Control.Instruction.Suspend _ -> true | _ -> false)
                         Successors = step.Successors |> List.map _.Target; Remaining = remaining[label] }) }
        | _ -> None

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
        | SemanticKind.TypeAnnotation(value, _) | SemanticKind.EagerExpr value | SemanticKind.Yield value -> Some [value]
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

let private sourceControl graph producer =
    let expected = Evaluation.forOwner graph producer
    let actual = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Evaluation && List.tryHead edge.Sources = Some producer.Id)
    if List.sort (List.map edgeKey expected.NewEdges) <> List.sort (List.map edgeKey actual) then None
    else
        match Control.forOwner graph producer with
        | Error _ -> None
        | Ok control ->
            let sites = actual |> List.collect (fun edge -> edge.Target :: List.skip 1 edge.Sources) |> Set.ofList |> Set.remove control.Generator |> Set.remove producer.Id
            if sites |> Set.forall (fun id -> graph.Nodes.TryFind id |> Option.exists (fun node -> node.IsReachable && structural graph node)) then
                finitePulls control |> Option.map (fun bound -> control, bound, sites)
            else None

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
                                | Some(control, pulls, producerSites) when pulls.MaximumPulls > 0I ->
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
                                                           Cell = cell; Initial = initial; Delta = delta; Update = update; Store = store; Pulls = pulls; Participants = participants }
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
     { Class = EdgeClass.Range; Role = EdgeRole.SequenceAccumulation; Ordinal = 0; Sources = accumulationSources item; Target = item.Cell }])

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
            Enrichment.combine
                (make "pulls" "finite-sequence-pulls" "The complete acyclic source control bounds successful pulls of this fresh, unescaped iterator." (ObligationBody.FiniteSequencePull item.Pulls))
                (make "additive" "sequence-additive-invariant" "The local additive update stays in the enclosure for every admitted successful pull." (ObligationBody.AdditiveLoopInvariant invariant)))
    |> Enrichment.concat

type private ProofPair = {
    Item: Accumulation
    PullProof: SemanticNode
    PullInfo: ObligationInfo
    PullRow: Hyperedge
    Pulls: FiniteSequencePullModel
    Additive: NodeId
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
                                     enclosed invariant.Lower invariant.Upper item.Update ->
                    Some { Item = item; PullProof = pull; PullInfo = pullInfo; PullRow = pullRow; Pulls = old; Additive = additive.Id }
                | _ -> None
            | _ -> None
        | _ -> None)
    let found = pairs |> List.choose id
    let ids = found |> List.collect (fun pair -> [pair.PullProof.Id; pair.Additive])
    if found.Length = items.Length && ids.Length = (Set.ofList ids).Count && Set.ofList ids = (owned |> List.map _.Id |> Set.ofList) then
        Some found
    else None

/// The representation recipe revalidates its current control before rewriting
/// the generator. The numeric envelope already used by range selection cannot
/// grow here; a changed producer requiring more pulls is an explicit refusal.
let handoff (graph: SemanticGraph) (controls: Map<NodeId, Control.Control>) (fresh: Accumulation list option) =
    let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequencePullBound)
    let accumulationRows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceAccumulation)
    let invalid = rows |> List.tryFind (fun edge -> edge.Class <> EdgeClass.Range || edge.Ordinal <> 0)
    let repeated = rows |> List.groupBy _.Target |> List.tryFind (fun (_, rows) -> rows.Length <> 1)
    let incidenceAgrees =
        fresh |> Option.exists (fun items ->
            let expected = relations items |> List.map edgeKey |> List.sort
            let actual = rows @ accumulationRows |> List.map edgeKey |> List.sort
            actual = expected)
    let pairs = fresh |> Option.bind (proofPairs graph)
    let reject reason =
        let sites =
            (rows @ accumulationRows |> List.map _.Target) @
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
                | Some(actual, current, participants) when actual = control && current.MaximumPulls <= pair.Pulls.MaximumPulls ->
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
        if edge.Role = EdgeRole.SequencePullBound && edge.Ordinal = 0 && List.tryHead edge.Sources = Some owner then Some edge.Target else None) |> Set.ofList
    let finite = graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with SemanticKind.Obligation { Kind = "finite-sequence-pulls" } -> Some id | _ -> None) |> Set.ofList
    let edges = graph.Edges |> List.map (fun edge ->
        if finite.Contains edge.Target && edge.Role = EdgeRole.Constrains && (edge.Sources |> List.exists currents.Contains) then
            { edge with Sources = List.distinct (edge.Sources @ supports) }
        else edge)
    { graph with Edges = edges }

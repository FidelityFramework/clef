// SPDX-License-Identifier: MIT

/// Finite additive recurrences. Recognition cites the existing call-effect and
/// assignment projections; saturation reads their numeric premises jointly with
/// the range fixed point. Neither phase chooses a representation.
module Clef.Compiler.Baker.Recipes.LoopRangeRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations

type Inputs = {
    Operators: Map<NodeId, string * NodeId list>
    Assignments: Map<NodeId, NodeId list>
    Effects: Map<NodeId, Set<NodeId> * bool>
}

type Induction = {
    Owner: NodeId
    Loop: NodeId
    Guard: NodeId
    Cell: NodeId
    Initial: NodeId
    Limit: NodeId
    Step: NodeId
    Update: NodeId
    Store: NodeId
    Ascending: bool
    Inclusive: bool
}

type Accumulation = {
    Induction: Induction
    Cell: NodeId
    Initial: NodeId
    Delta: NodeId
    Update: NodeId
    Store: NodeId
}

type Recognition = {
    Accumulations: Accumulation list
    Edges: Hyperedge list
}

let private edge role sources target =
    { Class = EdgeClass.Range; Role = role; Sources = sources; Target = target; Ordinal = 0 }

let inductionSources (item: Induction) =
    [item.Owner; item.Guard; item.Cell; item.Initial; item.Limit; item.Step; item.Update; item.Store]

let accumulationSources (item: Accumulation) =
    [item.Induction.Loop; item.Induction.Cell; item.Initial; item.Store; item.Update; item.Delta]

/// Only a straight, owner-local integer recurrence is admitted here. In
/// particular a suspension does not confer privacy on a captured source cell.
let recognize (graph: SemanticGraph) (inputs: Inputs) : Recognition =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let node id = nodes.TryFind id
    let definition id =
        match node id with Some { Kind = SemanticKind.VarRef(_, Some cell) } -> Some cell | _ -> None
    let initial id =
        match node id with
        | Some { Kind = SemanticKind.Binding(_, true, _, _); Children = [value]; Type = ty } when Types.isIntegerType ty -> Some value
        | _ -> None
    let noEffects id =
        match inputs.Effects.TryFind id with Some (writes, false) -> writes.IsEmpty | _ -> false
    let captured =
        nodes.Values |> Seq.collect (fun item ->
            match item.Kind with
            | SemanticKind.Lambda(_, _, captures, _, _)
            | SemanticKind.SeqExpr(_, captures)
            | SemanticKind.LazyExpr(_, captures) -> captures |> Seq.choose (fun capture -> capture.SourceNodeId)
            | SemanticKind.EnvironmentRead(_, slot)
            | SemanticKind.EnvironmentBorrow(_, slot)
            | SemanticKind.EnvironmentWrite(_, slot, _) -> Seq.singleton slot
            | SemanticKind.AddressOf(operand, _) -> definition operand |> Option.toList |> Seq.ofList
            | _ -> Seq.empty) |> Set.ofSeq
    let rec stable allowed seen id =
        if Set.contains id seen then false else
        let seen = Set.add id seen
        match node id with
        | Some { Kind = SemanticKind.Literal(NativeLiteral.Int _ | NativeLiteral.UInt _) } -> true
        | Some { Kind = SemanticKind.VarRef(_, Some cell) } when Set.contains cell allowed -> true
        | Some { Kind = SemanticKind.VarRef(_, Some cell) } -> stable allowed seen cell
        | Some { Kind = SemanticKind.PatternBinding _ } -> true
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> stable allowed seen value
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) } -> stable allowed seen value
        | Some { Kind = SemanticKind.Application _ } ->
            match inputs.Operators.TryFind id with
            | Some (operation, args) when List.contains operation ["op_Addition"; "op_Subtraction"; "op_Multiply"; "op_UnaryNegation"] ->
                noEffects id && List.forall (stable allowed seen) args
            | _ -> false
        | _ -> false
    // Flatten sequencing only. Conditional stores, nested loops, exceptional
    // transfers and deferred bodies cannot become unconditional updates.
    let rec actions id =
        match node id with
        | Some { Kind = SemanticKind.Sequential ids } -> ids |> List.collect actions
        | _ -> [id]
    let store id =
        match node id with
        | Some { Kind = SemanticKind.Set(target, value) } -> definition target |> Option.map (fun cell -> cell, value)
        | _ -> None
    let allStores cell =
        nodes.Values |> Seq.choose (fun item ->
            store item.Id |> Option.bind (fun (target, value) -> if target = cell then Some(item.Id, value) else None)) |> Seq.toList
    let residual owner loop cell reason = edge (EdgeRole.LoopRangePending reason) [owner; loop] cell
    let recognizeLoop owner initialized reentry loop guard body =
        let writes = inputs.Effects.TryFind body |> Option.defaultValue (Set.empty, true) |> fst
        let cells = writes |> Set.toList |> List.filter (fun cell -> initial cell |> Option.isSome)
        let fail reason = [], (cells |> List.map (fun cell -> residual owner loop cell reason))
        let direct = actions body
        let guardShape =
            match inputs.Operators.TryFind guard with
            | Some (operation, [read; limit]) ->
                match definition read, operation with
                | Some cell, "op_LessThanOrEqual" -> Some(cell, limit, true, true)
                | Some cell, "op_LessThan" -> Some(cell, limit, true, false)
                | Some cell, "op_GreaterThanOrEqual" -> Some(cell, limit, false, true)
                | Some cell, "op_GreaterThan" -> Some(cell, limit, false, false)
                | _ -> None
            | _ -> None
        match guardShape with
        | None -> fail LoopRangeResidual.Guard
        | Some(cell, limit, ascending, inclusive) ->
            let directStores = direct |> List.choose (fun id -> store id |> Option.map (fun pair -> id, pair))
            let inductionStore = directStores |> List.filter (fun (_, (target, _)) -> target = cell)
            match initial cell, inductionStore with
            | Some seed, [set, (_, update)] when Set.contains cell initialized ->
                let step =
                    match inputs.Operators.TryFind update with
                    | Some(operation, [read; step]) when definition read = Some cell && operation = (if ascending then "op_Addition" else "op_Subtraction") -> Some step
                    | _ -> None
                if reentry then fail LoopRangeResidual.Reentry
                elif captured.Contains cell then fail LoopRangeResidual.CapturedCell
                elif not (noEffects guard) || not (stable Set.empty Set.empty limit) then fail LoopRangeResidual.Guard
                elif allStores cell <> [set, update] || inputs.Assignments.TryFind cell <> Some [update] then fail LoopRangeResidual.OtherWrites
                elif direct |> List.exists (fun id ->
                    match node id with
                    | Some { Kind = SemanticKind.IfThenElse _ | SemanticKind.WhileLoop _ | SemanticKind.Match _ | SemanticKind.CaseElimination _ | SemanticKind.TryWith _ | SemanticKind.TryFinally _ } -> true
                    | _ -> false) then fail LoopRangeResidual.ConditionalUpdate
                elif inputs.Effects.TryFind body |> Option.forall snd then fail LoopRangeResidual.UnknownEffect
                else
                    match step with
                    | None -> fail LoopRangeResidual.Step
                    | Some step when not (stable Set.empty Set.empty step) -> fail LoopRangeResidual.Step
                    | Some step ->
                        let induction = { Owner = owner; Loop = loop; Guard = guard; Cell = cell; Initial = seed; Limit = limit; Step = step; Update = update; Store = set; Ascending = ascending; Inclusive = inclusive }
                        // The backedge increment is the last assignment/action;
                        // every body delta therefore reads the guarded induction.
                        if List.tryLast direct <> Some set then fail LoopRangeResidual.ConditionalUpdate else
                        let admitted, pending =
                            cells |> List.filter ((<>) cell) |> List.fold (fun (accepted, pending) accumulator ->
                                let reject reason = accepted, residual owner loop accumulator reason :: pending
                                match initial accumulator, directStores |> List.filter (fun (_, (target, _)) -> target = accumulator) with
                                | Some seed, [assignment, (_, value)] when Set.contains accumulator initialized ->
                                    if captured.Contains accumulator then reject LoopRangeResidual.CapturedCell
                                    elif allStores accumulator <> [assignment, value] || inputs.Assignments.TryFind accumulator <> Some [value] then reject LoopRangeResidual.OtherWrites
                                    else
                                        match inputs.Operators.TryFind value with
                                        | Some("op_Addition", [read; delta]) when definition read = Some accumulator && stable (Set.singleton cell) Set.empty delta ->
                                            { Induction = induction; Cell = accumulator; Initial = seed; Delta = delta; Update = value; Store = assignment } :: accepted, pending
                                        | _ -> reject LoopRangeResidual.NonAdditive
                                | _ -> reject LoopRangeResidual.ConditionalUpdate) ([], [])
                        if admitted.IsEmpty then [], pending else
                        let relation = edge (EdgeRole.LoopInduction(ascending, inclusive)) (inductionSources induction) loop
                        admitted, relation :: pending @ (admitted |> List.map (fun item -> edge EdgeRole.LoopAccumulation (accumulationSources item) item.Cell))
            | _ -> fail LoopRangeResidual.ConditionalUpdate
    let rec walk owner initialized reentry seen id =
        if Set.contains id seen then [], [] else
        let seen = Set.add id seen
        match node id with
        | Some { Kind = SemanticKind.Sequential ids } ->
            let _, items, edges = ids |> List.fold (fun (initialized, items, edges) child ->
                let found, facts = walk owner initialized reentry seen child
                let initialized = if initial child |> Option.isSome then Set.add child initialized else initialized
                initialized, items @ found, edges @ facts) (initialized, [], [])
            items, edges
        | Some { Kind = SemanticKind.WhileLoop(guard, body) } ->
            let items, edges = recognizeLoop owner initialized reentry id guard body
            let nested, nestedEdges = walk owner initialized true seen body
            items @ nested, edges @ nestedEdges
        | Some { Kind = SemanticKind.IfThenElse(_, yes, no) } ->
            (yes :: Option.toList no) |> List.map (walk owner initialized reentry seen)
            |> List.fold (fun (xs, es) (ys, fs) -> xs @ ys, es @ fs) ([], [])
        | _ -> [], []
    let items, edges =
        nodes.Values |> Seq.choose (fun owner ->
            match owner.Kind with
            | SemanticKind.SeqExpr(generator, _) ->
                match node generator with
                | Some { Kind = SemanticKind.Lambda(_, body, _, _, LambdaContext.SeqGenerator) } -> Some(walk owner.Id Set.empty false Set.empty body)
                | _ -> None
            | _ -> None)
        |> Seq.fold (fun (xs, es) (ys, fs) -> xs @ ys, es @ fs) ([], [])
    { Accumulations = items; Edges = edges }

type Saturated = {
    Accumulation: Accumulation
    Trip: FiniteLoopTripModel
    Invariant: AdditiveLoopInvariantModel
}

/// Numeric conclusions are rebuilt from the current premise ranges. No bound
/// from a previous graph or narrowing round supplies its own premise.
let saturate (range: NodeId -> ValueRange) (item: Accumulation) : Result<Saturated, LoopRangeResidual> =
    let induction = item.Induction
    match range induction.Initial, range induction.Limit, range induction.Step, range item.Initial, range item.Delta with
    | ValueRange.Bounded(startLo, startHi), ValueRange.Bounded(limitLo, limitHi), ValueRange.Bounded(stepLo, _),
      ValueRange.Bounded(initialLo, initialHi), ValueRange.Bounded(deltaLo, deltaHi) when stepLo > 0I ->
        let start, limit = if induction.Ascending then startLo, limitHi else -startHi, -limitLo
        let distance = limit - start + (if induction.Inclusive then 1I else 0I)
        let count = if distance <= 0I then 0I else (distance + stepLo - 1I) / stepLo
        let trip = { InitialLower = start; LimitUpper = limit; MinimumStep = stepLo; Inclusive = induction.Inclusive; MaximumIterations = count }
        let invariant = {
            MaximumIterations = count; InitialLower = initialLo; InitialUpper = initialHi
            DeltaLower = deltaLo; DeltaUpper = deltaHi
            Lower = initialLo + count * min 0I deltaLo; Upper = initialHi + count * max 0I deltaHi }
        Ok { Accumulation = item; Trip = trip; Invariant = invariant }
    | _, _, ValueRange.Bounded(stepLo, _), _, _ when stepLo <= 0I -> Error LoopRangeResidual.Step
    | _ -> Error LoopRangeResidual.MissingBound

/// Replace only this recipe's range projection. Other proof incidences remain
/// resident; repeated range analysis retracts obsolete recurrence evidence.
let foldRelations (recognition: Recognition) (graph: SemanticGraph) =
    let retained =
        graph.Edges |> List.filter (fun edge ->
            match edge.Class, edge.Role with
            | EdgeClass.Range, (EdgeRole.LoopInduction _ | EdgeRole.LoopAccumulation | EdgeRole.LoopRangePending _) -> false
            | _ -> true)
    { graph with Edges = retained @ recognition.Edges }

let obligations (graph: SemanticGraph) (settled: Saturated list) : Enrichment =
    settled |> List.mapi (fun index result ->
        let item = result.Accumulation
        let (NodeId loopId), (NodeId cellId) = item.Induction.Loop, item.Cell
        let sources = inductionSources item.Induction @ accumulationSources item @ [item.Cell] |> List.distinct
        let subject = graph.Nodes[item.Cell]
        let make name kind statement body =
            let node = obligationNode subject index { Id = name; Kind = kind; Logic = "QF_LIA"; Statement = statement; Source = fmtRange subject.Range; Refs = []; Body = body }
            { NewNodes = [node]; NewEdges = [constrains sources node]; Annotated = [] }
        Enrichment.combine
            (make (sprintf "loop_trip_%d_%d" loopId cellId) "finite-loop-trip" "The admitted monotone guard and positive minimum step bound the number of complete iterations." (ObligationBody.FiniteLoopTrip result.Trip))
            (make (sprintf "loop_additive_%d_%d" loopId cellId) "additive-loop-invariant" "The admitted additive update preserves an enclosure at every iteration, including zero iterations and the final store." (ObligationBody.AdditiveLoopInvariant result.Invariant)))
    |> Enrichment.concat

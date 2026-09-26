// SPDX-License-Identifier: MIT

/// Finite additive and nonnegative linear recurrences. Recognition cites call-effect and
/// assignment projections; saturation reads their numeric premises jointly with
/// the range fixed point. Neither phase chooses a representation.
module Clef.Compiler.Baker.Recipes.LoopRangeRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module ExplicitDemand = Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand
module Evaluation = Clef.Compiler.Baker.Ingredients.Evaluation

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

type Coefficient = Constant of bigint | Value of NodeId

type LinearRecurrence = {
    Induction: Induction
    Cells: NodeId list
    Initials: NodeId list
    Coefficients: Coefficient list list
    /// A cell or actual intermediate, and its component in the common envelope.
    Targets: (NodeId * int) list
    Participants: NodeId list
}

type Recognition = {
    Accumulations: Accumulation list
    Linear: LinearRecurrence list
    Edges: Hyperedge list
}

let private edge role sources target =
    { Class = EdgeClass.Range; Role = role; Sources = sources; Target = target; Ordinal = 0 }

let inductionSources (item: Induction) =
    [item.Owner; item.Guard; item.Cell; item.Initial; item.Limit; item.Step; item.Update; item.Store]

let accumulationSources (item: Accumulation) =
    [item.Induction.Loop; item.Induction.Cell; item.Initial; item.Store; item.Update; item.Delta]

let linearSources (item: LinearRecurrence) =
    inductionSources item.Induction @ [item.Induction.Loop] @ item.Cells @ item.Initials @ item.Participants
    |> List.distinct

/// Only a straight, owner-local integer recurrence is admitted here. In
/// particular a suspension does not confer privacy on a captured source cell.
let recognize (graph: SemanticGraph) (inputs: Inputs) : Recognition =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let mutable linear = []
    let node id = nodes.TryFind id
    let sameTypes ids =
        match ids |> List.map (fun id -> node id |> Option.map (fun value -> applySubst value.Type)) with
        | Some first :: rest -> rest |> List.forall ((=) (Some first))
        | _ -> false
    let typeIs expected id = node id |> Option.exists (fun value -> applySubst value.Type = applySubst expected)
    let dimensionlessFactor cell factor =
        match node cell, node factor with
        | Some state, Some value ->
            match applySubst value.Type with
            | NativeType.TNum(_, dimension) ->
                dimension = Dimension.one && Types.isIntegerType (applySubst value.Type) &&
                Types.tryGetNTUKind (applySubst state.Type) = Types.tryGetNTUKind (applySubst value.Type)
            | _ -> false
        | _ -> false
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
    let edgeKey (item: Hyperedge) = item.Class, item.Role, item.Ordinal, item.Sources, item.Target
    let localOrder owner target expected =
        let actual = graph.Edges |> List.filter (fun item ->
            item.Class = EdgeClass.Evaluation && item.Target = target && List.tryHead item.Sources = Some owner)
        (List.map edgeKey actual |> List.sort) = (List.map edgeKey expected |> List.sort)
    let structuralAuthority id =
        match node id with
        | None -> false
        | Some value ->
            let expectedChildren =
                match value.Kind with
                | SemanticKind.Application(callee, arguments) -> Some(callee :: arguments)
                | SemanticKind.TypeAnnotation(inner, _) | SemanticKind.EagerExpr inner -> Some [inner]
                | SemanticKind.Yield inner -> Some [inner]
                | SemanticKind.Set(target, operand) -> Some [target; operand]
                | SemanticKind.WhileLoop(guard, body) -> Some [guard; body]
                | SemanticKind.Sequential children -> Some children
                | SemanticKind.VarRef _ | SemanticKind.Literal _ -> Some []
                | SemanticKind.Binding _ -> if value.Children.Length = 1 then Some value.Children else None
                | SemanticKind.PatternBinding _ -> Some value.Children
                | _ -> None
            match expectedChildren with
            | Some children when value.Children = children && (children |> List.forall nodes.ContainsKey) ->
                let expected = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence value |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Role = EdgeRole.Definition)
                let actual = graph.Edges |> List.filter (fun edge -> edge.Target = id && (edge.Class = EdgeClass.Structural || edge.Role = EdgeRole.Definition))
                // Kind/Children provide canonical source incidence before a
                // materialization pass stores redundant rows. Any resident row
                // must agree exactly, and duplication cannot add authority.
                let resident = List.map edgeKey actual
                let canonical = List.map edgeKey expected |> Set.ofList
                resident.Length = (Set.ofList resident).Count && List.forall canonical.Contains resident &&
                (match value.Kind with
                 | SemanticKind.VarRef(_, Some definition) -> sameTypes [id; definition]
                 | SemanticKind.VarRef(_, None) -> false
                 | SemanticKind.TypeAnnotation(inner, annotation) -> sameTypes [id; inner] && applySubst value.Type = applySubst annotation
                 | SemanticKind.Application(callee, arguments) ->
                     let rec supplied signature remaining =
                         match remaining, applySubst signature with
                         | [], result -> result = applySubst value.Type
                         | argument :: rest, NativeType.TFun(parameter, result) ->
                             typeIs parameter argument && supplied result rest
                         | _ -> false
                     node callee |> Option.exists (fun callee -> supplied callee.Type arguments)
                 | _ -> true)
            | _ -> false
    let rec valueAuthority seen id =
        if Set.contains id seen then false else
        let seen = Set.add id seen
        if not (structuralAuthority id) then false else
        match node id with
        | Some { Kind = SemanticKind.VarRef(_, Some definition) } ->
            match node definition with
            | Some { Kind = SemanticKind.Binding(_, false, _, _) } -> valueAuthority seen definition
            | _ -> true
        | Some { Kind = SemanticKind.Application(_, arguments) } -> List.forall (valueAuthority seen) arguments
        | Some { Kind = SemanticKind.Binding _; Children = [value] } -> sameTypes [id; value] && valueAuthority seen value
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) | SemanticKind.EagerExpr value } -> valueAuthority seen value
        | Some { Kind = SemanticKind.Set(target, value) } ->
            match definition target with
            | Some cell -> sameTypes [cell; target; value] && valueAuthority seen target && valueAuthority seen value
            | _ -> false
        | _ -> true
    let rec orderedActions owner id =
        match node id with
        | Some { Kind = SemanticKind.Sequential children; Children = actual } when actual = children ->
            let operands = List.indexed children
            let expected = (operands |> List.map (fun (slot, value) -> Evaluation.operand owner id slot EvaluationAccess.Value value)) @ Evaluation.ordered owner id operands EvaluationTransfer.Continue
            if not (localOrder owner id expected) then None else
            let nested = children |> List.map (orderedActions owner)
            if List.exists Option.isNone nested then None else
            let actions, participants = nested |> List.choose (fun value -> value) |> List.unzip
            Some(List.concat actions, id :: List.concat participants)
        | Some _ -> Some([id], [id])
        | None -> None
    let storeOrder owner id =
        match node id with
        | Some { Kind = SemanticKind.Set(target, value); Children = [actualTarget; actualValue] }
            when target = actualTarget && value = actualValue ->
            localOrder owner id
                ([Evaluation.operand owner id 0 EvaluationAccess.Storage target
                  Evaluation.operand owner id 1 EvaluationAccess.Value value] @
                 Evaluation.ordered owner id [1, value] EvaluationTransfer.Continue)
        | _ -> false
    let explicitSnapshot owner binding =
        match node binding with
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [initializer] } ->
            match ExplicitDemand.direct graph initializer with
            | Ok(Some marker) ->
                let rows = graph.Edges |> List.filter (fun item ->
                    item.Target = binding && (item.Role = EdgeRole.EagerDemand EagerFrontier.Binding || item.Role = EdgeRole.EagerDemandPending))
                let expected = marker.Marker :: marker.Operand :: marker.Wrappers
                match rows with
                | [row] when row.Class = EdgeClass.Demand && row.Ordinal = 0 && row.Sources = expected &&
                             localOrder owner binding
                                 ([Evaluation.operand owner binding 0 EvaluationAccess.Value initializer] @
                                  Evaluation.ordered owner binding [0, initializer] EvaluationTransfer.Continue) ->
                    Some(marker.Operand, binding :: expected)
                | _ -> None
            | _ -> None
        | _ -> None
    let linearLoop (induction: Induction) initialized body cells =
        let localCells = cells |> List.filter ((<>) induction.Cell)
        let candidate cell =
            match initial cell, allStores cell with
            | Some seed, [assignment, value] when Set.contains cell initialized && not (captured.Contains cell) &&
                                                sameTypes [cell; seed; value] && typeIs Types.unitType assignment &&
                                                inputs.Assignments.TryFind cell = Some [value] && storeOrder induction.Owner assignment ->
                Some(seed, assignment, value)
            | _ -> None
        let inductionTypes =
            sameTypes [induction.Cell; induction.Initial; induction.Limit; induction.Step; induction.Update] &&
            typeIs Types.boolType induction.Guard && typeIs Types.unitType induction.Store &&
            (match inputs.Operators.TryFind induction.Update, inputs.Operators.TryFind induction.Guard with
             | Some(_, [read; _]), Some(_, [guardRead; _]) -> sameTypes [induction.Cell; read; guardRead]
             | _ -> false)
        let loopOperands = [0, induction.Guard; 1, body]
        let link = Evaluation.flow induction.Owner induction.Loop loopOperands
        let loopOrder =
            localOrder induction.Owner induction.Loop
                ([Evaluation.operand induction.Owner induction.Loop 0 EvaluationAccess.Value induction.Guard
                  Evaluation.operand induction.Owner induction.Loop 1 EvaluationAccess.Value body
                  link EvaluationPort.Entry (EvaluationPort.OperandEntry 0) EvaluationTransfer.Continue
                  link (EvaluationPort.OperandExit 0) (EvaluationPort.OperandEntry 1) EvaluationTransfer.WhenTrue
                  link (EvaluationPort.OperandExit 0) EvaluationPort.Ready EvaluationTransfer.WhenFalse
                  link (EvaluationPort.OperandExit 1) (EvaluationPort.OperandEntry 0) EvaluationTransfer.Continue
                  link EvaluationPort.Ready EvaluationPort.Exit EvaluationTransfer.Continue])
        let admit recurrence =
            let participants = linearSources recurrence |> List.filter (fun id -> id <> induction.Owner)
            if List.forall (valueAuthority Set.empty) participants then Some recurrence else None
        if not inductionTypes || not loopOrder then None else
        match orderedActions induction.Owner body with
        | None -> None
        | Some(ordered, orderParticipants) ->
            let baseParticipants = orderParticipants @ [body]
            match localCells with
            | [cell] ->
                match candidate cell with
                | Some(seed, assignment, update) when List.contains assignment ordered ->
                    match inputs.Operators.TryFind update with
                    | Some("op_Multiply", [read; factor]) when definition read = Some cell && sameTypes [cell; read] &&
                                                             dimensionlessFactor cell factor && stable Set.empty Set.empty factor ->
                        admit {
                            Induction = induction; Cells = [cell]; Initials = [seed]
                            Coefficients = [[Value factor]]; Targets = [cell, 0; update, 0]
                            Participants = baseParticipants @ [assignment; update; read; factor]
                        }
                    | _ -> None
                | _ -> None
            | [left; right] ->
                // Id order is not update order. Try both assignments of the two
                // actual cells to a' = b; b' = the explicitly demanded a+b.
                [left, right; right, left] |> List.tryPick (fun (a, b) ->
                    match candidate a, candidate b with
                    | Some(aSeed, aStore, aValue), Some(bSeed, bStore, bValue) when definition aValue = Some b ->
                        match definition bValue with
                        | Some temp ->
                            match explicitSnapshot induction.Owner temp with
                            | Some(sum, demandParticipants) ->
                                match inputs.Operators.TryFind sum with
                                | Some("op_Addition", [first; second]) when
                                    sameTypes ([a; b; aSeed; bSeed; aValue; bValue; temp; sum; first; second] @ demandParticipants) &&
                                    ((definition first = Some a && definition second = Some b) ||
                                     (definition first = Some b && definition second = Some a)) ->
                                    let position id = List.tryFindIndex ((=) id) ordered
                                    match position temp, position aStore, position bStore with
                                    | Some snapshot, Some firstStore, Some secondStore when snapshot < firstStore && firstStore < secondStore ->
                                        admit {
                                            Induction = induction; Cells = [a; b]; Initials = [aSeed; bSeed]
                                            Coefficients = [[Constant 0I; Constant 1I]; [Constant 1I; Constant 1I]]
                                            Targets = [a, 0; aValue, 0; b, 1; bValue, 1; temp, 1; sum, 1] @
                                                      (demandParticipants |> List.filter ((<>) temp) |> List.map (fun id -> id, 1))
                                            Participants = baseParticipants @ demandParticipants @ [aStore; aValue; bStore; bValue; sum; first; second]
                                        }
                                    | _ -> None
                                | _ -> None
                            | _ -> None
                        | _ -> None
                    | _ -> None)
            | _ -> None
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
                        match linearLoop induction initialized body cells with
                        | Some recurrence ->
                            linear <- recurrence :: linear
                            [], edge (EdgeRole.LoopInduction(ascending, inclusive)) (inductionSources induction) loop ::
                                (recurrence.Targets |> List.map (fun (target, _) -> edge EdgeRole.LoopLinearRecurrence (linearSources recurrence) target))
                        | None ->
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
    { Accumulations = items; Linear = List.rev linear; Edges = edges }

type Saturated = {
    Accumulation: Accumulation
    Trip: FiniteLoopTripModel
    Invariant: AdditiveLoopInvariantModel
}

type LinearSaturated = {
    Recurrence: LinearRecurrence
    Trip: FiniteLoopTripModel
    Invariant: FiniteLinearRecurrenceModel
    WorkBits: bigint
}

let private finiteTrip range (induction: Induction) =
    match range induction.Initial, range induction.Limit, range induction.Step with
    | ValueRange.Bounded(startLo, startHi), ValueRange.Bounded(limitLo, limitHi), ValueRange.Bounded(stepLo, _) when stepLo > 0I ->
        let start, limit = if induction.Ascending then startLo, limitHi else -startHi, -limitLo
        let distance = limit - start + (if induction.Inclusive then 1I else 0I)
        let count = if distance <= 0I then 0I else (distance + stepLo - 1I) / stepLo
        Ok { InitialLower = start; LimitUpper = limit; MinimumStep = stepLo; Inclusive = induction.Inclusive; MaximumIterations = count }
    | _, _, ValueRange.Bounded(stepLo, _) when stepLo <= 0I -> Error LoopRangeResidual.Step
    | _ -> Error LoopRangeResidual.MissingBound

/// A compiler-work limit, not a source-width limit. Each exact scalar operation
/// and retained certificate integer is charged before allocation. The bounded
/// owner API below also permits callers/tests to supply a different work budget.
let defaultCertificateBits = 1048576I
exception private RecurrenceBudgetExceeded

/// Only current numeric premises feed the certificate. In particular no prior
/// cell/update conclusion may supply its own seed or transition coefficient.
let saturateLinearWithBudget maximumBits range (item: LinearRecurrence) : Result<LinearSaturated, LoopRangeResidual> =
    let bounded id = match range id with ValueRange.Bounded(lo, hi) when 0I <= lo && lo <= hi -> Some(lo, hi) | _ -> None
    let seeds = item.Initials |> List.map bounded
    let coefficients = item.Coefficients |> List.map (List.map (function Constant value when value >= 0I -> Some(value, value) | Value id -> bounded id | _ -> None))
    match finiteTrip range item.Induction with
    | Error reason -> Error reason
    | Ok _ when (seeds |> List.exists Option.isNone) || (coefficients |> List.exists (List.exists Option.isNone)) -> Error LoopRangeResidual.MissingBound
    | Ok trip ->
      try
        let mutable used = 0I
        let charge bits =
            if bits < 0I || used + bits > maximumBits then raise RecurrenceBudgetExceeded
            used <- used + bits
        let bits (value: bigint) = max 1I (bigint(value.GetBitLength()))
        let retain value = charge (bits value)
        let product (left: bigint) (right: bigint) =
            charge (if left.IsZero || right.IsZero then 1I else bits left + bits right)
            left * right
        let add left right =
            charge (1I + max (bits left) (bits right))
            left + right
        let dot left right = List.map2 product left right |> List.fold add 0I
        let multiply left right =
            let columns = List.transpose right
            left |> List.map (fun row -> columns |> List.map (dot row))
        let lower, upper = seeds |> List.choose (fun value -> value) |> List.unzip
        let coefficients = coefficients |> List.map (List.choose (fun value -> value))
        let matrixLower = coefficients |> List.map (List.map fst)
        let matrixUpper = coefficients |> List.map (List.map snd)
        [trip.InitialLower; trip.LimitUpper; trip.MinimumStep; trip.MaximumIterations] @
            lower @ upper @ List.concat matrixLower @ List.concat matrixUpper |> List.iter retain
        let project matrix = matrix |> List.map (fun row -> dot row upper)
        if not (List.forall2 (<=) upper (project matrixUpper)) then Error LoopRangeResidual.NonAdditive else
        let size = upper.Length
        let identity = List.init size (fun row -> List.init size (fun column -> if row = column then 1I else 0I))
        let rec exponentBits value acc =
            if value = 0I then acc else
            charge (bits value + 1I)
            exponentBits (value / 2I) ((value % 2I = 1I) :: acc)
        let _, power, steps =
            exponentBits trip.MaximumIterations [] |> List.fold (fun (exponent, power, steps) odd ->
                let squared = multiply power power
                let next = if odd then multiply squared matrixUpper else squared
                let exponent = add (product 2I exponent) (if odd then 1I else 0I)
                exponent :: List.concat next |> List.iter retain
                exponent, next, { Odd = odd; Exponent = exponent; Matrix = next } :: steps) (0I, identity, [])
        let model = {
            MaximumIterations = trip.MaximumIterations; InitialLower = lower; InitialUpper = upper
            CoefficientLower = matrixLower; CoefficientUpper = matrixUpper; Powers = List.rev steps
            Lower = List.replicate size 0I; Upper = project power }
        model.Lower @ model.Upper |> List.iter retain
        Ok { Recurrence = item; Trip = trip; Invariant = model; WorkBits = used }
      with RecurrenceBudgetExceeded -> Error LoopRangeResidual.ProofResources

let saturateLinear range item = saturateLinearWithBudget defaultCertificateBits range item

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
            | EdgeClass.Range, (EdgeRole.LoopInduction _ | EdgeRole.LoopAccumulation | EdgeRole.LoopLinearRecurrence | EdgeRole.LoopRangePending _) -> false
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

let linearObligations (graph: SemanticGraph) (settled: LinearSaturated list) : Enrichment =
    settled |> List.mapi (fun index result ->
        let item = result.Recurrence
        let (NodeId loopId), (NodeId cellId) = item.Induction.Loop, item.Cells.Head
        let sources = linearSources item
        let subject = graph.Nodes[item.Cells.Head]
        let make name kind statement body =
            let node = obligationNode subject index { Id = name; Kind = kind; Logic = "QF_LIA"; Statement = statement; Source = fmtRange subject.Range; Refs = []; Body = body }
            { NewNodes = [node]; NewEdges = [constrains sources node]; Annotated = [] }
        Enrichment.combine
            (make (sprintf "loop_trip_linear_%d_%d" loopId cellId) "finite-loop-trip" "The actual monotone induction bounds all completed iterations." (ObligationBody.FiniteLoopTrip result.Trip))
            (make (sprintf "loop_linear_%d_%d" loopId cellId) "finite-linear-recurrence" "The nonnegative transition enclosure covers every ordered update through the final iteration, certified by exact matrix powers." (ObligationBody.FiniteLinearRecurrence result.Invariant)))
    |> Enrichment.concat

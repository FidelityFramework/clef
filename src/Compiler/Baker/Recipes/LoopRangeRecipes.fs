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

/// Complete ordinary call correspondences, projected by the existing range reader.
type TailInputs = {
    Calls: Map<NodeId, NodeId * NodeId list * NodeId list>
    Suppliers: Map<NodeId, (NodeId * NodeId) list>
    OpenParameters: Set<NodeId>
}

/// Immutable simultaneous parameters are not mutable loop stores.
type TailRecurrence = {
    Owner: NodeId
    Guard: NodeId
    Call: NodeId
    Counter: NodeId
    Step: NodeId
    CounterUpdate: NodeId
    Entries: (NodeId * NodeId list * NodeId) list
    Matrix: bigint list list
    Targets: (NodeId * int) list
    Participants: NodeId list
}

type Recognition = {
    Accumulations: Accumulation list
    Linear: LinearRecurrence list
    Tail: TailRecurrence list
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
    { Accumulations = items; Linear = List.rev linear; Tail = []; Edges = edges }

/// Admit an exact closed tail transition. Only entry actuals seed the numeric
/// certificate; a recursive formal or an earlier recurrence result cannot do so.
let recognizeTail (graph: SemanticGraph) (inputs: Inputs) (calls: TailInputs) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let node id = nodes.TryFind id
    let sameType left right =
        match node left, node right with
        | Some left, Some right -> applySubst left.Type = applySubst right.Type
        | _ -> false
    let reference formal id =
        match node id with
        | Some { Kind = SemanticKind.VarRef(_, Some actual); Children = [] } -> actual = formal && sameType formal id
        | _ -> false
    let zero id = match node id with Some { Kind = SemanticKind.Literal(NativeLiteral.Int(0L, _)) } -> true | _ -> false
    let authority id =
        match node id with
        | None -> false
        | Some value ->
            let children =
                match value.Kind with
                | SemanticKind.Lambda(parameters, body, _, _, _) ->
                    if value.Children = [body] then [body] else (parameters |> List.map (fun (_, _, id) -> id)) @ [body]
                | SemanticKind.IfThenElse(guard, yes, no) -> guard :: yes :: Option.toList no
                | SemanticKind.Application(callee, arguments) -> callee :: arguments
                | SemanticKind.VarRef _ | SemanticKind.Literal _ -> []
                | _ -> value.Children
            let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
            let source (edge: Hyperedge) = edge.Class = EdgeClass.Structural || edge.Role = EdgeRole.Definition
            let expected = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence value |> List.filter source |> List.map key |> Set.ofList
            let actual = graph.Edges |> List.filter (fun edge -> edge.Target = id && source edge) |> List.map key
            children = value.Children && List.forall nodes.ContainsKey children &&
            actual.Length = (Set.ofList actual).Count && List.forall expected.Contains actual &&
            (match value.Kind with
             | SemanticKind.VarRef(_, Some definition) -> sameType id definition
             | SemanticKind.VarRef(_, None) -> false
             | _ -> true)
    let owner id =
        let mutable pending = Some id
        let mutable seen = Set.empty
        let mutable found = None
        while pending.IsSome do
            let current = pending.Value
            if seen.Contains current then pending <- None
            else
                seen <- seen.Add current
                match node current with
                | Some { Kind = SemanticKind.Lambda _ } -> found <- Some current; pending <- None
                | Some value -> pending <- value.Parent
                | _ -> pending <- None
        found
    // Owner-local postorder worklists visit each node once. Active-path checks
    // reject source cycles; shared subexpressions retain their exact incidence.
    let seedSupport (forbidden: Set<NodeId>) id =
        let mutable pending = [id, false]
        let mutable active = Set.empty
        let mutable completed = Set.empty
        let mutable valid = true
        while valid && not pending.IsEmpty do
            let (current, finish) = pending.Head
            pending <- pending.Tail
            if finish then
                active <- active.Remove current
                completed <- completed.Add current
            elif forbidden.Contains current || active.Contains current then valid <- false
            elif not (completed.Contains current) then
                match node current with
                | Some value when authority current ->
                    match value.Kind with
                    | SemanticKind.Lambda _ -> valid <- false
                    | _ ->
                        let children = match value.Kind with SemanticKind.VarRef(_, Some definition) -> [definition] | _ -> value.Children
                        active <- active.Add current
                        pending <- (children |> List.map (fun child -> child, false)) @ ((current, true) :: pending)
                | _ -> valid <- false
        if valid then Some(Set.toList completed) else None
    nodes.Values |> Seq.choose (fun lambda ->
        match lambda.Kind with
        | SemanticKind.Lambda(parameters, body, captures, _, _) when captures.IsEmpty && (parameters.Length = 2 || parameters.Length = 3) ->
            let formals = parameters |> List.map (fun (_, _, id) -> id)
            let counter = List.last formals
            let states = formals |> List.take (formals.Length - 1)
            let coefficients id =
                let mutable pending = [id, false]
                let mutable active = Set.empty
                let mutable rows: Map<NodeId, bigint list * Set<NodeId>> = Map.empty
                let mutable valid = true
                while valid && not pending.IsEmpty do
                    let (current, finish) = pending.Head
                    pending <- pending.Tail
                    if finish then
                        match inputs.Operators.TryFind current with
                        | Some("op_Addition", [left; right]) when rows.ContainsKey left && rows.ContainsKey right ->
                            let a, xs = rows[left]
                            let b, ys = rows[right]
                            rows <- rows.Add(current, (List.map2 (+) a b, Set.union xs ys |> Set.add current))
                            active <- active.Remove current
                        | _ -> valid <- false
                    elif active.Contains current then valid <- false
                    elif not (rows.ContainsKey current) then
                        if not (authority current) then valid <- false else
                        match states |> List.tryFindIndex (fun formal -> reference formal current) with
                        | Some index ->
                            rows <- rows.Add(current, (List.init states.Length (fun position -> if position = index then 1I else 0I), Set.singleton current))
                        | None ->
                            match inputs.Operators.TryFind current with
                            | Some("op_Addition", [left; right]) when sameType current left && sameType current right ->
                                active <- active.Add current
                                pending <- (left, false) :: (right, false) :: (current, true) :: pending
                            | _ -> valid <- false
                if valid then rows.TryFind id |> Option.map (fun (row, support) -> row, Set.toList support) else None
            let family = calls.Calls |> Map.toList |> List.choose (fun (site, (target, actualFormals, actuals)) ->
                if target = lambda.Id then Some(site, actualFormals, actuals) else None)
            let closed =
                not family.IsEmpty && authority lambda.Id &&
                (parameters |> List.forall (fun (_, ty, id) -> node id |> Option.exists (fun formal ->
                    applySubst formal.Type = applySubst ty && formal.Parent = Some lambda.Id))) &&
                (formals |> List.forall (fun formal -> not (calls.OpenParameters.Contains formal))) &&
                (family |> List.forall (fun (_, actualFormals, actuals) ->
                    actualFormals = formals && actuals.Length = formals.Length && List.forall2 sameType formals actuals)) &&
                (formals |> List.indexed |> List.forall (fun (index, formal) ->
                    let expected = family |> List.map (fun (site, _, actuals) -> site, actuals[index]) |> Set.ofList
                    let supplied = calls.Suppliers.TryFind formal |> Option.defaultValue [] |> Set.ofList
                    supplied = expected))
            match node counter, node body with
            | Some count, Some { Kind = SemanticKind.IfThenElse(guard, yes, Some no) } when
                closed && Types.isIntegerType count.Type &&
                (match applySubst count.Type with NativeType.TNum(_, dimension) -> dimension = Dimension.one | _ -> false) &&
                (states |> List.forall (fun id -> node id |> Option.exists (fun state -> Types.isIntegerType state.Type && sameType id states.Head))) &&
                authority body &&
                (match inputs.Effects.TryFind body with Some(writes, false) -> writes.IsEmpty | _ -> false) ->
                let continuing =
                    match inputs.Operators.TryFind guard with
                    | Some("op_LessThanOrEqual", [read; limit]) when reference counter read && zero limit && sameType counter limit -> Some(yes, no, [read; limit])
                    | Some("op_GreaterThan", [read; limit]) when reference counter read && zero limit && sameType counter limit -> Some(no, yes, [read; limit])
                    | _ -> None
                match continuing with
                | Some(baseCase, self, guardSupport) when authority guard && (states |> List.exists (fun formal -> reference formal baseCase)) ->
                    match family |> List.tryFind (fun (site, _, _) -> site = self) with
                    | Some(_, _, actuals) when authority self && owner self = Some lambda.Id ->
                        let updates = actuals |> List.take states.Length
                        let counterUpdate = List.last actuals
                        match inputs.Operators.TryFind counterUpdate with
                        | Some("op_Subtraction", [read; step]) when reference counter read && sameType counterUpdate counter && sameType counter step && authority counterUpdate ->
                            let positive = match node step with Some { Kind = SemanticKind.Literal(NativeLiteral.Int(value, _)) } -> value > 0L | _ -> false
                            let rows = updates |> List.map coefficients
                            let entries = family |> List.filter (fun (site, _, _) -> site <> self)
                            let forbidden = Set.ofList (lambda.Id :: body :: counterUpdate :: formals @ updates)
                            let supports = entries |> List.map (fun (site, _, actuals) ->
                                if owner site = Some lambda.Id || not (authority site) then None
                                else actuals |> List.map (seedSupport forbidden) |> fun support ->
                                    if List.exists Option.isNone support then None else Some(site :: (support |> List.choose id |> List.concat)))
                            if not positive || entries.IsEmpty || List.exists Option.isNone rows || List.exists Option.isNone supports then None
                            else
                                let matrix, transitionSupport = rows |> List.choose id |> List.unzip
                                let participants = lambda.Id :: body :: guard :: baseCase :: self :: counterUpdate :: read :: step ::
                                                   (formals @ guardSupport @ List.concat transitionSupport @ (supports |> List.choose id |> List.concat)) |> List.distinct
                                Some { Owner = lambda.Id; Guard = guard; Call = self; Counter = counter; Step = step; CounterUpdate = counterUpdate
                                       Entries = entries |> List.map (fun (site, _, actuals) -> site, List.take states.Length actuals, List.last actuals)
                                       Matrix = matrix; Targets = (List.indexed states @ List.indexed updates) |> List.map (fun (index, id) -> id, index)
                                       Participants = participants }
                        | _ -> None
                    | _ -> None
                | _ -> None
            | _ -> None
        | _ -> None) |> Seq.toList

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

/// Check a finite nonnegative numeric enclosure. The caller separately proves
/// the source transition and activation bound; no loop or storage fact follows
/// merely from this literal certificate.
let certifyLinearWithBudget maximumBits maximumIterations
                            (lower: bigint list) (upper: bigint list)
                            (matrixLower: bigint list list) (matrixUpper: bigint list list)
                            : Result<FiniteLinearRecurrenceModel * bigint, LoopRangeResidual> =
    let size = upper.Length
    let square (matrix: bigint list list) = matrix.Length = size && matrix |> List.forall (fun row -> row.Length = size)
    if (size <> 1 && size <> 2) || lower.Length <> size || not (square matrixLower && square matrixUpper) ||
       maximumIterations < 0I || not (List.forall2 (fun lo hi -> 0I <= lo && lo <= hi) lower upper) ||
       not (List.forall2 (List.forall2 (fun lo hi -> 0I <= lo && lo <= hi)) matrixLower matrixUpper) then
        Error LoopRangeResidual.MissingBound
    else
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
        [maximumIterations] @
            lower @ upper @ List.concat matrixLower @ List.concat matrixUpper |> List.iter retain
        let project matrix = matrix |> List.map (fun row -> dot row upper)
        if not (List.forall2 (<=) upper (project matrixUpper)) then Error LoopRangeResidual.NonAdditive else
        let identity = List.init size (fun row -> List.init size (fun column -> if row = column then 1I else 0I))
        let rec exponentBits value acc =
            if value = 0I then acc else
            charge (bits value + 1I)
            exponentBits (value / 2I) ((value % 2I = 1I) :: acc)
        let _, power, steps =
            exponentBits maximumIterations [] |> List.fold (fun (exponent, power, steps) odd ->
                let squared = multiply power power
                let next = if odd then multiply squared matrixUpper else squared
                let exponent = add (product 2I exponent) (if odd then 1I else 0I)
                exponent :: List.concat next |> List.iter retain
                exponent, next, { Odd = odd; Exponent = exponent; Matrix = next } :: steps) (0I, identity, [])
        let model = {
            MaximumIterations = maximumIterations; InitialLower = lower; InitialUpper = upper
            CoefficientLower = matrixLower; CoefficientUpper = matrixUpper; Powers = List.rev steps
            Lower = List.replicate size 0I; Upper = project power }
        model.Lower @ model.Upper |> List.iter retain
        Ok(model, used)
      with RecurrenceBudgetExceeded -> Error LoopRangeResidual.ProofResources

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
        let lower, upper = seeds |> List.choose id |> List.unzip
        let coefficients = coefficients |> List.map (List.choose id)
        let matrixLower = coefficients |> List.map (List.map fst)
        let matrixUpper = coefficients |> List.map (List.map snd)
        certifyLinearWithBudget maximumBits trip.MaximumIterations lower upper matrixLower matrixUpper
        |> Result.map (fun (model, used) -> { Recurrence = item; Trip = trip; Invariant = model; WorkBits = used })

let saturateLinear range item = saturateLinearWithBudget defaultCertificateBits range item

type TailSaturated = {
    Recurrence: TailRecurrence
    Certificates: (NodeId * FiniteLoopTripModel * FiniteLinearRecurrenceModel) list
    Ranges: Map<NodeId, ValueRange>
}

/// Each entry retains its tuple/trip correlation. Recursive inputs and previous
/// conclusions are deliberately absent from these numeric premises.
let saturateTailWithBudget maximumBits range (item: TailRecurrence) =
    let bounded id = match range id with ValueRange.Bounded(lo, hi) when 0I <= lo && lo <= hi -> Some(lo, hi) | _ -> None
    match bounded item.Step with
    | Some(stepLo, stepHi) when stepLo > 0I ->
        item.Entries |> List.fold (fun result (site, seeds, count) ->
            match result, bounded count, seeds |> List.map bounded with
            | Ok(certificates, ranges, budget), Some(countLo, countHi), seedRanges when List.forall Option.isSome seedRanges ->
                let lower, upper = seedRanges |> List.choose id |> List.unzip
                let iterations = (countHi + stepLo - 1I) / stepLo
                match certifyLinearWithBudget budget iterations lower upper item.Matrix item.Matrix with
                | Error reason -> Error reason
                | Ok(model, used) ->
                    let trip = { InitialLower = -countHi; LimitUpper = 0I; MinimumStep = stepLo; Inclusive = false; MaximumIterations = iterations }
                    let values = item.Targets |> List.map (fun (id, index) -> id, ValueRange.Bounded(model.Lower[index], model.Upper[index]))
                    let counter = ValueRange.Bounded(min countLo (min 0I (1I - stepHi)), countHi)
                    let ranges = (item.Counter, counter) :: (item.CounterUpdate, counter) :: values |> List.fold (fun ranges (id, range) ->
                        Map.add id (ValueRange.join (Map.tryFind id ranges |> Option.defaultValue ValueRange.Empty) range) ranges) ranges
                    Ok((site, trip, model) :: certificates, ranges, budget - used)
            | Error reason, _, _ -> Error reason
            | _ -> Error LoopRangeResidual.MissingBound) (Ok([], Map.empty, maximumBits))
        |> Result.map (fun (certificates, ranges, _) -> { Recurrence = item; Certificates = List.rev certificates; Ranges = ranges })
    | Some _ -> Error LoopRangeResidual.Step
    | _ -> Error LoopRangeResidual.MissingBound

let saturateTail range item = saturateTailWithBudget defaultCertificateBits range item

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

let private obligationsCore (graph: SemanticGraph) (settled: Saturated list) : Enrichment =
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

let obligations graph settled =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> obligationsCore graph settled)

let private linearObligationsCore (graph: SemanticGraph) (settled: LinearSaturated list) : Enrichment =
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

let linearObligations graph settled =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> linearObligationsCore graph settled)

let tailObligations graph (settled: TailSaturated list) =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () ->
    settled |> List.collect (fun result ->
        let item = result.Recurrence
        let subject = graph.Nodes[item.Counter]
        let (NodeId owner) = item.Owner
        result.Certificates |> List.mapi (fun index (site, trip, model) ->
            let (NodeId call) = site
            let make name kind statement body =
                let node = obligationNode subject index { Id = name; Kind = kind; Logic = "QF_LIA"; Statement = statement; Source = fmtRange subject.Range; Refs = []; Body = body }
                { NewNodes = [node]; NewEdges = [constrains item.Participants node]; Annotated = [] }
            Enrichment.combine
                (make (sprintf "tail_trip_%d_%d" owner call) "finite-loop-trip" "The closed entry tuple and positive counter decrement bound all continuing tail transitions." (ObligationBody.FiniteLoopTrip trip))
                (make (sprintf "tail_linear_%d_%d" owner call) "finite-linear-recurrence" "The source-backed simultaneous parameter transition preserves this enclosure through the final invocation." (ObligationBody.FiniteLinearRecurrence model))))
    |> Enrichment.concat)

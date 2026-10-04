// SPDX-License-Identifier: MIT

/// Source guard occurrences survive a continuation rewrite only through the
/// checked action dispatch and closed storage census. No range annotation or
/// previously issued numeric certificate supplies a guard or a bound here.
module Clef.Compiler.Baker.Recipes.ContinuationGuardRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Control = Clef.Compiler.Baker.Recipes.SequenceControlRecipes
module Sources = Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes
module Current = Clef.Compiler.PSGSaturation.SemanticGraph.ContinuationCurrentInputs
module Ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress
module Incidence = Clef.Compiler.Baker.Ingredients.Closures
module Machine = Clef.Compiler.Baker.Recipes.SequenceMachineRecipes

type GuardedRead = {
    Read: NodeId
    Cell: NodeId
    Guard: NodeId
    Operand: NodeId
    Polarity: bool
    Participants: NodeId list
}

type private Fact = {
    Source: NodeId
    Guard: NodeId
    Polarity: bool
    Cells: Set<NodeId>
}

let private single = function [value] -> Some value | _ -> None
let private comparisons =
    Set.ofList ["op_LessThan"; "op_LessThanOrEqual"; "op_GreaterThan";
                "op_GreaterThanOrEqual"; "op_Equality"; "op_Inequality"]

/// effectAt names current action writes and uncertainty, never numeric facts.
/// A complete closed slot census can discharge an unrelated call effect for
/// that private cell; all observed writes still kill its earlier observation.
let forGraph (graph: SemanticGraph) (effectAt: NodeId -> Set<NodeId> * bool) : GuardedRead list =
    let ingress = lazy (Ingress.analyze graph)
    let node id = graph.Nodes.TryFind id
    let live id = node id |> Option.filter _.IsReachable
    let same left right =
        match node left, node right with
        | Some left, Some right -> applySubst left.Type = applySubst right.Type
        | _ -> false
    // Keep complete row lists: indexing must not hide duplicate provenance.
    // These indexes live only for this immutable graph reading.
    let originRows =
        graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ContinuationValue)
        |> List.groupBy _.Target |> Map.ofList
    let origin target =
        originRows.TryFind target |> Option.defaultValue []
        |> function
            | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [source] }] -> Some source
            | _ -> None
    let literal id =
        match live id with
        | Some { Kind = SemanticKind.Literal(NativeLiteral.Int(value, _)) } -> Some(bigint value)
        | Some { Kind = SemanticKind.Literal(NativeLiteral.UInt(value, _)) } -> Some(bigint value)
        | _ -> None
    let operation id =
        match node id with
        | Some { Kind = SemanticKind.Application(callee, args) } ->
            match node callee with
            | Some { Kind = SemanticKind.Intrinsic info } -> Some(info.Operation, args)
            | _ -> None
        | _ -> None
    let rec cell seen source =
        if Set.contains source seen then None else
        let seen = Set.add source seen
        match node source with
        | Some { Kind = SemanticKind.Binding(_, true, _, _); Type = ty } when Types.isIntegerType ty -> Some source
        | Some { Kind = SemanticKind.VarRef(_, Some declaration) | SemanticKind.TypeAnnotation(declaration, _) }
            when same source declaration -> cell seen declaration
        | _ -> None
    let rec descendants seen pending =
        match pending with
        | [] -> seen
        | id :: rest when Set.contains id seen -> descendants seen rest
        | id :: rest ->
            match live id with
            | Some { Kind = SemanticKind.Lambda _ } -> descendants (Set.add id seen) rest
            | Some value ->
                let children = Incidence.structuralIncidence value |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                descendants (Set.add id seen) (children @ rest)
            | None -> descendants seen rest
    let readAccess id = Ingress.tryStorageAccess ingress.Value id
    let valueCorresponds actual source =
        same actual source &&
        match live actual with
        | Some { Kind = SemanticKind.FrameRead(_, slot) } when slot = source && origin actual = Some source ->
            readAccess actual |> Option.exists (fun access -> access.Source = source)
        | Some { Kind = SemanticKind.Literal _ | SemanticKind.Intrinsic _ | SemanticKind.PlatformBinding _ }
            when actual = source -> true
        | Some { Kind = SemanticKind.VarRef(_, Some declaration) } when actual = source ->
            match node declaration with
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } ->
                match node value with Some { Kind = SemanticKind.Lambda(_, _, [], _, _) } -> true | _ -> false
            | _ -> false
        | _ -> false
    let cloneCorresponds actual source =
        if origin actual <> Some source || not (same actual source) then false else
        match node source, live actual with
        | Some { Kind = SemanticKind.Application(callee, args) },
          Some { Kind = SemanticKind.Application(actualCallee, actualArgs) }
            when args.Length = actualArgs.Length ->
            valueCorresponds actualCallee callee && List.forall2 valueCorresponds actualArgs args
        | Some { Kind = SemanticKind.Literal expected }, Some { Kind = SemanticKind.Literal actual } -> expected = actual
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) }, Some { Kind = SemanticKind.TypeAnnotation(actual, _) } ->
            valueCorresponds actual value
        | _ -> false
    let forOwner (producer: SemanticNode) =
        match Sources.currentSourceControl graph producer, Current.forOwner graph producer.Id with
        | Some(control, sourceSites, _), Some machine when machine.Generator = control.Generator ->
            let scope = machine.Participants
            let dispatches = scope |> Set.toList |> List.choose (fun id ->
                match live id with
                | Some { Kind = SemanticKind.ContinuationDispatch(selector, cases, _) } ->
                    match live selector with
                    | Some { Kind = SemanticKind.VarRef(_, Some pc) } ->
                        match live pc with Some { Kind = SemanticKind.Binding(_, true, _, _) } -> Some(pc, cases) | _ -> None
                    | _ -> None
                | _ -> None)
            match single dispatches with
            | None -> []
            | Some(pc, cases) ->
                let rec destination seen label =
                    if Set.contains label seen then None else
                    match control.Steps.TryFind label with
                    | Some { Instruction = Control.Instruction.Pass; Successors = [{ Target = next; Transfer = EvaluationTransfer.Continue }] } ->
                        destination (Set.add label seen) next
                    | Some _ -> Some label
                    | None -> None
                let target label = destination Set.empty label
                let active = control.Steps |> Map.filter (fun label _ -> target label = Some label)
                let actual = Map.ofList cases
                let pcWrites = ResizeArray<NodeId>()
                let setPc (expected: int) id =
                    match live id with
                    | Some { Kind = SemanticKind.Set(reference, value); Children = [actualReference; actualValue] }
                        when reference = actualReference && value = actualValue ->
                        match live reference with
                        | Some { Kind = SemanticKind.VarRef(_, Some binding) } when binding = pc && same reference pc && same value pc && literal value = Some(bigint expected) ->
                            pcWrites.Add id
                            true
                        | _ -> false
                    | _ -> false
                let advance (step: Control.Step) id =
                    match step.Successors with
                    | [arc] -> target arc.Target |> Option.exists (fun expected -> setPc expected id)
                    | _ -> false
                let write slot source id =
                    match live id with
                    | Some { Kind = SemanticKind.FrameWrite(_, actualSlot, value) } ->
                        actualSlot = slot && (value = source || valueCorresponds value source)
                    | Some { Kind = SemanticKind.Literal NativeLiteral.Unit } ->
                        node slot |> Option.exists (fun value -> Types.tryGetNTUKind value.Type = Some NTUKind.NTUunit)
                    | _ -> false
                let evaluate source actualOperation =
                    match node source with
                    | Some _ when Machine.isSymbolic graph Set.empty source ->
                        match live actualOperation with Some { Kind = SemanticKind.Literal NativeLiteral.Unit } -> true | _ -> false
                    | Some { Kind = SemanticKind.Binding _; Children = [value] } -> write source value actualOperation
                    | Some { Kind = SemanticKind.VarRef(_, Some declaration) } -> write source declaration actualOperation
                    | Some { Kind = SemanticKind.Set(reference, value) } ->
                        match node reference with
                        | Some { Kind = SemanticKind.VarRef(_, Some declaration) } -> write declaration value actualOperation
                        | _ -> false
                    | Some { Kind = SemanticKind.Application _ | SemanticKind.Literal _ | SemanticKind.TypeAnnotation _ } ->
                        match live actualOperation with
                        | Some { Kind = SemanticKind.Sequential [cloned; save] } -> cloneCorresponds cloned source && write source cloned save
                        | _ -> false
                    // No guard facts cross an unverified operation. Unsupported
                    // source forms do not weaken the checked scalar protocol.
                    | _ -> false
                let actionCurrent label (step: Control.Step) =
                    match actual.TryFind label |> Option.bind live, step.Instruction with
                    | Some { Kind = SemanticKind.Sequential [operation; next] }, Control.Instruction.Evaluate source ->
                        evaluate source operation && advance step next
                    | Some { Kind = SemanticKind.Sequential [save; next] }, Control.Instruction.Copy(output, input) ->
                        write output input save && advance step next
                    | Some { Kind = SemanticKind.IfThenElse(condition, yes, Some no) }, Control.Instruction.Branch source ->
                        valueCorresponds condition source &&
                        ([EvaluationTransfer.WhenTrue, yes; EvaluationTransfer.WhenFalse, no] |> List.forall (fun (transfer, branch) ->
                            step.Successors |> List.filter (fun arc -> arc.Transfer = transfer) |> single
                            |> Option.bind (fun arc -> target arc.Target) |> Option.exists (fun expected -> setPc expected branch)))
                    | Some _, Control.Instruction.Suspend(payload, state) ->
                        machine.Cuts |> List.exists (fun cut -> cut.Yield = step.Origin && cut.Payload = payload && cut.State = state && actual[label] = cut.Action)
                    | Some { Kind = SemanticKind.Sequential [writer; _] }, Control.Instruction.Complete ->
                        machine.StateWrites |> List.exists (fun (actualWriter, value) -> actualWriter = writer && literal value = Some -1I)
                    | Some value, Control.Instruction.Pass -> advance step value.Id
                    | _ -> false
                let resumesCurrent =
                    control.ResumeEntries |> Map.forall (fun state entry ->
                        graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Suspension && edge.Role = EdgeRole.SuspensionResume state && List.tryHead edge.Sources = Some producer.Id)
                        |> single |> Option.bind (fun row -> live row.Target)
                        |> Option.exists (fun value ->
                            match value.Kind, target entry with
                            | SemanticKind.Sequential [setEntry; _], Some expected -> setPc expected setEntry
                            | _ -> false))
                let allPcWrites = scope |> Set.toList |> List.filter (fun id ->
                    match live id with
                    | Some { Kind = SemanticKind.Set(reference, _) } ->
                        match live reference with Some { Kind = SemanticKind.VarRef(_, Some binding) } -> binding = pc | _ -> false
                    | _ -> false)
                let actionsCurrent = actual.Count = cases.Length && (Map.keys actual |> Set.ofSeq) = (Map.keys active |> Set.ofSeq) &&
                                     (active |> Map.forall actionCurrent)
                if not resumesCurrent || not actionsCurrent || Set.ofSeq pcWrites <> Set.ofList allPcWrites || pcWrites.Count <> allPcWrites.Length then [] else
                let actionNodes = actual |> Map.map (fun _ id -> descendants Set.empty [id])
                let cloneCandidates =
                    actionNodes.Values |> Set.unionMany |> Set.toList
                    |> List.choose (fun id -> origin id |> Option.map (fun source -> source, id))
                    |> List.groupBy fst |> Map.ofList
                let checkedClones = System.Collections.Generic.Dictionary<NodeId, NodeId list>()
                let clones source =
                    match checkedClones.TryGetValue source with
                    | true, found -> found
                    | _ ->
                        let found = cloneCandidates.TryFind source |> Option.defaultValue []
                                    |> List.map snd |> List.filter (fun id -> cloneCorresponds id source)
                        checkedClones.Add(source, found)
                        found
                let operandCell operand =
                    match live operand with
                    | Some { Kind = SemanticKind.FrameRead(_, source) } ->
                        readAccess operand |> Option.bind (fun access -> if access.Source = source then cell Set.empty source else None)
                    | _ -> None
                let operands guard =
                    match live guard with
                    | Some { Kind = SemanticKind.Application(_, arguments) } -> arguments |> List.choose (fun operand -> operandCell operand |> Option.map (fun cell -> operand, cell))
                    | _ -> []
                let rec entailed seen source polarity =
                    if Set.contains source seen then [] else
                    let seen = Set.add source seen
                    match operation source with
                    | Some(name, [_; _]) when comparisons.Contains name ->
                        match clones source |> single with
                        | Some guard ->
                            let cells = operands guard |> List.map snd |> Set.ofList
                            if cells.IsEmpty then [] else [{ Source = source; Guard = guard; Polarity = polarity; Cells = cells }]
                        | _ -> []
                    | Some("op_BooleanAnd", [left; right]) when polarity -> entailed seen left true @ entailed seen right true
                    | Some("op_BooleanOr", [left; right]) when not polarity -> entailed seen left false @ entailed seen right false
                    | _ ->
                        match node source with
                        | Some { Kind = SemanticKind.TypeAnnotation(value, _) | SemanticKind.EagerExpr value } -> entailed seen value polarity
                        | Some { Kind = SemanticKind.IfThenElse(condition, yes, Some no) } ->
                            match node yes, node no, polarity with
                            | _, Some { Kind = SemanticKind.Literal(NativeLiteral.Bool false) }, true -> entailed seen condition true @ entailed seen yes true
                            | Some { Kind = SemanticKind.Literal(NativeLiteral.Bool true) }, _, false -> entailed seen condition false @ entailed seen no false
                            | _ -> []
                        | _ -> []
                let arcEvidence = System.Collections.Generic.Dictionary<int * EvaluationTransfer, Set<Fact>>()
                let arcFacts (step: Control.Step) transfer =
                    let key = step.Label, transfer
                    match arcEvidence.TryGetValue key with
                    | true, found -> found
                    | _ ->
                        let found =
                            match step.Instruction, transfer with
                            | Control.Instruction.Branch guard, EvaluationTransfer.WhenTrue -> entailed Set.empty guard true |> Set.ofList
                            | Control.Instruction.Branch guard, EvaluationTransfer.WhenFalse -> entailed Set.empty guard false |> Set.ofList
                            | _ -> Set.empty
                        arcEvidence.Add(key, found)
                        found
                let universe = control.Steps.Values |> Seq.collect (fun step ->
                    step.Successors |> Seq.collect (fun arc -> arcFacts step arc.Transfer)) |> Set.ofSeq
                let closedCells = universe |> Seq.collect _.Cells |> Seq.distinct |> Seq.filter (fun sourceCell ->
                    // Every generated occurrence of this declaration must have
                    // the same current, no-escape storage writer census.
                    let reads = scope |> Set.toList |> List.filter (fun id ->
                        match live id with
                        | Some { Kind = SemanticKind.FrameRead(_, source) } -> cell Set.empty source = Some sourceCell
                        | _ -> false)
                    let owned = Set.union sourceSites scope
                    let outsideUses =
                        graph.Nodes.Values |> Seq.exists (fun value ->
                            not (owned.Contains value.Id) &&
                            (kindEdges value.Id value.Kind |> List.exists (fun edge -> List.contains sourceCell edge.Sources)))
                    let outsideRows =
                        graph.Edges |> List.exists (fun edge ->
                            (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) &&
                            List.contains sourceCell edge.Sources && not (owned.Contains edge.Target))
                    sourceSites.Contains sourceCell && not outsideUses && not outsideRows && not reads.IsEmpty &&
                    (reads |> List.forall (fun id ->
                        readAccess id |> Option.exists (fun access -> access.SharedCell.IsNone)))) |> Set.ofSeq
                let predecessors =
                    control.Steps.Values |> Seq.collect (fun step -> step.Successors |> Seq.map (fun arc -> arc.Target, (step, arc)))
                    |> Seq.groupBy fst |> Seq.map (fun (label, rows) -> label, rows |> Seq.map snd |> Seq.toList) |> Map.ofSeq
                let cellsSurvive (step: Control.Step) cells =
                    let writes, unknown = actual.TryFind step.Label |> Option.map effectAt |> Option.defaultValue (Set.empty, false)
                    (Set.intersect writes cells |> Set.isEmpty) &&
                    (not unknown || Set.isSubset cells closedCells) &&
                    (match step.Instruction with Control.Instruction.Suspend _ -> Set.isSubset cells closedCells | _ -> true) &&
                    (Set.intersect step.Defines cells |> Set.isEmpty)
                let survives step (fact: Fact) = cellsSurvive step fact.Cells
                let references (fact: Fact) =
                    operands fact.Guard |> List.choose (fun (operand, sourceCell) ->
                        readAccess operand |> Option.map (fun access -> access.Source, sourceCell)) |> Set.ofList
                let referenceUniverse = universe |> Seq.collect references |> Set.ofSeq
                let referencesBy (step: Control.Step) =
                    let output =
                        match step.Instruction with
                        | Control.Instruction.Evaluate source -> Some source
                        | Control.Instruction.Copy(output, _) -> Some output
                        | _ -> None
                    referenceUniverse |> Set.filter (fun (reference, _) -> output = Some reference)
                let rec settleReferences (observed: Map<int, Set<NodeId * NodeId>>) =
                    let next = control.Steps |> Map.map (fun label _ ->
                        if label = control.Entry then Set.empty else
                        predecessors.TryFind label |> Option.defaultValue []
                        |> List.map (fun (step, _) ->
                            Set.union (observed[step.Label] |> Set.filter (fun (_, sourceCell) -> cellsSurvive step (Set.singleton sourceCell))) (referencesBy step))
                        |> function [] -> Set.empty | first :: rest -> List.fold Set.intersect first rest)
                    if next = observed then observed else settleReferences next
                let referenceObservations =
                    settleReferences (control.Steps |> Map.map (fun label _ -> if label = control.Entry then Set.empty else referenceUniverse))
                // A branch cannot revive an observation that was invalidated
                // after comparison evaluation. Track availability separately
                // from branch truth, through the same current action effects.
                let observedBy (step: Control.Step) =
                    match step.Instruction with
                    | Control.Instruction.Evaluate source ->
                        universe |> Set.filter (fun fact -> fact.Source = source && Set.isSubset (references fact) referenceObservations[step.Label])
                    | _ -> Set.empty
                let rec settleObserved (observed: Map<int, Set<Fact>>) =
                    let next = control.Steps |> Map.map (fun label _ ->
                        if label = control.Entry then Set.empty else
                        predecessors.TryFind label |> Option.defaultValue []
                        |> List.map (fun (step, _) ->
                            Set.union (observed[step.Label] |> Set.filter (survives step)) (observedBy step))
                        |> function [] -> Set.empty | first :: rest -> List.fold Set.intersect first rest)
                    if next = observed then observed else settleObserved next
                let observed = settleObserved (control.Steps |> Map.map (fun label _ -> if label = control.Entry then Set.empty else universe))
                let rec settle (facts: Map<int, Set<Fact>>) =
                    let next = control.Steps |> Map.map (fun label _ ->
                        if label = control.Entry then Set.empty else
                        predecessors.TryFind label |> Option.defaultValue []
                        |> List.map (fun (step, arc) ->
                            let available = Set.union (observed[step.Label] |> Set.filter (survives step)) (observedBy step)
                            Set.union (facts[step.Label] |> Set.filter (survives step)) (Set.intersect available (arcFacts step arc.Transfer)))
                        |> function [] -> Set.empty | first :: rest -> List.fold Set.intersect first rest)
                    if next = facts then facts else settle next
                let atEntry = settle (control.Steps |> Map.map (fun label _ -> if label = control.Entry then Set.empty else universe))
                let participants = Set.union sourceSites scope |> Set.toList
                active |> Map.toList |> List.collect (fun (label, _) ->
                    actionNodes[label] |> Set.toList |> List.collect (fun read ->
                        match operandCell read with
                        | Some sourceCell when closedCells.Contains sourceCell ->
                            atEntry[label] |> Set.toList |> List.collect (fun fact ->
                                operands fact.Guard |> List.choose (fun (operand, guardedCell) ->
                                    if guardedCell = sourceCell then
                                        Some { Read = read; Cell = sourceCell; Guard = fact.Guard; Operand = operand
                                               Polarity = fact.Polarity; Participants = participants }
                                    else None))
                        | _ -> []))
        | _ -> []
    graph.Nodes.Values |> Seq.filter (fun value -> value.IsReachable && (match value.Kind with SemanticKind.SeqExpr _ -> true | _ -> false))
    |> Seq.collect forOwner |> Seq.distinct |> Seq.toList

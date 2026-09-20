// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Compose Baker's local evaluation contracts into a finite continuation
/// graph. The labels below name evaluation occurrences, not source nodes: two
/// demands for one value retain its identity without conflating their paths.
/// This is source elaboration; no target operations or layout are chosen here.
module Clef.Compiler.Baker.Recipes.SequenceControlRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

[<RequireQualifiedAccess>]
type Instruction =
    | Pass
    | Evaluate of NodeId
    | Copy of destination: NodeId * value: NodeId
    | Branch of NodeId
    | Suspend of payload: NodeId * state: int
    | Complete

type Arc = { Target: int; Transfer: EvaluationTransfer }

type Step = {
    Label: int
    Origin: NodeId
    Port: EvaluationPort
    Instruction: Instruction
    Successors: Arc list
    Uses: Set<NodeId>
    Defines: Set<NodeId>
}

type Control = {
    Owner: NodeId
    Generator: NodeId
    Entry: int
    Steps: Map<int, Step>
    /// State zero starts the computation; a positive state resumes after its
    /// particular cut. Completion is represented separately, never guessed.
    ResumeEntries: Map<int, int>
    LiveAtEntry: Map<int, Set<NodeId>>
    LiveAcross: Map<int, Set<NodeId>>
    /// Suppressed evaluation occurrence -> its dominating producer occurrence.
    /// Labels distinguish executions of a source node on different loop visits.
    ReuseOrigins: Map<int, int>
    /// Definite source-value initialization before every retained occurrence.
    AssignedAtEntry: Map<int, Set<NodeId>>
}

type Residual = { Owner: NodeId; Site: NodeId; Reason: string }

type private Build = {
    Next: int
    NextState: int
    Steps: Map<int, Step>
    Resumes: Map<int, int>
}

let private isUnit (graph: SemanticGraph) id =
    graph.Nodes.TryFind id |> Option.exists (fun node -> Types.tryGetNTUKind node.Type = Some NTUKind.NTUunit)

let private instructionFacts (graph: SemanticGraph) operands instruction =
    let values ids = ids |> List.filter (isUnit graph >> not) |> Set.ofList
    match instruction with
    | Instruction.Pass | Instruction.Complete -> Set.empty, Set.empty
    | Instruction.Copy (target, value) -> values [value], values [target]
    | Instruction.Branch condition | Instruction.Suspend (condition, _) -> values [condition], Set.empty
    | Instruction.Evaluate id ->
        let node = graph.Nodes[id]
        let uses = operands |> List.choose (fun (_, access, value) -> if access = EvaluationAccess.Value then Some value else None)
        match node.Kind with
        | SemanticKind.VarRef (_, Some declaration) -> values [declaration], values [id]
        | SemanticKind.Set (target, value) ->
            match graph.Nodes[target].Kind with
            | SemanticKind.VarRef (_, Some declaration) -> values [value], Set.singleton declaration
            | _ -> values uses, Set.empty
        | SemanticKind.Lambda (_, _, captures, _, _)
        | SemanticKind.LazyExpr (_, captures) | SemanticKind.SeqExpr (_, captures) ->
            captures |> List.choose _.SourceNodeId |> values, values [id]
        | _ -> values uses, values [id]

let private add origin port instruction successors uses defines state =
    let label = state.Next
    let step = { Label = label; Origin = origin; Port = port; Instruction = instruction
                 Successors = successors; Uses = uses; Defines = defines }
    label, { state with Next = label + 1; Steps = state.Steps.Add(label, step) }

/// Backwards liveness over finite, explicitly enumerated successors. It is a
/// monotone fixed point: a loop changes only the sets that depend on its body.
let private liveness (steps: Map<int, Step>) =
    let rec settle (live: Map<int, Set<NodeId>>) =
        let next = steps |> Map.map (fun _ step ->
            let after = step.Successors |> List.fold (fun acc arc -> Set.union acc live[arc.Target]) Set.empty
            Set.union step.Uses (Set.difference after step.Defines))
        if next = live then live else settle next
    settle (steps |> Map.map (fun _ _ -> Set.empty))

/// Forward must facts meet at every predecessor, including resumption. The
/// caller supplies loop-iteration kills; an earlier iteration is not evidence
/// that a local expression has already run in the current iteration.
let private mustFacts (steps: Map<int, Step>) entry initial universe generates kills =
    let predecessors =
        steps.Values |> Seq.collect (fun step -> step.Successors |> Seq.map (fun arc -> arc.Target, (step, arc)))
        |> Seq.groupBy fst |> Seq.map (fun (label, incoming) -> label, incoming |> Seq.map snd |> Seq.toList) |> Map.ofSeq
    let rec settle (facts: Map<int, Set<'Fact>>) =
        let next = steps |> Map.map (fun label _ ->
            if label = entry then initial
            else
                predecessors.TryFind label |> Option.defaultValue []
                |> List.map (fun (predecessor, arc) ->
                    Set.difference (Set.union facts[predecessor.Label] (generates predecessor)) (kills predecessor arc))
                |> function [] -> Set.empty | first :: rest -> List.fold Set.intersect first rest)
        if next = facts then facts else settle next
    settle (steps |> Map.map (fun label _ -> if label = entry then initial else universe))

let private iterationScopes (graph: SemanticGraph) owner =
    let demands =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources with
            | EdgeClass.Evaluation, EdgeRole.EvaluationOperand _, [actualOwner; operand] when actualOwner = owner -> Some (edge.Target, operand)
            | _ -> None)
        |> List.groupBy fst |> List.map (fun (target, operands) -> target, List.map snd operands) |> Map.ofList
    let rec members seen = function
        | [] -> seen
        | id :: rest when Set.contains id seen -> members seen rest
        | id :: rest -> members (Set.add id seen) ((demands.TryFind id |> Option.defaultValue []) @ rest)
    graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.WhileLoop(guard, body) -> Some (id, members Set.empty [guard; body])
        | _ -> None) |> Map.ofList

let private backedgeScope (steps: Map<int, Step>) scopes (step: Step) (arc: Arc) =
    match step.Port, steps[arc.Target].Port with
    | EvaluationPort.OperandExit 1, EvaluationPort.OperandEntry 0 when step.Origin = steps[arc.Target].Origin ->
        Map.tryFind step.Origin scopes |> Option.defaultValue Set.empty
    | _ -> Set.empty

let private reuseEvaluations (graph: SemanticGraph) owner entry (steps: Map<int, Step>) =
    let scopes = iterationScopes graph owner
    let producers = steps |> Map.toList |> List.choose (fun (label, step) ->
        match step.Instruction with Instruction.Evaluate id -> Some (label, id) | _ -> None) |> Map.ofList
    let producerLabels = producers |> Map.keys |> Set.ofSeq
    let generates (step: Step) = if producers.ContainsKey step.Label then Set.singleton step.Label else Set.empty
    let kills step arc =
        let locals = backedgeScope steps scopes step arc
        producers |> Map.toList |> List.choose (fun (label, id) -> if locals.Contains id then Some label else None) |> Set.ofList
    let available = mustFacts steps entry Set.empty producerLabels generates kills
    let candidates = producers |> Map.toList |> List.choose (fun (label, id) ->
        available[label] |> Set.toList |> List.tryFind (fun previous -> producers[previous] = id)
        |> Option.map (fun previous -> label, previous)) |> Map.ofList
    let rec original label = match candidates.TryFind label with Some producer -> original producer | None -> label
    let reuse = candidates |> Map.map (fun _ producer -> original producer)
    let retained = steps |> Map.map (fun label step ->
        if reuse.ContainsKey label then { step with Instruction = Instruction.Pass; Uses = Set.empty; Defines = Set.empty }
        else step)
    retained, reuse, scopes

let private definiteAssignment (graph: SemanticGraph) (owner: SemanticNode) entry scopes (steps: Map<int, Step>) =
    let captures =
        match owner.Kind with
        | SemanticKind.SeqExpr(_, captures) -> captures |> List.choose _.SourceNodeId
        | _ -> []
    let declared =
        graph.ModuleClassifications.Value.Values
        |> Seq.collect (fun classification -> classification.ModuleInit @ classification.Definitions)
        |> Seq.append (graph.DeclarationRoots |> Seq.map fst)
        |> Seq.filter (fun id ->
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.Binding _; IsReachable = true } -> true
            | _ -> false)
    let implementations = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.implementationBindings graph
    let initial = seq { yield! captures; yield! declared; yield! implementations } |> Seq.filter (isUnit graph >> not) |> Set.ofSeq
    let universe = steps.Values |> Seq.fold (fun all step -> Set.union all step.Defines) initial
    let assigned = mustFacts steps entry initial universe (fun step -> step.Defines) (backedgeScope steps scopes)
    let missing = steps.Values |> Seq.tryPick (fun step ->
        let unavailable = Set.difference step.Uses assigned[step.Label]
        if Set.isEmpty unavailable then None
        else Some { Owner = owner.Id; Site = step.Origin
                    Reason = sprintf "Values lack definite initialization at occurrence %d: %A" step.Label (Set.toList unavailable) })
    match missing with Some residual -> Error residual | None -> Ok assigned

/// The local projection is the authority for demands and transfers. The kind
/// supplies the operation performed at Ready, never an inferred child order.
let forOwner (graph: SemanticGraph) (owner: SemanticNode) : Result<Control, Residual> =
    let fail site reason = Error { Owner = owner.Id; Site = site; Reason = reason }
    let relations =
        graph.Edges
        |> List.filter (fun edge -> edge.Class = EdgeClass.Evaluation && List.tryHead edge.Sources = Some owner.Id)
        |> List.groupBy _.Target |> Map.ofList
    let facts id = relations.TryFind id |> Option.defaultValue []
    let roots = graph.Edges |> List.filter (fun edge ->
        edge.Class = EdgeClass.Evaluation && edge.Role = EdgeRole.EvaluationRoot && List.tryHead edge.Sources = Some owner.Id)
    match roots with
    | [{ Sources = [_; generator]; Target = body }] ->
        let rec compose ancestors id continuation (state: Build) =
            if Set.contains id ancestors then fail id "Cyclic structural demand requires an explicit control relation."
            else
                let edges = facts id
                let pending = edges |> List.tryPick (fun edge -> match edge.Role with EdgeRole.EvaluationPending reason -> Some reason | _ -> None)
                let operands = edges |> List.choose (fun edge ->
                    match edge.Role, edge.Sources with
                    | EdgeRole.EvaluationOperand access, [_; value] -> Some (edge.Ordinal, access, value)
                    | _ -> None) |> List.sortBy (fun (slot, _, _) -> slot)
                let flows = edges |> List.choose (fun edge ->
                    match edge.Role with EdgeRole.EvaluationFlow (before, after, transfer) -> Some (before, after, transfer) | _ -> None)
                match pending with
                | Some reason -> fail id (sprintf "Local evaluation remains pending: %A" reason)
                | None when List.isEmpty flows -> fail id "Missing local evaluation contract."
                | None ->
                    let node = graph.Nodes[id]
                    let operand slot = operands |> List.find (fun (ordinal, _, _) -> ordinal = slot) |> fun (_, _, value) -> value
                    let stateNumber, state =
                        match node.Kind with
                        | SemanticKind.Yield _ -> state.NextState, { state with NextState = state.NextState + 1 }
                        | _ -> 0, state
                    let instruction port =
                        match port, node.Kind with
                        | EvaluationPort.Ready, SemanticKind.Yield payload -> Instruction.Suspend (payload, stateNumber)
                        | EvaluationPort.Ready, SemanticKind.Sequential ids ->
                            if isUnit graph id || List.isEmpty ids then Instruction.Pass
                            else Instruction.Copy (id, List.last ids)
                        | EvaluationPort.Ready, (SemanticKind.IfThenElse _ | SemanticKind.WhileLoop _) -> Instruction.Pass
                        | EvaluationPort.OperandExit 0, SemanticKind.IfThenElse (guard, _, _)
                        | EvaluationPort.OperandExit 0, SemanticKind.WhileLoop (guard, _) -> Instruction.Branch guard
                        | EvaluationPort.OperandExit slot, SemanticKind.IfThenElse _ when slot > 0 && not (isUnit graph id) ->
                            Instruction.Copy (id, operand slot)
                        | EvaluationPort.Ready, _ -> Instruction.Evaluate id
                        | _ -> Instruction.Pass
                    let ports = flows |> List.collect (fun (before, after, _) -> [before; after]) |> Set.ofList |> Set.toList
                    let labels, state =
                        ports |> List.fold (fun ((labels: Map<EvaluationPort, int>), (state: Build)) port ->
                            if port = EvaluationPort.Exit then labels.Add(port, continuation), state
                            else
                                let action = instruction port
                                let uses, defines = instructionFacts graph operands action
                                let label, state = add id port action [] uses defines state
                                labels.Add(port, label), state) (Map.empty, state)
                    let state =
                        flows |> List.groupBy (fun (before, _, _) -> before) |> List.fold (fun (state: Build) (before, outgoing) ->
                            if before = EvaluationPort.Exit then state
                            else
                                let label = labels[before]
                                let successors = outgoing |> List.map (fun (_, after, transfer) -> { Target = labels[after]; Transfer = transfer })
                                { state with Steps = state.Steps.Add(label, { state.Steps[label] with Successors = successors }) }) state
                    let rec children (state: Build) = function
                        | [] -> Ok state
                        | (_, EvaluationAccess.Storage, _) :: rest -> children state rest
                        | (slot, EvaluationAccess.Value, child) :: rest ->
                            match Map.tryFind (EvaluationPort.OperandEntry slot) labels, Map.tryFind (EvaluationPort.OperandExit slot) labels with
                            | Some entry, Some exit ->
                                match compose (Set.add id ancestors) child exit state with
                                | Error error -> Error error
                                | Ok (first, state) ->
                                    let step = state.Steps[entry]
                                    let state = { state with Steps = state.Steps.Add(entry, { step with Successors = [{ Target = first; Transfer = EvaluationTransfer.Continue }] }) }
                                    children state rest
                            | _ -> fail id "Value demand has no local entry/completion ports."
                    match children state operands with
                    | Error error -> Error error
                    | Ok state ->
                        let state =
                            if stateNumber = 0 then state
                            else { state with Resumes = state.Resumes.Add(stateNumber, continuation) }
                        Ok (labels[EvaluationPort.Entry], state)
        let final, initial = add owner.Id EvaluationPort.Exit Instruction.Complete [] Set.empty Set.empty
                                { Next = 0; NextState = 1; Steps = Map.empty; Resumes = Map.empty }
        match compose Set.empty body final initial with
        | Error error -> Error error
        | Ok (entry, built) ->
            let steps, reuse, scopes = reuseEvaluations graph owner.Id entry built.Steps
            match definiteAssignment graph owner entry scopes steps with
            | Error residual -> Error residual
            | Ok assigned ->
                let live = liveness steps
                let across = steps |> Map.toList |> List.choose (fun (label, step) ->
                    match step.Instruction with
                    | Instruction.Suspend _ ->
                        let remaining = step.Successors |> List.fold (fun acc arc -> Set.union acc live[arc.Target]) Set.empty
                        Some (label, remaining)
                    | _ -> None) |> Map.ofList
                Ok { Owner = owner.Id; Generator = generator; Entry = entry; Steps = steps
                     ResumeEntries = built.Resumes.Add(0, entry); LiveAtEntry = live; LiveAcross = across
                     ReuseOrigins = reuse; AssignedAtEntry = assigned }
    | _ -> fail owner.Id "Continuation composition requires one settled owner/generator root."

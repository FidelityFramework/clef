// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Resident continuation incidence and bounded discriminant obligations.
/// These relations retain Baker's checked cut/resume/liveness plan; they are
/// not a claim that frame lifetime or the whole continuation theorem discharged.
module Clef.Compiler.Baker.Recipes.SequenceContinuationEvidence

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
open Clef.Compiler.Baker.Ingredients.Closures
module Control = Clef.Compiler.Baker.Recipes.SequenceControlRecipes
module Machine = Clef.Compiler.Baker.Recipes.SequenceMachineRecipes
module ProgramStorage = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization

let private edge role sources target : Hyperedge =
    { Class = EdgeClass.Suspension; Role = role; Sources = sources; Target = target; Ordinal = 0 }

let forMachine (graph: SemanticGraph) (control: Control.Control)
               (frame: ContinuationFrame) (machine: Machine.Machine) : Result<Enrichment, Control.Residual> =
    let fail site reason : Result<Enrichment, Control.Residual> =
        Error { Owner = control.Owner; Site = site; Reason = reason }
    let generated = machine.Nodes |> List.map (fun node -> node.Id, node) |> Map.ofList
    let nodes = generated |> Map.fold (fun nodes id node -> Map.add id node nodes) graph.Nodes
    let exists id = nodes.ContainsKey id
    let children id =
        nodes.TryFind id |> Option.map (fun node ->
            structuralIncidence node |> List.filter Hyperedge.isStructural |> List.collect _.Sources)
        |> Option.defaultValue []
    let descendants root =
        let rec visit seen = function
            | [] -> seen
            | id :: rest when Set.contains id seen -> visit seen rest
            | id :: rest -> visit (Set.add id seen) (children id @ rest)
        visit Set.empty [root]
    let cuts =
        control.Steps.Values
        |> Seq.choose (fun step ->
            match step.Instruction with Control.Instruction.Suspend(payload, state) -> Some(step, payload, state) | _ -> None)
        |> Seq.toList
    let states = cuts |> List.map (fun (_, _, state) -> state)
    let maximum = states |> List.fold max 0 |> bigint
    let expectedStates = Set.ofList (0 :: states)
    let keys map = Map.keys map |> Set.ofSeq
    let rec target seen label =
        if Set.contains label seen then None
        else
            match control.Steps.TryFind label with
            | Some { Instruction = Control.Instruction.Pass; Successors = [{ Target = next; Transfer = EvaluationTransfer.Continue }] } ->
                target (Set.add label seen) next
            | Some _ -> Some label
            | None -> None
    let expectedTargets = control.ResumeEntries |> Map.map (fun _ label -> target Set.empty label)
    let active =
        control.Steps |> Map.toList
        |> List.choose (fun (label, _) -> if target Set.empty label = Some label then Some label else None)
        |> Set.ofList
    let sourceOwner = graph.Nodes.TryFind control.Owner
    let ownerValid =
        match sourceOwner, graph.Nodes.TryFind control.Generator with
        | Some { Kind = SemanticKind.SeqExpr(generator, _) },
          Some { Kind = SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) } -> generator = control.Generator
        | _ -> false
    let globals =
        graph.ModuleClassifications.Value.Values
        |> Seq.collect (fun classification -> classification.Definitions @ classification.ModuleInit)
        |> Seq.append (graph.DeclarationRoots |> Seq.map fst)
        |> Seq.filter (fun id ->
            match graph.Nodes.TryFind id with Some { Kind = SemanticKind.Binding(_, false, _, _) } -> true | _ -> false)
        |> Set.ofSeq
    // ProgramValue establishes the cell's program residence, not the lifetime
    // of storage addressed by a descriptor held in that cell.
    let programResidents =
        control.LiveAcross.Values |> Seq.fold Set.union Set.empty |> Set.toList
        |> List.choose (fun id ->
            match graph.Nodes.TryFind id |> Option.bind (fun node -> Types.tryGetNTUKind node.Type) with
            | Some (NTUKind.NTUint _ | NTUKind.NTUuint _ | NTUKind.NTUfloat _ | NTUKind.NTUposit _ | NTUKind.NTUbool | NTUKind.NTUchar) ->
                ProgramStorage.tryValueAuthority graph id |> Option.map (fun authority -> id, authority.Evidence)
            | _ -> None)
        |> Map.ofList
    let liveResident id =
        exists id && (
            (frame.Slots |> List.exists (fun slot -> slot.Source = id && slot.ValueType = nodes[id].Type))
            || globals.Contains id || programResidents.ContainsKey id || Machine.isSymbolic graph Set.empty id)
    let malformedStep = control.Steps.Values |> Seq.tryFind (fun step ->
        step.Successors |> List.exists (fun arc -> not (control.Steps.ContainsKey arc.Target)))
    let labelsConsistent = control.Steps |> Map.forall (fun label step -> label = step.Label)
    let rootScope = descendants machine.Root
    let entryDispatch =
        generated.Values
        |> Seq.filter (fun node ->
            match node.Kind with
            | SemanticKind.ContinuationDispatch(selector, cases, completed) when rootScope.Contains node.Id ->
                match nodes.TryFind selector with
                | Some { Kind = SemanticKind.FrameRead(_, slot) } ->
                    slot = frame.State && cases.Length = machine.ResumeBodies.Count
                    && Map.ofList cases = machine.ResumeBodies && completed = machine.CompletedBody
                | _ -> false
            | _ -> false)
        |> Seq.toList
    let actionDispatch =
        generated.Values
        |> Seq.filter (fun node ->
            match node.Kind with
            | SemanticKind.ContinuationDispatch(_, cases, _) when rootScope.Contains node.Id ->
                cases.Length = machine.CaseBodies.Count && Map.ofList cases = machine.CaseBodies
            | _ -> false)
        |> Seq.toList
    let literal id =
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Literal(NativeLiteral.Int(value, _)) } -> Some(bigint value)
        | Some { Kind = SemanticKind.Literal(NativeLiteral.UInt(value, _)) } -> Some(bigint value)
        | _ -> None
    let writesIn body =
        descendants body |> Set.toList |> List.choose (fun id ->
            match nodes.TryFind id with
            | Some { Kind = SemanticKind.FrameWrite(_, slot, value) } when slot = frame.State -> Some(id, value)
            | _ -> None)
    let failCut = cuts |> List.tryPick (fun (step, payload, state) ->
        let delimiter = graph.Edges |> List.filter (fun relation ->
            relation.Class = EdgeClass.Suspension && relation.Role = EdgeRole.Delimiter && relation.Target = step.Origin)
        match graph.Nodes.TryFind step.Origin, delimiter, step.Successors with
        | Some { Kind = SemanticKind.Yield actual }, [{ Sources = [owner; generator] }],
          [{ Target = next; Transfer = EvaluationTransfer.Resume }]
            when actual = payload && owner = control.Owner && generator = control.Generator
                 && control.ResumeEntries.TryFind state = Some next -> None
        | _ -> Some(step.Origin, "A continuation cut lacks its exact source delimiter and resume successor."))
    let livenessValid =
        labelsConsistent && keys control.LiveAtEntry = keys control.Steps
        && (control.Steps.Values |> Seq.forall (fun step ->
            if step.Successors |> List.exists (fun arc -> not (control.LiveAtEntry.ContainsKey arc.Target)) then false
            else
                let after = step.Successors |> List.fold (fun values arc -> Set.union values control.LiveAtEntry[arc.Target]) Set.empty
                control.LiveAtEntry[step.Label] = Set.union step.Uses (Set.difference after step.Defines)))
        && keys control.LiveAcross = (cuts |> List.map (fun (step, _, _) -> step.Label) |> Set.ofList)
        && (cuts |> List.forall (fun (step, _, _) ->
            let after = step.Successors |> List.fold (fun values arc ->
                Set.union values (control.LiveAtEntry.TryFind arc.Target |> Option.defaultValue Set.empty)) Set.empty
            control.LiveAcross.TryFind step.Label = Some after && Set.forall liveResident after))
    let machineEntriesValid =
        expectedTargets |> Map.forall (fun state targetLabel ->
            match targetLabel, machine.ResumeTargets.TryFind state, machine.ResumeBodies.TryFind state with
            | Some expected, Some actual, Some body when actual = expected && machine.CaseBodies.ContainsKey actual ->
                match nodes.TryFind body with
                | Some { Kind = SemanticKind.Sequential (setEntry :: _) } ->
                    match nodes.TryFind setEntry with
                    | Some { Kind = SemanticKind.Set(_, value) } -> literal value = Some(bigint actual)
                    | _ -> false
                | _ -> false
            | _ -> false)
    let stateWritesValid =
        control.Steps.Values |> Seq.forall (fun step ->
            let expected =
                match step.Instruction with Control.Instruction.Suspend(_, state) -> Some state | Control.Instruction.Complete -> Some -1 | _ -> None
            match expected with
            | None -> true
            | Some state ->
                match machine.CaseBodies.TryFind step.Label with
                | Some body -> match writesIn body with [_, value] -> literal value = Some(bigint state) | _ -> false
                | None -> false)
    if not ownerValid || frame.Owner <> control.Owner || frame.Generator <> control.Generator then
        fail control.Owner "Continuation evidence requires the exact source owner and generator."
    elif not (graph.Nodes.ContainsKey frame.State && graph.Nodes.ContainsKey frame.Current && exists machine.CompletedBody) then
        fail control.Owner "Continuation evidence has missing frame or completion participants."
    elif not labelsConsistent then fail control.Owner "Continuation control occurrence labels do not match their identities."
    elif malformedStep.IsSome then fail malformedStep.Value.Origin "Continuation control has a missing successor."
    elif control.ResumeEntries.TryFind 0 <> Some control.Entry || not (control.Steps.ContainsKey control.Entry)
         || List.exists (fun state -> state <= 0) states || (Set.ofList states).Count <> states.Length
         || (cuts |> List.map (fun (step, _, _) -> step.Origin) |> Set.ofList).Count <> cuts.Length
         || keys control.ResumeEntries <> expectedStates || Set.ofList frame.ResumeStates <> expectedStates
         || frame.ResumeStates.Length <> expectedStates.Count then
        fail control.Owner "Continuation states require one initial entry and unique positive source cuts."
    elif graph.Nodes[frame.State].ValueRange <> Some(ValueRange.bounded -1I maximum) then
        fail frame.State "The frame state range does not match its initial, cut and completed discriminants."
    elif failCut.IsSome then let site, reason = failCut.Value in fail site reason
    elif not livenessValid then fail control.Owner "Continuation liveness lacks exact control incidence or persistent value residence."
    elif keys machine.CaseBodies <> active || keys machine.ResumeBodies <> expectedStates
         || keys machine.ResumeTargets <> expectedStates || not machineEntriesValid
         || entryDispatch.Length <> 1 || actionDispatch.Length <> 1 then
        fail control.Owner "Generated continuation entries do not match their settled dispatch actions."
    elif not stateWritesValid then fail control.Owner "Generated continuation state writes do not match suspension and completion."
    else
        let owner = sourceOwner.Value
        let writes =
            generated.Values
            |> Seq.choose (fun node ->
                match node.Kind with SemanticKind.FrameWrite(_, slot, value) when slot = frame.State -> Some(node.Id, value) | _ -> None)
            |> Seq.toList
        let invalidWrite = writes |> List.tryFind (fun (_, value) ->
            match literal value with Some value -> value <> -1I && not (states |> List.exists (fun state -> bigint state = value)) | None -> true)
        match invalidWrite with
        | Some (site, _) -> fail site "A frame state write is not a settled cut or the completed discriminant."
        | None ->
            let initial = edge (EdgeRole.SuspensionResume 0) [owner.Id; control.Generator] machine.ResumeBodies[0]
            let initialAction = edge (EdgeRole.SuspensionResumeAction 0)
                                    [owner.Id; control.Generator; machine.ResumeBodies[0]]
                                    machine.CaseBodies[machine.ResumeTargets[0]]
            let completed = edge EdgeRole.SuspensionCompleted [owner.Id; control.Generator; frame.State] machine.CompletedBody
            let relations = cuts |> List.collect (fun (step, payload, state) ->
                edge (EdgeRole.SuspensionCut state) [owner.Id; control.Generator; payload] step.Origin
                :: edge (EdgeRole.SuspensionResume state) [owner.Id; control.Generator; step.Origin] machine.ResumeBodies[state]
                :: edge (EdgeRole.SuspensionResumeAction state)
                        [owner.Id; control.Generator; machine.ResumeBodies[state]; step.Origin]
                        machine.CaseBodies[machine.ResumeTargets[state]]
                :: (control.LiveAcross[step.Label] |> Set.toList |> List.map (fun value ->
                    let authority = programResidents.TryFind value |> Option.map _.Sources |> Option.defaultValue []
                    edge EdgeRole.SuspensionLiveAcross
                        (List.distinct ([owner.Id; control.Generator; step.Origin] @ authority)) value)))
            let numeric value participants site =
                let node = obligationNode owner (NodeId.value owner.Id) {
                    Id = sprintf "seq_%d_state_%d" (NodeId.value owner.Id) (NodeId.value site)
                    Kind = "continuation-state-range"; Logic = "QF_LIA"
                    Statement = "This enumerated continuation discriminant lies within its finite state range; this does not prove control flow, liveness or frame lifetime."
                    Source = fmtRange owner.Range; Refs = []
                    Body = ObligationBody.IntegerLiteralRange(value, -1I, maximum) }
                { Enrichment.empty with NewNodes = [node]; NewEdges = [constrains participants node] }
            let obligations =
                numeric 0I [owner.Id; control.Generator; frame.State; machine.ResumeBodies[0]] machine.ResumeBodies[0]
                :: (writes |> List.map (fun (site, value) ->
                    numeric (literal value).Value [owner.Id; control.Generator; frame.State; site; value] site))
                |> Enrichment.concat
            Ok { obligations with NewEdges = initial :: initialAction :: completed :: relations @ obligations.NewEdges }

// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Realize a settled continuation control graph as ordinary typed PSG regions.
/// Persistent slots hold only captures and values crossing suspension; scratch
/// slots are local to one pull. Alex sees the resulting regions and accesses.
module Clef.Compiler.Baker.Recipes.SequenceMachineRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
module C = Clef.Compiler.Baker.Ingredients.Continuations
module Aggregate = Clef.Compiler.Baker.Ingredients.AggregateCopies
module AggregateValues = Clef.Compiler.PSGSaturation.SemanticGraph.AggregateValues
module Control = Clef.Compiler.Baker.Recipes.SequenceControlRecipes

type Machine = {
    Nodes: SemanticNode list
    Root: NodeId
    PersistentReferences: NodeId list
    ScratchReferences: NodeId list
    ValueSources: (NodeId * NodeId) list
    Initializers: Map<NodeId, (NodeId * NodeId) list>
    CaseBodies: Map<int, NodeId>
    ResumeBodies: Map<int, NodeId>
    ResumeTargets: Map<int, int>
    CompletedBody: NodeId
    AggregateEvidence: Hyperedge list
}

// A recipe-local construction marker, extracted into finite provenance edges
// by the caller and removed from every node before it joins the graph.
let private sourceKey = "Continuation.RecipeSource"

let private isUnit ty = Types.tryGetNTUKind ty = Some NTUKind.NTUunit

/// Callable declarations are code identities, not mutable activation values.
/// Function-valued expressions still require their own settled representation.
let rec isSymbolic (graph: SemanticGraph) seen id =
    if Set.contains id seen then false else
    let seen = Set.add id seen
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.Intrinsic _ | SemanticKind.PlatformBinding _; Type = NativeType.TFun _ } -> true
    | Some { Kind = SemanticKind.VarRef (_, Some definition) } -> isSymbolic graph seen definition
    | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } ->
        match graph.Nodes.TryFind value with
        | Some ({ Kind = SemanticKind.Lambda(_, _, [], _, _) } as implementation) ->
            implementation.Metadata.TryFind ClosureMetadata.LambdaExpression <> Some(MetadataValue.Bool true)
            && implementation.Metadata.TryFind ClosureMetadata.RequiresClosurePair <> Some(MetadataValue.Bool true)
        | _ -> false
    | _ -> false

let requiredValues (graph: SemanticGraph) (control: Control.Control) =
    // Assignment defines a new cell value, not a new cell allocation. Only
    // declarations evaluated by this owner and explicit captures belong in its
    // frame or scratch storage. Other resolved declarations stay references.
    let declarations =
        control.Steps.Values |> Seq.choose (fun step ->
            match step.Instruction with
            | Control.Instruction.Evaluate id ->
                match graph.Nodes.TryFind id with
                | Some { Kind = SemanticKind.Binding _ } -> Some id
                | _ -> None
            | _ -> None) |> Set.ofSeq
    let captures =
        match graph.Nodes[control.Owner].Kind with
        | SemanticKind.SeqExpr(_, captures) -> captures |> List.choose _.SourceNodeId |> Set.ofList
        | _ -> Set.empty
    control.Steps.Values |> Seq.fold (fun all step -> Set.union all (Set.union step.Uses step.Defines)) Set.empty
    |> Set.filter (fun id ->
        graph.Nodes.TryFind id |> Option.exists (fun node ->
            not (isUnit node.Type)
            && not (isSymbolic graph Set.empty id)
            && (match node.Kind with
                | SemanticKind.Binding _ -> declarations.Contains id || captures.Contains id
                | _ -> true)))

let build (graph: SemanticGraph) (control: Control.Control) (frame: ContinuationFrame) : Machine =
    let owner = graph.Nodes[control.Owner]
    let generator = graph.Nodes[control.Generator]
    let formal = graph.Nodes[frame.Formal]
    let envType = match owner.Type with NativeType.TSeq item -> NativeType.TSeqEnumerator item | _ -> formal.Type
    let persistent = frame.Slots |> List.map _.Source |> Set.ofList
    let scratch = frame.ScratchSlots |> List.map _.Source |> Set.ofList
    let range = { owner.Range with End = owner.Range.Start }
    let state = SaturationState.create range "Seq.resume" (NodeId.value owner.Id) owner.Id graph.Platform
    let aggregateEvidence = ResizeArray<Hyperedge>()
    let body = saturation {
        let! storage = C.create (SemanticKind.ContinuationStorage owner.Id) (Types.mkArrayType Types.uint8Type) []
        let! storageBinding = letBind "__continuation_storage" storage (Types.mkArrayType Types.uint8Type)
        let! initialPc = C.index control.Entry
        let! pc = C.mutableBinding "__continuation_pc" initialPc Types.nintType
        let! no = boolLit false
        let! running = C.mutableBinding "__continuation_running" no Types.boolType
        let! noResult = boolLit false
        let! produced = C.mutableBinding "__continuation_produced" noResult Types.boolType

        let frameRef slot =
            if persistent.Contains slot then varRef "__continuation_environment" (Some formal.Id) envType
            else varRef "__continuation_storage" (Some storageBinding) (Types.mkArrayType Types.uint8Type)
        let read id = saturation {
            if persistent.Contains id || scratch.Contains id then
                let! source = frameRef id
                return! C.read source graph.Nodes[id]
            else
                return id
        }
        let write id value = saturation {
            if persistent.Contains id || scratch.Contains id then
                let! target = frameRef id
                match AggregateValues.scalarOption graph graph.Nodes[id].Type with
                | Some(inner, _, _) ->
                    let! destination = C.read target graph.Nodes[id]
                    let! copy, evidence = Aggregate.option value destination inner
                    aggregateEvidence.Add evidence
                    return copy
                | None -> return! C.write target id value
            else
                // Unit operations and symbolic callable identities have no
                // runtime slot. Their evaluation effects remain in the block.
                return! C.create (SemanticKind.Literal NativeLiteral.Unit) Types.unitType []
        }
        let setPc label = saturation {
            let! value = C.index label
            return! C.assign pc "__continuation_pc" Types.nintType value
        }
        let stop hasValue = saturation {
            let! value = boolLit hasValue
            let! record = C.assign produced "__continuation_produced" Types.boolType value
            let! no = boolLit false
            let! halt = C.assign running "__continuation_running" Types.boolType no
            return! C.block [record; halt] Types.unitType
        }
        let rec destination seen label =
            if Set.contains label seen then label else
            match control.Steps[label] with
            | { Instruction = Control.Instruction.Pass; Successors = [{ Target = next; Transfer = EvaluationTransfer.Continue }] } ->
                destination (Set.add label seen) next
            | _ -> label
        let target label = destination Set.empty label
        let next (step: Control.Step) =
            match step.Successors with
            | [arc] -> setPc (target arc.Target)
            | _ -> invalidOp "An evaluated continuation operation must have exactly one successor."

        let evaluate id = saturation {
            let source = graph.Nodes[id]
            match source.Kind with
            | SemanticKind.Binding _ ->
                match source.Children with
                | [value] -> let! input = read value
                             return! write id input
                | _ -> return! C.create (SemanticKind.Literal NativeLiteral.Unit) Types.unitType []
            | SemanticKind.VarRef (_, Some declaration) when persistent.Contains declaration || scratch.Contains declaration ->
                let! input = read declaration
                return! write id input
            | SemanticKind.Set (reference, value) ->
                match graph.Nodes[reference].Kind with
                | SemanticKind.VarRef (name, Some declaration) ->
                    let! input = read value
                    if persistent.Contains declaration || scratch.Contains declaration then
                        return! write declaration input
                    else
                        // The source resolves this existing cell outside the
                        // owner. Preserve that identity instead of allocating
                        // a private copy or discarding its observable write.
                        return! C.assign declaration name graph.Nodes[declaration].Type input
                | _ -> invalidOp "Continuation assignment requires a settled declaration identity."
            | _ when isSymbolic graph Set.empty id ->
                return! C.create (SemanticKind.Literal NativeLiteral.Unit) Types.unitType []
            | _ ->
                let dependencies =
                    kindEdges source.Id source.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                    |> fun derived -> (if List.isEmpty derived then source.Children else derived)
                    |> List.distinct
                let! inputs = dependencies |> C.collect (fun child -> saturation {
                    let! value = read child
                    return child, value
                })
                let references = Map.ofList inputs
                let kind = Clef.Compiler.Nanopass.FoldIn.remapKindReferences references source.Kind
                let! kind, formation = saturation {
                    match kind with
                    | SemanticKind.SeqExpr (generator, captures) ->
                        let! captures = captures |> C.collect (fun capture -> saturation {
                            match capture.SourceNodeId with
                            | Some id when persistent.Contains id || scratch.Contains id ->
                                let! value = saturation {
                                    if capture.IsMutable then
                                        let! storage = frameRef id
                                        return! C.create (SemanticKind.FrameBorrow(storage, id)) (NativeType.TByref(capture.Type, ByrefKind.InOut)) [storage]
                                    else return! read id
                                }
                                return { capture with SourceNodeId = Some value }, Some value
                            | _ -> return capture, None
                        })
                        return SemanticKind.SeqExpr(generator, List.map fst captures), List.choose snd captures
                    | _ -> return kind, []
                }
                let! kind, cloneType, cloneChildren, initializedInPlace = saturation {
                    match kind, AggregateValues.scalarOption graph source.Type with
                    | SemanticKind.DUConstruct(name, index, payload, None), Some _ when persistent.Contains id || scratch.Contains id ->
                        let! storage = frameRef id
                        let! destination = C.read storage source
                        return SemanticKind.DUInitialize(destination, name, index, payload), Types.unitType,
                               destination :: Option.toList payload, true
                    | _ ->
                        return kind, source.Type,
                               source.Children |> List.map (fun child -> references.TryFind child |> Option.defaultValue child), false
                }
                let! state = getUserState
                let clone = mkNode state kind cloneType cloneChildren
                let clone = { clone with ValueRange = source.ValueRange; SRTPResolution = source.SRTPResolution
                                         Range = source.Range
                                         Metadata = clone.Metadata.Add(sourceKey, MetadataValue.NodeId source.Id) }
                do! emit clone
                do! (match kind with
                     | SemanticKind.DUInitialize(destination, _, _, payload) ->
                         aggregateEvidence.Add {
                             Sources = List.distinct (source.Id :: destination :: Option.toList payload)
                             Target = clone.Id; Class = EdgeClass.Provenance; Role = EdgeRole.AggregateCopy; Ordinal = 1 }
                         preturn ()
                     | _ -> preturn ())
                let! save =
                    if initializedInPlace then C.create (SemanticKind.Literal NativeLiteral.Unit) Types.unitType []
                    else write id clone.Id
                // Capture formation is eager at this constructor occurrence.
                // Its reads/borrows are ordinary evaluation operands; the
                // deferred generator is not entered while forming the value.
                return! C.block (formation @ [clone.Id; save]) Types.unitType
        }

        let active = control.Steps |> Map.toList |> List.filter (fun (label, _) -> target label = label)
        let! cases = active |> C.collect (fun (label, step) -> saturation {
            let! action = saturation {
                match step.Instruction with
                | Control.Instruction.Evaluate id ->
                    let! operation = evaluate id
                    let! advance = next step
                    return! C.block [operation; advance] Types.unitType
                | Control.Instruction.Copy (output, input) ->
                    let! value = read input
                    let! save = write output value
                    let! advance = next step
                    return! C.block [save; advance] Types.unitType
                | Control.Instruction.Branch condition ->
                    let! condition = read condition
                    let yes = step.Successors |> List.find (fun arc -> arc.Transfer = EvaluationTransfer.WhenTrue)
                    let no = step.Successors |> List.find (fun arc -> arc.Transfer = EvaluationTransfer.WhenFalse)
                    let! yesBody = setPc (target yes.Target)
                    let! noBody = setPc (target no.Target)
                    return! C.create (SemanticKind.IfThenElse(condition, yesBody, Some noBody)) Types.unitType [condition; yesBody; noBody]
                | Control.Instruction.Suspend (payload, resume) ->
                    let! value = read payload
                    let! save = write frame.Current value
                    let! stateValue = C.integer resume
                    let! stateWrite = write frame.State stateValue
                    let! donePull = stop true
                    return! C.block [save; stateWrite; donePull] Types.unitType
                | Control.Instruction.Complete ->
                    let! finished = C.integer -1
                    let! mark = write frame.State finished
                    let! donePull = stop false
                    return! C.block [mark; donePull] Types.unitType
                | Control.Instruction.Pass -> return! next step
            }
            return label, action
        })
        let! exhausted = stop false
        let! pcValue = varRef "__continuation_pc" (Some pc) Types.nintType
        let! selection = C.dispatch pcValue cases exhausted
        let! guard = varRef "__continuation_running" (Some running) Types.boolType
        let! loop = C.create (SemanticKind.WhileLoop(guard, selection)) Types.unitType [guard; selection]

        let! entries = control.ResumeEntries |> Map.toList |> C.collect (fun (resume, entry) -> saturation {
            let! setEntry = setPc (target entry)
            let! yes = boolLit true
            let! start = C.assign running "__continuation_running" Types.boolType yes
            let! body = C.block [setEntry; start] Types.unitType
            return resume, body
        })
        let! stateValue = read frame.State
        let! alreadyDone = stop false
        let! enter = C.dispatch stateValue entries alreadyDone
        let! result = varRef "__continuation_produced" (Some produced) Types.boolType
        let! body = C.block [storageBinding; pc; running; produced; enter; loop; result] Types.boolType
        do! emit { formal with Type = envType }
        let kind = SemanticKind.Lambda(["__continuation_environment", envType, formal.Id], body, [], None, LambdaContext.SeqGenerator)
        do! enrich generator kind (NativeType.TFun(envType, Types.boolType)) [formal.Id; body] generator.EmissionStrategy false
        return body, Map.ofList cases, Map.ofList entries, control.ResumeEntries |> Map.map (fun _ entry -> target entry), alreadyDone
    }
    match run state body with
    | Matched (root, caseBodies, resumeBodies, resumeTargets, completed), nodes ->
        let envRefs = nodes |> List.choose (fun node ->
            match node.Kind with SemanticKind.VarRef (_, Some id) when id = formal.Id -> Some node.Id | _ -> None)
        let scratchAllocations = nodes |> List.choose (fun node ->
            match node.Kind with SemanticKind.ContinuationStorage _ -> Some node.Id | _ -> None) |> Set.ofList
        let scratchBindings = nodes |> List.choose (fun node ->
            match node.Kind, node.Children with SemanticKind.Binding _, [value] when scratchAllocations.Contains value -> Some node.Id | _ -> None) |> Set.ofList
        let scratchRefs = nodes |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.VarRef (_, Some id) when scratchBindings.Contains id -> Some node.Id
            | _ when scratchAllocations.Contains node.Id || scratchBindings.Contains node.Id -> Some node.Id
            | _ -> None)
        let valueSources = nodes |> List.choose (fun node ->
            match node.Kind, node.Metadata.TryFind sourceKey with
            | SemanticKind.FrameRead(_, source), _ | _, Some (MetadataValue.NodeId source) -> Some(node.Id, source)
            | _ -> None)
        let initializers =
            nodes |> List.choose (fun node ->
                match node.Kind, node.Metadata.TryFind sourceKey with
                | SemanticKind.SeqExpr(_, captures), Some (MetadataValue.NodeId source) ->
                    match graph.Nodes[source].Kind with
                    | SemanticKind.SeqExpr(_, original) ->
                        List.zip original captures
                        |> List.choose (fun (slot, value) -> Option.map2 (fun s v -> s, v) slot.SourceNodeId value.SourceNodeId)
                        |> fun pairs -> Some(node.Id, pairs)
                    | _ -> None
                | _ -> None) |> Map.ofList
        { Nodes = nodes |> List.map (fun node -> { node with Metadata = node.Metadata.Remove sourceKey })
          Root = root; PersistentReferences = formal.Id :: envRefs; ScratchReferences = scratchRefs
          ValueSources = valueSources; Initializers = initializers
          CaseBodies = caseBodies; ResumeBodies = resumeBodies
          ResumeTargets = resumeTargets; CompletedBody = completed
          AggregateEvidence = List.ofSeq aggregateEvidence }
    | NoMatch reason, _ -> invalidOp (sprintf "Continuation synthesis failed: %s" reason)

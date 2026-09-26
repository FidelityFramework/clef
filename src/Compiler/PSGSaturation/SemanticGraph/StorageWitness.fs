// SPDX-License-Identifier: MIT
/// Materialize storage, startup and requirement authority at the source
/// boundary. All graph/proof validation happens here, before an emitter can
/// obtain the immutable projection for the exact completed graph.
module Clef.Compiler.PSGSaturation.SemanticGraph.StorageWitness

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Lazies = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues
module LazyRuntime = Clef.Compiler.Nanopass.LazyRuntime
module SequencePrograms = Clef.Compiler.Nanopass.SequenceProgramInstances

let private edgeKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Sources, edge.Target, edge.Ordinal

let private sequence (graph: SemanticGraph) occurrence (flow: SequenceFlow) =
    let codata = graph.Codata.Value
    let element =
        graph.Nodes.TryFind occurrence |> Option.bind (fun node ->
            match applySubst node.Type with
            | NativeType.TSeq item -> Some(item, false)
            | NativeType.TSeqEnumerator item -> Some(item, true)
            | _ -> None)
    match element with
    | Some(item, iterator) when flow.Occurrence = occurrence && flow.Unknown.IsEmpty && not flow.Owners.IsEmpty &&
                               applySubst item = applySubst flow.ElementType && iterator = flow.IsEnumerator ->
        let families = codata.SequenceFamilies.Values |> Seq.filter (fun family -> family.Participants.Contains occurrence) |> Seq.toList
        match families with
        | [family] when family.Bytes > 0 && family.Alignment > 0 && applySubst family.ElementType = applySubst item &&
                        (flow.Owners |> Set.forall family.Members.ContainsKey) ->
            let validMember owner (memberContract: SequenceFamilyMember) =
                let dependencies =
                    List.distinct (List.ofSeq family.Members.Keys @
                        [memberContract.Generator; memberContract.Formal; memberContract.State] @
                        (memberContract.Slots |> List.map _.Source) @ memberContract.Obligations)
                let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceFamilyLayout && edge.Target = owner)
                let resident =
                    match rows with
                    | [{ Class = EdgeClass.Suspension; Ordinal = 0; Sources = sources }] -> sources = dependencies
                    | _ -> false
                match codata.ContinuationFrames.TryFind owner, graph.Nodes.TryFind owner,
                      graph.Nodes.TryFind memberContract.Generator, graph.Nodes.TryFind memberContract.Formal with
                | Some frame, Some { Kind = SemanticKind.SeqExpr(generator, _); Type = NativeType.TSeq element },
                  Some { Kind = SemanticKind.Lambda([_, parameterType, formal], body, _, _, LambdaContext.SeqGenerator); Type = signature },
                  Some { Kind = SemanticKind.PatternBinding _; Type = formalType } ->
                    resident && frame.Owner = owner && generator = frame.Generator && generator = memberContract.Generator &&
                    formal = frame.Formal && formal = memberContract.Formal &&
                    applySubst element = applySubst item && applySubst formalType = NativeType.TSeqEnumerator(applySubst item) &&
                    applySubst parameterType = applySubst formalType && applySubst signature = applySubst memberContract.Signature &&
                    applySubst signature = NativeType.TFun(applySubst formalType, Types.boolType) &&
                    (graph.Nodes.TryFind body |> Option.exists (fun node -> applySubst node.Type = Types.boolType)) &&
                    frame.Bytes = family.Bytes && frame.Alignment = family.Alignment && frame.State = memberContract.State &&
                    frame.Slots = memberContract.Slots &&
                    (frame.Slots |> List.tryFind (fun slot -> slot.Source = frame.State) |> Option.exists (fun slot ->
                        slot.Field.Slot = family.StateField.Slot && slot.Field.Offset = family.StateField.Offset &&
                        slot.Field.Size = family.StateField.Size && slot.Field.Align = family.StateField.Align)) &&
                    (frame.Slots |> List.filter _.IsCapture |> List.map _.Source |> Set.ofList) = memberContract.Captures &&
                    (frame.Slots |> List.filter (fun slot -> not slot.IsCapture && slot.Source <> frame.State) |> List.map _.Source |> Set.ofList) = memberContract.Uninitialized &&
                    frame.Obligations = memberContract.Obligations &&
                    (frame.Slots |> List.tryFind (fun slot -> slot.Source = frame.Current) |> Option.map _.Source) = memberContract.Current &&
                    (memberContract.Current |> Option.forall (fun current ->
                        match frame.Slots |> List.tryFind (fun slot -> slot.Source = current), family.CurrentField, family.CurrentRepresentation with
                        | Some slot, Some field, Some(valueType, holds) ->
                            slot.Field.Slot = field.Slot && slot.Field.Offset = field.Offset &&
                            slot.Field.Size = field.Size && slot.Field.Align = field.Align &&
                            slot.Holds = holds && applySubst slot.ValueType = applySubst valueType
                        | _ -> false))
                | _ -> false
            let hasCurrent = family.Members.Values |> Seq.exists (fun memberContract -> memberContract.Current.IsSome)
            if (family.Members |> Map.forall validMember) &&
               hasCurrent = family.CurrentField.IsSome && hasCurrent = family.CurrentRepresentation.IsSome &&
               (family.CurrentRepresentation |> Option.forall (fun (ty, _) -> applySubst ty = applySubst item)) then
                Ok { Flow = flow; Family = family }
            else Error "Sequence family disagrees with its actual generators, formals, fields or layout obligations."
        | _ -> Error "Sequence occurrence has no unique complete source protocol."
    | _ -> Error "Sequence occurrence has incomplete or differently typed source alternatives."

let private failure occurrence participants reason : WitnessProjectionFailure =
    { Occurrence = occurrence; Reason = reason; Participants = participants }

let project (graph: SemanticGraph) : Result<StorageWitnessProjection, WitnessProjectionFailure list> =
    let codata = graph.Codata.Value
    let errors = ResizeArray<WitnessProjectionFailure>()
    let reject site reason =
        let incidence = graph.Nodes.TryFind site |> Option.map (fun node -> kindEdges site node.Kind) |> Option.defaultValue []
        let participants =
            incidence @ (graph.Edges |> List.filter (fun edge -> edge.Target = site))
            |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList |> Set.add site
        errors.Add(failure (Some site) participants reason)
    let sourceLazies = Lazies.settle graph
    if graph.Platform.IsSome then
        for owner in sourceLazies.Instances.Keys do
            if not (codata.LazyLayouts.ContainsKey owner) then
                reject owner "Lazy source instance has no published storage layout."
    let lazyContracts =
        codata.LazyLayouts |> Map.toList |> List.choose (fun (owner, layout) ->
            match sourceLazies.Instances.TryFind owner with
            | Some contract when owner = layout.Owner && LazyRuntime.validate graph layout ->
                Some(owner, { Layout = layout; ElementType = applySubst contract.ElementType; ThunkBody = contract.ThunkBody })
            | _ -> reject owner "Lazy layout does not retain its current instance, storage and memoization proof."; None) |> Map.ofList
    let lazyOwner = Lazies.tryOwner graph
    for node in graph.Nodes.Values do
        if node.IsReachable then
            match lazyOwner node.Id with
            | Some owner when lazyContracts.ContainsKey owner && codata.LazyOrigins.TryFind node.Id <> Some owner ->
                reject node.Id "Lazy occurrence is missing its current source origin."
            | _ -> ()
    let lazyOccurrences =
        codata.LazyOrigins |> Map.toList |> List.choose (fun (occurrence, owner) ->
            match graph.Nodes.TryFind occurrence, lazyContracts.TryFind owner with
            | Some _, Some _ when lazyOwner occurrence = Some owner -> Some(occurrence, owner)
            | _ -> reject occurrence "Lazy origin has no current source layout."; None) |> Map.ofList
    let lazyValues =
        lazyOccurrences |> Map.toSeq |> Seq.choose (fun (occurrence, owner) ->
            match applySubst graph.Nodes[occurrence].Type with
            | NativeType.TLazy element when applySubst element = lazyContracts[owner].ElementType -> Some occurrence
            | _ -> None) |> Set.ofSeq
    let definitionOnlyThunks =
        lazyContracts.Values |> Seq.choose (fun contract ->
            match graph.Nodes.TryFind contract.Layout.Thunk with
            | Some { Kind = SemanticKind.Lambda(_, _, [], _, LambdaContext.LazyThunk) }
                when not (codata.Closures.ContainsKey contract.Layout.Thunk) -> Some contract.Layout.Thunk
            | _ -> None) |> Set.ofSeq
    let sequences =
        codata.SequenceFlows |> Map.toList |> List.choose (fun (occurrence, flow) ->
            match graph.Nodes.TryFind occurrence with
            | Some node when CallableCarriers.valueShape graph node = CallableValueShape.Sequence occurrence ->
                match sequence graph occurrence flow with
                | Ok contract -> Some(occurrence, contract)
                | Error reason -> reject occurrence reason; None
            | _ -> None) |> Map.ofList
    if graph.Platform.IsSome then
        for node in graph.Nodes.Values do
            if node.IsReachable && CallableCarriers.valueShape graph node = CallableValueShape.Sequence node.Id &&
               not (sequences.ContainsKey node.Id) then
                reject node.Id "Sequence source occurrence has no published complete protocol."
    let copies =
        if codata.SequenceTemplateCopies.IsEmpty then Map.empty else
        let current, evidence, _ =
            Clef.Compiler.Nanopass.SequenceFamilies.copies graph codata.SequenceFamilies codata.SequenceFlows
                codata.Escapes codata.ContinuationRegions codata.SequenceInitializers codata.SequenceDestinations
        codata.SequenceTemplateCopies |> Map.filter (fun acquisition expected ->
            let rows = evidence.NewEdges |> List.filter (fun edge -> edge.Target = acquisition)
            let valid =
                current.TryFind acquisition = Some expected && not rows.IsEmpty &&
                rows |> List.forall (fun edge ->
                    let resident = graph.Edges |> List.filter (fun candidate -> candidate.Role = edge.Role && candidate.Target = edge.Target && candidate.Ordinal = edge.Ordinal)
                    match resident with [actual] -> edgeKey actual = edgeKey edge | _ -> false)
            if not valid then reject acquisition "Sequence copy no longer retains its exact source representation, storage and initializer proof."
            valid)
    let startup =
        match ProgramInitialization.read graph with
        | Some plan ->
            Some { EntryBinding = plan.EntryBinding; EntryLambda = plan.EntryLambda; SourceBinding = plan.SourceBinding
                   SourceLambda = plan.SourceLambda; OriginalBody = plan.OriginalBody; Spine = plan.Spine
                   EntryCall = plan.EntryCall; Symbol = plan.Symbol; ValueBindings = plan.ValueBindings
                   Initializers = plan.Initializers |> List.map (fun row ->
                       { Module = row.Module; Binding = row.Binding; Initializer = row.Initializer; Ordinal = row.Ordinal }) }
        | None ->
            for row in graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ProgramInitialization) do
                reject row.Target "Program startup no longer retains its exact source execution contract."
            None
    let bindings = startup |> Option.map _.ValueBindings |> Option.defaultValue Set.empty
    let authorities = bindings |> Set.filter (fun binding -> ProgramInitialization.tryValueAuthority graph binding |> Option.isSome)
    let lazyPrograms =
        bindings |> Set.toList |> List.choose (fun binding ->
            LazyRuntime.programInstance graph binding |> Option.map (fun (owner, allocation) ->
                binding, ({ Owner = owner; Allocation = allocation }: LazyProgramWitness))) |> Map.ofList
    let sequencePrograms =
        bindings |> Set.toList |> List.choose (fun binding ->
            SequencePrograms.programInstance graph binding |> Option.map (fun instance ->
                binding, ({ Owner = instance.Owner; Generator = instance.Generator; Allocation = instance.Allocation
                            Participants = instance.Participants }: SequenceProgramWitness))) |> Map.ofList
    let requirements =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.IsReachable, node.Kind with
            | true, SemanticKind.Require _ ->
                match Requirements.tryRequirement graph node.Id with
                | Some contract ->
                    Some(node.Id, { Site = contract.Site; Condition = contract.Condition; Diagnostic = contract.Diagnostic
                                    Frontier = contract.Frontier; Continuation = contract.Continuation
                                    PatternTest = contract.PatternTest; Participants = contract.Participants })
                | None -> reject node.Id "Requirement has no current ordered source contract."; None
            | _ -> None) |> Map.ofSeq
    let patternRequirements =
        requirements.Values |> Seq.choose (fun contract ->
            contract.PatternTest |> Option.bind (fun _ ->
                match Requirements.tryPatternRequirement graph contract.Continuation with
                | Some actual when actual.Site = contract.Site -> Some(contract.Continuation, contract.Site)
                | _ -> reject contract.Site "Pattern requirement does not retain its exact selected continuation."; None)) |> Map.ofSeq
    let inventory =
        match ProgramStorage.read graph with
        | Some current ->
            for KeyValue(identity, reason) in current.Unresolved do reject (ProgramStorage.sourceOf identity) reason
            current
        | None ->
            let identities = Set.union (codata.ProgramStorage.Entries.Keys |> Set.ofSeq) (codata.ProgramStorage.Unresolved.Keys |> Set.ofSeq)
            for identity in identities do reject (ProgramStorage.sourceOf identity) "Writable program inventory does not retain its current source authority."
            if identities.IsEmpty then errors.Add(failure None Set.empty "Writable program inventory omits current source allocations.")
            ProgramStorageInventory.empty
    let anchors =
        match graph.StaticStringPool with
        | None ->
            let expected, _ = StaticStringLayout.settle graph
            match expected.StaticStringPool with
            | Some pool -> reject pool.DeclarationNode "Committed source literals have no published immutable allocation."
            | None -> ()
            []
        | Some pool ->
            let backing = StaticStringLayout.literalEvidence graph
            if pool.Entries |> List.collect _.NodeIds |> List.exists (backing.ContainsKey >> not) then
                reject pool.DeclarationNode "Static string pool no longer retains its exact source backing proof."
            let expected = ObligationBody.StaticStorageLayout(
                pool.Entries |> List.map (fun entry -> entry.Offset, entry.StorageLength, 1),
                pool.UsedSize, pool.Size, pool.Alignment, pool.Capacity, pool.SpaceAlignment, pool.Granularity)
            let anchors = graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with SemanticKind.Obligation info when info.Body = expected -> Some info.Id | _ -> None) |> Seq.toList
            if anchors.IsEmpty then reject pool.DeclarationNode "Static string pool has no matching source layout obligation."
            anchors
    if errors.Count > 0 then Error(List.ofSeq errors) else
    Ok { Lazies = lazyContracts; LazyOccurrences = lazyOccurrences; LazyValues = lazyValues
         DefinitionOnlyThunks = definitionOnlyThunks; LazyPrograms = lazyPrograms
         Sequences = sequences; SequenceCopies = copies; SequencePrograms = sequencePrograms
         Startup = startup; SlotAuthorities = authorities; Requirements = requirements; PatternRequirements = patternRequirements
         ProgramStorage = inventory; LiteralPoolAnchors = anchors }

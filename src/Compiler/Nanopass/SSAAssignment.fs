// SPDX-License-Identifier: MIT
/// Pure, cone-scoped SSA assignment and NodeId reconciliation nanopass.
///
/// In the Fidelity architecture, Alex witnesses values directly from published
/// `NodeId`s and ordinals (`Alex.Traversal.Values.value nodeId k = V(NodeId.value nodeId, k)`).
/// Where graph structure is unchanged (outside the delta cone in selective rebuild),
/// `reconcileAndAssign` retains the baseline `NodeId`s and `SSAId(node, ordinal)`
/// assignments across the graph and its codata; where structure is affected or newly
/// elaborated, `NodeId`s and `SSAId(node, ordinal)` assignments advance monotonically
/// above the baseline high-water mark without reuse; and a full release rebuild
/// (`normalize`) starts cold from the freshly reset graph without carrying prior state.
module Clef.Compiler.Nanopass.SSAAssignment

open Clef.Compiler.Baker.Ingredients
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

let nodeOf (SSAId(n, _)) = n
let ordinalOf (SSAId(_, k)) = k

let private normalizeContiguousRuns (isMatch: Participant -> bool) (renumber: bool) (participants: Participant list) : Participant list =
    let flushRun (runRev: Participant list) (acc: Participant list) =
        let sorted =
            runRev
            |> List.rev
            |> List.sortBy (fun p -> p.Node, p.Group, p.Ordinal)
        let normalized =
            if renumber then sorted |> List.mapi (fun i p -> { p with Ordinal = i })
            else sorted
        List.rev normalized @ acc
    let rec loop (runRev: Participant list) (acc: Participant list) (remaining: Participant list) =
        match remaining with
        | [] ->
            let finalAcc = if runRev.IsEmpty then acc else flushRun runRev acc
            List.rev finalAcc
        | head :: tail when isMatch head ->
            loop (head :: runRev) acc tail
        | head :: tail ->
            let nextAcc = if runRev.IsEmpty then acc else flushRun runRev acc
            loop [] (head :: nextAcc) tail
    loop [] [] participants

let private normalizeRuntimeParticipants (runtime: MemoryRegionRuntime) : MemoryRegionRuntime =
    let ordered =
        runtime.Participants
        |> normalizeContiguousRuns (fun p -> p.Role = ParticipantRole.RegionRuntimeDescriptor) true
        |> normalizeContiguousRuns (fun p -> p.Role = ParticipantRole.RegionRuntimeAcquire) true
        |> normalizeContiguousRuns (fun p -> p.Role = ParticipantRole.RegionRuntimeRelease) true
    { runtime with Participants = ordered }

let private normalizeMemoryOperation (operation: MemoryWitnessOperation) : MemoryWitnessOperation =
    match operation with
    | MemoryWitnessOperation.Region witness ->
        let participants =
            witness.Participants
            |> normalizeContiguousRuns (fun p -> p.Role = ParticipantRole.RegionDeclaration) false
        let runtime = witness.Runtime |> Option.map normalizeRuntimeParticipants
        MemoryWitnessOperation.Region { witness with Participants = participants; Runtime = runtime }
    | _ -> operation

let private normalizeBoundaryDomain (d: BoundaryDomain) : BoundaryDomain =
    { d with
        ResourceEvidence =
            d.ResourceEvidence
            |> Option.map (fun ev -> { ev with Accesses = List.sort ev.Accesses })
        WritableBufferDeclarations = List.sort d.WritableBufferDeclarations
        WritableBufferUses = List.sort d.WritableBufferUses
        ReadOnlyBufferDeclarations = List.sort d.ReadOnlyBufferDeclarations
        ReadOnlyBufferUses = List.sort d.ReadOnlyBufferUses
        BorrowedResultViewDeclarations = List.sort d.BorrowedResultViewDeclarations
        BorrowedResultViewUses = List.sort d.BorrowedResultViewUses
        BufferAbsences = List.sort d.BufferAbsences
        CountedEntryArrays = List.sort d.CountedEntryArrays
        ResourceDeclarations = List.sort d.ResourceDeclarations
        ResourceAccesses = List.sort d.ResourceAccesses
        Imports = List.sort d.Imports
        Calls = List.sort d.Calls
        Entries = List.sort d.Entries
        CallbackInvocations = List.sort d.CallbackInvocations
        CallbackAbsences = List.sort d.CallbackAbsences
        ClosedEntries = List.sort d.ClosedEntries }

let private normalizeSequenceRangeAuthority (authority: SequenceRangeAuthority) : SequenceRangeAuthority =
    { authority with
        Relations = List.sort authority.Relations
        Obligations = List.sortBy fst authority.Obligations }

let private normalizeRangeContextFacts (facts: RangeContextFacts) : RangeContextFacts =
    { facts with CaptureRelations = List.sort facts.CaptureRelations }

let private normalizeNumericDomain (d: NumericDomain) : NumericDomain =
    { d with
        SequenceRangeAuthority = d.SequenceRangeAuthority |> Option.map normalizeSequenceRangeAuthority
        RangeContextFacts = d.RangeContextFacts |> Option.map normalizeRangeContextFacts
        ForeignResultUses = List.sortBy (fun (u: ForeignResultUse) -> u.Application.Context, u.Application.Call) d.ForeignResultUses
        FiniteCellObligations = List.sortBy fst d.FiniteCellObligations
        CaptureRelations = List.sort d.CaptureRelations }

let private normalizeEdge (edge: Hyperedge) : Hyperedge =
    match edge.Role with
    | EdgeRole.BoundaryDomain d ->
        { edge with Role = EdgeRole.BoundaryDomain (normalizeBoundaryDomain d) }
    | EdgeRole.NumericDomain d ->
        { edge with Role = EdgeRole.NumericDomain (normalizeNumericDomain d) }
    | EdgeRole.MemoryDomain d ->
        let operations = d.Operations |> List.map (fun (site, op) -> site, normalizeMemoryOperation op)
        { edge with Role = EdgeRole.MemoryDomain { d with Operations = operations } }
    | EdgeRole.MemoryOperation op ->
        { edge with Role = EdgeRole.MemoryOperation (normalizeMemoryOperation op) }
    | _ -> edge

let private sortSuffix (prefixLen: int) (originalSources: NodeId list) (currentSources: NodeId list) : NodeId list option =
    if originalSources.Length >= prefixLen && currentSources.Length = originalSources.Length then
        let _, origTail = List.splitAt prefixLen originalSources
        if origTail = List.sort origTail then
            let currPrefix, currTail = List.splitAt prefixLen currentSources
            let sortedTail = List.sort currTail
            if sortedTail <> currTail then Some (currPrefix @ sortedTail) else None
        else None
    else None

let private remapEdges (remap: NodeId -> NodeId) (edges: Hyperedge list) : Result<Hyperedge list, NodeId * string> =
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let unorderedKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, List.sort edge.Sources, edge.Target
    let callsBySite (rows: Hyperedge list) =
        rows
        |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCall call -> Some (call.Site, call) | _ -> None)
        |> Map.ofList
    let companionRows (calls: Map<NodeId, BoundaryCall>) (edge: Hyperedge) =
        let target = edge.Target
        match edge.Role with
        | EdgeRole.BoundaryDomain d ->
            [ Boundaries.domainRow target d; Boundaries.domainRewrite target d ]
            @ (d.IntrinsicDeclarations |> List.map (fun (site, imp) -> StringBytes.abiRow site imp))
            @ (d.IntrinsicImports |> List.map StringBytes.importRow)
            @ (d.IntrinsicCalls |> List.collect StringBytes.callRows)
            @ (d.IntrinsicProofs |> List.collect StringBytes.proofRows)
        | EdgeRole.BoundaryImport import -> [ Boundaries.importRow import ]
        | EdgeRole.BoundaryResourceDeclaration row -> [ Boundaries.row (EdgeRole.BoundaryResourceDeclaration row) 0 (Set.toList row.Participants) row.Identity ]
        | EdgeRole.BoundaryWritableBufferDeclaration row -> [ Boundaries.row (EdgeRole.BoundaryWritableBufferDeclaration row) 0 (Set.toList row.Participants) row.Identity ]
        | EdgeRole.BoundaryWritableBufferUse row -> [ Boundaries.row (EdgeRole.BoundaryWritableBufferUse row) 0 (Set.toList row.Participants) row.Call ]
        | EdgeRole.BoundaryBufferAbsence row -> [ Boundaries.row (EdgeRole.BoundaryBufferAbsence row) 0 (row.DeclarationFacts |> Map.keys |> Seq.toList) row.Quote ]
        | EdgeRole.BoundaryResourceAccess row -> [ Boundaries.row (EdgeRole.BoundaryResourceAccess row) 0 (Set.toList row.Participants) row.Site ]
        | EdgeRole.BoundaryEntry entry -> [ Boundaries.row (EdgeRole.BoundaryEntry entry) 0 (Set.toList entry.Participants) entry.Formation ]
        | EdgeRole.BoundaryCallbackInvocation invocation -> [ Boundaries.row (EdgeRole.BoundaryCallbackInvocation invocation) 0 (Set.toList invocation.Participants) invocation.Identity ]
        | EdgeRole.BoundaryCallbackAbsence row -> [ Boundaries.row (EdgeRole.BoundaryCallbackAbsence row) 0 (row.DeclarationFacts |> Map.keys |> Seq.toList) row.Quote ]
        | EdgeRole.BoundaryClosedEntry entry -> [ Boundaries.row (EdgeRole.BoundaryClosedEntry entry) 0 (Set.toList entry.Participants) entry.Formation ]
        | EdgeRole.BoundaryCall call -> Boundaries.callRow call :: Boundaries.operandRows call
        | EdgeRole.BoundaryCoverage coverage ->
            match calls.TryFind coverage.Site with
            | Some call -> Boundaries.coverageRows call coverage (Boundaries.coverageOutcome coverage)
            | None -> []
        | EdgeRole.NumericDomain d ->
            let valueProofRows =
                d.Values |> List.collect (fun carrier ->
                    match NumericValues.coverage carrier with
                    | Some body -> carrier.Obligations |> List.collect (fun ob -> NumericValues.proofRows carrier ob body)
                    | None -> [])
            [ NumericValues.domainRow target d; NumericValues.domainRewrite target d ]
            @ (d.Values |> List.map NumericValues.carrierRow)
            @ valueProofRows
            @ (d.Operations |> List.map NumericOperations.operationRow)
            @ (d.OperationProofs |> List.collect NumericOperations.proofRows)
            @ (d.IndexTransports |> List.collect NumericValues.indexRows)
            @ (d.ForeignResultUses |> List.collect NumericValues.foreignProofRows)
        | EdgeRole.MemoryDomain d ->
            let operations = Map.ofList d.Operations
            [ MemoryValues.domainRow target d; MemoryValues.domainRewrite target d ]
            @ (d.Operations |> List.map (MemoryValues.operationRow operations))
            @ (d.Proofs |> List.collect MemoryValues.proofRows)
            @ (d.ArrayCopies |> List.map MemoryValues.copyRow)
            @ (d.AllocationConstructions |> List.map MemoryValues.allocationConstructionRow)
            @ (d.CopyConstructions |> List.map MemoryValues.copyConstructionRow)
        | EdgeRole.SpatialModuleDomain d ->
            [ SpatialValues.domainRow target d; SpatialValues.domainRewrite target d ]
            @ (d.Hardware |> List.map SpatialValues.hardwareRow)
            @ (d.Kernels |> List.map SpatialValues.kernelRow)
            @ (d.Proofs |> List.collect SpatialValues.proofRows)
        | EdgeRole.KernelIngress ingress ->
            [ { Class = EdgeClass.Spatial; Role = EdgeRole.KernelIngress ingress; Ordinal = 0; Sources = Set.toList ingress.Participants; Target = ingress.Site } ]
        | _ -> []
    let paired = edges |> List.map (fun orig -> orig, normalizeEdge (NodeIdRemap.remapHyperedge remap orig))
    let origCalls = callsBySite edges
    let currCalls = callsBySite (paired |> List.map snd)
    let optionalClaimOwners (rows: Hyperedge list) =
        rows
        |> List.collect (fun edge ->
            match edge.Role with
            | EdgeRole.BoundaryCall call ->
                call.Arguments
                |> List.collect (fun operand ->
                    operand.OptionalEntry
                    |> Option.toList
                    |> List.collect BoundaryOptionalEntryChoice.leaves
                    |> List.map (fun leaf -> leaf.Obligation, call.Site))
            | _ -> [])
        |> Map.ofList
    let origOptionalClaims = optionalClaimOwners edges
    let origFiniteCellTargets =
        edges
        |> List.collect (fun edge ->
            match edge.Role with
            | EdgeRole.NumericDomain d -> d.FiniteCellObligations |> List.map fst
            | _ -> [])
        |> Set.ofList
    let expectedByPair =
        paired
        |> List.fold (fun acc (original, current) ->
            let origRows = companionRows origCalls original
            let currRows = companionRows currCalls current
            if origRows.IsEmpty || origRows.Length <> currRows.Length then acc
            else
                (acc, origRows, currRows)
                |||> List.fold2 (fun state origExpected currExpected ->
                    let pairKey = key origExpected, unorderedKey currExpected
                    Map.change pairKey (function
                        | None -> Some (Some currExpected)
                        | Some (Some prev) when key prev = key currExpected -> Some (Some prev)
                        | Some _ -> Some None) state)) Map.empty
    let rec mapAll acc remaining =
        match remaining with
        | [] -> Result.Ok (List.rev acc)
        | (original, current) :: rest ->
            match Map.tryFind (key original, unorderedKey current) expectedByPair with
            | Some (Some expected) ->
                let resolved = if current.Sources <> expected.Sources then { current with Sources = expected.Sources } else current
                mapAll (resolved :: acc) rest
            | Some None ->
                Result.Error (current.Target, "SSAAssignment: Ambiguous companion hyperedge correspondence during SSA remapping.")
            | None ->
                let canonicalTail =
                    match original.Role with
                    | EdgeRole.OrdinaryUnusedFormal -> sortSuffix 1 original.Sources current.Sources
                    | EdgeRole.OrdinaryUnusedActual -> sortSuffix 4 original.Sources current.Sources
                    | EdgeRole.OrdinaryUnusedBindingInitializer -> sortSuffix 2 original.Sources current.Sources
                    | EdgeRole.SequenceProgramBorrow -> sortSuffix 6 original.Sources current.Sources
                    | EdgeRole.Constrains | EdgeRole.EnrichedWith ->
                        match Map.tryFind original.Target origOptionalClaims, original.Sources with
                        | Some origCallSite, origHead :: _ when origHead = origCallSite ->
                            sortSuffix 1 original.Sources current.Sources
                        | _ when original.Role = EdgeRole.Constrains && origFiniteCellTargets.Contains original.Target ->
                            sortSuffix 0 original.Sources current.Sources
                        | _ -> None
                    | _ -> None
                let resolved =
                    match canonicalTail with
                    | Some sources -> { current with Sources = sources }
                    | None -> current
                mapAll (resolved :: acc) rest
    mapAll [] paired

let private remapSourceRangeRelations
    (remap: NodeId -> NodeId)
    (origRows: SourceRangeRelation list)
    : SourceRangeRelation list =
    origRows
    |> List.map (fun origRow ->
        let currRow = NodeIdRemap.remapSourceRangeRelation remap origRow
        let updated =
            match origRow.Kind with
            | SourceRangeRelationKind.Named "OrdinaryUnusedFormal" -> sortSuffix 1 origRow.Sources currRow.Sources
            | SourceRangeRelationKind.Named "OrdinaryUnusedActual" -> sortSuffix 4 origRow.Sources currRow.Sources
            | SourceRangeRelationKind.Named "OrdinaryUnusedBindingInitializer" -> sortSuffix 2 origRow.Sources currRow.Sources
            | SourceRangeRelationKind.KernelIngress _ -> sortSuffix 0 origRow.Sources currRow.Sources
            | _ -> None
        match updated with
        | Some sources -> { currRow with Sources = sources }
        | None -> currRow)

let private remapRangeContextFactsCanonical
    (remap: NodeId -> NodeId)
    (origFacts: RangeContextFacts)
    (currFacts: RangeContextFacts)
    : RangeContextFacts =
    let normalized = normalizeRangeContextFacts currFacts
    match origFacts.SourceRelations with
    | Result.Ok origRows ->
        { normalized with SourceRelations = Result.Ok (remapSourceRangeRelations remap origRows) }
    | Result.Error _ -> normalized

let private remapFiniteCellRelationsCanonical
    (remap: NodeId -> NodeId)
    (origFiniteTargets: Set<NodeId>)
    (origRows: FiniteCellSourceRelation list)
    : FiniteCellSourceRelation list =
    origRows
    |> List.map (fun origRow ->
        let currRow = NodeIdRemap.remapFiniteCellSourceRelation remap origRow
        if origRow.Kind = FiniteCellRelationKind.Named "Constrains" && origFiniteTargets.Contains origRow.Target then
            match sortSuffix 0 origRow.Sources currRow.Sources with
            | Some sources -> { currRow with Sources = sources }
            | None -> currRow
        else currRow)

let private fallbackSite (g: SemanticGraph) : NodeId =
    g.DeclarationRoots |> List.tryHead |> Option.map fst
    |> Option.orElseWith (fun () -> g.Nodes.Keys |> Seq.tryHead)
    |> Option.defaultValue (NodeId -1)

let private validatePreRemapCurrency (graph: SemanticGraph) : Result<unit, NodeId * string> =
    let origBoundaryOrigins =
        graph.Edges |> List.choose (fun edge ->
            match edge.Role with
            | EdgeRole.BoundaryDomain { StringOriginRelations = Some rows } -> Some (edge.Target, rows)
            | _ -> None)
    let origNumericDomains =
        graph.Edges |> List.choose (fun edge ->
            match edge.Role with
            | EdgeRole.NumericDomain d -> Some (edge.Target, d)
            | _ -> None)
    let checkReaderErrors () =
        let originReader =
            match origBoundaryOrigins with
            | [] -> Result.Ok None
            | (target, _) :: _ ->
                match StringOrigins.relations graph with
                | Result.Ok rows -> Result.Ok (Some rows)
                | Result.Error reason -> Result.Error (target, "SSAAssignment: " + reason)
        originReader |> Result.bind (fun originRows ->
            let rangeAnchor =
                origNumericDomains |> List.tryPick (fun (anchor, d) -> if d.RangeContextFacts.IsSome then Some anchor else None)
                |> Option.orElseWith (fun () -> if graph.RangeContextFacts.IsSome then Some (fallbackSite graph) else None)
            let rangeReader =
                match rangeAnchor with
                | None -> Result.Ok ()
                | Some anchor ->
                    match NumericValues.rangeContextRelations graph with
                    | Result.Ok _ -> Result.Ok ()
                    | Result.Error reason -> Result.Error (anchor, "SSAAssignment: " + reason)
            rangeReader |> Result.bind (fun () ->
                match origNumericDomains with
                | [] -> Result.Ok (originRows, None)
                | (anchor, _) :: _ ->
                    match NumericValues.finiteCellRelations graph with
                    | Result.Ok rows -> Result.Ok (originRows, Some rows)
                    | Result.Error reason -> Result.Error (anchor, "SSAAssignment: " + reason)))
    checkReaderErrors ()
    |> Result.bind (fun (currentOrigins, currentFinite) ->
        let originsCheck =
            match currentOrigins with
            | None -> Result.Ok ()
            | Some actualRows ->
                origBoundaryOrigins
                |> List.fold (fun acc (target, expectedRows) ->
                    acc |> Result.bind (fun () ->
                        if actualRows <> expectedRows then
                            Result.Error (target, "SSAAssignment: String-origin relation premises are not current before SSA remapping.")
                        else Result.Ok ())) (Result.Ok ())
        originsCheck |> Result.bind (fun () ->
            let rangeCheck =
                let domainRangeCheck =
                    origNumericDomains
                    |> List.fold (fun acc (anchor, domain) ->
                        acc |> Result.bind (fun () ->
                            match domain.RangeContextFacts with
                            | None -> Result.Ok ()
                            | Some expected ->
                                if graph.RangeContextFacts <> Some expected then
                                    Result.Error (anchor, "SSAAssignment: Invocation-context range premises disagree between graph root and NumericDomain before SSA remapping.")
                                elif not (NumericValues.rangeContextCurrent graph expected) then
                                    Result.Error (anchor, "SSAAssignment: Invocation-context range premises are not current before SSA remapping.")
                                else Result.Ok ())) (Result.Ok ())
                domainRangeCheck |> Result.bind (fun () ->
                    if origNumericDomains.IsEmpty then
                        match graph.RangeContextFacts with
                        | Some expected when not (NumericValues.rangeContextCurrent graph expected) ->
                            Result.Error (fallbackSite graph, "SSAAssignment: Invocation-context range premises are not current before SSA remapping.")
                        | _ -> Result.Ok ()
                    else Result.Ok ())
            rangeCheck |> Result.bind (fun () ->
                match currentFinite with
                | None -> Result.Ok ()
                | Some actualFinite ->
                    let actualObligations = NumericValues.finiteCellObligations graph
                    origNumericDomains
                    |> List.fold (fun acc (anchor, domain) ->
                        acc |> Result.bind (fun () ->
                            if actualFinite <> domain.FiniteCellRelations || actualObligations <> domain.FiniteCellObligations then
                                Result.Error (anchor, "SSAAssignment: Finite-cell relation premises are not current before SSA remapping.")
                            else Result.Ok ())) (Result.Ok ()))))

let private syncCallableContracts
    (graph: SemanticGraph)
    (remap: NodeId -> NodeId)
    (remappedPreContracts: SemanticGraph)
    : Result<SemanticGraph, NodeId * string> =
    let origCodata = graph.Codata.Value
    if origCodata.CallableContracts.IsEmpty then Result.Ok remappedPreContracts
    else
        let singleNumericOwner (g: SemanticGraph) =
            let owners =
                g.Edges |> List.choose (fun edge ->
                    match edge.Role with
                    | EdgeRole.NumericDomain d -> Some (edge.Target, d)
                    | _ -> None)
            match owners with
            | [] -> Result.Ok None
            | [ anchor, d ] ->
                match g.Nodes.TryFind anchor |> Option.filter NumericValues.owned with
                | Some n -> Result.Ok (Some (anchor, d, Boundaries.premise n))
                | None -> Result.Error (anchor, "SSAAssignment: NumericDomain anchor node is missing or unowned during callable contract SSA remapping.")
            | (anchor, _) :: _ ->
                Result.Error (anchor, "SSAAssignment: Ambiguous NumericDomain owners during callable contract SSA remapping.")
        let carrierSignature (c: CallableCarrier) = c.Kind, c.Implementation, c.Result, c.Parameters
        let buildCarrierMap (carriers: Map<NodeId, CallableCarrier>) =
            carriers.Values
            |> Seq.fold (fun state (c: CallableCarrier) ->
                state |> Result.bind (fun m ->
                    match c.Contract with
                    | Result.Error _ -> Result.Ok m
                    | Result.Ok contractId ->
                        match Map.tryFind contractId m with
                        | None -> Result.Ok (Map.add contractId c m)
                        | Some prev when carrierSignature prev = carrierSignature c -> Result.Ok m
                        | Some _ -> Result.Error (contractId, "SSAAssignment: Ambiguous callable carrier for implementation during SSA remapping.")))
                (Result.Ok Map.empty)
        singleNumericOwner graph
        |> Result.bind (fun origOwnerOpt ->
            singleNumericOwner remappedPreContracts
            |> Result.bind (fun currOwnerOpt ->
                match origOwnerOpt, currOwnerOpt with
                | None, None -> Result.Ok remappedPreContracts
                | Some (anchor, _, _), None ->
                    Result.Error (remap anchor, "SSAAssignment: NumericDomain owner disappeared during callable contract SSA remapping.")
                | None, Some (anchor, _, _) ->
                    Result.Error (anchor, "SSAAssignment: NumericDomain owner appeared unexpectedly during callable contract SSA remapping.")
                | Some origOwner, Some currOwner ->
                    let currCodata = remappedPreContracts.Codata.Value
                    buildCarrierMap origCodata.CallableCarriers
                    |> Result.bind (fun origCarrierByContract ->
                        buildCarrierMap currCodata.CallableCarriers
                        |> Result.bind (fun currCarrierByContract ->
                            let sourceNodes (ps: Participant list) =
                                ps |> List.filter (fun p -> p.Role = ParticipantRole.Source) |> List.map _.Node |> List.sort
                            let syncContracts =
                                origCodata.CallableContracts
                                |> Map.fold (fun state origId origContract ->
                                    state |> Result.bind (fun (contracts: Map<NodeId, CallableContract>) ->
                                        let currId = remap origId
                                        match contracts.TryFind currId with
                                        | None ->
                                            Result.Error (currId, "SSAAssignment: Callable contract disappeared during SSA remapping.")
                                        | Some currContract ->
                                            match origCarrierByContract.TryFind origContract.Identity,
                                                  currCarrierByContract.TryFind currContract.Identity with
                                            | None, _ | _, None ->
                                                Result.Error (currId, "SSAAssignment: Callable contract is missing its callable carrier during SSA remapping.")
                                            | Some origCarrier, Some currCarrier ->
                                                let origSources, _ = CallableContracts.conventionEvidence graph origContract.Convention origOwner origCarrier
                                                let expectedOrigParticipants = CallableContracts.conventionParticipants origContract.Convention origContract.Identity origCarrier origSources
                                                if origContract.Participants <> expectedOrigParticipants then
                                                    Result.Error (currId, "SSAAssignment: Callable contract participants are not canonical before SSA remapping.")
                                                else
                                                    let currSources, _ = CallableContracts.conventionEvidence remappedPreContracts currContract.Convention currOwner currCarrier
                                                    let expectedCurrParticipants = CallableContracts.conventionParticipants currContract.Convention currContract.Identity currCarrier currSources
                                                    if currContract.Participants.Length <> expectedCurrParticipants.Length
                                                       || sourceNodes currContract.Participants <> sourceNodes expectedCurrParticipants then
                                                        Result.Error (currId, "SSAAssignment: Callable contract participant set drifted during SSA remapping.")
                                                    elif currContract.Participants <> expectedCurrParticipants then
                                                        Result.Ok (contracts.Add(currId, { currContract with Participants = expectedCurrParticipants }))
                                                    else Result.Ok contracts))
                                    (Result.Ok currCodata.CallableContracts)
                            syncContracts |> Result.bind (fun updatedContracts ->
                                if updatedContracts = currCodata.CallableContracts then Result.Ok remappedPreContracts
                                else
                                    currCodata.CallableAggregateDependencies
                                    |> Map.fold (fun state accountId account ->
                                        state |> Result.bind (fun (deps: Map<NodeId, CallableAggregateDependencyAccount>) ->
                                            let synced =
                                                account.Contracts
                                                |> List.map (fun c -> updatedContracts.TryFind c.Identity |> Option.defaultValue c)
                                            if synced = account.Contracts then Result.Ok (deps.Add(accountId, account))
                                            else
                                                let participants =
                                                    (account.Slots |> List.collect _.Participants)
                                                    @ (account.Values |> List.collect (fun row -> row.Participants @ (row.Tag |> Option.map _.Participants |> Option.defaultValue [])))
                                                    @ (account.Carriers |> List.collect _.Lifetime)
                                                    @ (synced |> List.collect _.Participants)
                                                let participantNodes = participants |> List.map _.Node |> List.distinct
                                                let sourceByNode = account.Sources |> List.map (fun s -> s.Node, s) |> Map.ofList
                                                let claimByNode = account.Claims |> Map.ofList
                                                let sources = participantNodes |> List.choose sourceByNode.TryFind
                                                let claims = participantNodes |> List.choose (fun id -> claimByNode.TryFind id |> Option.map (fun c -> id, c))
                                                if participants.Length = account.Participants.Length
                                                   && sources.Length = account.Sources.Length
                                                   && claims.Length = account.Claims.Length then
                                                    Result.Ok (deps.Add(accountId, { account with Contracts = synced; Participants = participants; Sources = sources; Claims = claims }))
                                                else
                                                    Result.Error (accountId, "SSAAssignment: Callable aggregate dependency account lost participant coherence during SSA remapping.")))
                                        (Result.Ok Map.empty)
                                    |> Result.map (fun updatedDeps ->
                                        { remappedPreContracts with
                                            Codata = lazy { currCodata with CallableContracts = updatedContracts; CallableAggregateDependencies = updatedDeps } }))))))

let internal remapGraph (remap: NodeId -> NodeId) (graph: SemanticGraph) : Result<SemanticGraph, NodeId * string> =
    validatePreRemapCurrency graph
    |> Result.bind (fun () -> remapEdges remap graph.Edges)
    |> Result.bind (fun remappedEdges ->
        let remappedBase = NodeIdRemap.remapGraphRoots remap remappedEdges graph
        if remappedBase.Nodes.Count <> graph.Nodes.Count then
            let collidingTarget =
                graph.Nodes.Keys
                |> Seq.fold (fun (seen, found) id ->
                    match found with
                    | Some _ -> seen, found
                    | None ->
                        let target = remap id
                        if Set.contains target seen then seen, Some target
                        else Set.add target seen, None) (Set.empty, None)
                |> snd
                |> Option.defaultValue (fallbackSite graph)
            Result.Error (collidingTarget, "SSAAssignment: NodeId remapping collided distinct graph nodes.")
        else
            let origFiniteTargets =
                graph.Edges
                |> List.collect (fun edge ->
                    match edge.Role with
                    | EdgeRole.NumericDomain d -> d.FiniteCellObligations |> List.map fst
                    | _ -> [])
                |> Set.ofList
            let syncedEdges =
                (graph.Edges, remappedBase.Edges)
                ||> List.map2 (fun origEdge currEdge ->
                    match origEdge.Role, currEdge.Role with
                    | EdgeRole.NumericDomain origDom, EdgeRole.NumericDomain currDom ->
                        let syncedRangeFacts =
                            match origDom.RangeContextFacts, currDom.RangeContextFacts with
                            | Some origFacts, Some currFacts -> Some (remapRangeContextFactsCanonical remap origFacts currFacts)
                            | _, other -> other
                        let syncedFiniteCells =
                            match origDom.FiniteCellRelations with
                            | Some origRows -> Some (remapFiniteCellRelationsCanonical remap origFiniteTargets origRows)
                            | None -> currDom.FiniteCellRelations
                        { currEdge with
                            Role = EdgeRole.NumericDomain { currDom with RangeContextFacts = syncedRangeFacts; FiniteCellRelations = syncedFiniteCells } }
                    | _ -> currEdge)
            let syncedRootRangeFacts =
                match graph.RangeContextFacts, remappedBase.RangeContextFacts with
                | Some origFacts, Some currFacts -> Some (remapRangeContextFactsCanonical remap origFacts currFacts)
                | _, other -> other |> Option.map normalizeRangeContextFacts
            let remappedPreContracts =
                { remappedBase with
                    SequenceRangeProvenance = remappedBase.SequenceRangeProvenance |> Option.map normalizeSequenceRangeAuthority
                    RangeContextFacts = syncedRootRangeFacts
                    Edges = syncedEdges }
            syncCallableContracts graph remap remappedPreContracts
            |> Result.bind (fun remapped ->
                let remappedNumericDomains =
                    remapped.Edges |> List.choose (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericDomain d -> Some (edge.Target, d)
                        | _ -> None)
                let postRangeCheck =
                    let domainCheck =
                        remappedNumericDomains
                        |> List.fold (fun acc (anchor, domain) ->
                            acc |> Result.bind (fun () ->
                                match domain.RangeContextFacts with
                                | None -> Result.Ok ()
                                | Some facts ->
                                    match NumericValues.rangeContextRelations remapped with
                                    | Result.Error reason -> Result.Error (anchor, "SSAAssignment: " + reason)
                                    | Result.Ok _ when not (NumericValues.rangeContextCurrent remapped facts) ->
                                        Result.Error (anchor, "SSAAssignment: Invocation-context range premises drifted after SSA remapping.")
                                    | Result.Ok _ -> Result.Ok ())) (Result.Ok ())
                    domainCheck |> Result.bind (fun () ->
                        if remappedNumericDomains.IsEmpty then
                            match remapped.RangeContextFacts with
                            | Some facts ->
                                match NumericValues.rangeContextRelations remapped with
                                | Result.Error reason -> Result.Error (fallbackSite remapped, "SSAAssignment: " + reason)
                                | Result.Ok _ when not (NumericValues.rangeContextCurrent remapped facts) ->
                                    Result.Error (fallbackSite remapped, "SSAAssignment: Invocation-context range premises drifted after SSA remapping.")
                                | Result.Ok _ -> Result.Ok ()
                            | None -> Result.Ok ()
                        else Result.Ok ())
                let postFiniteCheck =
                    postRangeCheck |> Result.bind (fun () ->
                        match remappedNumericDomains with
                        | [] -> Result.Ok ()
                        | (anchor, _) :: _ ->
                            match NumericValues.finiteCellRelations remapped with
                            | Result.Error reason -> Result.Error (anchor, "SSAAssignment: " + reason)
                            | Result.Ok actualFinite ->
                                let actualObligations = NumericValues.finiteCellObligations remapped
                                remappedNumericDomains
                                |> List.fold (fun acc (a, domain) ->
                                    acc |> Result.bind (fun () ->
                                        if actualFinite <> domain.FiniteCellRelations || actualObligations <> domain.FiniteCellObligations then
                                            Result.Error (a, "SSAAssignment: Finite-cell relation premises drifted after SSA remapping.")
                                        else Result.Ok ())) (Result.Ok ()))
                postFiniteCheck |> Result.bind (fun () ->
                    let boundaryOriginTarget =
                        remapped.Edges |> List.tryPick (fun edge ->
                            match edge.Role with
                            | EdgeRole.BoundaryDomain { StringOriginRelations = Some _ } -> Some edge.Target
                            | _ -> None)
                    match boundaryOriginTarget with
                    | None -> Result.Ok remapped
                    | Some target ->
                        match StringOrigins.relations remapped with
                        | Result.Error reason -> Result.Error (target, "SSAAssignment: " + reason)
                        | Result.Ok fresh ->
                            let reorderedEnrichedTargets =
                                remapped.Edges
                                |> List.collect (fun edge ->
                                    match edge.Role with
                                    | EdgeRole.BoundaryDomain d -> edge.Target :: (d.IntrinsicProofs |> List.map _.Obligation)
                                    | EdgeRole.BoundaryCoverage c -> [ c.Obligation ]
                                    | EdgeRole.MemoryDomain d -> edge.Target :: (d.Proofs |> List.map _.Obligation)
                                    | EdgeRole.NumericDomain d ->
                                        edge.Target
                                        :: (d.Values |> List.collect _.Obligations)
                                        @ (d.OperationProofs |> List.map _.Obligation)
                                        @ (d.IndexTransports |> List.map _.Obligation)
                                    | EdgeRole.SpatialModuleDomain d -> edge.Target :: (d.Proofs |> List.map _.Obligation)
                                    | _ -> [])
                                |> Set.ofList
                            let canonicalRelation (row: StringOriginRelation) =
                                let sources =
                                    if row.Flavor = StringOriginRelationKind.Named "EnrichedWith" && reorderedEnrichedTargets.Contains row.Target then
                                        List.sort row.Sources
                                    else row.Sources
                                row.Recorded, row.Class, row.Flavor, row.Ordinal, row.Target, sources
                            let sortedFresh = fresh |> List.map canonicalRelation |> List.sort
                            let syncedOriginEdges =
                                remapped.Edges
                                |> List.fold (fun acc edge ->
                                    acc |> Result.bind (fun revEdges ->
                                        match edge.Role with
                                        | EdgeRole.BoundaryDomain ({ StringOriginRelations = Some relations } as domain) ->
                                            if relations = fresh then Result.Ok (edge :: revEdges)
                                            elif (relations |> List.map canonicalRelation |> List.sort) = sortedFresh then
                                                Result.Ok ({ edge with Role = EdgeRole.BoundaryDomain { domain with StringOriginRelations = Some fresh } } :: revEdges)
                                            else
                                                Result.Error (edge.Target, "SSAAssignment: String-origin relation premises drifted after SSA remapping.")
                                        | _ -> Result.Ok (edge :: revEdges))) (Result.Ok [])
                                |> Result.map List.rev
                            syncedOriginEdges |> Result.map (fun edges -> { remapped with Edges = edges }))))

let [<Literal>] Family = 512

let value (nodeId: NodeId) (ordinal: int) : SSAId =
    SSAId(NodeId.value nodeId, ordinal)

let familyValues (nodeId: NodeId) : SSAId list =
    List.init Family (value nodeId)

let private isAssignableNode (node: SemanticNode) : bool =
    match node.Kind with
    | SemanticKind.ModuleDef _
    | SemanticKind.TypeDef _
    | SemanticKind.Obligation _
    | SemanticKind.Error _ -> false
    | _ -> true

let private slotsForNode (nodeId: NodeId) (node: SemanticNode) : SSAId list =
    if not (isAssignableNode node) then
        []
    else
        familyValues nodeId

let private orderedReachableNodes (graph: SemanticGraph) : (NodeId * SemanticNode) list =
    graph.Nodes
    |> Map.toList
    |> List.filter (fun (_, node) -> node.IsReachable && isAssignableNode node)
    |> List.sortBy (fun (id, _) -> NodeId.value id)

let private occupiedHighWater (graph: SemanticGraph) : int =
    max 0 (Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.maxOccupiedNodeId graph)

/// Full-compilation cold-start SSA assignment pass.
let normalize (graph: SemanticGraph) : SemanticGraph =
    let reachable = orderedReachableNodes graph
    let assignments =
        reachable
        |> List.map (fun (id, node) -> id, slotsForNode id node)
        |> Map.ofList
    let assignedIds = assignments |> Map.keys |> Set.ofSeq
    let identityRemap =
        graph.Nodes.Keys
        |> Seq.map (fun id -> id, id)
        |> Map.ofSeq
    let codata = graph.Codata.Value
    let plan : SSAAssignmentPlan =
        { Assignments = assignments
          NodeHighWater = occupiedHighWater graph
          NodeRemap = identityRemap
          RetainedNodes = Set.empty
          ReassignedNodes = assignedIds }
    { graph with Codata = lazy { codata with SSAAssignment = Some plan } }

[<RequireQualifiedAccess>]
type ReconciliationFailure =
    | MissingBaselinePlan
    | MissingRetainedAssignment of NodeId
    | MissingRetainedCorrespondence of NodeId
    | AmbiguousRetainedCorrespondence of Diagnostic
    | InvalidCorrespondenceBaseline of SegmentationFailure list
    | InvalidCorrespondenceCandidate of SegmentationFailure list
    | InvalidReturnedIdentities of (NodeId * string) list

let private uncheckedPhysicalCorrespondence baseline candidate (correspondences: Map<NodeId, NodeId option>) =
    if correspondences.IsEmpty then None
    else
        match physicalOccurrenceAddresses baseline, physicalOccurrenceAddresses candidate with
        | Result.Error failures, _ -> Some(ReconciliationFailure.InvalidCorrespondenceBaseline failures)
        | _, Result.Error failures -> Some(ReconciliationFailure.InvalidCorrespondenceCandidate failures)
        | Result.Ok prior, Result.Ok current ->
            correspondences
            |> Map.toSeq
            |> Seq.tryPick (fun (receiving, predecessor) ->
                let address = predecessor |> Option.bind prior.TryFind
                if address.IsSome && address = current.TryFind receiving then None
                else Some(ReconciliationFailure.MissingRetainedCorrespondence receiving))

/// Cone-scoped selective-rebuild SSA reconciliation and assignment.
/// Retained structure outside the delta cone keeps its baseline `NodeId`s and
/// `SSAId(node, ordinal)` assignments across the graph and codata; affected or
/// newly elaborated nodes advance above the prior high-water mark and any
/// relation identities held in place.
let private reconcileAndAssignCore
    transportCallableRelations
    (baseline: SemanticGraph)
    (baselinePlan: SSAAssignmentPlan)
    (alignment: Map<NodeId, NodeId>)
    (retainedCandidateNodes: Set<NodeId>)
    (candidate: SemanticGraph)
    : Result<SemanticGraph * SSAAssignmentPlan, ReconciliationFailure> =
    let baselineFacts = baseline.Codata.Value
    let candidateFacts = candidate.Codata.Value
    let sameIdentityClass baseId candId =
        (baseline.Nodes.ContainsKey baseId && candidate.Nodes.ContainsKey candId)
        || (transportCallableRelations &&
            ((baselineFacts.CallableContracts.ContainsKey baseId && candidateFacts.CallableContracts.ContainsKey candId)
             || (baselineFacts.CallableAggregateSlots.ContainsKey baseId && candidateFacts.CallableAggregateSlots.ContainsKey candId)))
    let candToBase =
        alignment
        |> Map.fold (fun acc baseId candId ->
            if Set.contains candId retainedCandidateNodes && sameIdentityClass baseId candId then
                let correspondence = if Map.containsKey candId acc then None else Some baseId
                Map.add candId correspondence acc
            else
                acc) Map.empty
    // A region selected for retention already owns its exact SSA family.
    // Check that authority before remapping the graph or creating any families.
    let reachable = orderedReachableNodes candidate
    let retainedRefusal =
        retainedCandidateNodes
        |> Seq.tryPick (fun source ->
            match candToBase.TryFind source with
            | None -> Some(ReconciliationFailure.MissingRetainedCorrespondence source)
            | Some None ->
                let range = candidate.Nodes.TryFind source |> Option.map _.Range |> Option.defaultValue dummyRange
                Some(ReconciliationFailure.AmbiguousRetainedCorrespondence
                    { Severity = NativeDiagnosticSeverity.Error
                      Code = "CCS8407"
                      Message = "The retained occurrence has more than one admissible baseline identity."
                      Range = range
                      RelatedNodes = [source]
                      Reachability = ReachabilityContext.Unknown })
            | Some (Some id) ->
                match candidate.Nodes.TryFind source with
                | Some node when node.IsReachable && isAssignableNode node ->
                    match baselinePlan.Assignments.TryFind id with
                    | Some (_ :: _) -> None
                    | _ -> Some(ReconciliationFailure.MissingRetainedAssignment id)
                | _ -> None)
    let refusal =
        retainedRefusal |> Option.orElseWith (fun () ->
            if transportCallableRelations then None
            else uncheckedPhysicalCorrespondence baseline candidate candToBase)
    match refusal with
    | Some failure -> Result.Error failure
    | None ->
        // Temporary source coordinates do not contribute to destination history.
        // A callable identity left in place is an occupied destination coordinate.
        let initialHighWater =
            max baselinePlan.NodeHighWater (occupiedHighWater baseline)
        let assign (remap, highWater, retainedSet) candId =
            match candToBase.TryFind candId with
            | Some (Some baseId) ->
                Map.add candId baseId remap, highWater, Set.add baseId retainedSet
            | _ ->
                let nextId = highWater + 1
                Map.add candId (NodeId nextId) remap, nextId, retainedSet
        let relationRemap, relationHighWater =
            let ids = Seq.append candidateFacts.CallableContracts.Keys candidateFacts.CallableAggregateSlots.Keys
            if transportCallableRelations then
                let remap, highWater, _ =
                    ids
                    |> Seq.sortBy NodeId.value
                    |> Seq.fold assign (Map.empty, initialHighWater, Set.empty)
                remap, highWater
            else
                let occupied = ids |> Seq.fold (fun highWater id -> max highWater (NodeId.value id)) initialHighWater
                Map.empty, occupied
        let nodeRemap, finalHighWater, retainedReconciled =
            candidate.Nodes.Keys
            |> Seq.sortBy NodeId.value
            |> Seq.fold assign (Map.empty, relationHighWater, Set.empty)
        let remapNodeId (id: NodeId) : NodeId =
            match nodeRemap.TryFind id with
            | Some mapped -> mapped
            | None -> relationRemap.TryFind id |> Option.defaultValue id
        let assignments, retainedAssigned, reassigned =
            reachable
            |> List.fold (fun (acc, retained, fresh) (source, node) ->
                let id = nodeRemap[source]
                if Set.contains id retainedReconciled then
                    Map.add id baselinePlan.Assignments[id] acc, Set.add id retained, fresh
                else
                    Map.add id (slotsForNode id node) acc, retained, Set.add id fresh)
                (Map.empty, Set.empty, Set.empty)
        let plan : SSAAssignmentPlan =
            { Assignments = assignments
              NodeHighWater = finalHighWater
              NodeRemap = nodeRemap
              RetainedNodes = retainedAssigned
              ReassignedNodes = reassigned }
        match remapGraph remapNodeId candidate with
        | Result.Error failure -> Result.Error(ReconciliationFailure.InvalidReturnedIdentities [ failure ])
        | Result.Ok remappedGraph ->
            let codata = remappedGraph.Codata.Value
            match Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.validateTypedIdentities
                      remappedGraph.Nodes codata.CallableContracts codata.CallableAggregateSlots with
            | Result.Error failures -> Result.Error(ReconciliationFailure.InvalidReturnedIdentities failures)
            | Result.Ok () ->
                let reconciledGraph =
                    { remappedGraph with Codata = lazy { codata with SSAAssignment = Some plan } }
                Result.Ok(reconciledGraph, plan)

let private reconcileExistingPlan transportCallableRelations (baseline: SemanticGraph) alignment retainedCandidateNodes candidate =
    match baseline.Codata.Value.SSAAssignment with
    | Some plan -> reconcileAndAssignCore transportCallableRelations baseline plan alignment retainedCandidateNodes candidate
    | None -> Result.Error ReconciliationFailure.MissingBaselinePlan

/// Reassign structural occurrences and keep existing callable relation identities.
let reconcileAndAssign baseline alignment retainedCandidateNodes candidate =
    reconcileExistingPlan false baseline alignment retainedCandidateNodes candidate

/// Transport identities from the checked pair and its actual scoped Baker result.
let internal reconcileAndAssignWithCallableRelations scoped retainedCandidateNodes =
    let baseline, candidate, alignment, _ = scopedRebuildInputs scoped
    reconcileExistingPlan true baseline alignment retainedCandidateNodes candidate

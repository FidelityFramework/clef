// SPDX-License-Identifier: MIT
/// Validating projection only. Numeric choice belongs to Baker NumericCarrierRecipes.
module Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Numeric = Clef.Compiler.Baker.Ingredients.NumericValues
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries
module Operations = Clef.Compiler.Baker.Ingredients.NumericOperations

/// Completeness is checked before ledger emission as well as strict projection.
/// This validates the producer's rules without choosing a representation.
let completeness (graph: SemanticGraph) : WitnessProjectionFailure list =
    Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness graph
    |> List.map (fun (site, reason) ->
        {
            Kind = WitnessProjectionFailureKind.Settlement
            Occurrence = Some site
            Participants = Set.singleton site
            Reason = reason
        })

let private projectDomain (graph: SemanticGraph) : Result<NumericWitnessProjection, WitnessProjectionFailure list> =
    let domains = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.NumericDomain domain -> Some(edge.Target, domain) | _ -> None)
    let reject site participants reason =
        Error
            [
                {
                    Kind = WitnessProjectionFailureKind.Settlement
                    Occurrence = site
                    Participants = participants
                    Reason = "NumericPublication: " + reason
                }
            ]
    match domains with
    | [anchor, domain] ->
        let participants = Map.keys domain.Premises |> Set.ofSeq
        let sequenceCurrent =
            match domain.SequenceRangeAuthority, graph.SequenceRangeProvenance with
            | Some expected, Some current when expected = current -> Numeric.sequenceRangeCurrent graph expected
            | None, None -> not domain.RequiresSequenceReview && not (Numeric.sequenceRangeActive graph)
            | _ -> false
        let rangeCurrent =
            match domain.RangeContextFacts, graph.RangeContextFacts with
            | Some expected, Some current when expected = current -> Numeric.rangeContextCurrent graph expected
            | _ -> false
        if not sequenceCurrent then
            reject (Some anchor) participants "Finite-sequence relation premises changed or the source-to-machine range authority is absent; source settlement is required."
        elif Numeric.finiteCellRelations graph <> Ok domain.FiniteCellRelations ||
           Numeric.finiteCellObligations graph <> domain.FiniteCellObligations then
            reject (Some anchor) participants "finite-cell relation premises changed; source numeric settlement is required."
        elif domain.CaptureRelations <> Numeric.captureRelations graph then
            reject (Some anchor) participants "Closure capture relation premises changed; source numeric settlement is required."
        elif not domain.Unresolved.IsEmpty then
            Error(
                domain.Unresolved
                |> Map.toList
                |> List.map (fun (site, reason) ->
                    {
                        Kind = WitnessProjectionFailureKind.Settlement
                        Occurrence = Some site
                        Participants = Set.singleton site
                        Reason = "NumericPublication: " + reason
                    })
            )
        elif not rangeCurrent then
            reject (Some anchor) participants "Invocation-context range premises changed or the producer receipt is absent; source range settlement is required."
        elif domain.Premises <> Numeric.premises graph then
            reject (Some anchor) participants "Source node range, type, or occurrence premises changed; source numeric settlement is required."
        elif domain.Platform <> Boundary.platformPremise graph.Platform then
            reject (Some anchor) participants "Platform declaration premises changed; source numeric settlement is required."
        elif domain.Roots <> graph.DeclarationRoots then
            reject (Some anchor) participants "Declaration root premises changed; source numeric settlement is required."
        elif domain.Escaping <> graph.Escaping.Value then
            reject (Some anchor) participants "Escape premises changed; source numeric settlement is required."
        elif domain.Layouts <> graph.Layouts.Value then
            reject (Some anchor) participants "Layout premises changed; source numeric settlement is required."
        elif domain.ElementRanges <> graph.ElementRanges.Value then
            reject (Some anchor) participants "Element range premises changed; source numeric settlement is required."
        elif domain.ByteRanges <> Numeric.byteRanges graph then
            reject (Some anchor) participants "Byte range premises changed; source numeric settlement is required."
        elif domain.ByteReadRanges <> Numeric.byteReadRanges graph then
            reject (Some anchor) participants "Byte read range premises changed; source numeric settlement is required."
        elif domain.ByteViews <> Numeric.byteViews graph then
            reject (Some anchor) participants "Byte view premises changed; source numeric settlement is required."
        elif domain.StringExtents <> Numeric.stringExtents graph then
            reject (Some anchor) participants "String extent premises changed; source numeric settlement is required."
        elif (domain.Values |> List.map _.Site |> List.sort) <> (domain.Required |> Set.toList) then
            reject (Some anchor) participants "A required source scalar carrier is absent or duplicated."
        elif (domain.Operations |> List.map _.Site |> List.sort) <> Set.toList domain.OperationRequired then
            reject (Some anchor) participants "A required source operation construction is absent or duplicated."
        elif (domain.IndexTransports |> List.map _.Site |> List.sort) <> Set.toList domain.IndexRequired then
            reject (Some anchor) participants "A required source index transport is absent or duplicated."
        else
            let proofs = domain.Values |> List.collect (fun carrier ->
                carrier.Obligations |> List.map (fun obligation -> carrier, obligation, Numeric.coverage carrier))
            let carriersValid = domain.Values |> List.forall (fun carrier ->
                let kindValid = match carrier.Slot with
                                | SettledSlot.Integer(bits, _) -> bits > 0 && carrier.Obligations.Length = 1 && (carrier.Representation |> Option.forall (fun rep -> rep.Bits = bits))
                                | SettledSlot.Real bits -> bits > 0 && carrier.Obligations.IsEmpty
                                | SettledSlot.Bool | SettledSlot.Char -> carrier.Obligations.IsEmpty
                                | _ -> false
                kindValid && carrier.Participants.Contains anchor && carrier.Participants.Contains carrier.Site &&
                (carrier.Declaration |> Option.forall carrier.Participants.Contains) &&
                domain.SourceTypes.TryFind carrier.Site = Some carrier.SourceType &&
                domain.OccurrenceRepresentations.TryFind carrier.Site = Some(Ok(ValueRepresentation.Scalar carrier.Slot)) &&
                (domain.Premises.TryFind carrier.Site |> Option.exists (fun premise ->
                    premise.Shape.SourceType = carrier.SourceType &&
                    (match carrier.Slot with SettledSlot.Integer _ -> premise.Range = Some carrier.Range | _ -> true))))
            let valid = carriersValid && (proofs |> List.forall (fun (_, id, body) ->
                match graph.Nodes.TryFind id, body with
                | Some node, Some body when Numeric.owned node ->
                    (match node.Kind with SemanticKind.Obligation info -> info.Kind = "numeric-carrier-coverage" && info.Body = body | _ -> false) &&
                    Clef.Compiler.Baker.Ingredients.StringBytes.proofOutcome body = BoundaryProofOutcome.Proven
                | _ -> false))
            let operationProofsValid = domain.OperationProofs |> List.forall (fun proof ->
                proof.Proven && Operations.proofOutcome proof.Body &&
                (graph.Nodes.TryFind proof.Obligation |> Option.exists (fun node ->
                    let bodyAgrees = match node.Kind with SemanticKind.Obligation info -> info.Kind = "numeric-operation-proof" && info.Body = proof.Body | _ -> false
                    Numeric.owned node && bodyAgrees)))
            let operationValuesValid = domain.Operations |> List.forall (fun operation ->
                let ownProofs = domain.OperationProofs |> List.filter (fun proof -> proof.Site = operation.Site)
                let bodies = operation.Obligations |> List.map (fun id -> ownProofs |> List.tryFind (fun proof -> proof.Obligation = id) |> Option.map _.Body)
                operation.OperationCarrier.IsSome &&
                (Operations.requiredBodies operation |> Option.exists (fun expected -> List.map Some expected = bodies)) &&
                (domain.Values |> List.tryFind (fun value -> value.Site = operation.Site)) = Some operation.Result &&
                (operation.Operands |> List.forall (fun input -> input.Carrier |> Option.forall (fun carrier ->
                    carrier.Site = input.Actual && (domain.Values |> List.tryFind (fun value -> value.Site = input.Actual)) = Some carrier))) &&
                (operation.Obligations |> List.sort) = (domain.OperationProofs |> List.filter (fun proof -> proof.Site = operation.Site) |> List.map _.Obligation |> List.sort) &&
                domain.OperationMeets.TryFind operation.Site = Some(Operations.meets operation) &&
                (Operations.meets operation |> List.forall (fun meet ->
                    graph.Codata.Value.Meets.TryFind operation.Site |> Option.defaultValue [] |> List.filter (fun candidate -> candidate.Operand = meet.Operand) = [meet])))
            let indexValuesValid = domain.IndexTransports |> List.forall (fun transport ->
                let expectedCapacity =
                    if transport.PointerBits <= 0 then None
                    elif transport.Unsigned then Some(Clef.Compiler.NativeTypedTree.NativeTypes.ValueRange.unsignedOf transport.PointerBits)
                    else Some(Clef.Compiler.NativeTypedTree.NativeTypes.ValueRange.twosComplement transport.PointerBits)
                let signAgrees = match transport.Carrier.Range with
                                 | Clef.Compiler.NativeTypedTree.NativeTypes.ValueRange.Bounded(lo,hi) -> lo <= hi && transport.Unsigned = (lo >= 0I)
                                 | _ -> false
                let sourceAgrees = graph.Nodes.TryFind transport.Site |> Option.exists (fun node ->
                    match node.Kind with SemanticKind.ContinuationDispatch(operand,_,_) -> operand = transport.Operand | _ -> false)
                let proofAgrees =
                    match Numeric.indexBody transport, graph.Nodes.TryFind transport.Obligation with
                    | Some body, Some node when Numeric.owned node ->
                        Clef.Compiler.Baker.Ingredients.StringBytes.proofOutcome body = BoundaryProofOutcome.Proven &&
                        (match node.Kind with SemanticKind.Obligation info -> info.Kind = "numeric-index-coverage" && info.Body = body | _ -> false)
                    | _ -> false
                signAgrees && sourceAgrees && proofAgrees && expectedCapacity = Some transport.Capacity &&
                (domain.Platform |> Option.bind (fun platform -> platform.Dimensions.TryFind "Pointer")) = Some transport.PointerBits &&
                domain.Premises.ContainsKey transport.PointerDeclaration &&
                transport.Carrier.Site = transport.Operand &&
                (domain.Values |> List.tryFind (fun value -> value.Site = transport.Operand)) = Some transport.Carrier &&
                transport.Participants = (transport.Carrier.Participants |> Set.add transport.Site |> Set.add transport.PointerDeclaration))
            let foreignValuesValid =
                match RangeAnalysis.foreignResultApplications graph domain.RangeContextFacts with
                | Error _ -> false
                | Ok applications ->
                    (applications |> List.map (fun (evidence: RangeAnalysis.ForeignResultEvidence) -> evidence.Application)) =
                        (domain.ForeignResultUses |> List.map (fun account -> account.Application)) &&
                    List.forall2 (fun (evidence: RangeAnalysis.ForeignResultEvidence) (account: ForeignResultUse) ->
                        let models = Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.foreignResultModels graph domain.Values evidence
                        let participants = Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.foreignResultParticipants evidence.Application models
                        account.Participants = ParticipantEvidence.Established participants &&
                        List.map fst account.Claims = List.map fst models &&
                        (account.Claims |> List.map snd |> List.distinct).Length = models.Length &&
                        List.forall2 (fun (_, citizen) (_, model) ->
                            graph.Nodes.TryFind citizen |> Option.exists (fun node ->
                                Numeric.owned node &&
                                (match node.Kind with
                                 | SemanticKind.Obligation info -> info.Kind = "foreign-result-coverage" && info.Body = ObligationBody.ForeignResultCoverage model
                                 | _ -> false))) account.Claims models) applications domain.ForeignResultUses
            let proofRows = proofs |> List.collect (fun (carrier, id, body) -> body |> Option.toList |> List.collect (Numeric.proofRows carrier id))
            let expected = Numeric.domainRow anchor domain :: Numeric.domainRewrite anchor domain :: (domain.Values |> List.map Numeric.carrierRow) @ proofRows
                           @ (domain.Operations |> List.map Operations.operationRow) @ (domain.OperationProofs |> List.collect Operations.proofRows)
                           @ (domain.IndexTransports |> List.collect Numeric.indexRows)
                           @ (domain.ForeignResultUses |> List.collect Numeric.foreignProofRows)
            let targets = Set.add anchor ((proofs |> List.map (fun (_, id, _) -> id)) @ (domain.OperationProofs |> List.map _.Obligation) @ (domain.IndexTransports |> List.map _.Obligation) @ (domain.ForeignResultUses |> List.collect (_.Claims >> List.map snd)) |> Set.ofList)
            let actual = graph.Edges |> List.filter (fun edge ->
                match edge.Role with
                | EdgeRole.NumericDomain _ | EdgeRole.NumericCarrier _ | EdgeRole.NumericProof _ | EdgeRole.NumericOperation _ | EdgeRole.NumericOperationProof _ | EdgeRole.NumericIndexTransport _ -> true
                | EdgeRole.EnrichedWith | EdgeRole.Constrains when targets.Contains edge.Target -> true
                | _ -> false)
            let membership = graph.Nodes |> Map.toSeq |> Seq.filter (snd >> Numeric.owned) |> Seq.map fst |> Set.ofSeq
            let representationMembership = domain.OccurrenceRepresentations |> Map.keys |> Set.ofSeq
            let elementForms = domain.Elements |> Map.forall (fun site slot ->
                domain.OccurrenceRepresentations.TryFind site = Some(Ok(ValueRepresentation.Buffer(None, ValueRepresentation.Scalar slot))))
            if not valid || not operationProofsValid || not operationValuesValid || not indexValuesValid || not foreignValuesValid || not elementForms || representationMembership <> participants || domain.SourceTypes <> (domain.Premises |> Map.map (fun _ premise -> premise.Shape.SourceType)) || membership <> targets || not (Numeric.sameRows expected actual) then
                reject (Some anchor) participants "The numeric carrier, joint premises, rewrite record or checked coverage obligation is inconsistent."
            else
                Ok { Values = domain.Values |> List.map (fun carrier -> carrier.Site, carrier) |> Map.ofList
                     ForeignResultUses = domain.ForeignResultUses
                     Operations = domain.Operations |> List.map (fun operation -> operation.Site, operation) |> Map.ofList; OperationRequired = domain.OperationRequired
                     IndexTransports = domain.IndexTransports |> List.map (fun transport -> transport.Site, transport) |> Map.ofList
                     Required = domain.Required; ResultSites = domain.ResultSites; Unresolved = domain.Unresolved
                     SourceTypes = domain.SourceTypes; Layouts = domain.Layouts; Elements = domain.Elements
                     ElementTypes = domain.ElementTypes; DeclaredScalars = domain.DeclaredScalars
                     OccurrenceRepresentations = domain.OccurrenceRepresentations; TypeRepresentations = domain.TypeRepresentations }
    | _ -> reject None Set.empty "Exactly one source NumericSettlement domain is required before witnessing."

/// Retain each Pending identity beside the currentness refusal that explains it.
/// Completeness is checked first; neither a partial ledger nor a Pending claim
/// can grant physical publication.
let project (graph: SemanticGraph) : Result<NumericWitnessProjection, WitnessProjectionFailure list> =
    let pending =
        graph.Nodes
        |> Map.toList
        |> List.choose (fun (id, node) ->
            match node.Kind with
            | SemanticKind.Obligation info when Numeric.owned node ->
                match info.Body with
                | ObligationBody.Pending reasons ->
                    Some
                        {
                            Kind = WitnessProjectionFailureKind.Settlement
                            Occurrence = Some id
                            Participants = Set.singleton id
                            Reason =
                                "NumericPublication: Pending claim "
                                + info.Id
                                + ": "
                                + String.concat "; " reasons
                        }
                | ObligationBody.ForeignResultCoverage _ ->
                    Clef.Compiler.Nanopass.ObligationDischarge.unavailable [info]
                    |> List.tryHead
                    |> Option.map (fun unavailable ->
                        { Kind = WitnessProjectionFailureKind.Settlement; Occurrence = Some id; Participants = Set.singleton id
                          Reason = "NumericPublication: Pending claim " + info.Id + ": " + String.concat "; " unavailable.MissingPremises })
                | _ -> None
            | _ -> None)

    match completeness graph with
    | failures when not failures.IsEmpty -> Error(failures @ pending)
    | _ ->
        match projectDomain graph, pending with
        | Error failures, _ -> Error(failures @ pending)
        | Ok _, _ :: _ -> Error pending
        | Ok projection, [] -> Ok projection

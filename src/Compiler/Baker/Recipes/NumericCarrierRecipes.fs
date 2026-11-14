// SPDX-License-Identifier: MIT
/// One source-owned materialization of held carriers and their joint evidence.
module Clef.Compiler.Baker.Recipes.NumericCarrierRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph
open Clef.Compiler.Baker.Ingredients.Obligations
module Numeric = Clef.Compiler.Baker.Ingredients.NumericValues
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries
module RangeSources = Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources

let private scalarKind ty = Types.tryGetNTUKind ty |> Option.exists (function
    | NTUKind.NTUint _ | NTUKind.NTUuint _ | NTUKind.NTUbool | NTUKind.NTUchar
    | NTUKind.NTUfloat _ | NTUKind.NTUposit _ -> true
    | _ -> false)

let private declarationOnly graph =
    let rec collect seen id =
        if Set.contains id seen then seen else
        match graph.Nodes.TryFind id with
        | Some node -> List.fold collect (Set.add id seen) node.Children
        | None -> Set.add id seen
    graph.Edges |> List.fold (fun found edge ->
        match edge.Role with
        | EdgeRole.BoundaryDeclaration declaration -> collect found declaration.Binding
        | _ -> found) Set.empty

let private resultSite (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Binding _ | SemanticKind.PatternBinding _ | SemanticKind.Obligation _ -> false
    | _ -> true

/// The owed census is derived from source demand, never from surviving carrier
/// or obligation rows. Retention keeps an exported input visible even when a
/// closed caller would otherwise establish an unused-formal omission.
let private requiredSites (graph: SemanticGraph) =
    let deferred = OrdinaryDemand.tryDeferredOnly graph |> Result.defaultValue Set.empty
    let inactive =
        match OrdinaryDemand.tryInactivity graph with
        | Ok proof -> Set.union proof.Formals proof.Excluded
        | Error _ -> Set.empty
    let inactive = Set.union inactive (RangeAnalysis.tailInactiveOccurrences graph)
    let declarations = declarationOnly graph
    let purposes = Reachability.declarationPurposes graph
    let demanded id (node: SemanticNode) =
        let retained = purposes |> Map.tryFind id |> Option.exists (Set.exists (snd >> (=) DeclRoot.LibraryExport))
        node.IsReachable && not (declarations.Contains id) &&
        (retained || (not (deferred.Contains id) && not (inactive.Contains id)))
    let required = graph.Nodes |> Map.fold (fun ids id node ->
        if demanded id node && scalarKind node.Type then Set.add id ids else ids) Set.empty
    let indices = graph.Nodes.Values |> Seq.choose (fun node ->
        match node.Kind with
        | SemanticKind.ContinuationDispatch(operand, _, _) when demanded node.Id node -> Some(node, operand)
        | _ -> None) |> Seq.toList
    required, indices

let private coverageId (node: SemanticNode) =
    sourceClaimId "numeric-carrier-coverage" node
    |> Option.defaultValue ($"numeric_carrier_{NodeId.value node.Id}")

let private indexId (node: SemanticNode) =
    sourceClaimId "numeric-index-coverage" node
    |> Option.defaultValue ($"numeric_index_{NodeId.value node.Id}")

/// Claim provenance follows the declaration, source call and role. Current
/// graph numbers locate citizens; they never supply the claim's identity.
let private foreignClaimId (graph: SemanticGraph) (application: ForeignResultApplication) role =
    let anchor id =
        match graph.Nodes.TryFind id with
        | Some node ->
            match sourceClaimId "foreign-result-site" node with
            | Some identity -> identity, true
            | None -> fmtRange node.Range, false
        | None -> invalidOp "A foreign result claim has a missing source participant."

    let role =
        match role with
        | ForeignResultProofRole.LogicalCoverage -> "logical-coverage"
        | ForeignResultProofRole.AbiNarrowing -> "abi-narrowing"

    let anchors =
        anchor application.Declaration
        :: anchor application.Call
        :: List.map anchor application.Context

    let segments = List.map fst anchors @ [role]

    let provenance =
        segments
        |> List.map (fun value -> string value.Length + ":" + value)
        |> String.concat ""

    (if anchors |> List.forall snd then "foreign_result_" else "transient_foreign_result_")
    + System.Convert.ToHexString(System.Text.Encoding.UTF8.GetBytes provenance)

/// Passive readers compare the exact models issued by this owning recipe.
let foreignResultModels (graph: SemanticGraph) (values: ScalarCarrier list) (evidence: RangeAnalysis.ForeignResultEvidence) =
    let application = evidence.Application
    let bySite = values |> List.map (fun value -> value.Site, value) |> Map.ofList
    let carrier = bySite.TryFind application.Call

    let capacity =
        carrier
        |> Option.bind (fun carrier ->
            match carrier.Representation, carrier.Slot with
            | Some representation, _ -> RangeSources.declaredRange representation
            | None, SettledSlot.Integer(bits, _) when bits > 0 ->
                Some(
                    if ValueRange.contains (ValueRange.unsignedOf bits) carrier.Range then
                        ValueRange.unsignedOf bits
                    else
                        ValueRange.twosComplement bits
                )
            | _ -> None)
        |> Option.defaultValue ValueRange.Unbounded

    let abi = evidence.Abi |> Option.map _.Node

    let premiseIdentity role id =
        graph.Nodes.TryFind id |> Option.bind (sourceClaimId role)

    let abiRange =
        evidence.Abi
        |> Option.bind _.Return
        |> Option.map _.Range
        |> Option.defaultValue ValueRange.Unbounded

    let model role =
        {
            Application = application
            Role = role
            ResultRange = evidence.ResultRange
            Destination =
                if role = ForeignResultProofRole.LogicalCoverage then
                    evidence.ResultRange
                else
                    capacity
            DestinationDeclaration =
                if role = ForeignResultProofRole.LogicalCoverage then
                    None
                else
                    carrier |> Option.bind _.Declaration
            Abi = abi
            AbiIdentity = abi |> Option.bind (premiseIdentity "foreign-result-abi")
            DestinationIdentity =
                if role = ForeignResultProofRole.LogicalCoverage then
                    None
                else
                    carrier
                    |> Option.bind _.Declaration
                    |> Option.bind (premiseIdentity "foreign-result-destination")
            AbiRange = abiRange
        }

    // A complete ABI ingress needs its width/embedding claim, but supplies no
    // behavioral relation to project. Narrower requests retain MissingBehavior.
    let completeIngress =
        application.Hypothesis.IsNone && abi.IsSome &&
        (match abiRange,capacity with ValueRange.Bounded _,ValueRange.Bounded _ -> true | _ -> false) &&
        evidence.ResultRange=abiRange && ValueRange.contains capacity abiRange
    (if completeIngress then [ForeignResultProofRole.AbiNarrowing]
     else [ ForeignResultProofRole.LogicalCoverage; ForeignResultProofRole.AbiNarrowing ])
    |> List.map (fun role -> role, model role)

/// The existing coverage algebra checks complete ABI-to-logical embedding.
/// A behavioral/refined result still uses the conditional foreign relation.
let foreignResultBody (model: ForeignResultCoverageModel) =
    match model.Application.Hypothesis, model.Role, model.Abi, model.AbiRange, model.Destination with
    | None, ForeignResultProofRole.AbiNarrowing, Some _, ValueRange.Bounded(lo,hi), ValueRange.Bounded(minimum,maximum)
        when model.ResultRange=model.AbiRange && ValueRange.contains model.Destination model.AbiRange ->
        ObligationBody.IntegerRepresentationCoverage(lo,hi,minimum,maximum)
    | _ -> ObligationBody.ForeignResultCoverage model

let foreignResultParticipants (application: ForeignResultApplication) (models: (ForeignResultProofRole * ForeignResultCoverageModel) list) =
    let participant role ordinal node =
        {
            Node = node
            Role = role
            Ordinal = ordinal
            Group = application.Call
        }

    [
        participant ParticipantRole.ForeignResultDeclaration 0 application.Declaration
        participant ParticipantRole.ForeignResultCall 0 application.Call
    ]
    @ (application.Context
       |> List.mapi (participant ParticipantRole.ForeignResultContext))
    @ (application.Hypothesis
       |> Option.map (fun hypothesis -> participant ParticipantRole.ForeignResultHypothesis 0 hypothesis.Quote)
       |> Option.toList)
    @ (application.Arguments
       |> List.map (fun argument -> participant ParticipantRole.ForeignResultActual argument.Index argument.Node))
    @ (models
       |> List.collect (fun (role, model) ->
           let ordinal = if role=ForeignResultProofRole.LogicalCoverage then 0 else 1
           (model.Abi
            |> Option.map (participant ParticipantRole.ForeignResultAbi ordinal)
            |> Option.toList)
           @ (model.DestinationDeclaration
              |> Option.map (participant ParticipantRole.ForeignResultDestination ordinal)
              |> Option.toList)))

let private foreignClaims graph enrichId (values: ScalarCarrier list) rangeFacts =
    match RangeAnalysis.foreignResultApplications graph rangeFacts with
    | Error reason -> Error reason
    | Ok applications ->
        applications
        |> List.fold
            (fun (enrichment, uses) evidence ->
                let application = evidence.Application
                let models = foreignResultModels graph values evidence
                let participants = foreignResultParticipants application models

                let claims =
                    models
                    |> List.map (fun (role, model) ->
                        let node =
                            obligationNode
                                graph.Nodes[application.Call]
                                enrichId
                                {
                                    Id = foreignClaimId graph application role
                                    Kind = "foreign-result-coverage"
                                    Logic = "QF_LIA"
                                    Statement =
                                        if role = ForeignResultProofRole.LogicalCoverage then
                                            "the declared foreign relation covers the reachable argument domain and inferred result enclosure"
                                        else
                                            "the foreign result is representable at the selected Clef destination width"
                                    Source = fmtRange graph.Nodes[application.Call].Range
                                    Refs = []
                                    Body = foreignResultBody model
                                }
                            |> Numeric.markOwned

                        role, node)

                let use' =
                    {
                        Application = application
                        Participants = ParticipantEvidence.Established participants
                        Claims = claims |> List.map (fun (role, node) -> role, node.Id)
                    }

                let own =
                    {
                        NewNodes = claims |> List.map snd
                        Annotated = []
                        NewEdges = Numeric.foreignProofRows use'
                    }

                Enrichment.combine enrichment own, uses @ [ use' ])
            (Enrichment.empty, [])
        |> Ok

let rec private kinds ty =
    let own = Types.tryGetNTUKind ty |> Option.toList
    let children =
        match applySubst ty with
        | NativeType.TApp(_, args) | NativeType.TTuple(args, _) -> args
        | NativeType.TFun(a, b) -> [a; b]
        | NativeType.TForall(_, body) | NativeType.TNativePtr body | NativeType.TByref(body, _) -> [body]
        | _ -> []
    own @ (children |> List.collect kinds)

/// Array element settlement shares the same range/representation owner. It is
/// computed in Baker, never reconstructed by a collection witness.
let private elementSlot (graph: SemanticGraph) (classifyView: NodeId -> Clef.Compiler.Baker.Ingredients.ArrayShapes.ReadOnlyViewProvenance) (node: SemanticNode) =
    let settledElementSlot element =
        match Types.tryGetNTUKind element with
        | Some NTUKind.NTUbool -> Some SettledSlot.Bool
        | Some NTUKind.NTUchar -> Some SettledSlot.Char
        | Some kind when NTUKind.isInteger kind ->
            let key = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType element
            match graph.ElementRanges.Value.TryFind key with
            | Some range ->
                match range, RangeAnalysis.heldWidthOf graph range with
                | ValueRange.Bounded _, Some bits when bits > 0 ->
                    let representation = RangeAnalysis.selectedRepresentationOf graph range
                    let covered =
                        match representation with
                        | Some representation -> Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange representation |> Option.exists (fun capacity -> ValueRange.contains capacity range)
                        | None -> graph.Platform |> Option.exists (fun context -> PlatformContext.substrateKind context = SubstrateKind.FPGA)
                    if covered then Some(SettledSlot.Integer(bits, representation |> Option.map _.Name)) else None
                | _ -> None
            | None -> None
        | _ -> None
    match applySubst node.Type with
    | NativeType.TApp(tc, [element]) when tc.NTUKind = Some NTUKind.NTUarray || Types.isReadOnlyViewTypeCon tc ->
        match StringByteStorage.element graph node.Id with
        | Some slot -> Some slot
        | None when Types.isReadOnlyViewTypeCon tc ->
            match classifyView node.Id with
            | Clef.Compiler.Baker.Ingredients.ArrayShapes.ReadOnlyViewProvenance.ByteBacked ->
                Clef.Compiler.Baker.Ingredients.StringBytes.byteRepresentation graph
                |> Option.map (fun (rep, _) -> SettledSlot.Integer(8, Some rep.Name))
            | Clef.Compiler.Baker.Ingredients.ArrayShapes.ReadOnlyViewProvenance.MixedConflict -> None
            | Clef.Compiler.Baker.Ingredients.ArrayShapes.ReadOnlyViewProvenance.ArrayBacked
            | Clef.Compiler.Baker.Ingredients.ArrayShapes.ReadOnlyViewProvenance.Unknown -> settledElementSlot element
        | None -> settledElementSlot element
    | _ -> None

let private elaborateWithRangeReviewCore (inheritedFiniteReview: bool) (inheritedCaptureReview: bool) (inheritedSequenceReview: bool)
                             (inheritedSequenceAuthority: SequenceRangeAuthority option)
                             (inheritedRangeFacts: RangeContextFacts option) (graph: SemanticGraph) =
    let enrichId = Elaboration.freshId ()
    let anchor = Boundary.anchor enrichId graph |> fun node -> { node with Metadata = node.Metadata.Remove "Baker.BoundaryOwned" } |> Numeric.markOwned
    let sourceReading = PlatformResolution.read graph
    let sourceCore = sourceReading.Platform |> Option.bind _.Core
    let finiteRelations = Numeric.finiteCellRelations graph
    let finiteObligations = Numeric.finiteCellObligations graph
    let currentFiniteActive =
        match finiteRelations with
        | Ok None -> false
        | _ -> true
    let finiteActive = inheritedFiniteReview || currentFiniteActive
    let captureRelations = Numeric.captureRelations graph
    let captureActive = inheritedCaptureReview || not captureRelations.IsEmpty
    // Recompute through the owning fixed point on this settled revision. This
    // issues evidence without rewriting held annotations or selected widths.
    let issuedRange = RangeAnalysis.issue graph
    let issuedRangeFacts = issuedRange |> Result.toOption
    let required, indexSites = requiredSites { graph with RangeContextFacts = issuedRangeFacts }
    let rangeCurrent = Result.isOk issuedRange
    // A failed issue retains the previous requirement, never its authority.
    // NumericSettlement installs only issuedRangeFacts on the graph.
    let rangeFacts = issuedRangeFacts |> Option.orElse (graph.RangeContextFacts |> Option.orElse inheritedRangeFacts)
    let freshFacts =
        match issuedRangeFacts with
        | Some facts ->
            facts.Values |> Map.toList |> List.choose (function
                | (RangeContext.Shared, id), range -> Some(id, range)
                | _ -> None) |> Map.ofList
        | None -> Map.empty
    let finiteProofsCurrent = not finiteActive || FiniteCellRanges.evidenceCurrent graph
    let sequenceActive = inheritedSequenceReview || Numeric.sequenceRangeActive graph
    let sequenceAuthority =
        match graph.SequenceRangeProvenance with Some authority -> Some authority | None -> inheritedSequenceAuthority
    let sequenceCurrent =
        not sequenceActive ||
        (graph.SequenceRangeProvenance |> Option.exists (Numeric.sequenceRangeCurrent graph))
    let select (node: SemanticNode) =
        let participants declaration = Set.ofList (anchor.Id :: node.Id :: (Option.toList declaration) @ (kindEdges node.Id node.Kind |> List.collect _.Sources))
        let fact slot range representation declaration =
            { Site = node.Id; Slot = slot; Range = range; Representation = representation; Declaration = declaration
              SourceType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type; Obligations = []; Participants = participants declaration }
        match Types.tryGetNTUKind node.Type with
        | Some NTUKind.NTUbool -> Ok(fact SettledSlot.Bool ValueRange.boolean None None)
        | Some NTUKind.NTUchar -> Ok(fact SettledSlot.Char (ValueRange.bounded 0I 1114111I) None None)
        | Some kind when NTUKind.isInteger kind ->
            match node.ValueRange, RangeAnalysis.heldWidth graph node.Id with
            | Some(ValueRange.Bounded(lo, hi) as range), Some bits when lo <= hi && bits > 0 ->
                let current = rangeCurrent && (
                    match freshFacts.TryFind node.Id with
                    | Some(ValueRange.Bounded _ as fresh) -> ValueRange.contains range fresh
                    | _ -> false)
                if not current then
                    if finiteActive && captureActive then Error "Finite-cell and closure capture relation premises changed or current source facts no longer fit the held integer range."
                    elif finiteActive then Error "Finite-cell relation premises changed or current source facts no longer fit the held integer range."
                    elif captureActive then Error "Closure capture relation premises changed or current source facts no longer fit the held integer range."
                    else Error "Invocation-context range premises changed or the producer's shared facts no longer fit the held integer range."
                else
                    match RangeAnalysis.selectedRepresentation graph node.Id, sourceCore with
                    | Some representation, Some core when sourceReading.Findings.IsEmpty ->
                        match core.Representations |> List.filter (fun declaration -> declaration.Representation = representation) with
                        | [declaration] when NumericRepresentation.isOffered representation && representation.Bits = bits ->
                            Ok(fact (SettledSlot.Integer(bits, Some representation.Name)) range (Some representation) (Some declaration.Node))
                        | _ -> Error "The held scalar has no unique matching offered representation declaration."
                    | None, _ when graph.Platform |> Option.exists (fun context -> PlatformContext.substrateKind context = SubstrateKind.FPGA) ->
                        Ok(fact (SettledSlot.Integer(bits, None)) range None None)
                    | _ -> Error "The held integer carrier lacks its source representation/declaration authority."
            | _ -> Error "The required integer carrier has no finite observable range and settled positive width."
        | Some(NTUKind.NTUfloat width) ->
            let selected =
                match width with
                | NTUWidth.Fixed bits when bits > 0 -> Some(bits, None)
                | NTUWidth.Resolved dimension -> sourceCore |> Option.bind (fun core ->
                    match core.Widths |> List.filter (fun declared -> declared.Name = WidthDimension.name dimension) with
                    | [declared] when declared.Bits > 0 -> Some(declared.Bits, Some declared.Node)
                    | _ -> None)
                | _ -> None
            match selected with
            | Some(bits, declaration) -> Ok(fact (SettledSlot.Real bits) (node.ValueRange |> Option.defaultValue ValueRange.Unbounded) None declaration)
            | None -> Error "The real scalar carrier has no unique source width declaration."
        | Some(NTUKind.NTUposit _) -> Error "The posit carrier requires its exact source format identity; IEEE width alone cannot authorize a posit representation."
        | _ -> Error "The required scalar carrier has no source settlement rule."
    let pendingCoverage id reason =
        match Types.tryGetNTUKind graph.Nodes[id].Type with
        | Some kind when NTUKind.isInteger kind ->
            let node =
                obligationNode
                    graph.Nodes[id]
                    enrichId
                    {
                        Id = coverageId graph.Nodes[id]
                        Kind = "numeric-carrier-coverage"
                        Logic = "QF_LIA"
                        Statement = "the held scalar carrier covers its exact source range under the retained source domain"
                        Source = fmtRange graph.Nodes[id].Range
                        Refs = []
                        Body = ObligationBody.Pending [ reason ]
                    }
                |> Numeric.markOwned

            {
                NewNodes = [ node ]
                Annotated = []
                NewEdges = [ constrains [ id; anchor.Id ] node ]
            }
        | _ -> Enrichment.empty
    let values, unresolved, proofs = required |> Set.fold (fun (values, unresolved, proofs) id ->
        match select graph.Nodes[id] with
        | Error reason -> values, Map.add id reason unresolved, Enrichment.combine proofs (pendingCoverage id reason)
        | Ok carrier ->
            match carrier.Slot, Numeric.coverage carrier with
            | SettledSlot.Integer _, Some body ->
                let unresolved =
                    if Clef.Compiler.Baker.Ingredients.StringBytes.proofOutcome body = BoundaryProofOutcome.Proven then unresolved
                    else Map.add id "The selected scalar carrier does not cover its established source range." unresolved
                let node = obligationNode graph.Nodes[id] enrichId
                               { Id = coverageId graph.Nodes[id]; Kind = "numeric-carrier-coverage"; Logic = "QF_LIA"
                                 Statement = "the held scalar carrier covers its exact source range under the retained source domain"
                                 Source = fmtRange graph.Nodes[id].Range; Refs = []; Body = body } |> Numeric.markOwned
                let carrier = { carrier with Obligations = [node.Id] }
                carrier :: values, unresolved, Enrichment.combine proofs { NewNodes = [node]; Annotated = []; NewEdges = Numeric.proofRows carrier node.Id body }
            | SettledSlot.Integer _, None ->
                let reason = "The required scalar coverage obligation is unavailable."
                values, Map.add id reason unresolved, Enrichment.combine proofs (pendingCoverage id reason)
            | _ -> carrier :: values, unresolved, proofs) ([], Map.empty, Enrichment.empty)
    let classifyView = Clef.Compiler.Baker.Ingredients.ArrayShapes.readOnlyViewClassifier graph
    let elements = graph.Nodes |> Map.toList |> List.choose (fun (id, node) -> elementSlot graph classifyView node |> Option.map (fun slot -> id, slot)) |> Map.ofList
    let elementTypes =
        graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
            match applySubst node.Type, elements.TryFind id with
            | NativeType.TApp(tc, [element]), Some slot
                when tc.NTUKind = Some NTUKind.NTUarray ||
                     (Types.isReadOnlyViewTypeCon tc &&
                      classifyView id <> Clef.Compiler.Baker.Ingredients.ArrayShapes.ReadOnlyViewProvenance.ByteBacked &&
                      classifyView id <> Clef.Compiler.Baker.Ingredients.ArrayShapes.ReadOnlyViewProvenance.MixedConflict) ->
                Some(Clef.Compiler.NativeTypedTree.TypeIdentities.ofType element, slot)
            | _ -> None)
        |> List.groupBy fst |> List.choose (fun (key, entries) ->
            match entries |> List.map snd |> List.distinct with [slot] -> Some(key, slot) | _ -> None) |> Map.ofList
    let declaredScalars =
        graph.Nodes |> Map.toList |> List.collect (fun (_, node) -> kinds node.Type) |> List.distinct |> List.choose (fun kind ->
            match RangeSources.declarationOfKind graph.Platform kind with
            | Some declared when declared.Bits > 0 -> Some(kind, SettledSlot.Integer(declared.Bits, Some declared.Repr))
            | _ -> None) |> Map.ofList
    let occurrenceRepresentations, typeRepresentations =
        Clef.Compiler.Baker.Ingredients.ValueRepresentations.settle graph (List.rev values) elements elementTypes declaredScalars
    let operationEnrichment, operations, operationFailures, operationRequired, operationProofs =
        NumericOperationRecipes.settle graph anchor.Id (values |> List.map (fun carrier -> carrier.Site, carrier) |> Map.ofList) required
    let operationMeets = operations |> List.map (fun operation -> operation.Site, Clef.Compiler.Baker.Ingredients.NumericOperations.meets operation) |> Map.ofList
    let unresolved = Map.fold (fun failures id reason -> Map.add id reason failures) unresolved operationFailures
    let unresolved = operationMeets |> Map.fold (fun failures site meets ->
        let previous = graph.Codata.Value.Meets.TryFind site |> Option.defaultValue []
        let combined = previous @ meets |> List.distinct
        if combined |> List.groupBy _.Operand |> List.exists (fun (_, sameActual) -> sameActual.Length > 1) then
            Map.add site "An operation's ordered occurrences demand contradictory adaptations for one actual identity." failures
        else failures) unresolved
    let pointer = sourceCore |> Option.bind (fun core ->
        match core.Widths |> List.filter (fun width -> width.Name = "Pointer" && width.Bits > 0) with
        | [width] -> Some width
        | _ -> None)
    let bySite = values |> List.map (fun value -> value.Site, value) |> Map.ofList
    let indexEnrichment, indexTransports, unresolved =
        indexSites |> List.fold (fun (enrichment, transports, failures) (node, operand) ->
            let refuse reason =
                let proof =
                    obligationNode
                        node
                        enrichId
                        {
                            Id = indexId node
                            Kind = "numeric-index-coverage"
                            Logic = "QF_LIA"
                            Statement = "the exact dispatch selector range fits the declared platform index transport"
                            Source = fmtRange node.Range
                            Refs = []
                            Body = ObligationBody.Pending [ reason ]
                        }
                    |> Numeric.markOwned

                let own =
                    {
                        NewNodes = [ proof ]
                        Annotated = []
                        NewEdges = [ constrains [ node.Id; operand; anchor.Id ] proof ]
                    }

                Enrichment.combine enrichment own, transports, Map.add node.Id reason failures
            match pointer, bySite.TryFind operand with
            | Some width, Some carrier ->
                match carrier.Slot, carrier.Range with
                | (SettledSlot.Integer _ | SettledSlot.Bool | SettledSlot.Char), ValueRange.Bounded(lo, hi) when lo <= hi ->
                    let unsigned = lo >= 0I
                    let capacity = if unsigned then ValueRange.unsignedOf width.Bits else ValueRange.twosComplement width.Bits
                    if not(ValueRange.contains capacity carrier.Range) then
                        refuse "The dispatch selector range is not representable in the selected platform's index domain."
                    else
                        let minimum, maximum = match capacity with ValueRange.Bounded(a,b) -> a,b | _ -> invalidOp "Finite index capacity expected."
                        let body = ObligationBody.IntegerRepresentationCoverage(lo, hi, minimum, maximum)
                        let proof = obligationNode node enrichId
                                        { Id = indexId node; Kind = "numeric-index-coverage"; Logic = "QF_LIA"
                                          Statement = "the exact dispatch selector range fits the declared platform index transport"
                                          Source = fmtRange node.Range; Refs = []; Body = body } |> Numeric.markOwned
                        let transport =
                            { Site = node.Id; Operand = operand; Carrier = carrier; PointerDeclaration = width.Node; PointerBits = width.Bits
                              Unsigned = unsigned; Capacity = capacity; Obligation = proof.Id
                              Participants = carrier.Participants |> Set.add node.Id |> Set.add width.Node }
                        let own = { NewNodes = [proof]; Annotated = []; NewEdges = Numeric.indexRows transport }
                        Enrichment.combine enrichment own, transport :: transports, failures
                | _ -> refuse "The dispatch selector lacks a finite source integer carrier for index transport."
            | _ -> refuse "The dispatch selector lacks its source carrier or selected platform Pointer declaration.")
            (Enrichment.empty, [], unresolved)
    let unresolved =
        match finiteRelations with
        | Error reason -> unresolved.Add(anchor.Id, reason)
        | Ok _ when not finiteProofsCurrent ->
            unresolved.Add(anchor.Id, "Finite-cell relation premises changed or the retained recurrence certificate no longer matches current source transitions.")
        | Ok _ -> unresolved
    let unresolved =
        if sequenceCurrent then unresolved
        else unresolved.Add(anchor.Id, "Finite-sequence relation premises changed or the source-to-machine range authority is missing; renew the owning source proof and representation handoff.")
    let unresolved =
        match issuedRange with
        | Ok _ -> unresolved
        | Error reason -> unresolved.Add(anchor.Id, "Invocation-context range issuance failed: " + reason)
    let foreignEnrichment, foreignUses, unresolved =
        match foreignClaims graph enrichId values issuedRangeFacts with
        | Ok (claims, uses) -> claims, uses, unresolved
        | Error (site, reason) -> Enrichment.empty, [], unresolved.Add(site, "Foreign-result source census is unavailable: " + reason)
    let domain =
        { RequiresSequenceReview = sequenceActive
          SequenceRangeAuthority = sequenceAuthority
          RangeContextFacts = rangeFacts
          ForeignResultUses = foreignUses
          RequiresFiniteCellReview = currentFiniteActive || (inheritedFiniteReview && not unresolved.IsEmpty)
          FiniteCellRelations = finiteRelations |> Result.defaultValue None
          FiniteCellObligations = finiteObligations
          RequiresCaptureReview = not captureRelations.IsEmpty || (inheritedCaptureReview && not unresolved.IsEmpty)
          CaptureRelations = captureRelations
          Premises = Numeric.premises graph; Platform = Boundary.platformPremise graph.Platform
          Roots = graph.DeclarationRoots; Escaping = graph.Escaping.Value; Layouts = graph.Layouts.Value
          Required = required; ResultSites = required |> Set.filter (fun id -> resultSite graph.Nodes[id])
          SourceTypes = Numeric.premises graph |> Map.map (fun _ premise -> premise.Shape.SourceType)
          Elements = elements; ElementTypes = elementTypes; DeclaredScalars = declaredScalars
          ElementRanges = graph.ElementRanges.Value; ByteRanges = Numeric.byteRanges graph
          ByteReadRanges = Numeric.byteReadRanges graph; ByteViews = Numeric.byteViews graph; StringExtents = Numeric.stringExtents graph
          OccurrenceRepresentations = occurrenceRepresentations; TypeRepresentations = typeRepresentations
          Operations = List.rev operations; OperationRequired = operationRequired
          OperationMeets = operationMeets; OperationProofs = operationProofs
          IndexTransports = List.rev indexTransports; IndexRequired = indexSites |> List.map (fst >> _.Id) |> Set.ofList
          Values = List.rev values; Unresolved = unresolved }
    let enrichment =
        Enrichment.combine (Enrichment.combine (Enrichment.combine (Enrichment.combine proofs operationEnrichment) indexEnrichment) foreignEnrichment)
            { NewNodes = [anchor]; Annotated = []
              NewEdges = Numeric.domainRow anchor.Id domain :: Numeric.domainRewrite anchor.Id domain :: (domain.Values |> List.map Numeric.carrierRow) }
    enrichment, issuedRangeFacts

let elaborateWithRangeReview inheritedFiniteReview inheritedCaptureReview inheritedSequenceReview inheritedSequenceAuthority inheritedRangeFacts graph =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> elaborateWithRangeReviewCore inheritedFiniteReview inheritedCaptureReview inheritedSequenceReview inheritedSequenceAuthority inheritedRangeFacts graph)


/// Initial numeric settlement retains the existing current-source activation rule.
let elaborateWithFiniteReview inheritedFiniteReview graph =
    elaborateWithRangeReview inheritedFiniteReview false false None None graph |> fst

let elaborate graph = elaborateWithRangeReview false false false None None graph |> fst

/// Validate the source-rule census before a ledger or physical projection can
/// be accepted. Deleting a requirement row together with its claim cannot make
/// the surviving ledger appear complete.
let completeness (graph: SemanticGraph) : (NodeId * string) list =
    let required, indices = requiredSites graph
    let foreignApplications = RangeAnalysis.foreignResultApplications graph graph.RangeContextFacts
    let values =
        graph.Edges |> List.choose(fun edge -> match edge.Role with EdgeRole.NumericDomain domain -> Some domain.Values | _ -> None)
        |> function [values] -> values | _ -> []

    let expected =
        (required
         |> Set.toList
         |> List.collect (fun id ->
             let node = graph.Nodes[id]

             let carrier =
                 if Types.tryGetNTUKind node.Type |> Option.exists NTUKind.isInteger then
                     [ id, coverageId node, "numeric-carrier-coverage" ]
                 else
                     []

             let operations =
                 Clef.Compiler.Baker.Ingredients.NumericOperations.operation graph node
                 |> Option.map (fun recipe ->
                     Clef.Compiler.Baker.Ingredients.NumericOperations.obligationRoles graph recipe
                     |> List.mapi (fun ordinal role ->
                         id, Clef.Compiler.Baker.Ingredients.NumericOperations.claimId node ordinal role, "numeric-operation-proof"))
                 |> Option.defaultValue []

             carrier @ operations))
        @ (indices
           |> List.map (fun (node, _) -> node.Id, indexId node, "numeric-index-coverage"))
        @ (match foreignApplications with
           | Ok applications -> applications |> List.collect (fun evidence ->
               foreignResultModels graph values evidence
               |> List.map (fun (role,_) -> evidence.Application.Call, foreignClaimId graph evidence.Application role, "foreign-result-coverage"))
           | Error _ -> [])

    let numericKind kind =
        kind = "numeric-carrier-coverage"
        || kind = "numeric-operation-proof"
        || kind = "numeric-index-coverage"
        || kind = "foreign-result-coverage"

    let actual =
        graph.Nodes
        |> Map.toList
        |> List.choose (fun (id, node) ->
            match node.Kind with
            | SemanticKind.Obligation info when Numeric.owned node && numericKind info.Kind -> Some(id, info)
            | _ -> None)

    let collisions =
        expected
        |> List.groupBy (fun (_, key, _) -> key)
        |> List.collect (fun (key, claims) ->
            if claims.Length = 1 then
                []
            else
                claims
                |> List.map (fun (site, _, _) -> site, "Numeric obligation identity collision: " + key))

    let missing =
        expected
        |> List.choose (fun (site, key, kind) ->
            match actual |> List.filter (fun (_, info) -> info.Id = key && info.Kind = kind) with
            | [ id, _ ] ->
                let incidence =
                    graph.Edges
                    |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = id)

                match incidence with
                | [ edge ] when List.contains site edge.Sources -> None
                | _ ->
                    Some(
                        site,
                        "Numeric obligation completeness: missing or duplicate source incidence for "
                        + key
                    )
            | _ -> Some(site, "Numeric obligation completeness: missing or duplicate claim " + key))

    let unexpected =
        actual
        |> List.choose (fun (id, info) ->
            if
                expected
                |> List.exists (fun (_, key, kind) -> key = info.Id && kind = info.Kind)
            then
                None
            else
                Some(id, "Numeric obligation completeness: unexpected claim " + info.Id))

    let foreignCensusFailures =
        match foreignApplications with
        | Ok _ -> []
        | Error (site, reason) -> [site, "Numeric obligation completeness: foreign-result source census is unavailable: " + reason]
    foreignCensusFailures @ collisions @ missing @ unexpected

// SPDX-License-Identifier: MIT
/// Validate and project Baker's settled boundary rows. This module performs
/// no descriptor parsing, identity discovery, ABI choice or semantic repair.
module Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Ingredients = Clef.Compiler.Baker.Ingredients.Boundaries
module Declarations = Clef.Compiler.Baker.Recipes.BoundaryDeclarations
module Bytes = Clef.Compiler.Baker.Ingredients.StringBytes
module StringOrigins = Clef.Compiler.Baker.Ingredients.StringOrigins

let private failure occurrence participants reason =
    {
        Kind = WitnessProjectionFailureKind.Settlement
        Occurrence = occurrence
        Participants = participants
        Reason = "BoundaryEmission: " + reason
    }

let project (graph: SemanticGraph) : Result<BoundaryEmissionProjection, WitnessProjectionFailure list> =
    let domains = graph.Edges |> List.choose (fun edge ->
        match edge.Role with EdgeRole.BoundaryDomain domain -> Some (edge, domain) | _ -> None)
    match domains with
    | [domainRow, domain] ->
        let participants = Map.keys domain.Premises |> Set.ofSeq
        let stale reason = Error [failure (Some domainRow.Target) participants reason]
        let borrowMembership =
            let sites values = List.distinct values |> List.sort
            let snapshots = domain.StringBorrowSnapshots |> List.map _.Snapshot |> sites
            let copies = domain.StringBorrowCopies |> List.map _.Site |> sites
            let allocations = domain.StringBorrowAllocations |> List.map _.Site |> sites
            snapshots=copies &&
            (domain.StringBorrowCopies |> List.forall (fun copy -> copy.Allocation.IsSome)) &&
            (domain.StringBorrowCopies |> List.choose _.Allocation |> sites)=allocations &&
            (domain.IntrinsicCalls |> List.forall (fun call ->
                match domain.ByteViews |> List.filter (fun view -> view.Site=call.Buffer) with
                | [view] when view.StaticOrigins.IsEmpty ->
                    domain.StringBorrowSnapshots |> List.exists (fun snapshot -> snapshot.Site=view.ExtentSource)
                | _ -> true))
        let snapshotProofsCurrent =
            domain.IntrinsicCalls |> List.forall (fun call ->
                match domain.ByteViews |> List.filter (fun view -> view.Site=call.Buffer) with
                | [view] when view.StaticOrigins.IsEmpty ->
                    match domain.StringBorrowSnapshots |> List.filter (fun snapshot -> snapshot.Site=view.ExtentSource),
                          domain.IntrinsicProofs |> List.filter (fun proof -> proof.Site=call.Site && proof.Ordinal=1),
                          graph.Nodes.TryFind call.Count |> Option.bind _.ValueRange with
                    | [snapshot],[proof],Some(ValueRange.Bounded(minimum,maximum)) ->
                        match domain.StringBorrowCopies |> List.filter (fun copy -> copy.Site=snapshot.Snapshot) with
                        | [copy] ->
                            match copy.Allocation |> Option.bind (fun id -> domain.StringBorrowAllocations |> List.tryFind (fun allocation -> allocation.Site=id)) with
                            | Some allocation ->
                                snapshot.Extent=copy.CountCarrier && allocation.Count=copy.CountOperand.Reference &&
                                copy.Count=copy.CountOperand.Actual && copy.CountCarrier.Site=copy.CountOperand.Actual &&
                                snapshot.Extent.Range=ValueRange.bounded minimum maximum &&
                                allocation.CountCarrier.Range=ValueRange.bounded minimum maximum &&
                                allocation.MinimumCount=minimum && allocation.MaximumCount=maximum &&
                                (match proof.Body with
                                 | ObligationBody.InputBufferBound(count,capacity) when minimum=maximum ->
                                     bigint count=minimum && bigint capacity=minimum
                                 | ObligationBody.SnapshotBorrowBound(count,viewSite,copySite,allocationSite,lo,hi) ->
                                     minimum<maximum && 0I<=minimum && count=call.Count &&
                                     viewSite=snapshot.Site && copySite=copy.Site && allocationSite=allocation.Site &&
                                     lo=minimum && hi=maximum
                                 | _ -> false)
                            | None -> false
                        | _ -> false
                    | _ -> false
                | _ -> true)
        let anchorValid = graph.Nodes.TryFind domainRow.Target |> Option.exists (fun node ->
            Ingredients.ownedNode node && match node.Kind with SemanticKind.Literal NativeLiteral.Unit -> true | _ -> false)
        if not anchorValid || domain.Premises <> Ingredients.premises graph || domain.Platform <> Ingredients.platformPremise graph.Platform || domain.Meets <> graph.Codata.Value.Meets || domain.StringStorage <> Bytes.storagePremise graph then
            stale "A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed; Baker must settle the new source graph."
        elif not domain.Failures.IsEmpty then
            Error (domain.Failures |> List.map (fun (site, participants, reason) -> failure (Some site) participants reason))
        elif not borrowMembership then
            stale "The source-published snapshot, copy or allocation dependency account is incomplete."
        elif not snapshotProofsCurrent then
            stale "The runtime snapshot borrow proof lost its exact count, snapshot, copy, allocation or finite range incidence."
        elif (match domain.StringOriginRelations with
              | Some expected ->
                  StringOrigins.relations graph <> Ok expected || domain.StringOriginRoots <> Some graph.DeclarationRoots
              | None ->
                  (domain.ByteViews |> List.exists (fun view -> StringOrigins.used view.Participants)) ||
                  (domain.StringExtents |> List.exists (fun extent -> StringOrigins.used extent.Participants))) then
            stale "The string-origin relation premises changed; Baker must settle the new source graph."
        elif (not domain.StringComparisonReads.IsEmpty || not domain.StringBorrowSnapshots.IsEmpty || not domain.StringBorrowCopies.IsEmpty || not domain.StringBorrowAllocations.IsEmpty) &&
             (match MemoryPublication.project graph with
              | Error _ -> true
              | Ok memory ->
                  (domain.StringComparisonReads |> List.exists (fun fact -> memory.Operations.TryFind fact.Site <> Some(MemoryWitnessOperation.ArrayAccess fact))) ||
                  (domain.StringBorrowSnapshots |> List.exists (fun fact -> memory.Operations.TryFind fact.Site <> Some(MemoryWitnessOperation.StringView fact))) ||
                  (domain.StringBorrowCopies |> List.exists (fun fact -> memory.ArrayCopies.TryFind fact.Site <> Some fact)) ||
                  (domain.StringBorrowAllocations |> List.exists (fun fact -> memory.Operations.TryFind fact.Site <> Some(MemoryWitnessOperation.ArrayAllocation fact)))) then
            stale "A local string borrow lost its exact source-published guarded read, snapshot copy or lifetime correspondence."
        else
            let writableDeclarations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryWritableBufferDeclaration row -> Some row | _ -> None)
            let resourceDeclarations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryResourceDeclaration row -> Some row | _ -> None)
            let resourceAccesses = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryResourceAccess row -> Some row | _ -> None)
            let imports = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryImport import -> Some import | _ -> None)
            let entries = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryEntry entry -> Some entry | _ -> None)
            let callbackInvocations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCallbackInvocation invocation -> Some invocation | _ -> None)
            let closedEntries = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryClosedEntry entry -> Some entry | _ -> None)
            let calls = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCall call -> Some call | _ -> None)
            let coverages = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCoverage coverage -> Some coverage | _ -> None)
            let expectedCoverage = calls |> List.collect (fun call ->
                (call.Arguments |> List.mapi (fun ordinal operand -> match operand.Abi with BoundaryScalar.Entry _ | BoundaryScalar.ResourceHandle _ -> None | _ -> Some(call.Site, ordinal, operand.Actual)) |> List.choose id) @
                (call.Result |> Option.toList |> List.filter (function BoundaryScalar.Integer _ | BoundaryScalar.ResourceHandle _ -> false | _ -> true) |> List.map (fun _ -> call.Site, -1, call.Site))) |> List.sort
            let resourceOwners=domain.ResourceEvaluationRoots |> List.map(fun (owner,_,_)->owner) |> Set.ofList
            let currentRelations=graph.Edges |> List.choose(fun edge ->
                if edge.Class<>EdgeClass.Evaluation || not(edge.Sources |> List.tryHead |> Option.exists resourceOwners.Contains) then None else
                let role=match edge.Role with
                         | EdgeRole.EvaluationRoot -> Some ResourceEvaluationRole.Root
                         | EdgeRole.EvaluationOperand access -> Some(ResourceEvaluationRole.Operand access)
                         | EdgeRole.EvaluationFlow(source,target,transfer) -> Some(ResourceEvaluationRole.Flow(source,target,transfer))
                         | EdgeRole.EvaluationPending reason -> Some(ResourceEvaluationRole.Pending reason)
                         | _ -> None
                role |> Option.map(fun role->{Role=role;Ordinal=edge.Ordinal;Sources=edge.Sources;Target=edge.Target}:ResourceEvaluationRelation))
            let resourceFlowCurrent =
                List.sort currentRelations=List.sort domain.ResourceEvaluationRelations &&
                (domain.ResourceEvaluationRoots |> List.forall(fun (owner,implementation,body)->
                    match graph.Nodes.TryFind owner,graph.Nodes.TryFind implementation with
                    | Some {Kind=SemanticKind.Binding(_,false,_,_);Children=[actual]},Some {Kind=SemanticKind.Lambda(_,actualBody,[],_,_)} -> actual=implementation && actualBody=body
                    | _ -> false))
            let resourceEvidenceCurrent =
                match domain.ResourceEvidence with
                | None -> domain.ResourceEvaluationRoots.IsEmpty && domain.ResourceEvaluationRelations.IsEmpty && domain.ResourceAccesses.IsEmpty
                | Some evidence ->
                    evidence.Roots=List.distinct domain.ResourceEvaluationRoots && evidence.Relations=domain.ResourceEvaluationRelations && evidence.Accesses=domain.ResourceAccesses &&
                    evidence.Premises.ContainsKey evidence.Platform && evidence.Premises.ContainsKey evidence.Core &&
                    (evidence.Premises |> Map.forall(fun id premise->domain.Premises.TryFind id=Some premise))
            let claim role site citizen =
                graph.Nodes.TryFind citizen |> Option.bind(fun node ->
                    match node.Kind with
                    | SemanticKind.Obligation info when Ingredients.ownedNode node && info.Kind=role &&
                        (graph.Nodes.TryFind site |> Option.bind(Clef.Compiler.Baker.Ingredients.Obligations.sourceClaimId role))=Some info.Id -> Some info
                    | _ -> None)
            let conversionAt site citizen =
                claim "foreign-resource-nullable-conversion" site citizen |> Option.bind(fun info ->
                    match info.Body with ObligationBody.ResourceConversion model -> Some model | _ -> None)
            let cleanupAt site citizen =
                claim "foreign-resource-cleanup" site citizen |> Option.bind(fun info ->
                    match info.Body with ObligationBody.ResourceCleanup model -> Some model | _ -> None)
            let exactSupport site citizen (resource:BoundaryResourceDeclaration) (cleanup:ResourceCleanupModel) =
                let support=Set.union resource.Participants (cleanup.Relations |> List.collect(fun row->row.Target::row.Sources) |> Set.ofList)
                match graph.Edges |> List.filter(fun edge->edge.Target=citizen && edge.Role=EdgeRole.Constrains) with
                | [edge] -> edge.Sources |> List.tryHead = Some site && (Set.ofList edge.Sources).IsSupersetOf support
                | _ -> false
            let casesCurrent (cleanup:ResourceCleanupModel) =
                let expected=cleanup.Relations |> List.map _.Target |> List.distinct |> List.choose(fun site->
                    match graph.Nodes.TryFind site with
                    | Some {Kind=SemanticKind.CaseElimination(subject,arms)} ->
                        Some {Site=site;Subject=subject;Domain=[cleanup.ConversionModel.NoneCase;cleanup.ConversionModel.SomeCase]
                              Arms=arms |> List.map(fun arm->
                                {Ordinal=match arm.Pattern with Pattern.Union(_,ordinal,_,_)->Some ordinal | _->None
                                 Body=arm.Body;BooleanResult=match graph.Nodes.TryFind arm.Body with Some {Kind=SemanticKind.Literal(NativeLiteral.Bool value)}->Some value | _->None})}
                    | _->None)
                List.sort expected=List.sort cleanup.Cases
            let resourceErrors=calls |> List.choose(fun call ->
                let valid =
                    match call.Resource with
                    | Some(BoundaryResourceUse.AcquireNullable account) ->
                        match resourceDeclarations |> List.filter(fun row->row.Identity=account.Declaration),conversionAt call.Site account.Conversion,cleanupAt call.Site account.Cleanup with
                        | [resource],Some conversion,Some cleanup ->
                            conversion.Acquisition=call.Site && conversion.Declaration=resource.Identity && conversion.Import=call.Import &&
                            conversion.OptionType=resource.ResultType && conversion.HandleType=resource.HandleType && conversion.PointerBits=resource.PointerBits &&
                            cleanup.Acquisition=call.Site && cleanup.Declaration=resource.Identity && cleanup.Release=resource.Release &&
                            cleanup.Conversion=account.Conversion && cleanup.ConversionModel=conversion &&
                            (match cleanup.Relations |> List.filter(fun row->row.Role=ResourceEvaluationRole.Root) with
                             | [{Sources=[owner;_]}] ->
                                 List.sort cleanup.Relations=List.sort(currentRelations |> List.filter(fun row->row.Sources |> List.tryHead=Some owner))
                             | _->false) && casesCurrent cleanup &&
                            exactSupport call.Site account.Conversion resource cleanup && exactSupport call.Site account.Cleanup resource cleanup &&
                            (imports |> List.exists(fun row->row.Identity=call.Import && row.Binding=resource.Acquisition)) &&
                            (graph.Nodes.TryFind call.Site |> Option.exists(fun node->node.Children=call.Callee::(call.Arguments |> List.map _.Actual)))
                        | _ -> false
                    | Some(BoundaryResourceUse.ReleaseOwned account) ->
                        match cleanupAt account.Acquisition account.Cleanup with
                        | Some cleanup ->
                            cleanup.Declaration=account.Declaration &&
                            (cleanup.Points |> List.exists(fun point->
                                point.Site=call.Site && point.Port=EvaluationPort.Exit &&
                                (match point.Event,call.Arguments,imports |> List.tryFind(fun row->row.Identity=call.Import) with
                                 | Some(ResourceFlowEvent.Release(actual,binding)),[operand],Some import -> actual=operand.Actual && binding=import.Binding
                                 | _ -> false)))
                        | _ -> false
                    | None -> not((call.Result |> Option.toList)@(call.Arguments |> List.map _.Abi) |> List.exists(function BoundaryScalar.ResourceHandle _->true|_->false))
                if valid then None else Some(failure (Some call.Site) call.Participants "The resource call lost its exact current conversion, cleanup or original declaration/operand account."))
            let resourceAccessErrors=resourceAccesses |> List.choose(fun access->
                let valid =
                    match cleanupAt access.Acquisition access.Cleanup,resourceDeclarations |> List.tryFind(fun row->row.Identity=access.Declaration),graph.Nodes.TryFind access.Site with
                    | Some cleanup,Some resource,Some node when cleanup.Acquisition=access.Acquisition && cleanup.Declaration=access.Declaration ->
                        let sourceType=graph.Nodes.TryFind access.Source |> Option.map(fun node->Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type)
                        let siteType=Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type
                        let incidence =
                            match access.Kind,node.Kind,node.Children with
                            | BoundaryResourceAccessKind.OptionTag,SemanticKind.CaseElimination(subject,_),_ -> subject=access.Source && sourceType=Some resource.ResultType
                            | BoundaryResourceAccessKind.OptionTag,SemanticKind.DUGetTag(subject,_),_ -> subject=access.Source && sourceType=Some resource.ResultType
                            | BoundaryResourceAccessKind.OptionPayload,SemanticKind.DUEliminate(subject,ordinal,"Some",_),_ ->
                                subject=access.Source && ordinal=cleanup.ConversionModel.SomeCase && sourceType=Some resource.ResultType && siteType=resource.HandleType
                            | BoundaryResourceAccessKind.ImmutableAlias,SemanticKind.VarRef(_,Some binding),_ -> binding=access.Source && sourceType=Some siteType
                            | BoundaryResourceAccessKind.ImmutableAlias,SemanticKind.Binding(_,false,false,_),[initializer] -> initializer=access.Source && sourceType=Some siteType
                            | BoundaryResourceAccessKind.ImmutableAlias,SemanticKind.TypeAnnotation(inner,_),[actual] -> inner=access.Source && inner=actual && sourceType=Some siteType
                            | _->false
                        let selections=access.Selection |> List.forall(fun selection->
                            match graph.Nodes.TryFind selection.Decision with
                            | Some {Kind=SemanticKind.CaseElimination(subject,arms)} when subject=selection.Scrutinee && selection.Arm>=0 && selection.Arm<arms.Length ->
                                let arm=arms[selection.Arm]
                                (match arm.Pattern with Pattern.Union(_,ordinal,_,_)->Some ordinal | _->None)=selection.CaseOrdinal && arm.Guard=None && selection.Guard=None
                            | _->false)
                        incidence && selections && (siteType=resource.HandleType || access.Kind=BoundaryResourceAccessKind.OptionTag || siteType=resource.ResultType) &&
                        access.Participants.Contains access.Site && access.Participants.Contains access.Source && access.Participants.Contains access.Cleanup
                    | _->false
                if valid then None else Some(failure (Some access.Site) access.Participants "A resource read lost its exact original Option case, payload or immutable alias incidence."))
            let foreignResultErrors =
                let integerCalls = calls |> List.filter (fun call -> match call.Result with Some(BoundaryScalar.Integer _) -> true | _ -> false)
                if integerCalls.IsEmpty then [] else
                match NumericPublication.project graph with
                | Error failures -> failures
                | Ok numeric -> integerCalls |> List.choose (fun call ->
                    let declaration = imports |> List.tryFind (fun import -> import.Identity = call.Import) |> Option.map _.Binding
                    let accounts = numeric.ForeignResultUses |> List.filter (fun account -> account.Application.Call = call.Site)
                    let sourceHypotheses = domain.ResultHypotheses |> List.filter (fun hypothesis -> Some hypothesis.Declaration = declaration)
                    if not accounts.IsEmpty && (accounts |> List.forall (fun account ->
                        Some account.Application.Declaration = declaration &&
                        (match account.Application.Hypothesis, sourceHypotheses with
                         | Some hypothesis, [current] -> hypothesis = current
                         // The numeric owner has already validated complete ABI
                         // ingress and its retained width-embedding claim. This
                         // supplies no behavioral refinement or success fact.
                         | None, [] -> List.map fst account.Claims = [ForeignResultProofRole.AbiNarrowing]
                         | _ -> false))) then None
                    else Some(failure (Some call.Site) call.Participants "The integer result lacks its complete current conditional numeric account and declared behavioral hypothesis."))
            let projectedCallbackErrors =
                calls |> List.collect (fun call ->
                    call.Arguments |> List.choose (fun operand ->
                        match operand.Abi, PlatformResolution.valuePath graph operand.Actual with
                        | BoundaryScalar.Entry invocation, Some({ Kind = SemanticKind.FieldGet _; Id = projection }, _) ->
                            let current =
                                match closedEntries |> List.filter (fun entry ->
                                    entry.Invocation = invocation && entry.Transport.Contains operand.Actual) with
                                | [entry] ->
                                    Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.nativeProjection graph projection entry.Formation
                                | _ -> Error "The receiving projection lost its exact closed entry correspondence."
                            match current with
                            | Ok () -> None
                            | Error reason -> Some(failure (Some call.Site) call.Participants reason)
                        | _ -> None))
            let coverageMembership = coverages |> List.map (fun coverage -> coverage.Site, coverage.Ordinal, coverage.Operand) |> List.sort
            if (imports |> List.map _.Identity |> List.sort) <> domain.Imports || (entries |> List.map _.Formation |> List.sort) <> domain.Entries || (calls |> List.map _.Site |> List.sort) <> domain.Calls || expectedCoverage <> coverageMembership then
                stale "The boundary domain lost or duplicated an import, call or ordered coverage occurrence."
            else
                let callsById = calls |> List.map (fun call -> call.Site, call) |> Map.ofList
                let proofErrors, proofRows = coverages |> List.fold (fun (errors, rows) coverage ->
                    let call = callsById[coverage.Site]
                    let body = Ingredients.coverageBody coverage
                    let outcome = Ingredients.coverageOutcome coverage
                    let obligationValid =
                        graph.Nodes.TryFind coverage.Obligation |> Option.exists (fun node ->
                            Ingredients.ownedNode node &&
                            match node.Kind with
                            | SemanticKind.Obligation info -> info.Kind = "boundary-range-coverage" && Some info.Body = body
                            | _ -> false)
                    let inputValid =
                        if coverage.Ordinal = -1 then
                            call.Result |> Option.exists (fun scalar -> snd (PlatformResolution.scalarRange scalar) = coverage.Input)
                        else
                            let operand = call.Arguments[coverage.Ordinal]
                            let input = match operand.Abi with BoundaryScalar.Boolean -> Some ValueRange.boolean | _ -> domain.Premises[operand.Actual].Range
                            input = Some coverage.Input && snd (PlatformResolution.scalarRange operand.Abi) = coverage.Destination
                    let errors =
                        if obligationValid && inputValid && outcome = BoundaryProofOutcome.Proven then errors
                        else failure (Some coverage.Site) call.Participants "The boundary coverage obligation has no valid checked proof outcome for these exact range premises." :: errors
                    errors, rows @ Ingredients.coverageRows call coverage outcome) ([], [])
                let intrinsicProofErrors = domain.IntrinsicProofs |> List.choose (fun proof ->
                    let valid = graph.Nodes.TryFind proof.Obligation |> Option.exists (fun node ->
                        Ingredients.ownedNode node &&
                        (match node.Kind with
                         | SemanticKind.Obligation info -> info.Kind = "intrinsic-write-proof" && info.Body = proof.Body
                         | _ -> false))
                    if valid && Bytes.proofOutcome proof.Body = BoundaryProofOutcome.Proven then None else
                    Some(failure (Some proof.Site) proof.Participants "The intrinsic write obligation has no checked proof outcome for its exact settled premises."))
                let expected =
                    [Ingredients.row (EdgeRole.BoundaryDomain domain) 0 (Map.keys domain.Premises |> Seq.toList) domainRow.Target
                     { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = Map.keys domain.Premises |> Seq.toList; Target = domainRow.Target }]
                    @ (domain.Declarations |> List.map Declarations.row)
                    @ (resourceDeclarations |> List.map (fun row -> Ingredients.row (EdgeRole.BoundaryResourceDeclaration row) 0 (Set.toList row.Participants) row.Identity))
                    @ (writableDeclarations |> List.map (fun row -> Ingredients.row (EdgeRole.BoundaryWritableBufferDeclaration row) 0 (Set.toList row.Participants) row.Identity))
                    @ (resourceAccesses |> List.map (fun row -> Ingredients.row (EdgeRole.BoundaryResourceAccess row) 0 (Set.toList row.Participants) row.Site))
                    @ (imports |> List.map Ingredients.importRow)
                    @ (entries |> List.map (fun entry -> Ingredients.row (EdgeRole.BoundaryEntry entry) 0 (Set.toList entry.Participants) entry.Formation))
                    @ (callbackInvocations |> List.map (fun invocation -> Ingredients.row (EdgeRole.BoundaryCallbackInvocation invocation) 0 (Set.toList invocation.Participants) invocation.Identity))
                    @ (closedEntries |> List.map (fun entry -> Ingredients.row (EdgeRole.BoundaryClosedEntry entry) 0 (Set.toList entry.Participants) entry.Formation))
                    @ (calls |> List.collect (fun call -> Ingredients.callRow call :: Ingredients.operandRows call))
                    @ proofRows
                    @ (domain.ByteViews |> List.collect (fun view -> [Bytes.viewRow view; Bytes.storageRow view; Bytes.rewriteRow view]))
                    @ (domain.StringExtents |> List.map Bytes.extentRow)
                    @ (domain.StringComparisons |> List.map (fun (site,negated,sources) -> Clef.Compiler.Baker.Recipes.StringComparisonRecipes.row site negated sources))
                    @ (domain.StringLengthComparisons |> List.map (fun (site,negated,sources) -> Clef.Compiler.Baker.Recipes.StringComparisonRecipes.lengthRow site negated sources))
                    @ (domain.IntrinsicDeclarations |> List.map (fun (site, import) -> Bytes.abiRow site import))
                    @ (domain.IntrinsicImports |> List.map Bytes.importRow)
                    @ (domain.IntrinsicCalls |> List.collect Bytes.callRows)
                    @ (domain.IntrinsicProofs |> List.collect Bytes.proofRows)
                let resourceClaims =
                    calls |> List.collect(fun call->
                        match call.Resource with
                        | Some(BoundaryResourceUse.AcquireNullable account)->[account.Conversion;account.Cleanup]
                        | _->[]) |> Set.ofList
                let ownedTargets = Set.add domainRow.Target ((coverages |> List.map _.Obligation) @ (domain.IntrinsicProofs |> List.map _.Obligation) |> Set.ofList)
                let expected=expected @ (graph.Edges |> List.filter(fun edge->resourceClaims.Contains edge.Target && (edge.Role=EdgeRole.Constrains || edge.Role=EdgeRole.EnrichedWith)))
                let ownedTargets=Set.union ownedTargets resourceClaims
                let completeMembership = Set.union participants ownedTargets = (Map.keys graph.Nodes |> Set.ofSeq)
                let actual = graph.Edges |> List.filter (fun edge ->
                    edge.Class = EdgeClass.Boundary ||
                    (match edge.Role with
                     | EdgeRole.StringByteView _ | EdgeRole.StringExtent _ | EdgeRole.IntrinsicWriteAbi _ | EdgeRole.StringComparisonConstruction _ | EdgeRole.StringLengthComparison _ -> true
                     | EdgeRole.StringByteStorage _ -> domain.ByteViews |> List.exists (fun view -> view.Site = edge.Target)
                     | _ -> false) ||
                    (edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.EnrichedWith &&
                     domain.ByteViews |> List.exists (fun view -> edge.Target = view.Site && edge.Sources = [view.Source])) ||
                    (ownedTargets.Contains edge.Target && (edge.Role = EdgeRole.Constrains || edge.Role = EdgeRole.EnrichedWith)))
                // A multiset check preserves repetitions. Set equality would erase
                // duplicated occurrences and accidentally accept partial evidence.
                let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
                let rec subtract (remaining: Hyperedge list) = function
                    | [] -> remaining.IsEmpty
                    | expected :: rest ->
                        let rec remove prefix = function
                            | [] -> None
                            | edge :: tail when key edge = key expected -> Some (List.rev prefix @ tail)
                            | edge :: tail -> remove (edge :: prefix) tail
                        match remove [] remaining with Some remaining -> subtract remaining rest | None -> false
                let proofErrors = resourceAccessErrors @ resourceErrors @ projectedCallbackErrors @ foreignResultErrors @ intrinsicProofErrors @ proofErrors
                let expectedIntrinsicProofs = domain.IntrinsicCalls |> List.collect (fun call -> [-1;0;1;2] |> List.map (fun ordinal -> call.Site, ordinal)) |> List.sort
                let actualIntrinsicProofs = domain.IntrinsicProofs |> List.map (fun proof -> proof.Site, proof.Ordinal) |> List.sort
                let callbackMembership =
                    (callbackInvocations |> List.map _.Identity |> List.sort) = List.sort domain.CallbackInvocations &&
                    (closedEntries |> List.map _.Formation |> List.sort) = List.sort domain.ClosedEntries
                if not proofErrors.IsEmpty then Error (List.rev proofErrors)
                elif (writableDeclarations |> List.map _.Identity |> List.sort) <> List.sort domain.WritableBufferDeclarations then
                    stale "The source writable buffer declaration account was withdrawn or duplicated."
                elif (resourceDeclarations |> List.map _.Identity |> List.sort) <> List.sort domain.ResourceDeclarations then
                    stale "The source resource declaration account was withdrawn or duplicated."
                elif not resourceFlowCurrent || not resourceEvidenceCurrent then stale "The complete current resource evaluation relation, original root or scoped source premise incidence changed."
                elif (resourceAccesses |> List.map _.Site |> List.sort)<>List.sort domain.ResourceAccesses then stale "The resource read or immutable alias account was withdrawn or duplicated."
                elif not callbackMembership then stale "The closed native callback or receiving invocation account was withdrawn or duplicated."
                elif expectedIntrinsicProofs <> actualIntrinsicProofs then stale "The intrinsic boundary lost or duplicated an ordered proof occurrence."
                elif not completeMembership || not (subtract actual expected) then stale "The ordered boundary relation, adaptation, rewrite record or proof outcome is missing, duplicated or inconsistent."
                else
                    let imports = imports |> List.map (fun import -> import.Identity, import) |> Map.ofList
                    let byScope = imports.Values |> Seq.groupBy _.Scope |> Seq.map (fun (scope, imports) -> scope, imports |> Seq.map _.Identity |> Seq.sort |> Seq.toList) |> Map.ofSeq
                    Ok { ResourceEvidence = domain.ResourceEvidence
                         WritableBufferDeclarations = writableDeclarations |> List.map(fun row -> row.Identity,row) |> Map.ofList
                         ResourceDeclarations = resourceDeclarations |> List.map (fun row -> row.Identity,row) |> Map.ofList
                         ResourceAccesses = resourceAccesses |> List.map(fun row->row.Site,row) |> Map.ofList
                         Imports = imports; Loading = domain.Loading; Entries = entries |> List.map (fun entry -> entry.Formation, entry) |> Map.ofList
                         Calls = callsById; ByScope = byScope; ResultHypotheses = domain.ResultHypotheses
                         CallbackInvocations = callbackInvocations |> List.map (fun invocation -> invocation.Identity, invocation) |> Map.ofList
                         ClosedEntries = closedEntries |> List.map (fun entry -> entry.Formation, entry) |> Map.ofList
                         ByteViews = domain.ByteViews |> List.map (fun view -> view.Site, view) |> Map.ofList
                         StringExtents = domain.StringExtents |> List.map (fun extent -> extent.Site, extent) |> Map.ofList
                         IntrinsicWriteImports = domain.IntrinsicImports |> List.map (fun import -> import.Identity, import) |> Map.ofList
                         IntrinsicWrites = domain.IntrinsicCalls |> List.map (fun call -> call.Site, call) |> Map.ofList
                         IntrinsicWriteProofs = domain.IntrinsicProofs |> List.groupBy _.Site |> Map.ofList
                         DeclarationLeaves = domain.DeclarationLeaves; DeclarationOnly = domain.DeclarationOnly; Links = domain.Links }
    | _ ->
        let site = graph.Nodes |> Map.toSeq |> Seq.tryHead |> Option.map fst
        Error [failure site (site |> Option.toList |> Set.ofList) "Exactly one Baker boundary domain is required before publication."]

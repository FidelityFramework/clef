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
        let anchorValid = graph.Nodes.TryFind domainRow.Target |> Option.exists (fun node ->
            Ingredients.ownedNode node && match node.Kind with SemanticKind.Literal NativeLiteral.Unit -> true | _ -> false)
        if not anchorValid || domain.Premises <> Ingredients.premises graph || domain.Platform <> Ingredients.platformPremise graph.Platform || domain.Meets <> graph.Codata.Value.Meets || domain.StringStorage <> Bytes.storagePremise graph then
            stale "A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed; Baker must settle the new source graph."
        elif not domain.Failures.IsEmpty then
            Error (domain.Failures |> List.map (fun (site, participants, reason) -> failure (Some site) participants reason))
        elif not borrowMembership then
            stale "The source-published snapshot, copy or allocation dependency account is incomplete."
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
            let imports = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryImport import -> Some import | _ -> None)
            let entries = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryEntry entry -> Some entry | _ -> None)
            let callbackInvocations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCallbackInvocation invocation -> Some invocation | _ -> None)
            let closedEntries = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryClosedEntry entry -> Some entry | _ -> None)
            let calls = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCall call -> Some call | _ -> None)
            let coverages = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCoverage coverage -> Some coverage | _ -> None)
            let expectedCoverage = calls |> List.collect (fun call ->
                (call.Arguments |> List.mapi (fun ordinal operand -> match operand.Abi with BoundaryScalar.Entry _ -> None | _ -> Some(call.Site, ordinal, operand.Actual)) |> List.choose id) @
                (call.Result |> Option.toList |> List.filter (function BoundaryScalar.Integer _ -> false | _ -> true) |> List.map (fun _ -> call.Site, -1, call.Site))) |> List.sort
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
                let ownedTargets = Set.add domainRow.Target ((coverages |> List.map _.Obligation) @ (domain.IntrinsicProofs |> List.map _.Obligation) |> Set.ofList)
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
                let proofErrors = projectedCallbackErrors @ foreignResultErrors @ intrinsicProofErrors @ proofErrors
                let expectedIntrinsicProofs = domain.IntrinsicCalls |> List.collect (fun call -> [-1;0;1;2] |> List.map (fun ordinal -> call.Site, ordinal)) |> List.sort
                let actualIntrinsicProofs = domain.IntrinsicProofs |> List.map (fun proof -> proof.Site, proof.Ordinal) |> List.sort
                let callbackMembership =
                    (callbackInvocations |> List.map _.Identity |> List.sort) = List.sort domain.CallbackInvocations &&
                    (closedEntries |> List.map _.Formation |> List.sort) = List.sort domain.ClosedEntries
                if not proofErrors.IsEmpty then Error (List.rev proofErrors)
                elif not callbackMembership then stale "The closed native callback or receiving invocation account was withdrawn or duplicated."
                elif expectedIntrinsicProofs <> actualIntrinsicProofs then stale "The intrinsic boundary lost or duplicated an ordered proof occurrence."
                elif not completeMembership || not (subtract actual expected) then stale "The ordered boundary relation, adaptation, rewrite record or proof outcome is missing, duplicated or inconsistent."
                else
                    let imports = imports |> List.map (fun import -> import.Identity, import) |> Map.ofList
                    let byScope = imports.Values |> Seq.groupBy _.Scope |> Seq.map (fun (scope, imports) -> scope, imports |> Seq.map _.Identity |> Seq.sort |> Seq.toList) |> Map.ofSeq
                    Ok { Imports = imports; Loading = domain.Loading; Entries = entries |> List.map (fun entry -> entry.Formation, entry) |> Map.ofList
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

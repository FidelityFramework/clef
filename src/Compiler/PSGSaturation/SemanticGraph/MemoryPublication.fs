// SPDX-License-Identifier: MIT
/// Memory publication validates source-owned operations; it does not elaborate
/// guards, choose carriers, classify residence or repair an absent place.
module Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.NativeTypedTree.NativeTypes
module Memory = Clef.Compiler.Baker.Ingredients.MemoryValues
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries

let private projectWith (graph: SemanticGraph) excluded : Result<MemoryWitnessProjection, WitnessProjectionFailure list> =
    let reject site participants reason =
        Error
            [
                {
                    Kind = WitnessProjectionFailureKind.Settlement
                    Occurrence = site
                    Participants = participants
                    Reason = "MemoryPublication: " + reason
                }
            ]
    let domains = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.MemoryDomain domain -> Some(edge.Target, domain) | _ -> None)
    match domains with
    | [anchor, domain] ->
        let participants = Map.keys domain.Premises |> Set.ofSeq
        if domain.Premises <> Memory.premises graph || domain.Platform <> Boundary.platformPremise graph.Platform ||
           domain.Meets <> graph.Codata.Value.Meets || domain.Guards <> Memory.guards graph || domain.Requirements <> Memory.requirements graph ||
           domain.StringRelations <> Memory.stringRelations graph ||
           domain.AllocationConstructions <> Memory.allocationConstructions graph ||
           domain.CopyConstructions <> Memory.copyConstructions graph then
            reject (Some anchor) participants "The exact memory source, guard, meet or declaration premises changed; source settlement is required."
        elif not domain.Unresolved.IsEmpty then
            Error(
                domain.Unresolved
                |> Map.toList
                |> List.map (fun (site, reason) ->
                    {
                        Kind = WitnessProjectionFailureKind.Settlement
                        Occurrence = Some site
                        Participants = Set.singleton site
                        Reason = "MemoryPublication: " + reason
                    })
            )
        elif domain.StringRelations |> List.exists(fun row ->
            match row.Premise with
            | MemoryStringPremise.Checked {Returned=Some life} ->
                (graph.Platform |> Option.bind _.ProjectMemoryPolicy) <>
                    Some(life.Policy.ProjectPath,life.Policy.SourceVersion,life.Policy.Model,true)
            | _ -> false) then
            reject (Some anchor) participants "The returned checked project allocation permission or captured policy changed; source settlement is required."
        elif domain.StringRelations |> List.exists(fun row ->
            match row.Premise with
            | MemoryStringPremise.Checked {Returned=Some life} ->
                not(graph.Edges |> List.exists(fun edge ->
                    edge.Target=life.Capacity && edge.Role=EdgeRole.Constrains &&
                    ([life.Application;life.Platform;life.Space;life.SomeBackingRetirement;life.SomeCarrierRetirement;life.NoneCarrierRetirement]
                     |> List.forall(fun source->List.contains source edge.Sources))))
            | _ -> false) then
            reject (Some anchor) participants "The returned checked capacity citizen lost its exact owning source support; source settlement is required."
        elif domain.Operations |> List.exists(fun (_,operation) ->
            let construction=match operation with MemoryWitnessOperation.Utf8Validation row -> Some row.Construction | MemoryWitnessOperation.SnapshotRetirement row -> Some row.Construction | _ -> None
            construction |> Option.exists(fun construction ->
                match Map.tryFind construction.Text (Map.ofList domain.Operations) with
                | Some(MemoryWitnessOperation.StringView view) when view.Checked=Some construction -> false
                | _ -> true)) then
            reject (Some anchor) participants "The checked memory support lacks its exact current source string view."
        elif (domain.Operations |> List.map fst |> List.sort) <> Set.toList domain.Required then
            reject (Some anchor) participants "A required source memory operation is absent or duplicated."
        elif domain.Operations |> List.exists(fun (_,operation) ->
            let storage =
                match operation with
                | MemoryWitnessOperation.Utf8Validation row -> Some row.Storage
                | MemoryWitnessOperation.SnapshotRetirement row -> Some row.Storage
                | _ -> None
            storage |> Option.exists(fun storage ->
                let site,expected =
                    match storage with
                    | MemoryCheckedSnapshotStorage.Allocated row -> row.Site,MemoryWitnessOperation.ArrayAllocation row
                    | MemoryCheckedSnapshotStorage.Empty row -> row.Site,MemoryWitnessOperation.EmptySnapshot row
                not(domain.Required.Contains site) || Map.tryFind site (Map.ofList domain.Operations) <> Some expected)) then
            reject (Some anchor) participants "The checked snapshot lost its exact current allocated or empty storage operation."
        elif (domain.AllocationConstructions |> List.map _.Site |> List.filter(Memory.executable graph excluded) |> List.sort) <>
             (domain.Operations |> List.choose(fun (_,operation) ->
                match operation with
                | MemoryWitnessOperation.ArrayAllocation row -> Some row.Site
                | MemoryWitnessOperation.EmptySnapshot row -> Some row.Site
                | _ -> None) |> List.sort) then
            reject (Some anchor) participants "A required source array producer has no unique allocated or empty storage receipt."
        elif domain.Operations |> List.exists (fun (_,operation) ->
            match operation with
            | MemoryWitnessOperation.EmptySnapshot empty ->
                match domain.AllocationConstructions |> List.filter(fun row -> row.Site=empty.Site) with
                | [construction] ->
                    construction.Owner<>empty.Snapshot || construction.Count.Reference<>empty.Count ||
                    not(domain.Operations |> List.exists(fun (_,operation) ->
                        match operation with
                        | MemoryWitnessOperation.Utf8Validation validation ->
                            validation.Storage=MemoryCheckedSnapshotStorage.Empty empty &&
                            validation.Construction.Owner=empty.Owner && validation.Construction.Snapshot=empty.Snapshot &&
                            validation.Construction.Returned.IsSome && validation.Copy.CountOperand.Reference=empty.Count &&
                            validation.Copy.CountCarrier.Range=ValueRange.point 0I
                        | _ -> false))
                | _ -> true
            | MemoryWitnessOperation.ArrayAllocation allocation ->
                let construction=allocation.Construction
                (domain.AllocationConstructions |> List.filter (fun value -> value.Site=allocation.Site)) <> [construction] ||
                construction.Site<>allocation.Site || construction.Count.Reference<>allocation.Count ||
                allocation.CountCarrier.Site<>allocation.Count ||
                construction.Guard.Requirement<>allocation.Requirement.Site ||
                construction.Guard.Predicate<>allocation.Requirement.Condition ||
                construction.Guard.Frontier<>allocation.Requirement.Frontier ||
                construction.Guard.Continuation<>allocation.Requirement.Continuation
            | _ -> false) then
            reject (Some anchor) participants "The allocation witness lost its exact validated construction, count or initialization account."
        elif (domain.CopyConstructions |> List.map _.Site |> List.filter(Memory.executable graph excluded) |> List.sort) <> (domain.ArrayCopies |> List.map _.Site |> List.sort) then
            reject (Some anchor) participants "A required source array-copy construction has no unique validated copy receipt."
        else
            let proofTargets = domain.Proofs |> List.map _.Obligation |> Set.ofList
            let proofsValid = domain.Proofs |> List.forall (fun proof ->
                proof.Proven && (graph.Nodes.TryFind proof.Obligation |> Option.exists (fun node ->
                    Memory.owned node && (match node.Kind with SemanticKind.Obligation info -> info.Body = proof.Body | _ -> false))))
            let expected = Memory.domainRow anchor domain :: Memory.domainRewrite anchor domain :: (domain.Operations |> List.map (Memory.operationRow (Map.ofList domain.Operations))) @ (domain.Proofs |> List.collect Memory.proofRows) @ (domain.ArrayCopies |> List.map Memory.copyRow)
                           @ (domain.AllocationConstructions |> List.map Memory.allocationConstructionRow) @ (domain.CopyConstructions |> List.map Memory.copyConstructionRow)
            let actual = graph.Edges |> List.filter (fun edge ->
                match edge.Role with
                | EdgeRole.MemoryDomain _ | EdgeRole.MemoryOperation _ | EdgeRole.MemoryProof _ | EdgeRole.MemoryArrayCopy _
                | EdgeRole.ArrayAllocationConstruction _ | EdgeRole.ArrayCopyConstruction _ -> true
                | EdgeRole.EnrichedWith | EdgeRole.Constrains when edge.Target = anchor || proofTargets.Contains edge.Target -> true
                | _ -> false)
            let membership = graph.Nodes |> Map.toSeq |> Seq.filter (snd >> Memory.owned) |> Seq.map fst |> Set.ofSeq
            if not proofsValid || membership <> Set.add anchor proofTargets || not (Clef.Compiler.Baker.Ingredients.NumericValues.sameRows expected actual) then
                reject (Some anchor) participants "The memory operation, complete participants or source rewrite record is inconsistent."
            else Ok { Operations = Map.ofList domain.Operations; ArrayCopies=domain.ArrayCopies |> List.map (fun copy -> copy.Site,copy) |> Map.ofList
                      Required = domain.Required; Unresolved = domain.Unresolved }
    | _ -> reject None Set.empty "Exactly one source MemorySettlement domain is required before witnessing."

let project graph =
    Memory.excludedValidated graph |> Result.bind(projectWith graph)

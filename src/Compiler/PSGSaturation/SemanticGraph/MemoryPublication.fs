// SPDX-License-Identifier: MIT
/// Memory publication validates source-owned operations; it does not elaborate
/// guards, choose carriers, classify residence or repair an absent place.
module Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Memory = Clef.Compiler.Baker.Ingredients.MemoryValues
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries

let private projectWith (graph: SemanticGraph) excluded : Result<MemoryWitnessProjection, WitnessProjectionFailure list> =
    let reject site participants reason = Error [{ Occurrence = site; Participants = participants; Reason = "MemoryPublication: " + reason }]
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
            Error(domain.Unresolved |> Map.toList |> List.map (fun (site, reason) -> { Occurrence = Some site; Participants = Set.singleton site; Reason = "MemoryPublication: " + reason }))
        elif (domain.Operations |> List.map fst |> List.sort) <> Set.toList domain.Required then
            reject (Some anchor) participants "A required source memory operation is absent or duplicated."
        elif (domain.CopyConstructions |> List.map _.Site |> List.filter(Memory.executable graph excluded) |> List.sort) <> (domain.ArrayCopies |> List.map _.Site |> List.sort) then
            reject (Some anchor) participants "A required source array-copy construction has no unique validated copy receipt."
        else
            let proofTargets = domain.Proofs |> List.map _.Obligation |> Set.ofList
            let proofsValid = domain.Proofs |> List.forall (fun proof ->
                proof.Proven && (graph.Nodes.TryFind proof.Obligation |> Option.exists (fun node ->
                    Memory.owned node && (match node.Kind with SemanticKind.Obligation info -> info.Body = proof.Body | _ -> false))))
            let expected = Memory.domainRow anchor domain :: Memory.domainRewrite anchor domain :: (domain.Operations |> List.map Memory.operationRow) @ (domain.Proofs |> List.collect Memory.proofRows) @ (domain.ArrayCopies |> List.map Memory.copyRow)
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

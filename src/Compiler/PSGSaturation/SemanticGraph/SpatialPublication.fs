// SPDX-License-Identifier: MIT
/// Passive validation of the spatial owner’s complete source construction.
module Clef.Compiler.PSGSaturation.SemanticGraph.SpatialPublication

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Spatial = Clef.Compiler.Baker.Ingredients.SpatialValues
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries

let private hardwareProofsAgree (proofs: SpatialProof list) (plan: HardwareModuleWitness) =
    let fields =
        match plan.StateRepresentation with
        | ValueRepresentation.Record(fields, _) -> fields |> List.map (fun (name, representation) ->
            match representation with ValueRepresentation.Scalar slot -> Some(name,slot) | _ -> None)
        | _ -> [None]
    let declared = plan.ResetFields |> List.map (fun field -> Some(field.Name,field.Slot))
    let bodies = plan.ResetFields |> List.map (fun field ->
        match field.Range, field.Capacity with
        | ValueRange.Bounded(lower,upper), ValueRange.Bounded(minimum,maximum) ->
            Some [ObligationBody.IntegerRepresentationCoverage(field.Reset,field.Reset,lower,upper)
                  ObligationBody.IntegerRepresentationCoverage(lower,upper,minimum,maximum)]
        | _ -> None)
    let expected = bodies |> List.choose id |> List.concat
    let actual = plan.Obligations |> List.map (fun obligation ->
        match proofs |> List.filter (fun proof -> proof.Site=plan.Site && proof.Obligation=obligation) with
        | [proof] when Set.isSubset plan.Participants proof.Participants -> Some proof.Body
        | _ -> None)
    fields=declared && not(List.contains None fields) && not(List.contains None bodies) &&
    actual=(expected |> List.map Some) &&
    (plan.ResetFields |> List.forall (fun field -> plan.Participants.Contains field.Literal))

let project (graph: SemanticGraph) : Result<SpatialModuleProjection, WitnessProjectionFailure list> =
    let reject site participants reason = Error [{ Occurrence=site; Participants=participants; Reason="SpatialPublication: " + reason }]
    let domains = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.SpatialModuleDomain domain -> Some(edge.Target,domain) | _ -> None)
    match domains with
    | [anchor,domain] ->
        let participants = Map.keys domain.Premises |> Set.ofSeq
        match NumericPublication.project graph with
        | Error failures -> Error failures
        | Ok numeric ->
        if domain.Premises <> Spatial.premises graph || domain.SourceFiles <> Spatial.sourceFiles graph || domain.Platform <> Boundary.platformPremise graph.Platform ||
           domain.Meets <> graph.Codata.Value.Meets || domain.Pins <> graph.Codata.Value.Pins || domain.FieldRanges <> graph.FieldRanges.Value ||
           domain.Representations <> numeric.OccurrenceRepresentations || domain.Carriers <> numeric.Values || domain.NumericOperations <> numeric.Operations then
            reject (Some anchor) participants "The exact spatial declaration, numeric construction, pin or source premises changed; source settlement is required."
        elif not domain.Unresolved.IsEmpty then
            Error(domain.Unresolved |> Map.toList |> List.map (fun (site,reason) -> { Occurrence=Some site; Participants=Set.singleton site; Reason="SpatialPublication: " + reason }))
        elif ((domain.Hardware |> List.map _.Site) @ (domain.Kernels |> List.map _.Site) |> List.sort) <> Set.toList domain.Required then
            reject (Some anchor) participants "A required source spatial module is absent or duplicated."
        else
            let proofTargets = domain.Proofs |> List.map _.Obligation |> Set.ofList
            let proofsValid = domain.Proofs |> List.forall (fun proof ->
                proof.Proven && (graph.Nodes.TryFind proof.Obligation |> Option.exists (fun node ->
                    Spatial.owned node && (match node.Kind with SemanticKind.Obligation info -> info.Body=proof.Body | _ -> false))))
            let expected = Spatial.domainRow anchor domain :: Spatial.domainRewrite anchor domain ::
                           (domain.Hardware |> List.map Spatial.hardwareRow) @ (domain.Kernels |> List.map Spatial.kernelRow) @ (domain.Proofs |> List.collect Spatial.proofRows)
            let actual = graph.Edges |> List.filter (fun edge ->
                match edge.Role with
                | EdgeRole.SpatialModuleDomain _ | EdgeRole.HardwareModule _ | EdgeRole.KernelModule _ | EdgeRole.SpatialProof _ -> true
                | EdgeRole.EnrichedWith | EdgeRole.Constrains when edge.Target=anchor || proofTargets.Contains edge.Target -> true
                | _ -> false)
            let membership = graph.Nodes |> Map.toSeq |> Seq.filter (snd >> Spatial.owned) |> Seq.map fst |> Set.ofSeq
            let declarations = (domain.Hardware |> List.map (fun plan -> plan.Site,plan.Scope,plan.MetadataOnly,plan.Participants,plan.Obligations)) @
                               (domain.Kernels |> List.map (fun plan -> plan.Site,plan.Scope,plan.MetadataOnly,plan.Participants,plan.Obligations))
            let validPlans = declarations |> List.forall (fun (site,scope,metadata,complete,obligations) ->
                complete.Contains site && complete.Contains scope && not(metadata.Contains site) && Set.isSubset metadata complete &&
                Set.isSubset complete (Set.union participants proofTargets) &&
                List.sort obligations = (domain.Proofs |> List.filter (fun proof -> proof.Site=site) |> List.map _.Obligation |> List.sort))
            let validKernels = domain.Kernels |> List.forall (fun plan ->
                let ownProofs = domain.Proofs |> List.filter (fun proof -> proof.Site=plan.Site)
                let carriersValid = plan.Steps |> List.forall (function
                    | KernelScalarStep.Parameter(site,ordinal,carrier) ->
                        numeric.Values.TryFind site=Some carrier && (plan.Parameters |> List.tryItem ordinal |> Option.map snd)=Some site
                    | KernelScalarStep.Literal(site,value,carrier) ->
                        let expected =
                            match value with
                            | KernelScalarLiteral.Integer value -> value
                            | KernelScalarLiteral.Boolean value -> if value then 1I else 0I
                            | KernelScalarLiteral.Character value -> bigint(int value)
                        numeric.Values.TryFind site=Some carrier && (domain.Premises.TryFind site |> Option.exists (fun premise -> premise.Shape.Numbers=[expected]))
                    | KernelScalarStep.Alias(site,source,carrier,adaptation) ->
                        let meets=domain.Meets.TryFind site |> Option.defaultValue [] |> List.filter (fun meet -> meet.Consumer=site && meet.Operand=source)
                        numeric.Values.TryFind site=Some carrier &&
                        (match adaptation with Some meet -> meets=[meet] | None -> meets.IsEmpty && (numeric.Values.TryFind source |> Option.exists (fun actual -> actual.Slot=carrier.Slot)))
                    | KernelScalarStep.Operation operation -> numeric.Operations.TryFind operation.Site=Some operation)
                let outputProof =
                    match numeric.Values.TryFind plan.Result with
                    | Some {Range=ValueRange.Bounded(lower,upper)} ->
                        match plan.Ingress.Output.Range with
                        | ValueRange.Bounded(minimum,maximum) -> Some(ObligationBody.IntegerRepresentationCoverage(lower,upper,minimum,maximum))
                        | _ -> None
                    | _ -> None
                Clef.Compiler.Baker.Recipes.KernelDeclarations.read graph plan.Site=Ok plan.Ingress &&
                plan.Scope=plan.Ingress.Scope && plan.ComputeBinding=plan.Ingress.ComputeBinding && plan.Implementation=plan.Ingress.Implementation &&
                plan.Parameters=plan.Ingress.Parameters && plan.Result=plan.Ingress.Result && plan.Target.Declaration=plan.Ingress.Target &&
                outputProof.IsSome && (ownProofs |> List.map _.Body)=([Spatial.kernelProofBody plan] @ Option.toList outputProof) && carriersValid)
            let validHardware = domain.Hardware |> List.forall (hardwareProofsAgree domain.Proofs)
            if not proofsValid || not validPlans || not validKernels || not validHardware || membership <> Set.add anchor proofTargets || not(Clef.Compiler.Baker.Ingredients.NumericValues.sameRows expected actual) then
                reject (Some anchor) participants "The complete spatial plan, participants, proof census or source rewrite record is inconsistent."
            else
                Ok { Hardware=domain.Hardware |> List.map (fun plan -> plan.Site,plan) |> Map.ofList
                     Kernels=domain.Kernels |> List.map (fun plan -> plan.Site,plan) |> Map.ofList
                     Required=domain.Required
                     CodeRoots=domain.Hardware |> List.map _.StepBinding |> Set.ofList
                     MetadataOnly=declarations |> List.fold (fun ids (_,_,metadata,_,_) -> Set.union ids metadata) Set.empty
                     ByScope=declarations |> List.groupBy (fun (_,scope,_,_,_) -> scope) |> List.map (fun (scope,plans) -> scope,plans |> List.map (fun (site,_,_,_,_) -> site)) |> Map.ofList }
    | _ -> reject None Set.empty "Exactly one source SpatialSettlement domain is required before witnessing."

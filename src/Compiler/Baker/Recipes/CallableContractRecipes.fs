// SPDX-License-Identifier: MIT
/// Author ordinary receiving contracts from admitted physical boundaries.
/// Relation identities belong to these source rows, not invented runtime nodes.
module Clef.Compiler.Baker.Recipes.CallableContractRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Contract = Clef.Compiler.Baker.Ingredients.CallableContracts

let settle (graph: SemanticGraph) (layouts: Map<NodeId, EnvironmentLayout>)
           (previous: Map<NodeId, CallableContract>) (carriers: Map<NodeId, CallableCarrier>) =
    // The source owner is checked once for this forward fold. No consumer can
    // mint support from a stale domain or a convenient signature alone.
    let domain = Contract.currentNumericOwner graph
    let contracts =
        carriers.Values
        |> Seq.groupBy (fun carrier -> carrier.Kind, carrier.Implementation)
        |> Seq.choose (fun (_, occurrences) ->
            let carriers = List.ofSeq occurrences
            let signatures = carriers |> List.map (Contract.signature graph layouts) |> List.distinct
            match signatures, domain with
            | [Some signature], Some owner ->
                let first = carriers.Head
                let identity = Contract.tryIdentity graph layouts previous first |> Option.defaultWith NodeId.fresh
                let representationPremises, sourcePremises = Contract.conventionEvidence graph signature.Convention owner first
                Some(identity, {
                    Identity = identity; Kind = signature.Kind
                    Convention = signature.Convention
                    ParameterTypes = signature.Parameters; ResultType = signature.Result
                    EnvironmentBytes = signature.EnvironmentBytes; OmittedParameters = signature.Omitted
                    ParameterRepresentations = signature.ParameterRepresentations
                    ResultRepresentation = signature.ResultRepresentation
                    SourcePremises = sourcePremises
                    Participants = Contract.conventionParticipants signature.Convention identity first representationPremises
                })
            // A polymorphic implementation with incompatible actual conventions
            // needs source specialization. Choosing its first instance is not a
            // receiving-family proof. Native entries require the explicit
            // compiler-owned portable convention supplied by the ingredient.
            | _ -> None)
        |> Map.ofSeq
    contracts, carriers |> Map.map (fun _ carrier -> Contract.assign graph layouts contracts carrier)

/// An aggregate placement step reports the exact occurrence representations it
/// changed. Renew only callable families whose parameter/result sites intersect
/// that delta; all other contract and carrier rows retain their current values.
let renewForSites (graph: SemanticGraph) layouts (sites: Set<NodeId>)
                  (contracts: Map<NodeId, CallableContract>) (carriers: Map<NodeId, CallableCarrier>) =
    let implementations =
        carriers.Values |> Seq.filter (fun carrier ->
            sites.Contains carrier.Result || (carrier.Parameters |> List.exists (fun (_, _, formal) -> sites.Contains formal)))
        |> Seq.map _.Implementation |> Set.ofSeq
    if implementations.IsEmpty then contracts, carriers else
    let affected = carriers |> Map.filter (fun _ carrier -> implementations.Contains carrier.Implementation)
    let replacements, current = settle graph layouts contracts affected
    let retained = contracts |> Map.filter (fun _ contract ->
        contract.Participants |> List.exists (fun participant ->
            participant.Role = ParticipantRole.CallableImplementation && implementations.Contains participant.Node) |> not)
    let renewed = replacements |> Map.fold (fun table identity contract ->
        let row = contracts.TryFind identity |> Option.filter ((=) contract) |> Option.defaultValue contract
        table |> Map.add identity row) retained
    let nextCarriers = current |> Map.fold (fun table occurrence carrier ->
        if (table |> Map.tryFind occurrence) = Some carrier then table else table |> Map.add occurrence carrier) carriers
    (if renewed = contracts then contracts else renewed), nextCarriers

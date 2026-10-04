// SPDX-License-Identifier: MIT
/// Author ordinary receiving contracts from admitted physical boundaries.
/// Relation identities belong to these source rows, not invented runtime nodes.
module Clef.Compiler.Baker.Recipes.CallableContractRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Contract = Clef.Compiler.Baker.Ingredients.CallableContracts

let settle (graph: SemanticGraph) (layouts: Map<NodeId, EnvironmentLayout>)
           (previous: Map<NodeId, CallableContract>) (carriers: Map<NodeId, CallableCarrier>) =
    let contracts =
        carriers.Values
        |> Seq.groupBy _.Implementation
        |> Seq.choose (fun (implementation, occurrences) ->
            let carriers = List.ofSeq occurrences
            let signatures = carriers |> List.map (Contract.signature graph layouts) |> List.distinct
            match signatures with
            | [Some signature] ->
                let first = carriers.Head
                let identity = Contract.tryIdentity graph layouts previous first |> Option.defaultWith NodeId.fresh
                let participant role ordinal node = { Node = node; Role = role; Ordinal = ordinal; Group = identity }
                let sites = first.Result :: (first.Parameters |> List.map (fun (_, _, formal) -> formal)) |> Set.ofList
                let representationPremises =
                    graph.Edges |> List.collect (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericDomain domain ->
                            domain.Values |> List.filter (fun value -> sites.Contains value.Site)
                            |> List.collect (fun value -> Set.toList value.Participants @ value.Obligations)
                        | _ -> []) |> List.distinct
                Some(identity, {
                    Identity = identity; Kind = CallableKind.OrdinaryFlatClosure
                    ParameterTypes = signature.Parameters; ResultType = signature.Result
                    EnvironmentBytes = signature.EnvironmentBytes; OmittedParameters = signature.Omitted
                    ParameterRepresentations = signature.ParameterRepresentations
                    ResultRepresentation = signature.ResultRepresentation
                    Participants =
                        [ yield participant ParticipantRole.CallableContract 0 identity
                          yield participant ParticipantRole.CallableImplementation 0 implementation
                          yield participant ParticipantRole.CalleeBody 0 first.Result
                          for ordinal, (_, _, formal) in List.indexed first.Parameters do
                              yield participant ParticipantRole.CalleeParameter ordinal formal
                          for ordinal, premise in List.indexed representationPremises do
                              yield participant ParticipantRole.Source ordinal premise ]
                })
            // A polymorphic implementation with incompatible actual conventions
            // needs source specialization. Choosing its first instance is not a
            // receiving-family proof. Native entries never enter this recipe.
            | _ -> None)
        |> Map.ofSeq
    contracts, carriers |> Map.map (fun _ carrier -> Contract.assign graph layouts contracts carrier)

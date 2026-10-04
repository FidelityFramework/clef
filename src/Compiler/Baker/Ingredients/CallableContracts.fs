// SPDX-License-Identifier: MIT
/// Read an ordinary callable's actual convention. Native entries require their
/// boundary recipe; a source arrow type never supplies that contract.
module Clef.Compiler.Baker.Ingredients.CallableContracts

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Identity = Clef.Compiler.NativeTypedTree.TypeIdentities

type Signature = {
    Parameters: TypeIdentity list
    Result: TypeIdentity
    EnvironmentBytes: int option
    Omitted: int list
    ParameterRepresentations: (int * ValueRepresentation) list
    ResultRepresentation: ValueRepresentation
}

let signature (graph: SemanticGraph) (layouts: Map<NodeId, EnvironmentLayout>)
              (carrier: CallableCarrier) =
    let environment =
        match carrier.Environment with
        | None -> Some None
        | Some environment ->
            layouts.TryFind environment.Owner
            |> Option.filter (fun layout ->
                layout.Implementation = carrier.Implementation && layout.Formal = environment.Formal)
            |> Option.map (fun layout -> Some layout.Bytes)
    let domain =
        graph.Edges |> List.choose (fun edge ->
            match edge.Role with EdgeRole.NumericDomain domain -> Some domain | _ -> None)
        |> function [domain] -> Some domain | _ -> None
    let representations = domain |> Option.bind (fun domain ->
        let selected =
            carrier.Parameters |> List.indexed
            |> List.filter (fun (_, (_, _, formal)) -> not (carrier.OmittedParameters.Contains formal))
            |> List.map (fun (ordinal, (_, _, formal)) ->
                domain.OccurrenceRepresentations.TryFind formal
                |> Option.bind Result.toOption |> Option.map (fun representation -> ordinal, representation))
        if List.exists Option.isNone selected then None else
        domain.OccurrenceRepresentations.TryFind carrier.Result
        |> Option.bind Result.toOption |> Option.map (fun result -> List.choose id selected, result))
    match carrier.Kind, graph.Nodes.TryFind carrier.Result, environment, representations with
    | CallableKind.OrdinaryFlatClosure, Some result, Some bytes, Some(parameters, resultRepresentation) ->
        Some {
            Parameters = carrier.Parameters |> List.map (fun (_, ty, _) -> Identity.ofType ty)
            Result = Identity.ofType result.Type
            EnvironmentBytes = bytes
            Omitted = carrier.Parameters |> List.indexed |> List.choose (fun (ordinal, (_, _, formal)) ->
                if carrier.OmittedParameters.Contains formal then Some ordinal else None)
            ParameterRepresentations = parameters
            ResultRepresentation = resultRepresentation
        }
    | _ -> None

let agrees (signature: Signature) (contract: CallableContract) =
    contract.Kind = CallableKind.OrdinaryFlatClosure &&
    contract.ParameterTypes = signature.Parameters && contract.ResultType = signature.Result &&
    contract.EnvironmentBytes = signature.EnvironmentBytes && contract.OmittedParameters = signature.Omitted &&
    contract.ParameterRepresentations = signature.ParameterRepresentations &&
    contract.ResultRepresentation = signature.ResultRepresentation

/// One implementation's convention is reusable at its aliases. Unifying two
/// different implementations additionally requires the receiving-family recipe
/// to settle their physical components; equal source signatures alone do not.
let tryIdentity graph layouts (contracts: Map<NodeId, CallableContract>) (carrier: CallableCarrier) =
    signature graph layouts carrier |> Option.bind (fun signature ->
        let candidates = contracts.Values |> Seq.filter (fun contract ->
            agrees signature contract &&
            contract.Participants |> List.exists (fun participant ->
                participant.Role = ParticipantRole.CallableImplementation &&
                participant.Node = carrier.Implementation && participant.Group = contract.Identity)) |> Seq.toList
        match candidates with [contract] -> Some contract.Identity | _ -> None)

let assign graph layouts contracts (carrier: CallableCarrier) =
    let contract =
        match tryIdentity graph layouts contracts carrier with
        | Some identity -> Ok identity
        | None -> Error "Callable receiving convention has not been settled by its source recipe."
    { carrier with Contract = contract }

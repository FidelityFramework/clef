// SPDX-License-Identifier: MIT
/// Read an ordinary callable's actual convention. Native entries require their
/// boundary recipe; a source arrow type never supplies that contract.
module Clef.Compiler.Baker.Ingredients.CallableContracts

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Identity = Clef.Compiler.NativeTypedTree.TypeIdentities
module Numeric = Clef.Compiler.Baker.Ingredients.NumericValues
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries
module Entries = Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries

/// Read the exact typed owner and its physical target. Consumers below compare
/// the selected premise facts against current source nodes; unrelated source
/// occurrences do not belong to this local callable reading.
let private numericOwner (graph: SemanticGraph) =
    graph.Edges |> List.choose (fun edge ->
        match edge.Role with EdgeRole.NumericDomain domain -> Some(edge.Target, domain) | _ -> None)
    |> function
        | [anchor, domain] when domain.Platform = Boundary.platformPremise graph.Platform ->
            graph.Nodes.TryFind anchor |> Option.filter Numeric.owned
            |> Option.map (fun node -> anchor, domain, Boundary.premise node)
        | _ -> None

/// Source authorship requires the complete current numeric premise inventory.
/// NumericPublication remains the full owner/proof admission gate downstream.
let currentNumericOwner (graph: SemanticGraph) =
    numericOwner graph |> Option.filter (fun (_, domain, _) -> domain.Premises = Numeric.premises graph)

/// Exact scalar support selected by the already settled physical signature.
/// The typed numeric owner anchor is outside its ordinary premise inventory.
let sourceEvidence (owner: NodeId * NumericDomain * BoundarySourcePremise) (carrier: CallableCarrier) =
    let anchor, domain, anchorPremise = owner
    let sites = carrier.Result :: (carrier.Parameters |> List.map (fun (_, _, formal) -> formal)) |> Set.ofList
    let sources =
        domain.Values |> List.filter (fun value -> sites.Contains value.Site)
        |> List.collect (fun value -> Set.toList value.Participants @ value.Obligations)
        |> List.distinct
    let premises = sources |> List.choose (fun id ->
        if id = anchor then Some(id, anchorPremise)
        else domain.Premises.TryFind id |> Option.map (fun premise -> id, premise)) |> Map.ofList
    sources, premises

let participants identity (carrier: CallableCarrier) sources =
    let participant role ordinal node = { Node = node; Role = role; Ordinal = ordinal; Group = identity }
    [ yield participant ParticipantRole.CallableContract 0 identity
      yield participant ParticipantRole.CallableImplementation 0 carrier.Implementation
      yield participant ParticipantRole.CalleeBody 0 carrier.Result
      for ordinal, (_, _, formal) in List.indexed carrier.Parameters do
          yield participant ParticipantRole.CalleeParameter ordinal formal
      for ordinal, premise in List.indexed sources do
          yield participant ParticipantRole.Source ordinal premise ]

let lifetimeParticipants identity = function
    | CallableConvention.Ordinary -> []
    | CallableConvention.CompilerOwnedPortable convention ->
        Entries.lifetimeParticipants identity convention.CodeLifetime

let conventionEvidence (graph: SemanticGraph) convention owner carrier =
    let sources, premises = sourceEvidence owner carrier
    match convention with
    | CallableConvention.Ordinary -> sources, premises
    | CallableConvention.CompilerOwnedPortable convention ->
        let residence = Entries.lifetimeNodes convention.CodeLifetime
        let premises = residence |> List.fold (fun premises id ->
            match graph.Nodes.TryFind id with
            | Some node -> Map.add id (Boundary.premise node) premises
            | None -> premises) premises
        List.distinct (sources @ residence), premises

let conventionParticipants convention identity carrier sources =
    participants identity carrier sources @ lifetimeParticipants identity convention

/// Re-observe only the facts this contract actually owns. NumericPublication
/// separately validates the complete numeric owner and its proof discharge.
/// A cached premise, an equal physical result or a live declaration alone is
/// not authority to reuse a different source dependency account.
let sourcePremisesCurrent (graph: SemanticGraph) (contract: CallableContract) =
    let sources = contract.Participants |> List.filter (fun participant -> participant.Role = ParticipantRole.Source)
    let expected =
        sources |> List.choose (fun participant ->
            graph.Nodes.TryFind participant.Node |> Option.bind (fun node ->
                match node.Kind with
                | SemanticKind.Obligation _ -> None
                | _ -> Some(participant.Node, Boundary.premise node))) |> Map.ofList
    (sources |> List.forall (fun participant ->
        participant.Group = contract.Identity && graph.Nodes.ContainsKey participant.Node)) &&
    contract.SourcePremises = expected &&
    (match contract.Kind, contract.Convention with
     | CallableKind.OrdinaryFlatClosure, CallableConvention.Ordinary -> true
     | CallableKind.NativeEntry, CallableConvention.CompilerOwnedPortable convention ->
         Boundary.platformPremise graph.Platform = Some convention.Target &&
         Entries.current graph convention.CodeLifetime
     | _ -> false)

type Signature = {
    Kind: CallableKind
    Convention: CallableConvention
    Parameters: TypeIdentity list
    Result: TypeIdentity
    EnvironmentBytes: int option
    Omitted: int list
    ParameterRepresentations: (int * ValueRepresentation) list
    ResultRepresentation: ValueRepresentation
}

let signature (graph: SemanticGraph) (layouts: Map<NodeId, EnvironmentLayout>)
              (carrier: CallableCarrier) =
    // A foreign declaration's source lambda is its typed placeholder, not an
    // ordinary Clef implementation. Reuse the declaration owner's exact path;
    // a representable handle parameter does not turn that stub into a closure.
    let foreignDeclaration =
        graph.Edges
        |> List.exists (fun edge ->
            match edge.Role with
            | EdgeRole.BoundaryDeclaration declaration when
                edge.Target = declaration.Binding
                && declaration.Implementation = carrier.Implementation
                && declaration.Body = carrier.Result
                && declaration.Formals = (carrier.Parameters |> List.map (fun (_, _, formal) -> formal))
                ->
                match
                    graph.Nodes.TryFind declaration.Binding,
                    Clef.Compiler.Baker.Recipes.BoundaryDeclarations.bindingPath graph declaration.Binding
                with
                | Some binding, Ok(path, formals, body) ->
                    Clef.Compiler.Baker.Recipes.BoundaryDeclarations.isExternal binding
                    && path = declaration.Path
                    && body = declaration.Body
                    && List.last path = declaration.Implementation
                    && (formals |> List.map (fun (_, _, formal) -> formal)) = declaration.Formals
                | _ -> false
            | _ -> false)

    let environment =
        match carrier.Environment with
        | None -> Some None
        | Some environment ->
            layouts.TryFind environment.Owner
            |> Option.filter (fun layout ->
                layout.Implementation = carrier.Implementation && layout.Formal = environment.Formal)
            |> Option.map (fun layout -> Some layout.Bytes)
    let domain =
        graph.Edges
        |> List.choose (fun edge ->
            match edge.Role with
            | EdgeRole.NumericDomain domain -> Some domain
            | _ -> None)
        |> function
            | [ domain ] when not (carrier.Kind = CallableKind.OrdinaryFlatClosure && foreignDeclaration) -> Some domain
            | _ -> None

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
    match graph.Nodes.TryFind carrier.Result, environment, representations with
    | Some result, Some bytes, Some(parameters, resultRepresentation) ->
        let cHandle = function
            | ValueRepresentation.Scalar(SettledSlot.CHandle(_, bits, align)) ->
                bits > 0 && align > 0 && (graph.Platform |> Option.bind (fun p -> p.Dimensions.TryFind "Pointer") |> Option.forall ((=) bits))
            | _ -> false
        let nullableCHandle = function
            | ValueRepresentation.Union([("None", []); ("Some", [inner])], Some _) -> cHandle inner
            | _ -> false
        let scalar = function
            | ValueRepresentation.Scalar(SettledSlot.Integer _ | SettledSlot.Real _ | SettledSlot.Bool | SettledSlot.Char) -> true
            | rep -> cHandle rep
        let nativeBufferElement = function
            | ValueRepresentation.Scalar(SettledSlot.Integer(8, _)) -> true
            | rep -> cHandle rep || nullableCHandle rep
        let nativeParameter = function
            | ValueRepresentation.Buffer(None, elem) -> nativeBufferElement elem
            | rep -> scalar rep || nullableCHandle rep
        let unitResult =
            resultRepresentation = ValueRepresentation.Scalar SettledSlot.Unit
            && Types.tryGetNTUKind result.Type = Some NTUKind.NTUunit
        let unitParameterOmission =
            match carrier.Parameters with
            | [(_, ty, formal)] ->
                carrier.OmittedParameters = Set.singleton formal &&
                Types.tryGetNTUKind ty = Some NTUKind.NTUunit && unitResult &&
                (graph.Nodes.TryFind formal |> Option.exists (fun node -> Types.tryGetNTUKind node.Type = Some NTUKind.NTUunit)) &&
                (domain |> Option.bind (fun domain -> domain.OccurrenceRepresentations.TryFind formal)) =
                    Some(Ok(ValueRepresentation.Scalar SettledSlot.Unit))
            | _ -> false
        let convention =
            match carrier.Kind with
            | CallableKind.OrdinaryFlatClosure -> Some CallableConvention.Ordinary
            | CallableKind.NativeEntry when bytes.IsNone && carrier.EnvironmentValue.IsNone &&
                                           (carrier.OmittedParameters.IsEmpty || unitParameterOmission) &&
                                           (parameters |> List.forall (snd >> nativeParameter)) && (scalar resultRepresentation || nullableCHandle resultRepresentation || unitResult) ->
                match domain |> Option.bind _.Platform, Entries.tryImplementation graph carrier.Implementation,
                      Entries.tryFormation graph carrier.Occurrence with
                | Some target, Some entry, Some formation
                    when entry.Lifetime = formation.Entry.Lifetime && carrier.Formation = formation.Formation ->
                    Some(CallableConvention.CompilerOwnedPortable {
                        Target = target
                        ParameterConversions = parameters |> List.map (fun (ordinal, representation) -> ordinal, CallableConversion.Identity representation)
                        ResultConversion = CallableConversion.Identity resultRepresentation
                        CodeLifetime = entry.Lifetime
                    })
                | _ -> None
            | _ -> None
        convention |> Option.map (fun convention -> {
            Kind = carrier.Kind
            Convention = convention
            Parameters = carrier.Parameters |> List.map (fun (_, ty, _) -> Identity.ofType ty)
            Result = Identity.ofType result.Type
            EnvironmentBytes = bytes
            Omitted = carrier.Parameters |> List.indexed |> List.choose (fun (ordinal, (_, _, formal)) ->
                if carrier.OmittedParameters.Contains formal then Some ordinal else None)
            ParameterRepresentations = parameters
            ResultRepresentation = resultRepresentation
        })
    | _ -> None

let agrees (signature: Signature) (contract: CallableContract) =
    contract.Kind = signature.Kind && contract.Convention = signature.Convention &&
    contract.ParameterTypes = signature.Parameters && contract.ResultType = signature.Result &&
    contract.EnvironmentBytes = signature.EnvironmentBytes && contract.OmittedParameters = signature.Omitted &&
    contract.ParameterRepresentations = signature.ParameterRepresentations &&
    contract.ResultRepresentation = signature.ResultRepresentation

/// One implementation's convention is reusable at its aliases. Unifying two
/// different implementations additionally requires the receiving-family recipe
/// to settle their physical components; equal source signatures alone do not.
let tryIdentity graph layouts (contracts: Map<NodeId, CallableContract>) (carrier: CallableCarrier) =
    signature graph layouts carrier |> Option.bind (fun signature ->
        let candidates = contracts |> Map.toSeq |> Seq.choose (fun (key, contract) ->
            if key = contract.Identity && agrees signature contract &&
               (contract.Participants |> List.exists (fun participant ->
                participant.Role = ParticipantRole.CallableImplementation &&
                participant.Node = carrier.Implementation && participant.Group = contract.Identity))
            then Some contract else None) |> Seq.toList
        match candidates with [contract] -> Some contract.Identity | _ -> None)

let assign graph layouts contracts (carrier: CallableCarrier) =
    let contract =
        match tryIdentity graph layouts contracts carrier with
        | Some identity when sourcePremisesCurrent graph contracts[identity] -> Ok identity
        | Some _ -> Error "Callable source proof premises changed after their owning recipe settled the convention."
        | None -> Error "Callable receiving convention has not been settled by its source recipe."
    let lifetime =
        match contract with
        | Ok identity when carrier.Kind = CallableKind.NativeEntry ->
            lifetimeParticipants identity contracts[identity].Convention
        | _ -> carrier.Lifetime
    { carrier with Contract = contract; Lifetime = lifetime }

/// A native carrier's lifetime is the typed program-image relation of its exact
/// receiving contract. A nonempty unrelated participant list is not evidence.
let lifetimeCurrent (contract: CallableContract) (carrier: CallableCarrier) =
    match carrier.Kind, contract.Convention with
    | CallableKind.NativeEntry, CallableConvention.CompilerOwnedPortable convention ->
        convention.CodeLifetime.Implementation = carrier.Implementation &&
        carrier.Environment.IsNone && carrier.EnvironmentValue.IsNone &&
        carrier.Lifetime = lifetimeParticipants contract.Identity contract.Convention
    | CallableKind.OrdinaryFlatClosure, CallableConvention.Ordinary -> true
    | _ -> false

/// Preserve the existing mutable-storage protocol while updating only its
/// references to carrier rows changed by a source contract fold.
let refreshStorage (carriers: Map<NodeId, CallableCarrier>) (storage: Map<NodeId, MutableCallableStorage>) =
    let refreshed = storage |> Map.map (fun _ row ->
        let alternatives = row.AlternativeCarriers |> List.map (fun carrier ->
            carriers.TryFind carrier.Occurrence |> Option.defaultValue carrier)
        {row with AlternativeCarriers = alternatives})
    if refreshed = storage then storage else refreshed

/// Pure admission of held source rows. No identity is allocated, no contract is
/// authored and no missing fact is repaired at witness preparation. The recipe
/// is the only writer; this reading checks its exact current support inventory.
let validate (graph: SemanticGraph) layouts (contracts: Map<NodeId, CallableContract>)
             (carriers: Map<NodeId, CallableCarrier>) : WitnessProjectionFailure list =
    let failures = ResizeArray<WitnessProjectionFailure>()
    let fail site reason =
        failures.Add { Kind = WitnessProjectionFailureKind.Settlement; Occurrence = Some site; Participants = Set.singleton site
                       Reason = "Callable contract: " + reason }
    let owner = numericOwner graph
    let mutable required = Set.empty
    for (_, implementation), occurrences in carriers.Values |> Seq.groupBy (fun carrier -> carrier.Kind, carrier.Implementation) do
        let occurrences = List.ofSeq occurrences
        match occurrences |> List.map (signature graph layouts) |> List.distinct with
        | [Some _] ->
            let identities = occurrences |> List.map (tryIdentity graph layouts contracts) |> List.distinct
            match identities, owner with
            | [Some identity], Some owner ->
                required <- required.Add identity
                let held = contracts[identity]
                let sources, premises = conventionEvidence graph held.Convention owner occurrences.Head
                if held.Identity <> identity || held.Participants <> conventionParticipants held.Convention identity occurrences.Head sources ||
                   held.SourcePremises <> premises || not (sourcePremisesCurrent graph held) ||
                   (occurrences |> List.exists (lifetimeCurrent held >> not)) then
                    fail implementation "The exact signature, participant account or source premises changed; its owning recipe must settle the convention."
            | _, None -> fail implementation "The current numeric source owner is absent; a held receiving convention is not evidence."
            | _ -> fail implementation "The required receiving convention is absent or ambiguous."
        | _ -> ()
    for KeyValue(identity, _) in contracts do
        if not (required.Contains identity) then
            fail identity "A held receiving convention has no matching current callable boundary."
    List.ofSeq failures

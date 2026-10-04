// SPDX-License-Identifier: MIT
/// Exact account of already authored callable aggregate relations. This reader
/// follows declared FormationInputs only; it discovers no callable origins,
/// receiving convention, layout, residence or activation semantics.
module Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Identity = Clef.Compiler.NativeTypedTree.TypeIdentities
module AggregateTypes = Clef.Compiler.Baker.Ingredients.CallableAggregateTypes

type Inputs = {
    Slots: Map<NodeId, CallableAggregateSlot>
    Values: Map<NodeId, CallableAggregateValue list>
    Carriers: Map<NodeId, CallableCarrier>
    Contracts: Map<NodeId, CallableContract>
    Flows: Map<NodeId, CallableFlow>
    Joins: Map<NodeId, CallableJoin>
}

let private collect (lookup: NodeId -> 'value option) (label: string) (keys: NodeId list) : Result<'value list, string> =
    let values = keys |> List.map (fun key ->
        match lookup key with
        | Some value -> Ok value
        | None -> Error($"Callable aggregate account lacks {label} {NodeId.value key}."))
    match values |> List.tryPick (function Error reason -> Some reason | _ -> None) with
    | Some reason -> Error reason
    | None -> Ok(values |> List.choose (function Ok value -> Some value | _ -> None))

/// Re-observe the declaration evidence under its source owner. The held fact
/// cannot certify itself, and native substitution cells are never retained.
let private declarationsCurrent (graph: SemanticGraph) (values: CallableAggregateValue list)
                                (slot: CallableAggregateSlot) =
    let aggregates =
        values |> List.filter (fun row -> row.Slot = slot.Identity) |> List.map _.Aggregate |> List.distinct
    let types = aggregates |> List.map (fun id -> graph.Nodes.TryFind id |> Option.map _.Type)
    if types.IsEmpty || (types |> List.exists Option.isNone) ||
       (types |> List.choose id |> List.exists (fun ty -> Identity.ofType ty <> slot.AggregateType)) then
        Error "Callable aggregate declaration evidence lacks its exact instantiated source occurrence."
    else
        let instance = types |> List.choose id |> List.head
        let candidates = AggregateTypes.slots graph instance |> List.filter (fun current -> current.Path = slot.Path)
        match candidates with
        | [current] when current.Declaration = slot.Declaration && Identity.ofType current.ValueType = slot.SourceType ->
            AggregateTypes.declarationFacts graph current.Declarations |> Result.bind (fun declarations ->
                let expected = declarations |> List.mapi (fun ordinal (fact: CallableAggregateDeclarationFact) ->
                    { Node = fact.Identity; Role = ParticipantRole.AggregateDeclaration; Ordinal = ordinal; Group = slot.Identity })
                let held = slot.Participants |> List.filter (fun participant -> participant.Role = ParticipantRole.AggregateDeclaration)
                if declarations = slot.DeclarationFacts && held = expected then Ok ()
                else Error "Callable aggregate declaration facts or their ordered path participants changed before commitment.")
        | _ -> Error "Callable aggregate declaration path no longer has its current instantiated source type."

/// Build a dependency account after the producing fold has installed its
/// slot/value/carrier tables. No old receipt supplies any premise to this read.
let authorWith (facts: Inputs) (graph: SemanticGraph) (occurrence: NodeId) : Result<CallableAggregateDependencyAccount, string> =
    let rec closure (seen: Set<NodeId>) (pending: NodeId list) (accumulated: CallableAggregateValue list)
                    : Result<CallableAggregateValue list, string> =
        match pending with
        | [] -> Ok accumulated
        | site :: rest when Set.contains site seen -> closure seen rest accumulated
        | site :: rest ->
            match facts.Values.TryFind site with
            | None when site = occurrence -> Error "Callable aggregate account has no owning occurrence rows."
            | None -> closure (Set.add site seen) rest accumulated
            | Some rows ->
                if rows.IsEmpty || (rows |> List.exists (fun row -> row.Occurrence <> site)) ||
                   (rows |> List.map _.Slot |> List.distinct |> List.length) <> rows.Length then
                    Error "Callable aggregate account has absent, repeated or misfiled value rows."
                else
                    let dependencies = rows |> List.collect _.FormationInputs
                    closure (Set.add site seen) (rest @ dependencies) (accumulated @ rows)
    closure Set.empty [occurrence] [] |> Result.bind (fun (values: CallableAggregateValue list) ->
        let slotIds = values |> List.map _.Slot |> List.distinct
        let carrierIds = values |> List.collect (fun value -> value.Alternatives |> List.collect (fun alternative ->
            alternative.Carrier :: Option.toList alternative.Adapter)) |> List.distinct
        collect facts.Slots.TryFind "slot" slotIds |> Result.bind (fun (slots: CallableAggregateSlot list) ->
        collect facts.Carriers.TryFind "carrier" carrierIds |> Result.bind (fun (carriers: CallableCarrier list) ->
            let contractIds =
                (slots |> List.choose (fun slot -> Result.toOption slot.Contract)) @
                (carriers |> List.choose (fun carrier -> Result.toOption carrier.Contract)) |> List.distinct
            collect facts.Contracts.TryFind "contract" contractIds |> Result.bind (fun (contracts: CallableContract list) ->
                let declarationFailure = slots |> List.tryPick (fun slot ->
                    declarationsCurrent graph values slot |> function Error reason -> Some reason | Ok () -> None)
                let declarationIdentities = slots |> List.collect _.DeclarationFacts |> List.map (fun (fact: CallableAggregateDeclarationFact) -> fact.Identity) |> Set.ofList
                let inputs = values |> List.collect (fun value -> value.Occurrence :: value.FormationInputs) |> List.distinct
                let flows = inputs |> List.choose facts.Flows.TryFind
                let joins = inputs |> List.choose facts.Joins.TryFind
                let participants =
                    (slots |> List.collect _.Participants) @
                    (values |> List.collect (fun value -> value.Participants @ (value.Tag |> Option.map _.Participants |> Option.defaultValue []))) @
                    (carriers |> List.collect _.Lifetime) @
                    (contracts |> List.collect _.Participants)
                let participantNodes = participants |> List.map _.Node |> List.distinct
                let sources : Result<CallableAggregateSourceIncidence, string> list = participantNodes |> List.choose (fun id ->
                    graph.Nodes.TryFind id
                    |> Option.filter (fun node ->
                        match node.Kind with
                        | SemanticKind.Obligation _ -> false
                        | SemanticKind.TypeDef _ when declarationIdentities.Contains id -> false
                        | _ -> true)
                    |> Option.map (fun node ->
                        let anchors =
                            match node.Metadata.TryFind ObligationMetadata.Anchors with
                            | None -> Ok []
                            | Some(MetadataValue.StringList names) -> Ok names
                            | Some _ -> Error "Callable aggregate participant has malformed obligation anchor metadata."
                        anchors |> Result.map (fun anchors ->
                            { Node = id; Kind = node.Kind; Type = Identity.ofType node.Type
                              Children = node.Children; Anchors = anchors })))
                let claims = participantNodes |> List.choose (fun id ->
                    graph.Nodes.TryFind id |> Option.bind (fun node ->
                        match node.Kind with SemanticKind.Obligation claim -> Some(id, claim) | _ -> None))
                match declarationFailure |> Option.orElseWith (fun () -> sources |> List.tryPick (function Error reason -> Some reason | _ -> None)) with
                | Some reason -> Error reason
                | None ->
                    Ok { Occurrence = occurrence; Slots = slots; Values = values; Carriers = carriers
                         Contracts = contracts; Flows = flows; Joins = joins; Participants = participants
                         Sources = sources |> List.choose (function Ok source -> Some source | _ -> None); Claims = claims }))))

let author (graph: SemanticGraph) (occurrence: NodeId) =
    let facts = graph.Codata.Value
    authorWith { Slots = facts.CallableAggregateSlots; Values = facts.CallableAggregateValues
                 Carriers = facts.CallableCarriers; Contracts = facts.CallableContracts
                 Flows = facts.CallableFlows; Joins = facts.CallableJoins } graph occurrence

/// Equality is over complete rows and ordered role/ordinal incidence, including
/// actual source and obligation bodies. Equal selected code is insufficient.
let current (graph: SemanticGraph) (occurrence: NodeId) =
    match graph.Codata.Value.CallableAggregateDependencies.TryFind occurrence with
    | None -> Error "Callable aggregate lacks its published source dependency account (CCS8414)."
    | Some held ->
        author graph occurrence |> Result.bind (fun actual ->
            if held = actual then Ok held
            else Error "Callable aggregate source support changed after its dependency account was authored (CCS8414).")

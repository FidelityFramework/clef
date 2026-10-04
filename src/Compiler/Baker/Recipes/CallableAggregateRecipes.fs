// SPDX-License-Identifier: MIT
/// Author callable components from the existing origin reading. This recipe
/// does not discover another flow fixed point or manufacture native contracts,
/// environment residence, selectors or mutable read frontiers.
module Clef.Compiler.Baker.Recipes.CallableAggregateRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module AggregateTypes = Clef.Compiler.Baker.Ingredients.CallableAggregateTypes
module Accounts = Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts
module Identity = Clef.Compiler.NativeTypedTree.TypeIdentities
module Codes = Clef.Compiler.NativeTypedTree.Expressions.Types.DiagnosticCodes

type Inputs = {
    Carriers: Map<NodeId, CallableCarrier>
    Contracts: Map<NodeId, CallableContract>
    Flows: Map<NodeId, CallableFlow>
    Joins: Map<NodeId, CallableJoin>
    PreviousSlots: Map<NodeId, CallableAggregateSlot>
}

/// A source location is available through Occurrence. The owning commitment
/// turns a required residual into a diagnostic; a dormant value alone does not.
type Residual = { Occurrence: NodeId; Code: string; Reason: string }
type Settlement = {
    Slots: Map<NodeId, CallableAggregateSlot>
    Values: Map<NodeId, CallableAggregateValue list>
    Dependencies: Map<NodeId, CallableAggregateDependencyAccount>
    Residuals: Residual list
}

let private participant (group: NodeId) role ordinal (node: NodeId) : Participant =
    { Node = node; Role = role; Ordinal = ordinal; Group = group }

let private sourceSupport (reading: Origins.AggregateResolution) site =
    [ for ordinal, (source, operands) in reading.Dependencies |> Map.toList |> List.indexed do
          yield participant site ParticipantRole.Source ordinal source
          for index, operand in List.indexed operands do
              yield participant source ParticipantRole.Path index operand ]

let private closedCarrier (graph: SemanticGraph) (inputs: Inputs) (slot: AggregateTypes.Slot) value : Result<CallableCarrier, string * string> =
    let refuse code reason = Error(code, reason)
    match inputs.Carriers.TryFind value with
    | None when inputs.Flows.ContainsKey value || inputs.Joins.ContainsKey value ->
        refuse Codes.CCS8411_CallableAggregateSelector "The stored callable value needs a source-authored selection or mutable snapshot; a flow family cannot stand in for a selected write."
    | None -> refuse Codes.CCS8414_CallableAggregateEvidence "The actual callable input has no settled carrier formation."
    | Some carrier when carrier.Occurrence <> value || carrier.Kind <> slot.Kind ||
                        Identity.ofType carrier.SourceType <> Identity.ofType slot.ValueType ->
        refuse Codes.CCS8412_CallableAggregatePairing "The stored value and its carrier disagree on occurrence, callable kind or instantiated source type."
    | Some carrier ->
        match carrier.Contract with
        | Error reason -> refuse Codes.CCS8413_CallableAggregateContract reason
        | Ok identity ->
            match inputs.Contracts.TryFind identity with
            | None -> refuse Codes.CCS8413_CallableAggregateContract "The callable input's receiving contract has no current source row."
            | Some contract when contract.Identity <> identity || contract.Kind <> carrier.Kind ->
                refuse Codes.CCS8413_CallableAggregateContract "The callable input differs from its exact receiving contract identity or kind."
            | Some _ when not (graph.Nodes.ContainsKey carrier.Formation) ->
                refuse Codes.CCS8414_CallableAggregateEvidence "The callable formation has no current source occurrence."
            | Some _ when carrier.Environment.IsSome <> carrier.EnvironmentValue.IsSome ->
                refuse Codes.CCS8412_CallableAggregatePairing "The carrier drops or crosses its actual environment occurrence."
            | Some _ when (carrier.Environment.IsSome || carrier.Kind = CallableKind.NativeEntry) && carrier.Lifetime.IsEmpty ->
                refuse Codes.CCS8101_LifetimeError "The stored environment or native entry has no source-owned lifetime evidence."
            | Some contract when carrier.Kind = CallableKind.NativeEntry &&
                                 not (Clef.Compiler.Baker.Ingredients.CallableContracts.lifetimeCurrent contract carrier) ->
                refuse Codes.CCS8101_LifetimeError "The native entry's retained lifetime differs from its exact program-image declaration evidence."
            | Some _ when carrier.Environment.IsSome ->
                refuse Codes.CCS8410_CallableAggregateDataPlacement "This callable component still requires source-owned environment placement; a code word or guessed environment descriptor cannot replace it."
            | Some _ -> Ok carrier

let private tag (graph: SemanticGraph) construction path (presentValue: NodeId option) : Result<CallableAggregateTag option, string> =
    match path with
    | [CallableAggregatePathStep.RecordField _] -> Ok None
    | [CallableAggregatePathStep.UnionPayload(expectedCase, payloadOrdinal)] ->
        match graph.Nodes.TryFind construction with
        | Some ({ Kind = SemanticKind.UnionCase(_, actualCase, payload) } as constructor)
        | Some ({ Kind = SemanticKind.DUConstruct(_, actualCase, payload, _) } as constructor) ->
            let actualPayload =
                match payload, presentValue with
                | Some actual, Some expected when payloadOrdinal = 0 && actual = expected -> Some actual
                | Some tuple, Some _ ->
                    graph.Nodes.TryFind tuple |> Option.bind (fun node ->
                        match node.Kind with
                        | SemanticKind.TupleExpr fields -> List.tryItem payloadOrdinal fields
                        | _ -> None)
                | _ -> None
            if presentValue.IsSome && (actualCase <> expectedCase || actualPayload <> presentValue) then
                Error "The actual union constructor does not pair this callable payload with its declared case and ordinal."
            elif presentValue.IsNone && actualCase = expectedCase then
                Error "The selected union constructor does not establish absence of this callable payload."
            else
                let actualTagPayload =
                    match presentValue, AggregateTypes.shape graph constructor.Type with
                    | Some value, _ -> Ok(Some(payloadOrdinal, value), [payloadOrdinal, value], None)
                    | None, Some(AggregateTypes.Shape.Union(_, cases)) ->
                        match cases |> List.tryItem actualCase, payload with
                        | Some(_, []), None -> Ok(None, [], None)
                        | Some(_, [_]), Some value -> Ok(Some(0, value), [0, value], None)
                        | Some(_, fields), Some tuple when fields.Length > 1 ->
                            match graph.Nodes.TryFind tuple with
                            | Some { Kind = SemanticKind.TupleExpr (first :: rest) } when rest.Length + 1 = fields.Length ->
                                Ok(Some(0, first), List.indexed (first :: rest), Some tuple)
                            | _ -> Error "The inactive callable case has no exact current tuple payload."
                        | _ -> Error "The inactive callable case does not agree with its declared payload."
                    | _ -> Error "The inactive callable case has no exact instantiated union declaration."
                actualTagPayload |> Result.map (fun (selectedPayload, payloads, packaging) ->
                    Some {
                        Constructor = construction; TagRead = None; CaseOrdinal = actualCase
                        PayloadOrdinal = selectedPayload |> Option.map fst
                        Payload = selectedPayload |> Option.map snd
                        Participants =
                            [ yield participant construction ParticipantRole.AggregateConstructor 0 construction
                              for ordinal, value in payloads do
                                  yield participant construction ParticipantRole.AggregatePayload ordinal value
                              for tuple in Option.toList packaging do
                                  yield participant construction ParticipantRole.AggregateInput 0 tuple ]
                    })
        | _ -> Error "The callable union component has no current source constructor."
    | _ -> Error "The nested callable path still requires its source-owned aggregate formation protocol."

let private alternatives (carrier: CallableCarrier option) : CallableAggregateAlternative list =
    match carrier with
    | None -> []
    | Some carrier ->
        match carrier.Contract with
        | Error _ -> [] // Called only after closedCarrier has admitted this row.
        | Ok contract ->
            [{ Ordinal = 0; Carrier = carrier.Occurrence; Formation = carrier.Formation
               EnvironmentValue = carrier.EnvironmentValue; Contract = contract
               Adapter = None; EnvironmentPlacement = None }]

let private valueRow slot occurrence aggregate operation formationInputs actualValue selected tag carrier support : CallableAggregateValue =
    let alternatives = alternatives carrier
    { Occurrence = occurrence; Aggregate = aggregate; Slot = slot
      Alternatives = alternatives
      Selector = if alternatives.IsEmpty then None else Some { Lower = 0; UpperExclusive = 1; Storage = None; Slot = None; ByteOffset = None }
      FormationInputs = formationInputs; Value = actualValue; SelectedAlternative = selected
      Operation = operation; Frontier = None; Tag = tag; Bytes = 0; Alignment = 1
      Participants =
        [ yield participant occurrence ParticipantRole.AggregateValue 0 occurrence
          yield participant occurrence ParticipantRole.AggregateSource 0 aggregate
          yield participant occurrence ParticipantRole.AggregateSlot 0 slot
          for ordinal, input in List.indexed formationInputs do
              yield participant occurrence ParticipantRole.AggregateInput ordinal input
          for value in Option.toList actualValue do
              yield participant occurrence ParticipantRole.AggregateWrite 0 value
          for alternative in alternatives do
              yield participant occurrence ParticipantRole.CallableCarrier alternative.Ordinal alternative.Carrier
              yield participant occurrence ParticipantRole.CallableFormation alternative.Ordinal alternative.Formation
              yield participant occurrence ParticipantRole.CallableContract alternative.Ordinal alternative.Contract
          yield! support ] }

/// Resolve direct fields/payloads with one closed formation per component.
/// Wider families remain residuals until their source selector/adapter/storage
/// recipes can establish the complete protocol. No old account supplies facts.
let settle (resolution: Origins.Resolution) (inputs: Inputs) (graph: SemanticGraph) : Settlement =
    let residuals = ResizeArray<Residual>()
    let refuse occurrence code reason = residuals.Add { Occurrence = occurrence; Code = code; Reason = reason }
    let mutable slots : Map<NodeId, CallableAggregateSlot> = Map.empty
    let mutable values : Map<NodeId, CallableAggregateValue list> = Map.empty
    let mutable conflicts : Set<NodeId * NodeId> = Set.empty
    let addValue (row: CallableAggregateValue) =
        let previous = values.TryFind row.Occurrence |> Option.defaultValue []
        match conflicts.Contains(row.Occurrence, row.Slot), previous |> List.tryFind (fun old -> old.Slot = row.Slot) with
        | true, _ -> ()
        | false, None -> values <- values.Add(row.Occurrence, previous @ [row])
        | false, Some old when old = row -> ()
        | false, Some _ ->
            conflicts <- conflicts.Add(row.Occurrence, row.Slot)
            values <- values.Add(row.Occurrence, previous |> List.filter (fun old -> old.Slot <> row.Slot))
            refuse row.Occurrence Codes.CCS8414_CallableAggregateEvidence "The aggregate occurrence has conflicting source formations for the same slot."
    let readings =
        resolution.Aggregates |> Map.toList |> List.choose (fun (site, reading) ->
            graph.Nodes.TryFind site |> Option.map (fun node -> site, node.Type, reading))
    let groups =
        readings |> List.collect (fun (site, ty, reading) ->
            AggregateTypes.slots graph ty |> List.map (fun slot -> (reading.AggregateType, slot.Path), (site, slot, reading)))
        |> List.groupBy fst
    for (aggregateType, path), rows in groups do
        let group = rows |> List.map snd
        let _, specification, _ = group.Head
        let report code reason = group |> List.iter (fun (site, _, _) -> refuse site code reason)
        if path.Length <> 1 then
            report Codes.CCS8414_CallableAggregateEvidence "The nested callable path still requires its source-owned aggregate formation protocol."
        else
            let contributions =
                group |> List.collect (fun (_, _, reading) ->
                    reading.Alternatives |> List.choose (fun alternative ->
                        alternative.Slots |> List.tryFind (fun slot -> slot.Path = path)
                        |> Option.map (fun slot -> alternative.Construction, slot)))
                |> List.distinct
            let storedValues = contributions |> List.collect (snd >> _.Values) |> List.distinct
            let carrierResults = storedValues |> List.map (closedCarrier graph inputs specification)
            let failure = carrierResults |> List.tryPick (function Error reason -> Some reason | _ -> None)
            let declarations = AggregateTypes.declarationFacts graph specification.Declarations
            let carriers = carrierResults |> List.choose (function Ok carrier -> Some carrier | _ -> None)
            let contracts = carriers |> List.choose (fun carrier -> Result.toOption carrier.Contract) |> List.distinct
            match failure, declarations with
            | Some(code, reason), _ -> report code reason
            | None, Error reason -> report Codes.CCS8414_CallableAggregateEvidence reason
            | None, Ok _ when contracts.Length > 1 ->
                report Codes.CCS8413_CallableAggregateContract "The callable slot requires one receiving contract identity or a source-authored adaptation."
            | None, Ok _ when carriers.Length > 1 ->
                report Codes.CCS8411_CallableAggregateSelector "The callable component has multiple source formations and no authored finite selector or adaptation."
            | None, Ok declarationFacts ->
                let contract =
                    match contracts with
                    | [identity] -> Ok identity
                    | _ -> Error "No callable is present in this union payload; no receiving convention has been manufactured."
                let previous = inputs.PreviousSlots.Values |> Seq.filter (fun row -> row.AggregateType = aggregateType && row.Path = path) |> Seq.toList
                let identity = match previous with [row] -> row.Identity | _ -> NodeId.fresh()
                let slot : CallableAggregateSlot = {
                    Identity = identity; AggregateType = aggregateType; Declaration = specification.Declaration
                    DeclarationFacts = declarationFacts
                    Path = path; SourceType = Identity.ofType specification.ValueType; Contract = contract
                    Participants =
                        [ yield participant identity ParticipantRole.AggregateSlot 0 identity
                          for ordinal, declaration in List.indexed declarationFacts do
                              yield participant identity ParticipantRole.AggregateDeclaration ordinal declaration.Identity
                          match contract with
                          | Ok declared -> yield participant identity ParticipantRole.CallableContract 0 declared
                          | Error _ -> () ]
                }
                let carrier = List.tryHead carriers
                let select construction (slotOrigins: Origins.AggregateSlotOrigins) =
                    if not slotOrigins.UnknownOrigins.IsEmpty || (slotOrigins.Absent && not slotOrigins.Values.IsEmpty) then
                        Error(Codes.CCS8414_CallableAggregateEvidence, "The aggregate constructor has opaque or mixed absent/present callable support.")
                    elif slotOrigins.Absent && slotOrigins.Values.IsEmpty then
                        tag graph construction path None |> Result.map (fun tag -> None, None, tag)
                        |> Result.mapError (fun reason -> Codes.CCS8414_CallableAggregateEvidence, reason)
                    else
                        match slotOrigins.Values, carrier with
                        | [value], Some carrier when carrier.Occurrence = value ->
                            tag graph construction path (Some value) |> Result.map (fun tag -> Some value, Some carrier, tag)
                            |> Result.mapError (fun reason -> Codes.CCS8412_CallableAggregatePairing, reason)
                        | _ -> Error(Codes.CCS8414_CallableAggregateEvidence, "The aggregate constructor does not establish one actual callable input or a proved absent union arm.")
                for site, _, reading in group do
                    let hasWrites = reading.Dependencies |> Map.exists (fun id _ ->
                        graph.Nodes.TryFind id |> Option.exists (fun node -> match node.Kind with SemanticKind.FieldSet _ -> true | _ -> false))
                    if not reading.UnknownOrigins.IsEmpty || not reading.AbsentOrigins.IsEmpty then
                        refuse site Codes.CCS8414_CallableAggregateEvidence "The aggregate occurrence has unresolved source origins or an unformed absent value."
                    elif hasWrites then
                        refuse site Codes.CCS8411_CallableAggregateSelector "The aggregate's stored callable needs an authored mutable write and read-snapshot protocol."
                    else
                        let support = sourceSupport reading site
                        match reading.Alternatives with
                        | [formation] ->
                            match formation.Slots |> List.tryFind (fun candidate -> candidate.Path = path) with
                            | None -> refuse site Codes.CCS8414_CallableAggregateEvidence "The origin reading omits the resolved callable slot."
                            | Some slotOrigins ->
                                match select formation.Construction slotOrigins with
                                | Error(code, reason) -> refuse site code reason
                                | Ok(actual, carrier, tag) ->
                                    if site = formation.Construction then
                                        let inputs = Option.toList actual
                                        addValue (valueRow identity site site CallableAggregateOperation.Construct inputs actual
                                                      (actual |> Option.map (fun _ -> 0)) tag carrier support)
                                    for projection, projectedPath in reading.Projections do
                                        if projectedPath = path then
                                            if actual.IsNone then
                                                refuse projection Codes.CCS8414_CallableAggregateEvidence "A callable projection names an absent union payload; it needs source inactivity evidence before demand may be excluded."
                                            else
                                                let inputs = formation.Construction :: Option.toList actual
                                                addValue (valueRow identity projection site CallableAggregateOperation.Project inputs None None tag carrier
                                                              (sourceSupport reading projection))
                        | [] -> refuse site Codes.CCS8414_CallableAggregateEvidence "The aggregate occurrence has no current construction evidence."
                        | _ -> refuse site Codes.CCS8414_CallableAggregateEvidence "Several constructors reach this aggregate occurrence; a single tag record cannot express the required source selection."
                if values |> Map.exists (fun _ rows -> rows |> List.exists (fun row -> row.Slot = identity)) then
                    slots <- slots.Add(identity, slot)
    // A projection must retain its admitted formation row, including the
    // constructor's dependencies. It cannot bypass a refused source write.
    values <- values |> Map.map (fun site rows -> rows |> List.filter (fun row ->
        if row.Operation <> CallableAggregateOperation.Project then true else
        let formed = row.FormationInputs |> List.tryHead |> Option.exists (fun construction ->
            values.TryFind construction |> Option.exists (List.exists (fun formation ->
                formation.Slot = row.Slot && formation.Operation = CallableAggregateOperation.Construct)))
        if not formed then refuse site Codes.CCS8414_CallableAggregateEvidence "The callable projection has no admitted source construction row."
        formed)) |> Map.filter (fun _ rows -> not rows.IsEmpty)
    let usedSlots = values.Values |> Seq.collect id |> Seq.map _.Slot |> Set.ofSeq
    slots <- slots |> Map.filter (fun identity _ -> usedSlots.Contains identity)
    let tables : Accounts.Inputs = {
        Slots = slots; Values = values; Carriers = inputs.Carriers; Contracts = inputs.Contracts
        Flows = inputs.Flows; Joins = inputs.Joins
    }
    let dependencies =
        values |> Map.toList |> List.choose (fun (site, _) ->
            match Accounts.authorWith tables graph site with
            | Ok account -> Some(site, account)
            | Error reason -> refuse site Codes.CCS8414_CallableAggregateEvidence reason; None) |> Map.ofList
    { Slots = slots; Values = values; Dependencies = dependencies; Residuals = List.ofSeq residuals |> List.distinct }

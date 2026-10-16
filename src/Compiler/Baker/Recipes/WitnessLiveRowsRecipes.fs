// SPDX-License-Identifier: MIT
/// Baker selects complete settled fact rows for its demanded live occurrences.
/// Source support validation remains over the complete owner. References in a
/// selected row authorize facts, never additional executable bodies.
module Clef.Compiler.Baker.Recipes.WitnessLiveRowsRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let private selected ids (rows: Map<NodeId, 'row>) = rows |> Map.filter (fun id _ -> Set.contains id ids)
let private selectedSet ids values = Set.intersect ids values
let private storageIdentity = function ProgramStorageIdentity.Allocation id | ProgramStorageIdentity.BindingSlot id -> id

/// A selected optional anchor is declaration metadata until the existing
/// demand account also supplies an executable occurrence or binding use.
let private metadataDeclarations (emission: WitnessEmissionProjection) (scope: WitnessLiveScopePlan) =
    let demanded = Set.union (scope.Occurrences.Keys |> Set.ofSeq) (scope.BindingUses.Values |> Seq.map _.Binding |> Set.ofSeq)
    let anchors = emission.Boundary.CallbackInvocations.Values |> Seq.choose(fun row ->
        match row.Extent with BoundaryCallbackExtent.ProcessExit(anchor,_) -> anchor | _ -> None) |> Set.ofSeq
    emission.Boundary.Imports.Values |> Seq.filter(fun row ->
        anchors.Contains row.Binding && not(List.exists demanded.Contains row.DeclarationPath) &&
        not(emission.Boundary.Calls.Values |> Seq.exists(fun call -> call.Import=row.Identity)))
    |> Seq.collect _.DeclarationPath |> Set.ofSeq

let private branches ids (value: CallableBranchAuthority) =
    { value with Observations = selected ids value.Observations
                 CarrierUses = selectedSet ids value.CarrierUses
                 FlowUses = selectedSet ids value.FlowUses
                 CallUses = selectedSet ids value.CallUses }

let private programStorage ids (value: ProgramStorageInventory) =
    let entries = value.Entries |> Map.filter (fun key _ -> ids |> Set.contains (storageIdentity key))
    let spaces = entries.Values |> Seq.map _.SpaceNode |> Set.ofSeq
    { Entries = entries
      Reservations = selected spaces value.Reservations
      Unresolved = value.Unresolved |> Map.filter (fun key _ -> ids |> Set.contains (storageIdentity key)) }

/// Only typed executable/fact references advance this closure. Aggregate
/// participants also select their explicit fact rows, including slot/contract
/// identities that are not executable nodes. Owner-wide support inventories
/// remain complete fields in their selected rows; they do not authorize bodies.
let private closeFacts (graph: SemanticGraph) (emission: WitnessEmissionProjection) (scope: WitnessLiveScopePlan) =
    let metadata = metadataDeclarations emission scope
    let mutable ids =
        scope.Occurrences.Keys |> Set.ofSeq
        |> Set.union (scope.BindingUses.Values |> Seq.map _.Binding |> Set.ofSeq)
        |> Set.union (scope.Entries |> Seq.map _.Focus |> Set.ofSeq)
    let add id = ids <- ids.Add id
    let addMany values = ids <- Set.union ids (Set.ofSeq values)
    let addOptional value = Option.iter add value
    let participants values = values |> List.iter (fun (value: Participant) -> add value.Node; add value.Group)
    let rec representation = function
        | ValueRepresentation.CallableComponent(slot, data) -> add slot; representation data
        | ValueRepresentation.Buffer(_, element) -> representation element
        | ValueRepresentation.Record(fields, _) -> fields |> List.iter (snd >> representation)
        | ValueRepresentation.Union(cases, _) -> cases |> List.iter (snd >> List.iter representation)
        | ValueRepresentation.Scalar _ | ValueRepresentation.Tag _ -> ()
    let shape = function
        | CallableValueShape.Data id | CallableValueShape.Callable id
        | CallableValueShape.Sequence id | CallableValueShape.Lazy id -> add id
    let parameters values = values |> List.iter (fun (_, _, id) -> add id)
    let carrier (row: CallableCarrier) =
        add row.Formation; addOptional row.EnvironmentValue
        match row.Contract with Ok identity -> add identity | Error _ -> ()
        participants row.Lifetime
        add row.Implementation; parameters row.Parameters; add row.Result
        List.iter shape row.ParameterShapes; shape row.ResultShape
        row.Environment |> Option.iter (fun value -> add value.Owner; add value.Formal)
    let contract (row: CallableContract) =
        add row.Identity; participants row.Participants
        row.ParameterRepresentations |> List.iter (snd >> representation)
        representation row.ResultRepresentation
    let aggregateSlot (row: CallableAggregateSlot) =
        add row.Identity; addOptional row.Declaration; participants row.Participants
        match row.Contract with Ok identity -> add identity | Error _ -> ()
    let aggregateValue (row: CallableAggregateValue) =
        add row.Occurrence; add row.Aggregate; add row.Slot; addMany row.FormationInputs
        addOptional row.Value; addOptional row.Frontier; participants row.Participants
        row.Selector |> Option.iter (fun selector -> addOptional selector.Storage)
        row.Alternatives |> List.iter (fun alternative ->
            add alternative.Carrier; add alternative.Formation; add alternative.Contract
            addOptional alternative.EnvironmentValue; addOptional alternative.Adapter
            alternative.EnvironmentPlacement |> Option.iter (fun placement ->
                add placement.Value; add placement.Owner; addOptional placement.Adaptation))
        row.Tag |> Option.iter (fun tag ->
            add tag.Constructor; addOptional tag.TagRead; addOptional tag.Payload; participants tag.Participants)
    let flow (row: CallableFlow) =
        add row.Occurrence; addMany row.Alternatives
        row.Dependencies |> Map.iter (fun key values -> add key; addMany values)
        row.Calls |> List.iter (fun call -> add call.Call; add call.Implementation; addMany call.Parameters; addMany call.Arguments; add call.Result)
    let join (row: CallableJoin) =
        add row.Occurrence; add row.Storage; add row.Read; addMany row.Alternatives
    let aggregateAccount (row: CallableAggregateDependencyAccount) =
        add row.Occurrence
        List.iter aggregateSlot row.Slots; List.iter aggregateValue row.Values
        List.iter carrier row.Carriers; List.iter contract row.Contracts
        List.iter flow row.Flows; List.iter join row.Joins; participants row.Participants
        row.Sources |> List.iter (fun source -> add source.Node; addMany source.Children)
        row.Claims |> List.iter (fst >> add)
        row.Symbols |> List.iter (fun (implementation, name) ->
            add implementation
            match name with
            | CallableSymbolName.LocalBinding(id, _) | CallableSymbolName.Anonymous id -> add id
            | _ -> ())
    let slots values = values |> List.iter (fun (slot: ContinuationSlot) -> add slot.Source)
    let pairs values = values |> List.iter (fun (left, right) -> add left; add right)
    let family (row: SequenceFamily) =
        add row.Identity
        row.Members |> Map.iter (fun owner memberRow ->
            add owner; add memberRow.Generator; add memberRow.Formal; add memberRow.State
            addOptional memberRow.Current; slots memberRow.Slots
            addMany memberRow.Captures; addMany memberRow.Uninitialized)
    let facts = graph.Codata.Value
    let rec advance () =
        let before = ids
        let callableIds = Set.difference before metadata
        selected before emission.Ordinary.Parameters |> Map.iter (fun _ row -> addMany row)
        selected before emission.Ordinary.Calls |> Map.iter (fun _ row -> add row.Implementation; addMany row.Actuals)
        selected callableIds emission.Callable.Carriers |> Map.iter (fun _ row -> carrier row)
        selected callableIds emission.Callable.Contracts |> Map.iter (fun _ row -> contract row)
        selected callableIds emission.Callable.AggregateSlots |> Map.iter (fun _ row -> aggregateSlot row)
        selected callableIds emission.Callable.AggregateValues |> Map.iter (fun _ rows -> List.iter aggregateValue rows)
        selected callableIds emission.Callable.AggregateDependencies |> Map.iter (fun _ row -> aggregateAccount row)
        selected callableIds emission.Callable.Joins |> Map.iter (fun _ row -> join row)
        selected callableIds emission.Callable.Flows |> Map.iter (fun _ row -> flow row)
        selected callableIds emission.Callable.MutableStorage |> Map.iter (fun _ row ->
            add row.Binding
            let write (value: MutableCallableWrite) = add value.Site; add value.Destination; add value.Value
            write row.Initializer; List.iter write row.Writes; addMany row.Reads; addMany row.Alternatives
            List.iter carrier row.AlternativeCarriers; addMany row.Captures; addMany row.Borrows)
        selected callableIds emission.Callable.SignatureData |> Map.iter (fun _ row -> addMany row)
        selected callableIds emission.Callable.ValueShapes |> Map.iter (fun _ row -> shape row)
        selected callableIds emission.Callable.Calls |> Map.iter (fun _ row ->
            add row.Implementation; parameters row.Parameters; addMany row.Arguments; add row.Result; addMany row.SignatureData)
        selected callableIds emission.Callable.Transports |> Map.iter (fun _ row -> addMany row)
        selected callableIds emission.Callable.Declarations |> Map.iter (fun _ row ->
            add row.Lookup; add row.Implementation; parameters row.Parameters; add row.Result
            row.Captures |> List.iter (fun capture -> addOptional capture.SourceNodeId))
        selected callableIds emission.Callable.Symbols |> Map.iter (fun _ row ->
            match row with
            | CallableSymbolName.LocalBinding(id, _) | CallableSymbolName.Anonymous id -> add id
            | _ -> ())
        selected callableIds emission.Callable.DirectCallees |> Map.iter (fun _ row -> add row)
        selected callableIds emission.Callable.AliasTargets |> Map.iter (fun _ row -> add row)
        selected callableIds emission.Callable.Arguments |> Map.iter (fun _ row -> row.Keys |> addMany)
        selected callableIds emission.Callable.ProgramInstances |> Map.iter (fun _ row -> carrier row.Carrier; addOptional row.Allocation)
        selected before emission.Storage.Lazies |> Map.iter (fun _ row ->
            add row.Layout.Owner; add row.Layout.Thunk; add row.Layout.Formal
            add row.Layout.Computed; add row.Layout.Cached; slots row.Layout.Slots; add row.ThunkBody)
        selected before emission.Storage.LazyOccurrences |> Map.iter (fun _ row -> add row)
        selected before emission.Storage.LazyPrograms |> Map.iter (fun _ row -> add row.Owner; add row.Allocation)
        selected before emission.Storage.Sequences |> Map.iter (fun _ row -> addMany row.Flow.Owners; family row.Family)
        selected before emission.Storage.SequencePrograms |> Map.iter (fun _ row -> add row.Owner; add row.Generator; add row.Allocation)
        selected before emission.Storage.SequenceCopies |> Map.iter (fun _ row ->
            add row.Family; add row.Template; add row.SourceAcquisition; add row.StorageSite
            row.TemplateStorage |> Map.iter (fun key values -> add key; addMany values)
            row.Initializers |> Map.iter (fun key values -> add key; pairs values)
            row.UninitializedRegions |> Map.iter (fun key values -> add key; addMany values)
            row.Captures |> Map.iter (fun key values -> add key; addMany values)
            row.Uninitialized |> Map.iter (fun key values -> add key; addMany values))
        emission.Storage.Startup |> Option.iter (fun row ->
            if before.Contains row.EntryLambda || before.Contains row.EntryBinding || before.Contains row.Spine then
                add row.EntryBinding; add row.EntryLambda; add row.SourceBinding; add row.SourceLambda
                add row.OriginalBody; add row.Spine; add row.EntryCall; addMany row.ValueBindings
                row.Initializers |> List.iter (fun value -> add value.Module; add value.Binding; add value.Initializer))
        selected before emission.Storage.Requirements |> Map.iter (fun _ row ->
            add row.Condition; add row.Frontier; add row.Continuation; addOptional row.PatternTest)
        selected before emission.Storage.PatternRequirements |> Map.iter (fun _ row -> add row)
        selected before emission.Boundary.Calls |> Map.iter (fun _ row ->
            add row.Import; add row.Callee
            row.Arguments |> List.iter (fun value ->
                add value.Actual; add value.Formal
                match value.Abi with BoundaryScalar.Entry invocation -> add invocation | _ -> ()))
        selected before emission.Boundary.CallbackInvocations |> Map.iter (fun _ row ->
            add row.Import; add row.Formal; add row.Scope; addMany row.Participants
            match row.Extent with
            | BoundaryCallbackExtent.ProcessExit(Some anchor,_) ->
                emission.Boundary.Imports.Values |> Seq.filter(fun imported -> imported.Binding=anchor) |> Seq.iter(fun imported -> add imported.Identity)
            | _ -> ())
        selected before emission.Boundary.ClosedEntries |> Map.iter (fun _ row ->
            add row.Operand; add row.Declaration; add row.Implementation; addMany row.Formals; add row.Body
            add row.Lifetime.Module; add row.Lifetime.Binding; add row.Lifetime.Implementation
            add row.Invocation; addMany row.Transport; addMany row.Participants)
        selected before emission.Boundary.Imports |> Map.iter (fun _ row -> add row.Identity; add row.Binding; add row.Scope; row.Parameters |> List.iter (fst >> add))
        emission.Numeric.ForeignResultUses
        |> List.filter (fun account -> before.Contains account.Application.Call)
        |> List.iter (fun account ->
            add account.Application.Declaration; addMany account.Application.Context
            account.Application.Arguments |> List.iter (fun argument -> add argument.Node)
            account.Application.Hypothesis |> Option.iter (fun hypothesis -> add hypothesis.Quote; add hypothesis.Declaration)
            match account.Participants with
            | ParticipantEvidence.Established rows -> participants rows
            | ParticipantEvidence.Pending early -> participants early.Derived
            account.Claims |> List.iter (snd >> add))
        selected before emission.Boundary.IntrinsicWrites |> Map.iter (fun _ row -> add row.Import; add row.Callee; add row.Fd; add row.Buffer; add row.Count)
        selected before emission.Numeric.Operations |> Map.iter (fun _ row -> add row.Callee; row.Operands |> List.iter (fun value -> add value.Actual))
        selected before emission.Numeric.IndexTransports |> Map.iter (fun _ row -> add row.Operand)
        selected before emission.Numeric.OccurrenceRepresentations |> Map.iter (fun _ row ->
            match row with Ok value -> representation value | Error _ -> ())
        selected before facts.EnvironmentLayouts |> Map.iter (fun _ row -> add row.Owner; add row.Implementation; add row.Formal; slots row.Slots)
        selected before facts.KnownCallables |> Map.iter (fun _ row -> add row.Implementation; add row.EnvironmentOwner)
        selected before facts.ContinuationFrames |> Map.iter (fun _ row ->
            add row.Owner; add row.Generator; add row.Formal; add row.State; add row.Current
            slots row.Slots; slots row.ScratchSlots; pairs row.Initializers)
        selected before facts.SequenceFamilies |> Map.iter (fun _ row -> family row)
        [facts.EnvironmentDestinations; facts.EnvironmentOrigins; facts.LazyOrigins; facts.LazyDestinations
         facts.SequenceOrigins; facts.ContinuationStorage; facts.SequenceDestinations]
        |> List.iter (fun table -> selected before table |> Map.iter (fun _ value -> add value))
        selected before facts.SequenceInitializers |> Map.iter (fun _ row -> pairs row)
        selected before facts.ContinuationRegions |> Map.iter (fun _ row -> add row.ParentOwner; add row.ParentFormal; add row.ChildOwner)
        selected before facts.Curry.PartialApplications |> Map.iter (fun _ row -> add row.TargetBindingId; addMany row.SuppliedArgNodes)
        selected before facts.Curry.SaturatedCalls |> Map.iter (fun _ row -> add row.TargetBindingId; addMany row.AllArgNodes)
        selected before facts.FunctionPointers |> Map.iter (fun _ row ->
            match row with
            | FunctionPointerPlan.Address(_, lambda) -> add lambda
            | FunctionPointerPlan.Invoke(pointer, arguments, _, _) -> add pointer; addMany arguments
            | FunctionPointerPlan.ExternAddress formation -> add formation)
        if ids <> before then advance ()
    advance ()
    ids

/// Generic value facts are read by executable occurrences, callable signatures
/// and their explicit storage operands. A retained declaration/provenance ID
/// alone is not a value consumer: imports and spatial plans carry those facts
/// in their own typed accounts. Follow only the selected value contracts here.
let private valueFacts (graph: SemanticGraph) (emission: WitnessEmissionProjection) (scope: WitnessLiveScopePlan) ids =
    let callableIds = Set.difference ids (metadataDeclarations emission scope)
    let mutable values =
        scope.Occurrences |> Map.toSeq |> Seq.choose (fun (id, occurrence) ->
            match occurrence.Body.Kind with
            // These live declaration shells consume a settled spatial plan.
            // Their descriptor child is source metadata, not a runtime record
            // or an alias read. Actual ordinary uses retain their own roots.
            | SemanticKind.Binding(_, _, _, Some DeclRoot.HardwareModule)
            | SemanticKind.Binding(_, _, _, Some DeclRoot.KernelModule) -> None
            | _ -> Some id) |> Set.ofSeq
        |> Set.union (scope.BindingUses.Values |> Seq.map _.Binding |> Set.ofSeq)
    let add id = values <- values.Add id
    let addMany source = values <- Set.union values (Set.ofSeq source)
    let shape = function
        | CallableValueShape.Data id | CallableValueShape.Callable id
        | CallableValueShape.Sequence id | CallableValueShape.Lazy id -> add id
    let parameters source = source |> List.iter (fun (_, _, id) -> add id)
    let slots source = source |> List.iter (fun (slot: ContinuationSlot) -> add slot.Source)
    let carrier (row: CallableCarrier) =
        parameters row.Parameters; add row.Result
        Option.iter add row.EnvironmentValue
        List.iter shape row.ParameterShapes; shape row.ResultShape
        row.Environment |> Option.iter (fun environment -> add environment.Formal)
    let aggregateValue (row: CallableAggregateValue) =
        add row.Aggregate; addMany row.FormationInputs; Option.iter add row.Value
        row.Selector |> Option.iter (fun selector -> Option.iter add selector.Storage)
        row.Alternatives |> List.iter (fun alternative ->
            Option.iter add alternative.EnvironmentValue
            alternative.EnvironmentPlacement |> Option.iter (fun placement -> add placement.Value))
        row.Tag |> Option.iter (fun tag -> Option.iter add tag.TagRead; Option.iter add tag.Payload)
    selected ids emission.Ordinary.Parameters |> Map.iter (fun _ formals -> addMany formals)
    selected ids emission.Ordinary.Calls |> Map.iter (fun _ call -> addMany call.Actuals)
    selected callableIds emission.Callable.Carriers |> Map.iter (fun _ row -> carrier row)
    selected callableIds emission.Callable.AggregateValues |> Map.iter (fun _ rows -> List.iter aggregateValue rows)
    selected callableIds emission.Callable.AggregateDependencies |> Map.iter (fun _ account ->
        List.iter aggregateValue account.Values; List.iter carrier account.Carriers)
    selected callableIds emission.Callable.SignatureData |> Map.iter (fun _ data -> addMany data)
    selected callableIds emission.Callable.Declarations |> Map.iter (fun _ row ->
        parameters row.Parameters; add row.Result
        row.Captures |> List.iter (fun capture -> Option.iter add capture.SourceNodeId))
    selected callableIds emission.Callable.Calls |> Map.iter (fun _ row ->
        parameters row.Parameters; add row.Result; addMany row.Arguments; addMany row.SignatureData)
    selected callableIds emission.Callable.Arguments |> Map.iter (fun _ row -> addMany row.Keys)
    selected callableIds emission.Callable.Transports |> Map.iter (fun _ row -> addMany row)
    selected callableIds emission.Callable.ProgramInstances |> Map.iter (fun _ row -> carrier row.Carrier)
    selected callableIds emission.Callable.Joins |> Map.iter (fun _ row -> add row.Storage; add row.Read; addMany row.Alternatives)
    selected callableIds emission.Callable.Flows |> Map.iter (fun _ row ->
        addMany row.Alternatives
        row.Calls |> List.iter (fun call -> addMany call.Parameters; addMany call.Arguments; add call.Result))
    selected callableIds emission.Callable.MutableStorage |> Map.iter (fun _ row ->
        let write (value: MutableCallableWrite) = add value.Site; add value.Destination; add value.Value
        add row.Binding; write row.Initializer; List.iter write row.Writes; addMany row.Reads
        List.iter carrier row.AlternativeCarriers; addMany row.Captures; addMany row.Borrows)
    selected ids emission.Storage.Lazies |> Map.iter (fun _ row ->
        add row.Layout.Formal; add row.Layout.Computed; add row.Layout.Cached; slots row.Layout.Slots)
    selected ids emission.Storage.Sequences |> Map.iter (fun _ row ->
        row.Family.Members |> Map.iter (fun _ memberRow ->
            add memberRow.Formal; add memberRow.State; Option.iter add memberRow.Current; slots memberRow.Slots
            addMany memberRow.Captures; addMany memberRow.Uninitialized))
    selected ids graph.Codata.Value.EnvironmentLayouts |> Map.iter (fun _ row -> add row.Formal; slots row.Slots)
    selected ids graph.Codata.Value.ContinuationFrames |> Map.iter (fun _ row ->
        add row.Formal; add row.State; add row.Current; slots row.Slots; slots row.ScratchSlots
        row.Initializers |> List.iter (fun (destination, source) -> add destination; add source))
    selected ids emission.Boundary.Imports |> Map.iter (fun _ row -> addMany row.SourceTypes.Keys)
    selected ids emission.Boundary.Calls |> Map.iter (fun _ row ->
        row.Arguments |> List.iter (fun argument -> add argument.Actual; add argument.Formal))
    // A module used as a source boundary can carry its exact unit convention
    // without a body. No declaration child or metadata descriptor is included.
    scope.ContextHeaders.Keys |> Seq.filter (fun id -> ids.Contains id && emission.Callable.UnitNodes.Contains id) |> addMany
    let rec references () =
        let before = values
        selected before emission.Callable.ValueShapes |> Map.iter (fun _ row -> shape row)
        selected before emission.Callable.AliasTargets |> Map.iter (fun _ target -> add target)
        if values <> before then references ()
    references ()
    values

let private closeTypes (graph: SemanticGraph) ids valueIds (emission: WitnessEmissionProjection) =
    let rec visit seen identity =
        if seen |> Set.contains identity then seen else
        let seen = Set.add identity seen
        let children =
            match identity with
            | TypeIdentity.Application(_, values) | TypeIdentity.Tuple(_, values) -> values
            | TypeIdentity.Function(left, right) | TypeIdentity.Map(left, right) -> [left; right]
            | TypeIdentity.AnonymousRecord(_, fields) -> List.map snd fields
            | TypeIdentity.Union(_, cases) -> cases |> List.collect (fun (_, _, fields) -> List.map snd fields)
            | TypeIdentity.Forall(_, value) | TypeIdentity.Byref(_, value) | TypeIdentity.NativePointer value
            | TypeIdentity.Lazy value | TypeIdentity.Sequence value | TypeIdentity.Enumerator value
            | TypeIdentity.List value | TypeIdentity.Set value -> [value]
            | _ -> []
        List.fold visit seen children
    let identities =
        selected valueIds graph.Nodes |> Map.toSeq |> Seq.map (fun (_, node) -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type)
        |> Seq.append (selected valueIds emission.Numeric.SourceTypes |> Map.values)
        |> Seq.append (selected valueIds emission.Numeric.Values |> Map.values |> Seq.map _.SourceType)
        |> Seq.append (selected valueIds emission.Boundary.Imports |> Map.values |> Seq.collect (fun row -> row.SourceTypes.Values))
        |> Seq.append (selected ids emission.Callable.Contracts |> Map.values |> Seq.collect (fun row -> row.ResultType :: row.ParameterTypes))
        |> Seq.append (selected ids emission.Callable.AggregateSlots |> Map.values |> Seq.collect (fun row -> [row.AggregateType; row.SourceType]))
        |> Seq.append (selected ids emission.Callable.AggregateDependencies |> Map.values |> Seq.collect (fun account ->
            seq {
                for row in account.Contracts do yield row.ResultType; yield! row.ParameterTypes
                for row in account.Slots do yield row.AggregateType; yield row.SourceType
                for row in account.Sources do yield row.Type
            }))
    Seq.fold visit Set.empty identities

let private emissionRows ids valueIds types metadata (value: WitnessEmissionProjection) : WitnessEmissionProjection =
    let rows table = selected ids table
    let values entries = selectedSet ids entries
    let valueRows table = selected valueIds table
    let typeRows table = table |> Map.filter (fun key _ -> Set.contains key types)
    let callables = value.Callable
    let callableRows table = selected (Set.difference ids metadata) table
    let callableValueRows table = selected (Set.difference valueIds metadata) table
    let callableValues entries = selectedSet (Set.difference ids metadata) entries
    let callableValueSet entries = selectedSet (Set.difference valueIds metadata) entries
    let storage = value.Storage
    let boundary = value.Boundary
    let numeric = value.Numeric
    // A current source occurrence selects its complete account as facts. Its
    // retained descriptor, arguments and citizens do not demand new bodies.
    let foreignUses = numeric.ForeignResultUses |> List.filter (fun account -> ids.Contains account.Application.Call)
    let foreignDeclarations = foreignUses |> List.map (fun account -> account.Application.Declaration) |> Set.ofList
    let resultHypotheses = boundary.ResultHypotheses |> List.filter (fun hypothesis -> foreignDeclarations.Contains hypothesis.Declaration)
    let imports = rows boundary.Imports
    let startup = storage.Startup |> Option.filter (fun row -> ids |> Set.contains row.EntryLambda)
    let inactivityIds =
        rows callables.AggregateDependencies |> Map.values
        |> Seq.collect (fun account -> account.Inactivity |> List.map fst)
        |> Set.ofSeq |> Set.union ids
    { Ordinary = { Parameters = rows value.Ordinary.Parameters; Calls = rows value.Ordinary.Calls
                   DeferredOnly = values value.Ordinary.DeferredOnly
                   // Source premises carry dormant support; retaining this
                   // consumed proof does not make that support executable.
                   Inactivity = value.Ordinary.Inactivity |> Map.filter (fun implementation proof ->
                       inactivityIds.Contains implementation ||
                       (proof.Parameters |> List.exists ids.Contains) ||
                       (proof.Excluded |> Set.exists ids.Contains) ||
                       (proof.Calls |> Set.exists ids.Contains)) }
      Callable = {
        Branches = branches ids callables.Branches
        Contracts = callableRows callables.Contracts
        Carriers = callableRows callables.Carriers; Joins = callableRows callables.Joins; Flows = callableRows callables.Flows
        AggregateSlots = callableRows callables.AggregateSlots; AggregateValues = callableRows callables.AggregateValues
        AggregateDependencies = callableRows callables.AggregateDependencies
        MutableStorage = callableRows callables.MutableStorage; ValueShapes = callableValueRows callables.ValueShapes
        SignatureData = callableRows callables.SignatureData; Calls = callableRows callables.Calls; Transports = callableRows callables.Transports
        Declarations = callableRows callables.Declarations; Symbols = callableRows callables.Symbols
        IntrinsicAliases = callableValues callables.IntrinsicAliases; DirectCallees = callableRows callables.DirectCallees
        ForeignCalls = callableValues callables.ForeignCalls; MutableRetentions = callableValues callables.MutableRetentions
        ProgramInstances = callableRows callables.ProgramInstances; VoidCallbacks = callableValues callables.VoidCallbacks
        VoidPointers = callableValues callables.VoidPointers; NativeEntries = callableRows callables.NativeEntries
        FunctionBindings = callableValues callables.FunctionBindings; DefinitionOnlyBindings = callableValues callables.DefinitionOnlyBindings
        DefinitionOnlyLambdas = callableValues callables.DefinitionOnlyLambdas; Arguments = callableRows callables.Arguments
        AliasTargets = callableValueRows callables.AliasTargets; TakesEnvironment = callableValues callables.TakesEnvironment
        UnitNodes = callableValueSet callables.UnitNodes; ClosedData = callableValueSet callables.ClosedData; Supports = callableValueRows callables.Supports }
      Storage = { Lazies = rows storage.Lazies; LazyOccurrences = rows storage.LazyOccurrences
                  LazyValues = values storage.LazyValues; DefinitionOnlyThunks = values storage.DefinitionOnlyThunks
                  LazyPrograms = rows storage.LazyPrograms; Sequences = rows storage.Sequences; SequenceCopies = rows storage.SequenceCopies
                  SequencePrograms = rows storage.SequencePrograms; Startup = startup; SlotAuthorities = values storage.SlotAuthorities
                  Requirements = rows storage.Requirements; PatternRequirements = rows storage.PatternRequirements
                  ProgramStorage = programStorage ids storage.ProgramStorage; LiteralPoolAnchors = storage.LiteralPoolAnchors
                  // Every proposal for a demanded allocation survives, including
                  // refused proposals. Premise identities do not demand bodies.
                  EnvironmentReservations = storage.EnvironmentReservations |> Map.filter (fun _ row -> ids.Contains row.Allocation)
                  EnvironmentFactoryResults = rows storage.EnvironmentFactoryResults
                  EnvironmentResidences = rows storage.EnvironmentResidences
                  ProgramInitializationOrders = rows storage.ProgramInitializationOrders }
      // Project the issued loading account whenever retained native-entry/callback
      // incidence still needs it; this projection never creates loading authority.
      Boundary = { WritableBufferDeclarations = boundary.WritableBufferDeclarations; WritableBufferUses = boundary.WritableBufferUses |> Map.filter(fun (site,_) _->ids.Contains site); ResourceEvidence = boundary.ResourceEvidence; ResourceDeclarations = boundary.ResourceDeclarations; ResourceAccesses = rows boundary.ResourceAccesses; Imports = imports; Loading = if (rows boundary.Entries).IsEmpty && (rows boundary.ClosedEntries).IsEmpty && (rows boundary.CallbackInvocations).IsEmpty && (imports.Values |> Seq.forall (fun import -> import.Library = "c")) then None else boundary.Loading
                   Entries = rows boundary.Entries; CallbackInvocations = rows boundary.CallbackInvocations; ClosedEntries = rows boundary.ClosedEntries; ResultHypotheses = resultHypotheses
                   ByScope = boundary.ByScope |> Map.map (fun _ entries -> entries |> List.filter imports.ContainsKey) |> Map.filter (fun _ entries -> not entries.IsEmpty)
                   Calls = rows boundary.Calls; ByteViews = rows boundary.ByteViews; StringExtents = rows boundary.StringExtents
                   IntrinsicWriteImports = rows boundary.IntrinsicWriteImports; IntrinsicWrites = rows boundary.IntrinsicWrites
                   IntrinsicWriteProofs = rows boundary.IntrinsicWriteProofs; DeclarationLeaves = values boundary.DeclarationLeaves
                   DeclarationOnly = values boundary.DeclarationOnly
                   Links = imports.Values |> Seq.map _.Library |> Set.ofSeq }
      Numeric = { Values = valueRows numeric.Values; ForeignResultUses = foreignUses; Operations = rows numeric.Operations; OperationRequired = values numeric.OperationRequired
                  IndexTransports = rows numeric.IndexTransports; Required = values numeric.Required; ResultSites = values numeric.ResultSites
                  Unresolved = rows numeric.Unresolved; SourceTypes = valueRows numeric.SourceTypes; Layouts = typeRows numeric.Layouts
                  Elements = rows numeric.Elements; ElementTypes = typeRows numeric.ElementTypes; DeclaredScalars = numeric.DeclaredScalars
                  OccurrenceRepresentations = valueRows numeric.OccurrenceRepresentations; TypeRepresentations = typeRows numeric.TypeRepresentations }
      Memory = { Operations = rows value.Memory.Operations; ArrayCopies = rows value.Memory.ArrayCopies
                 Required = values value.Memory.Required; Unresolved = rows value.Memory.Unresolved }
      Spatial = { Hardware = rows value.Spatial.Hardware; Kernels = rows value.Spatial.Kernels
                  Required = values value.Spatial.Required; MetadataOnly = values value.Spatial.MetadataOnly
                  ByScope = value.Spatial.ByScope |> Map.map (fun _ entries -> List.filter (fun id -> ids.Contains id) entries) |> Map.filter (fun _ entries -> not entries.IsEmpty)
                  CodeRoots = values value.Spatial.CodeRoots } }

let project (graph: SemanticGraph) (emission: WitnessEmissionProjection) (scope: WitnessLiveScopePlan)
            (prepared: WitnessPreparedRows) (segmentation: WitnessSegmentation) : WitnessLiveRows =
    let ids = closeFacts graph emission scope
    let valueIds = valueFacts graph emission scope ids
    let ids = Set.union ids valueIds
    let types = closeTypes graph ids valueIds emission
    let selectedEmission = emissionRows ids valueIds types (metadataDeclarations emission scope) emission
    let rows table = selected ids table
    let values entries = selectedSet ids entries
    let facts = graph.Codata.Value
    let live = scope.Occurrences.Keys |> Set.ofSeq
    let eager = scope.Occurrences |> Map.toSeq |> Seq.choose (fun (id, occurrence) ->
        match occurrence.Body.Kind with SemanticKind.EagerExpr _ -> Some id | _ -> None) |> Set.ofSeq
    // Common support is a source owner account, not a retained-node census.
    // Its authority is carried by the source scope's WholePreparedOwner stamp.
    let selectedSegmentation =
        { segmentation with
            Regions =
                segmentation.Regions |> List.map (fun region ->
                    { region with Members = Set.intersect live region.Members
                                  Supports = Set.intersect ids region.Supports }) }
    let codata : WitnessLiveCodata = {
        WitnessSegmentation = Some selectedSegmentation
        // Allocation residence is consumed at an actual executable allocation
        // occurrence. Imported descriptor/design metadata may have a retained
        // type or correspondence identity without allocating at runtime.
        // Preserve the complete private analysis while delivering only these
        // live residence consequences; an absent live fact remains an error.
        Escapes = selected live facts.Escapes
        Curry = { PartialApplications = rows facts.Curry.PartialApplications; SaturatedCalls = rows facts.Curry.SaturatedCalls
                  PartialAppBindings = values facts.Curry.PartialAppBindings; AbsorbedLambdas = values facts.Curry.AbsorbedLambdas }
        Meets = rows facts.Meets; ReturnMeets = rows facts.ReturnMeets; Closures = rows facts.Closures
        EnvironmentLayouts = rows facts.EnvironmentLayouts; EnvironmentDestinations = rows facts.EnvironmentDestinations
        EnvironmentOrigins = rows facts.EnvironmentOrigins; LazyLayouts = rows facts.LazyLayouts
        LazyOrigins = rows facts.LazyOrigins; LazyDestinations = rows facts.LazyDestinations
        KnownCallables = rows facts.KnownCallables; CallableCarriers = rows facts.CallableCarriers
        CallableContracts = rows facts.CallableContracts
        CallableJoins = rows facts.CallableJoins; CallableFlows = rows facts.CallableFlows
        CallableAggregateSlots = rows facts.CallableAggregateSlots; CallableAggregateValues = rows facts.CallableAggregateValues
        CallableAggregateDependencies = rows facts.CallableAggregateDependencies
        CallableBranches = selectedEmission.Callable.Branches; MutableCallableStorage = rows facts.MutableCallableStorage
        ContinuationFrames = rows facts.ContinuationFrames; SequenceOrigins = rows facts.SequenceOrigins
        SequenceFlows = rows facts.SequenceFlows; SequenceFamilies = rows facts.SequenceFamilies
        SequenceTemplateCopies = rows facts.SequenceTemplateCopies; ContinuationStorage = rows facts.ContinuationStorage
        ContinuationRegions = rows facts.ContinuationRegions; SequenceInitializers = rows facts.SequenceInitializers
        SequenceDestinations = rows facts.SequenceDestinations; SequenceCurrentReads = values facts.SequenceCurrentReads
        Pins = if selectedEmission.Spatial.Hardware.IsEmpty then None else facts.Pins
        DeclarationRootLambdas = rows facts.DeclarationRootLambdas; FunctionPointers = rows facts.FunctionPointers
        Mmio = rows facts.Mmio; ProgramStorage = programStorage ids facts.ProgramStorage }
    { FactIdentities = ids; TypeIdentities = types; Codata = codata; Emission = selectedEmission
      Foreign = { BorrowedViews = rows prepared.Foreign.BorrowedViews; Mmio = rows prepared.Foreign.Mmio; MappedCalls = values prepared.Foreign.MappedCalls }
      // Explicit eager demand belongs only to a live marker occurrence. A
      // declaration's retained identity does not activate its old demand edge.
      Demand = { Operands = selected eager prepared.Demand.Operands; Relations = selected eager prepared.Demand.Relations }
      // PHG emission reads saturated facts, not the owner's analytical F.
      // Complete relations remain in prepared.Edges for Baker revalidation.
      Edges = []
      DeclarationRoots = graph.DeclarationRoots |> List.filter (fun (id, _) -> live.Contains id)
      ModuleClassifications =
        graph.ModuleClassifications.Value
        |> Map.filter (fun id _ -> scope.ContextHeaders.ContainsKey id || live.Contains id)
        |> Map.map (fun _ row ->
            { row with ModuleInit = List.filter live.Contains row.ModuleInit
                       Definitions = List.filter live.Contains row.Definitions
                       DeclarationRoot = row.DeclarationRoot |> Option.filter (fst >> live.Contains) })
      StaticStringPool = graph.StaticStringPool |> Option.map (fun pool ->
        { pool with Entries = pool.Entries |> List.map (fun entry -> { entry with NodeIds = List.filter live.Contains entry.NodeIds }) })
      LiteralStorage = selected live graph.LiteralStorage }

let matches (held: WitnessLiveRows) (current: WitnessLiveRows) =
    let edge (row: Hyperedge) = row.Class, row.Role, row.Sources, row.Target, row.Ordinal
    held.FactIdentities = current.FactIdentities && held.TypeIdentities = current.TypeIdentities &&
    held.Codata = current.Codata && held.Emission = current.Emission &&
    held.Foreign = current.Foreign && held.Demand = current.Demand &&
    List.map edge held.Edges = List.map edge current.Edges &&
    held.DeclarationRoots = current.DeclarationRoots && held.ModuleClassifications = current.ModuleClassifications &&
    held.StaticStringPool = current.StaticStringPool && held.LiteralStorage = current.LiteralStorage

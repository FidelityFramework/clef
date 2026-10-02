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

/// Only typed executable/fact references advance this closure. Participants,
/// obligation support inventories and owner-wide membership/absence accounts
/// remain complete fields in their selected rows; they never select more rows.
let private closeFacts (graph: SemanticGraph) (emission: WitnessEmissionProjection) (scope: WitnessLiveScopePlan) =
    let mutable ids =
        scope.Occurrences.Keys |> Set.ofSeq
        |> Set.union (scope.BindingUses.Values |> Seq.map _.Binding |> Set.ofSeq)
        |> Set.union (scope.Entries |> Seq.map _.Focus |> Set.ofSeq)
    let add id = ids <- ids.Add id
    let addMany values = ids <- Set.union ids (Set.ofSeq values)
    let addOptional value = Option.iter add value
    let shape = function
        | CallableValueShape.Data id | CallableValueShape.Callable id
        | CallableValueShape.Sequence id | CallableValueShape.Lazy id -> add id
    let parameters values = values |> List.iter (fun (_, _, id) -> add id)
    let carrier (row: CallableCarrier) =
        add row.Implementation; parameters row.Parameters; add row.Result
        List.iter shape row.ParameterShapes; shape row.ResultShape
        row.Environment |> Option.iter (fun value -> add value.Owner; add value.Formal)
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
        selected before emission.Ordinary.Parameters |> Map.iter (fun _ row -> addMany row)
        selected before emission.Ordinary.Calls |> Map.iter (fun _ row -> add row.Implementation; addMany row.Actuals)
        selected before emission.Callable.Carriers |> Map.iter (fun _ row -> carrier row)
        selected before emission.Callable.Joins |> Map.iter (fun _ row -> add row.Storage; add row.Read; addMany row.Alternatives)
        selected before emission.Callable.Flows |> Map.iter (fun _ row ->
            addMany row.Alternatives
            row.Dependencies |> Map.iter (fun key values -> add key; addMany values)
            row.Calls |> List.iter (fun call -> add call.Call; add call.Implementation; addMany call.Parameters; addMany call.Arguments; add call.Result))
        selected before emission.Callable.MutableStorage |> Map.iter (fun _ row ->
            add row.Binding
            let write (value: MutableCallableWrite) = add value.Site; add value.Destination; add value.Value
            write row.Initializer; List.iter write row.Writes; addMany row.Reads; addMany row.Alternatives
            List.iter carrier row.AlternativeCarriers; addMany row.Captures; addMany row.Borrows)
        selected before emission.Callable.SignatureData |> Map.iter (fun _ row -> addMany row)
        selected before emission.Callable.ValueShapes |> Map.iter (fun _ row -> shape row)
        selected before emission.Callable.Calls |> Map.iter (fun _ row ->
            add row.Implementation; parameters row.Parameters; addMany row.Arguments; add row.Result; addMany row.SignatureData)
        selected before emission.Callable.Transports |> Map.iter (fun _ row -> addMany row)
        selected before emission.Callable.Declarations |> Map.iter (fun _ row ->
            add row.Lookup; add row.Implementation; parameters row.Parameters; add row.Result
            row.Captures |> List.iter (fun capture -> addOptional capture.SourceNodeId))
        selected before emission.Callable.Symbols |> Map.iter (fun _ row ->
            match row with
            | CallableSymbolName.LocalBinding(id, _) | CallableSymbolName.Anonymous id -> add id
            | _ -> ())
        selected before emission.Callable.DirectCallees |> Map.iter (fun _ row -> add row)
        selected before emission.Callable.AliasTargets |> Map.iter (fun _ row -> add row)
        selected before emission.Callable.Arguments |> Map.iter (fun _ row -> row.Keys |> addMany)
        selected before emission.Callable.ProgramInstances |> Map.iter (fun _ row -> carrier row.Carrier; addOptional row.Allocation)
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
            row.Arguments |> List.iter (fun value -> add value.Actual; add value.Formal))
        selected before emission.Boundary.Imports |> Map.iter (fun _ row -> add row.Identity; add row.Binding; add row.Scope; row.Parameters |> List.iter (fst >> add))
        selected before emission.Boundary.IntrinsicWrites |> Map.iter (fun _ row -> add row.Import; add row.Callee; add row.Fd; add row.Buffer; add row.Count)
        selected before emission.Numeric.Operations |> Map.iter (fun _ row -> add row.Callee; row.Operands |> List.iter (fun value -> add value.Actual))
        selected before emission.Numeric.IndexTransports |> Map.iter (fun _ row -> add row.Operand)
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
            match row with FunctionPointerPlan.Address(_, lambda) -> add lambda | FunctionPointerPlan.Invoke(pointer, arguments, _, _) -> add pointer; addMany arguments)
        if ids <> before then advance ()
    advance ()
    ids

let private closeTypes (graph: SemanticGraph) ids (emission: WitnessEmissionProjection) =
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
        selected ids graph.Nodes |> Map.toSeq |> Seq.map (fun (_, node) -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type)
        |> Seq.append (selected ids emission.Numeric.SourceTypes |> Map.values)
        |> Seq.append (selected ids emission.Numeric.Values |> Map.values |> Seq.map _.SourceType)
        |> Seq.append (selected ids emission.Boundary.Imports |> Map.values |> Seq.collect (fun row -> row.SourceTypes.Values))
    Seq.fold visit Set.empty identities

let private emissionRows ids types (value: WitnessEmissionProjection) : WitnessEmissionProjection =
    let rows table = selected ids table
    let values entries = selectedSet ids entries
    let typeRows table = table |> Map.filter (fun key _ -> Set.contains key types)
    let callables = value.Callable
    let storage = value.Storage
    let boundary = value.Boundary
    let numeric = value.Numeric
    let imports = rows boundary.Imports
    let startup = storage.Startup |> Option.filter (fun row -> ids |> Set.contains row.EntryLambda)
    { Ordinary = { Parameters = rows value.Ordinary.Parameters; Calls = rows value.Ordinary.Calls; DeferredOnly = values value.Ordinary.DeferredOnly }
      Callable = {
        Branches = branches ids callables.Branches
        Carriers = rows callables.Carriers; Joins = rows callables.Joins; Flows = rows callables.Flows
        MutableStorage = rows callables.MutableStorage; ValueShapes = rows callables.ValueShapes
        SignatureData = rows callables.SignatureData; Calls = rows callables.Calls; Transports = rows callables.Transports
        Declarations = rows callables.Declarations; Symbols = rows callables.Symbols
        IntrinsicAliases = values callables.IntrinsicAliases; DirectCallees = rows callables.DirectCallees
        ForeignCalls = values callables.ForeignCalls; MutableRetentions = values callables.MutableRetentions
        ProgramInstances = rows callables.ProgramInstances; VoidCallbacks = values callables.VoidCallbacks
        VoidPointers = values callables.VoidPointers; NativeEntries = rows callables.NativeEntries
        FunctionBindings = values callables.FunctionBindings; DefinitionOnlyBindings = values callables.DefinitionOnlyBindings
        DefinitionOnlyLambdas = values callables.DefinitionOnlyLambdas; Arguments = rows callables.Arguments
        AliasTargets = rows callables.AliasTargets; TakesEnvironment = values callables.TakesEnvironment
        UnitNodes = values callables.UnitNodes; ClosedData = values callables.ClosedData; Supports = rows callables.Supports }
      Storage = { Lazies = rows storage.Lazies; LazyOccurrences = rows storage.LazyOccurrences
                  LazyValues = values storage.LazyValues; DefinitionOnlyThunks = values storage.DefinitionOnlyThunks
                  LazyPrograms = rows storage.LazyPrograms; Sequences = rows storage.Sequences; SequenceCopies = rows storage.SequenceCopies
                  SequencePrograms = rows storage.SequencePrograms; Startup = startup; SlotAuthorities = values storage.SlotAuthorities
                  Requirements = rows storage.Requirements; PatternRequirements = rows storage.PatternRequirements
                  ProgramStorage = programStorage ids storage.ProgramStorage; LiteralPoolAnchors = storage.LiteralPoolAnchors }
      Boundary = { Imports = imports
                   ByScope = boundary.ByScope |> Map.map (fun _ entries -> entries |> List.filter imports.ContainsKey) |> Map.filter (fun _ entries -> not entries.IsEmpty)
                   Calls = rows boundary.Calls; ByteViews = rows boundary.ByteViews; StringExtents = rows boundary.StringExtents
                   IntrinsicWriteImports = rows boundary.IntrinsicWriteImports; IntrinsicWrites = rows boundary.IntrinsicWrites
                   IntrinsicWriteProofs = rows boundary.IntrinsicWriteProofs; DeclarationLeaves = values boundary.DeclarationLeaves
                   DeclarationOnly = values boundary.DeclarationOnly
                   Links = imports.Values |> Seq.map _.Library |> Set.ofSeq }
      Numeric = { Values = rows numeric.Values; Operations = rows numeric.Operations; OperationRequired = values numeric.OperationRequired
                  IndexTransports = rows numeric.IndexTransports; Required = values numeric.Required; ResultSites = values numeric.ResultSites
                  Unresolved = rows numeric.Unresolved; SourceTypes = rows numeric.SourceTypes; Layouts = typeRows numeric.Layouts
                  Elements = rows numeric.Elements; ElementTypes = typeRows numeric.ElementTypes; DeclaredScalars = numeric.DeclaredScalars
                  OccurrenceRepresentations = rows numeric.OccurrenceRepresentations; TypeRepresentations = typeRows numeric.TypeRepresentations }
      Memory = { Operations = rows value.Memory.Operations; ArrayCopies = rows value.Memory.ArrayCopies
                 Required = values value.Memory.Required; Unresolved = rows value.Memory.Unresolved }
      Spatial = { Hardware = rows value.Spatial.Hardware; Kernels = rows value.Spatial.Kernels
                  Required = values value.Spatial.Required; MetadataOnly = values value.Spatial.MetadataOnly
                  ByScope = value.Spatial.ByScope |> Map.map (fun _ entries -> List.filter (fun id -> ids.Contains id) entries) |> Map.filter (fun _ entries -> not entries.IsEmpty)
                  CodeRoots = values value.Spatial.CodeRoots } }

let project (graph: SemanticGraph) (emission: WitnessEmissionProjection) (scope: WitnessLiveScopePlan)
            (prepared: WitnessPreparedRows) (segmentation: WitnessSegmentation) : WitnessLiveRows =
    let ids = closeFacts graph emission scope
    let types = closeTypes graph ids emission
    let selectedEmission = emissionRows ids types emission
    let rows table = selected ids table
    let values entries = selectedSet ids entries
    let facts = graph.Codata.Value
    let live = scope.Occurrences.Keys |> Set.ofSeq
    // Common support is a source owner account, not a retained-node census.
    // Its authority is carried by the source scope's WholePreparedOwner stamp.
    let selectedSegmentation =
        { segmentation with Regions = segmentation.Regions |> List.map (fun region ->
            { region with Members = Set.intersect live region.Members
                          Supports = Set.intersect ids region.Supports }) }
    let codata : WitnessLiveCodata = {
        WitnessSegmentation = Some selectedSegmentation
        Escapes = rows facts.Escapes
        Curry = { PartialApplications = rows facts.Curry.PartialApplications; SaturatedCalls = rows facts.Curry.SaturatedCalls
                  PartialAppBindings = values facts.Curry.PartialAppBindings; AbsorbedLambdas = values facts.Curry.AbsorbedLambdas }
        Meets = rows facts.Meets; ReturnMeets = rows facts.ReturnMeets; Closures = rows facts.Closures
        EnvironmentLayouts = rows facts.EnvironmentLayouts; EnvironmentDestinations = rows facts.EnvironmentDestinations
        EnvironmentOrigins = rows facts.EnvironmentOrigins; LazyLayouts = rows facts.LazyLayouts
        LazyOrigins = rows facts.LazyOrigins; LazyDestinations = rows facts.LazyDestinations
        KnownCallables = rows facts.KnownCallables; CallableCarriers = rows facts.CallableCarriers
        CallableJoins = rows facts.CallableJoins; CallableFlows = rows facts.CallableFlows
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
      Demand = { Operands = rows prepared.Demand.Operands; Relations = rows prepared.Demand.Relations }
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

let matches (held: WitnessLiveRows) (current: WitnessLiveRows) = held = current

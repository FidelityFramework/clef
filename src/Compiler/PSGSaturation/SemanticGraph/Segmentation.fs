// SPDX-License-Identifier: MIT
/// Baker's dependency plan. This is source scheduling evidence, never a PSG revision.
module Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation

open System
open System.Collections
open System.Reflection
open Microsoft.FSharp.Reflection
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

[<RequireQualifiedAccess>]
type DependencyKind = Call | Storage | CapturedEnvironment | ProofSupport

type RegionDependency = { Consumer: string; Provider: string; Kind: DependencyKind; SupportNodes: Set<NodeId> }
type SupportEdge = { Consumer: string; Domain: string; Identity: string; Providers: Set<string>; SupportNodes: Set<NodeId>; Fingerprint: string }

type Region =
    { Identity: string
      Root: NodeId
      Members: Set<NodeId>
      CallableInterfaceDigest: CallableInterfaceDigest
      SemanticRealizationDigest: SemanticRealizationDigest
      CanonicalProofSupportDigest: CanonicalProofSupportDigest }

[<RequireQualifiedAccess>]
type SegmentationFailure =
    | InvalidGraph of NodeId option * string
    | AmbiguousIdentity of string
    | UnresolvedCallable of NodeId * NodeId
    | BrokenEnvironment of NodeId * string
    | UnsupportedInput of string

type SegmentationPlan =
    { Regions: Map<string, Region>
      Dependencies: RegionDependency list
      SupportEdges: SupportEdge list
      NodeIdentities: Map<NodeId, string>
      CallableRelationIdentities: Map<NodeId, string>
      NodeOwners: Map<NodeId, string>
      NodeFingerprints: Map<NodeId, string> }

let regions plan = plan.Regions |> Map.values |> Seq.toList
let dependencies identity plan = plan.Dependencies |> List.filter (fun edge -> edge.Consumer = identity)
let supportEdges identity plan = plan.SupportEdges |> List.filter (fun edge -> edge.Consumer = identity)
let internal hash (text: string) = WitnessSegmentation.hash text
let private flags = BindingFlags.Public ||| BindingFlags.NonPublic
let private property (ty: Type) name =
    ty.GetProperty name |> Option.ofObj |> Option.defaultWith (fun () -> invalidOp ("Missing source row field " + name))

/// Inspect source rows only; NativeType is frozen by the shared witness encoder.
let rec private references (value: objnull) : Set<NodeId> =
    match value with
    | null -> Set.empty
    | :? NodeId as id -> Set.singleton id
    | :? NativeType | :? SourceRange | :? string -> Set.empty
    | :? IEnumerable as items -> items |> Seq.cast<objnull> |> Seq.map references |> Set.unionMany
    | _ ->
        let value = value |> Option.ofObj |> Option.get
        let ty = value.GetType()
        let values =
            if FSharpType.IsTuple ty then FSharpValue.GetTupleFields value
            elif FSharpType.IsRecord(ty, flags) then FSharpValue.GetRecordFields(value, flags)
            elif FSharpType.IsUnion(ty, flags) then FSharpValue.GetUnionFields(value, ty, flags) |> snd
            elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<Collections.Generic.KeyValuePair<_, _>> then
                [| (property ty "Key").GetValue value; (property ty "Value").GetValue value |]
            else [||]
        values |> Seq.map references |> Set.unionMany

let private rowAnchor (value: objnull) =
    match value with
    | null -> None
    | :? NodeId as id -> Some id
    | _ ->
        let value = value |> Option.ofObj |> Option.get
        let ty = value.GetType()
        let head =
            if FSharpType.IsTuple ty then FSharpValue.GetTupleFields value |> Array.tryHead
            else
                ["Site"; "Owner"; "Binding"; "Call"] |> List.tryPick (fun name ->
                    ty.GetProperty name |> Option.ofObj |> Option.map (fun field -> field.GetValue value))
        head |> Option.bind (function :? NodeId as id -> Some id | _ -> None)

/// True when `id` is an immutable, non-inline callable function declaration root
/// whose callers depend on its CallableInterfaceDigest rather than its internal body.
let internal isCallableBoundary (graph: SemanticGraph) (id: NodeId) : bool =
    match graph.Nodes.TryFind id with
    | Some ({ Kind = SemanticKind.Binding(_, false, _, declRoot); Children = [ lambdaId ] } as binding)
        when declRoot <> Some DeclRoot.HardwareModule &&
             declRoot <> Some DeclRoot.KernelModule &&
             Map.tryFind "Inline" binding.Metadata <> Some (MetadataValue.Bool true) ->
        match binding.Parent |> Option.bind graph.Nodes.TryFind, graph.Nodes.TryFind lambdaId with
        | Some { Kind = SemanticKind.ModuleDef _ }, Some { Kind = SemanticKind.Lambda _ } -> true
        | None, Some { Kind = SemanticKind.Lambda _ } -> true
        | _ -> false
    | _ -> false

let private isCrossCallableProvenanceRole (role: EdgeRole) =
    match role with
    | EdgeRole.ProgramActivationCall
    | EdgeRole.ProgramActivationCoverage
    | EdgeRole.EagerDemand _
    | EdgeRole.EagerDemandPending
    | EdgeRole.EnrichedWith -> true
    | _ -> false

let private ambiguousAddresses (addresses: Map<NodeId, string>) =
    addresses
    |> Map.toList
    |> List.groupBy snd
    |> List.choose (fun (address, entries) ->
        if entries.Length > 1 then Some address else None)

let private structuralFailures (graph: SemanticGraph) =
    [ for KeyValue(id, node) in graph.Nodes do
        if node.Id <> id then
            yield SegmentationFailure.InvalidGraph(Some id, "The graph node is filed under a different identity.")
        for target in node.Children @ Option.toList node.Parent @ (kindEdges id node.Kind |> List.collect (fun edge -> edge.Target :: edge.Sources)) do
            if not (graph.Nodes.ContainsKey target) then
                yield SegmentationFailure.InvalidGraph(Some id, "A structural or reference target is absent from the graph.")
      for id, _ in graph.DeclarationRoots do
        if not (graph.Nodes.ContainsKey id) then
            yield SegmentationFailure.InvalidGraph(Some id, "A declaration root is absent from the graph.") ]

// The existing legacy projection can signal unsupported input from its encoder.
let private readLegacyProjection read =
    try read ()
    with :? InvalidOperationException as error ->
        Result.Error [SegmentationFailure.UnsupportedInput error.Message]

let segment (graph: SemanticGraph) : Result<SegmentationPlan, SegmentationFailure list> =
    let errors = ResizeArray<SegmentationFailure>(structuralFailures graph)
    let fail id reason = errors.Add(SegmentationFailure.InvalidGraph(id, reason))
    // Module, binding, detached, and obligation addresses are independent of allocation order,
    // Elaboration.Id counters, and SourceRange line/column trivia.
    let platformReading =
        if errors.Count = 0 then Some (PlatformResolution.read graph) else None
    let allResolved =
        match platformReading with
        | None -> Map.empty
        | Some read ->
            match readLegacyProjection (fun () ->
                WitnessSegmentation.canonicalAddresses graph read
                |> Result.mapError (List.map SegmentationFailure.InvalidGraph)) with
            | Result.Ok (resolved, _, _) -> resolved
            | Result.Error failures ->
                for failure in failures do errors.Add failure
                Map.empty
    let names = allResolved |> Map.filter (fun id _ -> graph.Nodes.ContainsKey id)
    for identity in ambiguousAddresses allResolved do
        errors.Add(SegmentationFailure.AmbiguousIdentity identity)
    // Every top-level declaration owns its local storage. Module containers and
    // off-spine Obligation citizens do not own sibling declarations.
    let rec owner seen id =
        if Set.contains id seen then None else
        let node = graph.Nodes[id]
        match node.Kind with
        | SemanticKind.ModuleDef _
        | SemanticKind.Obligation _ -> None
        | _ ->
            match node.Parent |> Option.bind graph.Nodes.TryFind with
            | Some { Kind = SemanticKind.ModuleDef _ } -> Some id
            | Some parent -> owner (Set.add id seen) parent.Id
            | None -> Some id
    let owners =
        if errors.Count > 0 then Map.empty else
        graph.Nodes.Keys |> Seq.choose (fun id -> owner Set.empty id |> Option.map (fun root -> id, names[root])) |> Map.ofSeq
    let regionRootsByIdentity =
        owners
        |> Map.toSeq
        |> Seq.choose (fun (id, identity) -> if names.TryFind id = Some identity then Some(identity, id) else None)
        |> Map.ofSeq
    let codata = graph.Codata.Value
    let indexed id = graph.Nodes.ContainsKey id || codata.CallableContracts.ContainsKey id || codata.CallableAggregateSlots.ContainsKey id
    for edge in graph.Edges do
        if edge.Target :: edge.Sources |> List.exists (indexed >> not) then
            fail (Some edge.Target) "A proof-support edge has an unindexed participant."
    let deps = ResizeArray<RegionDependency>()
    let addDependency kind consumer provider support =
        match owners.TryFind consumer, owners.TryFind provider with
        | Some consumer, Some provider when consumer <> provider ->
            deps.Add { Consumer = consumer; Provider = provider; Kind = kind; SupportNodes = support }
        | _ -> ()
    let addRegionDependency kind consumerIdentity providerIdentity support =
        if consumerIdentity <> providerIdentity then
            deps.Add { Consumer = consumerIdentity; Provider = providerIdentity; Kind = kind; SupportNodes = support }
    let projectedImplementation target =
        let current = Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current graph target
        match current with
        | Result.Ok account when account.Flows.IsEmpty && account.Joins.IsEmpty &&
                                 (account.Participants |> List.forall (fun p -> indexed p.Node && indexed p.Group)) ->
            match account.Values |> List.filter (fun row -> row.Occurrence = target && row.Operation = CallableAggregateOperation.Project) with
            | [row] when row.Tag.IsNone && row.SelectedAlternative.IsNone ->
                match row.FormationInputs, row.Alternatives, row.Selector with
                | [construction; actual], [alt], Some { Lower = 0; UpperExclusive = 1; Storage = None; Slot = None; ByteOffset = None }
                    when alt.Ordinal = 0 && alt.Carrier = actual && alt.Adapter.IsNone &&
                         alt.EnvironmentValue.IsNone && alt.EnvironmentPlacement.IsNone ->
                    let supplier = account.Values |> List.filter (fun value ->
                        value.Occurrence = construction && value.Slot = row.Slot && value.Operation = CallableAggregateOperation.Construct)
                    let slot = account.Slots |> List.filter (fun entry -> entry.Identity = row.Slot)
                    let carrier = account.Carriers |> List.filter (fun entry -> entry.Occurrence = actual)
                    let contract = account.Contracts |> List.filter (fun entry -> entry.Identity = alt.Contract)
                    match supplier, slot, carrier, contract with
                    | [origin], [{ Path = [CallableAggregatePathStep.RecordField _]; Contract = Result.Ok slotContract }], [code], [abi]
                        when origin.Value = Some actual && origin.Alternatives = row.Alternatives &&
                             slotContract = alt.Contract && code.Contract = Result.Ok alt.Contract &&
                             code.Formation = alt.Formation && code.Kind = CallableKind.OrdinaryFlatClosure &&
                             code.Environment.IsNone && code.EnvironmentValue.IsNone && owners.ContainsKey construction ->
                        match abi.Participants |> List.filter (fun p -> p.Role = ParticipantRole.CallableImplementation) with
                        | [p] when p.Group = abi.Identity && p.Ordinal = 0 && p.Node = code.Implementation &&
                                   owners.ContainsKey p.Node -> Some code.Implementation
                        | _ -> None
                    | _ -> None
                | _ -> None
            | _ -> None
        | _ -> None
    let rec callable seen site target =
        if Set.contains target seen then
            errors.Add(SegmentationFailure.UnresolvedCallable(site, target))
        else
            let seen = Set.add target seen
            match graph.Nodes.TryFind target with
            | Some { Kind = SemanticKind.Intrinsic _ } -> ()
            | Some { Kind = SemanticKind.Lambda _ } when owners.ContainsKey target ->
                addDependency DependencyKind.Call site target (Set.singleton target)
            | Some { Kind = SemanticKind.VarRef(_, Some definition) }
            | Some { Kind = SemanticKind.TypeAnnotation(definition, _) }
            | Some { Kind = SemanticKind.Application(definition, _) } -> callable seen site definition
            | Some { Kind = SemanticKind.Binding _; Children = [definition] } -> callable seen site definition
            | Some { Kind = SemanticKind.ClosureValue(implementation, environment) } ->
                callable seen site implementation
                addDependency DependencyKind.CapturedEnvironment site environment (Set.singleton environment)
            | _ ->
                match codata.KnownCallables.TryFind target with
                | Some known when graph.Nodes.ContainsKey known.Implementation ->
                    callable seen site known.Implementation
                    addDependency DependencyKind.CapturedEnvironment site known.EnvironmentOwner (Set.singleton known.EnvironmentOwner)
                | _ ->
                    match graph.Nodes.TryFind target with
                    | Some { Kind = SemanticKind.FieldGet _ } ->
                        match projectedImplementation target with
                        | Some implementation -> callable seen site implementation
                        | None -> errors.Add(SegmentationFailure.UnresolvedCallable(site, target))
                    | _ -> errors.Add(SegmentationFailure.UnresolvedCallable(site, target))
    if errors.Count = 0 then
        for KeyValue(id, node) in graph.Nodes do
            match node.Kind with
            | SemanticKind.Application(target, _) -> callable Set.empty id target
            | SemanticKind.Lambda(_, _, captures, _, _) ->
                for capture in captures do
                    match capture.SourceNodeId with
                    | Some source when graph.Nodes.ContainsKey source -> addDependency DependencyKind.CapturedEnvironment id source (Set.singleton source)
                    | _ -> errors.Add(SegmentationFailure.BrokenEnvironment(id, "A capture has no indexed source declaration."))
            | SemanticKind.ClosureValue(implementation, environment) ->
                addDependency DependencyKind.CapturedEnvironment id implementation (Set.singleton implementation)
                addDependency DependencyKind.CapturedEnvironment id environment (Set.singleton environment)
            | SemanticKind.EnvironmentCreate(environmentOwner, initializers) ->
                match codata.EnvironmentLayouts.TryFind environmentOwner with
                | Some layout when (initializers |> List.map fst |> Set.ofList) = (layout.Slots |> List.map _.Source |> Set.ofList) ->
                    addDependency DependencyKind.CapturedEnvironment id environmentOwner (Set.singleton environmentOwner)
                | _ -> errors.Add(SegmentationFailure.BrokenEnvironment(id, "Environment formation requires its exact indexed layout and slots."))
            | SemanticKind.EnvironmentRead(environment, slot)
            | SemanticKind.EnvironmentBorrow(environment, slot)
            | SemanticKind.EnvironmentWrite(environment, slot, _) ->
                let origin = codata.EnvironmentOrigins.TryFind environment
                match origin |> Option.bind codata.EnvironmentLayouts.TryFind with
                | Some layout when layout.Slots |> List.exists (fun row -> row.Source = slot) ->
                    addDependency DependencyKind.CapturedEnvironment id layout.Owner (Set.ofList [environment; slot])
                | _ -> errors.Add(SegmentationFailure.BrokenEnvironment(id, "Environment access requires an indexed origin and a slot in its exact layout."))
            | _ -> ()
            // Reference dependencies include reads, stores and address-taking;
            // references to immutable callable declarations are Call dependencies
            // governed by CallableInterfaceDigest rather than mutable Storage.
            for edge in kindEdges id node.Kind do
                if Hyperedge.isReference edge && edge.Role <> EdgeRole.Member then
                    for source in edge.Sources do
                        let depKind =
                            if edge.Role = EdgeRole.Definition && isCallableBoundary graph source then
                                DependencyKind.Call
                            else
                                DependencyKind.Storage
                        addDependency depKind id source (Set.singleton source)
        for KeyValue(key, layout) in codata.EnvironmentLayouts do
            let receivingFormal =
                match graph.Nodes.TryFind layout.Implementation with
                | Some { Kind = SemanticKind.Lambda((_, _, formal) :: _, _, _, _, _) } -> formal = layout.Formal
                | _ -> false
            if key <> layout.Owner || not (graph.Nodes.ContainsKey layout.Implementation) ||
               not (graph.Nodes.ContainsKey layout.Formal) || layout.Alignment <= 0 || layout.Bytes < 0 ||
               not receivingFormal || (layout.Slots |> List.map _.Source |> Set.ofList |> Set.count) <> layout.Slots.Length ||
               (layout.Obligations |> List.exists (graph.Nodes.ContainsKey >> not)) ||
               (layout.Slots |> List.exists (fun slot -> not (graph.Nodes.ContainsKey slot.Source))) then
                errors.Add(SegmentationFailure.BrokenEnvironment(key, "The environment layout has invalid ownership, implementation, formal or slots."))
        for KeyValue(occurrence, origin) in codata.EnvironmentOrigins do
            if not (graph.Nodes.ContainsKey occurrence) || not (codata.EnvironmentLayouts.ContainsKey origin) then
                errors.Add(SegmentationFailure.BrokenEnvironment(occurrence, "An environment origin has no indexed occurrence or layout."))
    match platformReading with
    | Some read when errors.Count = 0 ->
      readLegacyProjection (fun () ->
        // Contract identities are relation citizens rather than executable nodes.
        for KeyValue(id, contract) in codata.CallableContracts do
                let participants = contract.Participants |> List.filter (fun p -> p.Role = ParticipantRole.CallableImplementation)
                match participants with
                | [implementation] when contract.Identity = id && implementation.Group = id &&
                                        implementation.Ordinal = 0 && names.ContainsKey implementation.Node && not (names.ContainsKey id) ->
                    ()
                | _ ->
                    fail (Some id) "A callable contract has no unique indexed implementation."
        let names = allResolved
        let encode = WitnessSegmentation.encoder names
        let nodeFingerprints =
            graph.Nodes |> Map.map (fun _ node ->
                let kind = match node.Kind with SemanticKind.ModuleDef(name, _) -> SemanticKind.ModuleDef(name, []) | kind -> kind
                encode (box (kind, node.Type, node.SRTPResolution, node.ArenaAffinity, node.LayoutHint,
                             (match kind with SemanticKind.ModuleDef _ -> [] | _ -> node.Children),
                             node.Parent, WitnessSegmentation.normalizeMetadata node.Metadata,
                             node.IsReachable, node.EmissionStrategy, node.ValueRange))
                |> hash)
        let environmentLayoutOwners =
            codata.EnvironmentLayouts.Values
            |> Seq.choose (fun l -> owners.TryFind l.Owner)
            |> Set.ofSeq
        let classifyProviderDependency (providerIdentity: string) =
            match regionRootsByIdentity.TryFind providerIdentity with
            | Some rootId when isCallableBoundary graph rootId && not (environmentLayoutOwners.Contains providerIdentity) ->
                DependencyKind.Call
            | _ ->
                DependencyKind.ProofSupport
        let supports = ResizeArray<SupportEdge>()
        let addSupportWithProviders domain key anchor value (explicitProviders: Set<string> option) =
            let refs = references value
            let consumers =
                match anchor |> Option.bind owners.TryFind with
                | Some consumer -> Set.singleton consumer
                | None ->
                    let referenced = refs |> Seq.choose owners.TryFind |> Set.ofSeq
                    if referenced.IsEmpty then regionRootsByIdentity.Keys |> Set.ofSeq else referenced
            let rawProviders =
                match explicitProviders with
                | Some p -> p
                | None -> refs |> Seq.choose owners.TryFind |> Set.ofSeq
            let fingerprint = encode value |> hash
            for consumer in consumers do
                let providers = rawProviders.Remove consumer
                supports.Add { Consumer = consumer; Domain = domain; Identity = key; Providers = providers
                               SupportNodes = refs; Fingerprint = fingerprint }
                for provider in providers do
                    addRegionDependency (classifyProviderDependency provider) consumer provider refs
        let addSupport domain key anchor value =
            addSupportWithProviders domain key anchor value None
        let mapRows domain (rows: Map<NodeId, 'a>) =
            for KeyValue(id, value) in rows do
                let anchor =
                    if owners.ContainsKey id then Some id
                    else references (box value) |> Seq.tryFind owners.ContainsKey
                addSupport domain (names.TryFind id |> Option.defaultValue domain) anchor (box value)
        // CallableContracts: anchor at CallableImplementation without backward ProofSupport coupling from callers.
        for KeyValue(id, contract) in codata.CallableContracts do
            let implAnchor =
                contract.Participants
                |> List.tryFind (fun p -> p.Role = ParticipantRole.CallableImplementation)
                |> Option.map _.Node
            let nonCallerRefs =
                contract.Participants
                |> List.filter (fun p -> p.Role <> ParticipantRole.Source)
                |> List.choose (fun p -> owners.TryFind p.Node)
                |> Set.ofList
            addSupportWithProviders
                "CallableContracts"
                (names.TryFind id |> Option.defaultValue "CallableContracts")
                implAnchor
                (box contract)
                (Some nonCallerRefs)
        mapRows "MutableCallableStorage" codata.MutableCallableStorage
        mapRows "ClosureDomain.Layouts" codata.EnvironmentLayouts
        mapRows "ClosureDomain.Origins" codata.EnvironmentOrigins
        mapRows "ClosureDomain.Placement" codata.Closures
        mapRows "ClosureDomain.Callables" codata.KnownCallables
        for KeyValue(identity, entry) in codata.ProgramStorage.Entries do
            let id = match identity with ProgramStorageIdentity.Allocation id | ProgramStorageIdentity.BindingSlot id -> id
            addSupport "ProgramStorage" names[id] (Some id) (box entry)
        // Preserve authored domain edges at row granularity so unrelated declarations
        // do not share a monolithic whole-program receipt.
        let rec domainRows domain (value: objnull) =
            let value = value |> Option.ofObj |> Option.get
            for field in FSharpType.GetRecordFields(value.GetType(), flags) do
                let fieldDomain = domain + "." + field.Name
                let raw = field.GetValue value
                let isOption = field.PropertyType.IsGenericType && field.PropertyType.GetGenericTypeDefinition() = typedefof<option<_>>
                let row =
                    if isOption then
                        let present = not (isNull raw)
                        for KeyValue(_, rootId) in regionRootsByIdentity do
                            addSupport domain (fieldDomain + ".presence") (Some rootId) (box ("present:" + (if present then "true" else "false")))
                        if present then (FSharpValue.GetUnionFields(raw, field.PropertyType, flags) |> snd)[0] else null
                    else raw
                let rec route (row: objnull) =
                    match row with
                    | :? IEnumerable as items when not (row :? string) ->
                        for item in items do
                            let refs = references item
                            let key = domain + "." + field.Name + ":" + (refs |> Seq.choose names.TryFind |> Seq.sort |> String.concat "|")
                            let ty = item |> Option.ofObj |> Option.map (fun value -> value.GetType())
                            match ty with
                            | Some ty when ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<Collections.Generic.KeyValuePair<_, _>> ->
                                let rowKey = (property ty "Key").GetValue item
                                let itemVal = (property ty "Value").GetValue item
                                let anchor = match rowKey with :? NodeId as id -> Some id | _ -> None
                                addSupport domain key anchor (box (rowKey, itemVal))
                            | _ -> addSupport domain key (rowAnchor item) item
                    | _ when row |> Option.ofObj |> Option.exists (fun value -> value.GetType().IsGenericType && value.GetType().GetGenericTypeDefinition() = typedefof<Result<_, _>>) ->
                        let value = row |> Option.ofObj |> Option.get
                        let case, fields = FSharpValue.GetUnionFields(value, value.GetType(), flags)
                        for KeyValue(_, rootId) in regionRootsByIdentity do
                            addSupport domain (fieldDomain + ".case") (Some rootId) (box case.Name)
                        for item in fields do route item
                    | _ when isOption && (row |> Option.ofObj |> Option.exists (fun value -> FSharpType.IsRecord(value.GetType(), flags))) ->
                        domainRows fieldDomain row
                    | _ ->
                        // Scalar headers/negative observations carry no sibling body references.
                        for regionIdentity, rootId in Map.toSeq regionRootsByIdentity do
                            let _ = regionIdentity
                            addSupport domain (domain + "." + field.Name) (Some rootId) row
                if not isOption || not (isNull row) then route row
        for edge in graph.Edges do
            match edge.Role with
            | EdgeRole.NumericDomain domain -> domainRows "NumericDomain" (box domain)
            | EdgeRole.MemoryDomain domain -> domainRows "MemoryDomain" (box domain)
            | EdgeRole.SpatialModuleDomain domain -> domainRows "SpatialModuleDomain" (box domain)
            | EdgeRole.BoundaryDomain domain -> domainRows "BoundaryDomain" (box domain)
            | role when isCrossCallableProvenanceRole role ->
                ()
            | _ ->
                let anchor =
                    if owners.ContainsKey edge.Target then Some edge.Target
                    else edge.Sources |> List.tryFind owners.ContainsKey
                for source in edge.Sources do
                    match owners.TryFind edge.Target, owners.TryFind source with
                    | Some targetOwner, Some sourceOwner when targetOwner <> sourceOwner ->
                        addRegionDependency (classifyProviderDependency sourceOwner) targetOwner sourceOwner (Set.ofList (edge.Target :: edge.Sources))
                    | _ -> ()
                let encodedKey = encode (box (edge.Class, edge.Ordinal, edge.Target, edge.Sources))
                let payload =
                    match graph.Nodes.TryFind edge.Target with
                    | Some { Kind = SemanticKind.Obligation info } -> box (edge, info)
                    | _ -> box edge
                addSupport "Relation" encodedKey anchor payload
        let settledDependencies = deps |> Seq.distinct |> Seq.sort |> Seq.toList
        let settledSupports = supports |> Seq.distinct |> Seq.sort |> Seq.toList
        let platformInterface =
            graph.Platform |> Option.map (fun p -> p.PlatformId, p.SubstrateKind, p.RuntimeModel, p.Dimensions)
        let platformCensuses =
            WitnessSegmentation.platformLayoutCensus graph.Platform @
            WitnessSegmentation.platformSpaceCensus read
        let numericResolutionSummary =
            match read.Platform with
            | Some p when read.Findings.IsEmpty ->
                let coreSummary =
                    p.Core |> Option.map (fun c ->
                        c.Widths |> List.map (fun w -> w.Name, w.Bits),
                        c.Representations |> List.map (fun r -> r.Representation))
                Some(p.Id, coreSummary)
            | _ -> None
        let groupedRegions = owners |> Map.toList |> List.groupBy snd
        // Pass 1: compute CallableInterfaceDigest for every segmented declaration region.
        let interfaceDigests =
            groupedRegions
            |> List.map (fun (identity, nodes) ->
                let members = nodes |> List.map fst |> Set.ofList
                let root = regionRootsByIdentity[identity]
                let rootNode = graph.Nodes[root]
                let ownedContracts =
                    codata.CallableContracts.Values
                    |> Seq.filter (fun contract ->
                        contract.Participants |> List.exists (fun p ->
                            p.Role = ParticipantRole.CallableImplementation && members.Contains p.Node))
                    |> Seq.map (fun contract ->
                        { contract with
                            SourcePremises = Map.empty
                            Participants = contract.Participants |> List.filter (fun p -> p.Role <> ParticipantRole.Source) })
                    |> Seq.map (fun c -> names[c.Identity] + ":" + encode (box c))
                    |> Seq.sort
                    |> String.concat "|"
                let interfacePreimage =
                    if isCallableBoundary graph root then
                        let lambdaId = rootNode.Children.Head
                        let lambdaNode = graph.Nodes[lambdaId]
                        let paramSummary, captures, context =
                            match lambdaNode.Kind with
                            | SemanticKind.Lambda(parameters, _, captures, _, context) ->
                                let ps =
                                    parameters |> List.map (fun (pName, pType, pId) ->
                                        let pNode = graph.Nodes[pId]
                                        pName, pType, pNode.ArenaAffinity, pNode.LayoutHint, codata.Escapes.TryFind pId)
                                ps, captures, context
                            | _ -> [], [], LambdaContext.RegularClosure
                        let ownedCarriers =
                            [ root; lambdaId ]
                            |> List.choose (fun nid -> codata.CallableCarriers.TryFind nid |> Option.map (fun c -> names[nid] + ":" + encode (box c)))
                            |> String.concat "|"
                        let envLayoutHeader =
                            codata.EnvironmentLayouts.TryFind lambdaId
                            |> Option.map (fun l -> encode (box (l.Bytes, l.Alignment, l.Slots |> List.map (fun s -> s.Field, s.Holds, s.IsCapture))))
                            |> Option.defaultValue ""
                        [ "callable-interface-v1"
                          identity
                          encode (box (rootNode.Kind, rootNode.Type, rootNode.SRTPResolution, rootNode.ArenaAffinity, rootNode.LayoutHint, rootNode.IsReachable, rootNode.EmissionStrategy, WitnessSegmentation.normalizeMetadata rootNode.Metadata))
                          encode (box (lambdaNode.Type, lambdaNode.SRTPResolution, lambdaNode.ArenaAffinity, lambdaNode.LayoutHint, lambdaNode.EmissionStrategy, WitnessSegmentation.normalizeMetadata lambdaNode.Metadata))
                          encode (box (paramSummary, captures, context))
                          encode (box (codata.Escapes.TryFind root, codata.Escapes.TryFind lambdaId))
                          encode (box (codata.Closures.TryFind lambdaId))
                          envLayoutHeader
                          ownedContracts
                          ownedCarriers
                          encode (box platformInterface) ]
                        |> String.concat "\n"
                    else
                        let memberSummary =
                            members
                            |> Seq.map (fun id -> names[id] + ":" + nodeFingerprints[id])
                            |> Seq.sort
                            |> String.concat "|"
                        let storageEntries =
                            codata.ProgramStorage.Entries
                            |> Map.toSeq
                            |> Seq.choose (fun (sid, entry) ->
                                let nid = match sid with ProgramStorageIdentity.Allocation n | ProgramStorageIdentity.BindingSlot n -> n
                                if members.Contains nid then Some(names[nid] + ":" + encode (box entry)) else None)
                            |> Seq.sort
                            |> String.concat "|"
                        [ "callable-interface-storage-v1"
                          identity
                          memberSummary
                          ownedContracts
                          storageEntries
                          encode (box platformInterface) ]
                        |> String.concat "\n"
                identity, CallableInterfaceDigest(CallableInterfaceDigest.DomainPrefix + hash interfacePreimage))
            |> Map.ofList
        // Pass 2: compute SemanticRealizationDigest (using referenced callees' CallableInterfaceDigest)
        // and CanonicalProofSupportDigest for every segmented declaration region.
        let regionMap =
            groupedRegions
            |> List.map (fun (identity, nodes) ->
                let members = nodes |> List.map fst |> Set.ofList
                let root = regionRootsByIdentity[identity]
                let ownInterface = interfaceDigests[identity]
                let memberInputs =
                    members
                    |> Seq.map (fun id -> names[id] + ":" + nodeFingerprints[id])
                    |> Seq.sort
                    |> String.concat "|"
                let referencedCallInterfaces =
                    settledDependencies
                    |> List.choose (fun edge ->
                        if edge.Consumer = identity && edge.Kind = DependencyKind.Call then
                            interfaceDigests.TryFind edge.Provider
                            |> Option.map (fun d -> edge.Provider + ":" + d.Value)
                        else None)
                    |> List.distinct
                    |> List.sort
                    |> String.concat "|"
                let referencedStorageAndEnv =
                    settledDependencies
                    |> List.choose (fun edge ->
                        if edge.Consumer = identity && (edge.Kind = DependencyKind.Storage || edge.Kind = DependencyKind.CapturedEnvironment) then
                            interfaceDigests.TryFind edge.Provider
                            |> Option.map (fun d -> sprintf "%A:%s:%s" edge.Kind edge.Provider d.Value)
                        else None)
                    |> List.distinct
                    |> List.sort
                    |> String.concat "|"
                let memberTypes =
                    members
                    |> Set.map (fun id -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[id].Type)
                let scopedLayouts =
                    graph.Layouts.Value
                    |> Map.toSeq
                    |> Seq.choose (fun (tyId, layout) ->
                        if memberTypes.Contains tyId then Some(encode (box (tyId, layout))) else None)
                    |> Seq.sort
                    |> String.concat "|"
                let envRealization =
                    codata.EnvironmentLayouts
                    |> Map.toSeq
                    |> Seq.choose (fun (lid, layout) ->
                        if members.Contains lid then Some(names[lid] + ":" + encode (box layout)) else None)
                    |> Seq.sort
                    |> String.concat "|"
                let realizationPreimage =
                    [ "semantic-realization-v1"
                      identity
                      ownInterface.Value
                      memberInputs
                      referencedCallInterfaces
                      referencedStorageAndEnv
                      scopedLayouts
                      envRealization
                      encode (box graph.Platform) ]
                    |> String.concat "\n"
                let realizationDigest =
                    SemanticRealizationDigest(SemanticRealizationDigest.DomainPrefix + hash realizationPreimage)
                let proofInputs =
                    settledSupports
                    |> List.filter (fun edge -> edge.Consumer = identity)
                    |> List.map (fun edge -> edge.Domain + ":" + edge.Identity + ":" + edge.Fingerprint)
                    |> List.sort
                    |> String.concat "|"
                let proofPreimage =
                    [ "proof-support-v1"
                      identity
                      proofInputs
                      encode (box platformCensuses)
                      encode (box numericResolutionSummary)
                      encode (box graph.Platform) ]
                    |> String.concat "\n"
                let proofSupportDigest =
                    CanonicalProofSupportDigest(CanonicalProofSupportDigest.DomainPrefix + hash proofPreimage)
                identity,
                { Identity = identity
                  Root = root
                  Members = members
                  CallableInterfaceDigest = ownInterface
                  SemanticRealizationDigest = realizationDigest
                  CanonicalProofSupportDigest = proofSupportDigest })
            |> Map.ofList
        if errors.Count > 0 then Result.Error(List.ofSeq errors) else
        Result.Ok { Regions = regionMap
                    Dependencies = settledDependencies
                    SupportEdges = settledSupports
                    NodeIdentities = allResolved |> Map.filter (fun id _ -> graph.Nodes.ContainsKey id)
                    CallableRelationIdentities = allResolved |> Map.filter (fun id _ -> codata.CallableContracts.ContainsKey id || codata.CallableAggregateSlots.ContainsKey id)
                    NodeOwners = owners
                    NodeFingerprints = nodeFingerprints })
    | _ -> Result.Error(List.ofSeq errors)

let private alignRelations (baseline: SemanticGraph) (candidate: SemanticGraph)
                           (oldPlan: SegmentationPlan) (newPlan: SegmentationPlan) (physical: Map<NodeId, NodeId>) =
    let prior = baseline.Codata.Value
    let current = candidate.Codata.Value
    let unique pairs =
        pairs |> Seq.groupBy fst |> Seq.choose (fun (_, values) ->
            match Seq.toList values with [pair] -> Some pair | _ -> None) |> Map.ofSeq
    let slots =
        current.CallableAggregateSlots |> Map.toSeq |> Seq.choose (fun (id, slot) ->
            let previous = Clef.Compiler.Baker.Recipes.CallableAggregateRecipes.tryPreviousSlotIdentity
                                slot.AggregateType slot.Path prior.CallableAggregateSlots
            previous |> Option.bind (fun old ->
                if oldPlan.CallableRelationIdentities.ContainsKey old && newPlan.CallableRelationIdentities.ContainsKey id
                then Some(old, id) else None))
        |> unique
    let contracts =
        current.CallableCarriers.Values
        |> Seq.choose (fun carrier -> carrier.Contract |> Result.toOption |> Option.map (fun id -> id, carrier))
        |> Seq.groupBy fst
        |> Seq.choose (fun (id, occurrences) ->
            let previous = occurrences |> Seq.map (fun (_, carrier) ->
                Clef.Compiler.Baker.Ingredients.CallableContracts.tryIdentityAcross physical.TryFind slots.TryFind candidate
                    current.EnvironmentLayouts prior.CallableContracts carrier) |> Seq.distinct |> Seq.toList
            match previous, newPlan.CallableRelationIdentities.TryFind id with
            | [Some old], Some address when oldPlan.CallableRelationIdentities.TryFind old = Some address -> Some(old, id)
            | _ -> None)
    Seq.append contracts (Map.toSeq slots) |> unique

[<RequireQualifiedAccess>]
type internal RebuildPairFailure =
    | Baseline of SegmentationFailure list
    | Candidate of SegmentationFailure list

type internal CheckedRebuildPair =
    private
        { Baseline: SemanticGraph
          Candidate: SemanticGraph
          BaselinePlan: SegmentationPlan
          CandidatePlan: SegmentationPlan
          Alignment: Map<NodeId, NodeId>
          RelationAlignment: Map<NodeId, NodeId> }

let internal checkRebuildPair baseline candidate =
    match segment baseline, segment candidate with
    | Result.Error failures, _ -> Result.Error(RebuildPairFailure.Baseline failures)
    | _, Result.Error failures -> Result.Error(RebuildPairFailure.Candidate failures)
    | Result.Ok oldPlan, Result.Ok newPlan ->
        let newByAddress =
            newPlan.NodeIdentities |> Map.toSeq |> Seq.map (fun (id, address) -> address, id) |> Map.ofSeq
        let alignment =
            oldPlan.NodeIdentities |> Map.toSeq |> Seq.choose (fun (id, address) ->
                newByAddress.TryFind address |> Option.map (fun target -> id, target)) |> Map.ofSeq
        Result.Ok
            { Baseline = baseline; Candidate = candidate
              BaselinePlan = oldPlan; CandidatePlan = newPlan
              Alignment = alignment
              RelationAlignment = alignRelations baseline candidate oldPlan newPlan alignment }

let internal rebuildPairPlans (pair: CheckedRebuildPair) =
    pair.BaselinePlan, pair.CandidatePlan, pair.Alignment, pair.RelationAlignment

[<RequireQualifiedAccess>]
type internal ScopedSettlementFailure =
    | RecipeRefused of NodeId * string
    | MissingCallableSettlement

type internal ScopedRebuildPair =
    private
        { Baseline: SemanticGraph
          Receiving: SemanticGraph
          Alignment: Map<NodeId, NodeId>
          RelationAlignment: Map<NodeId, NodeId> }

/// Bind the receiving graph by running the existing scoped Baker operation on
/// the checked candidate and the scopes selected by Rebuild.
let internal settleRebuildScopes (pair: CheckedRebuildPair) scopes =
    let recipes = Clef.Compiler.Nanopass.BakerSaturation.fanOutScopes scopes pair.Candidate
    let refusal =
        recipes.Diagnostics |> List.tryPick (fun diagnostic ->
            match diagnostic.Result with
            | Clef.Compiler.Nanopass.Recipe.CreationFailed(reason, _) ->
                Some(ScopedSettlementFailure.RecipeRefused(diagnostic.NodeId, reason))
            | _ -> None)
    match refusal with
    | Some failure -> Result.Error failure
    | None ->
        let receiving =
            if recipes.Recipes.IsEmpty then pair.Candidate
            else Clef.Compiler.Nanopass.BakerSaturation.foldIn recipes pair.Candidate
        let before = pair.Candidate.Codata.Value
        let after = receiving.Codata.Value
        if (not before.CallableContracts.IsEmpty && after.CallableContracts.IsEmpty)
           || (not before.CallableAggregateSlots.IsEmpty && after.CallableAggregateSlots.IsEmpty) then
            Result.Error ScopedSettlementFailure.MissingCallableSettlement
        else
            let relations =
                if recipes.Recipes.IsEmpty then pair.RelationAlignment
                else alignRelations pair.Baseline receiving pair.BaselinePlan pair.CandidatePlan pair.Alignment
            let alignment = relations |> Map.fold (fun acc old current -> Map.add old current acc) pair.Alignment
            Result.Ok ({ Baseline = pair.Baseline; Receiving = receiving
                         Alignment = alignment; RelationAlignment = relations }, recipes)

let internal scopedRebuildInputs (pair: ScopedRebuildPair) =
    pair.Baseline, pair.Receiving, pair.Alignment, pair.RelationAlignment

/// Physical-only reconciliation uses the same source address author as segment.
let internal physicalOccurrenceAddresses graph =
    match structuralFailures graph with
    | [] ->
        readLegacyProjection (fun () ->
            WitnessSegmentation.canonicalAddresses graph (PlatformResolution.read graph)
            |> Result.mapError (List.map SegmentationFailure.InvalidGraph)
            |> Result.map (fun (addresses, _, _) ->
                let ambiguous = ambiguousAddresses addresses |> Set.ofList
                addresses |> Map.filter (fun id address -> graph.Nodes.ContainsKey id && not (ambiguous.Contains address))))
    | failures -> Result.Error failures

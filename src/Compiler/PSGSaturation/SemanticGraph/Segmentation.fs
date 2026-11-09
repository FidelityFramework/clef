// SPDX-License-Identifier: MIT
/// Baker's dependency plan. This is source scheduling evidence, never a PSG revision.
module Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation

open System
open System.Collections
open System.Reflection
open System.Security.Cryptography
open System.Text
open Microsoft.FSharp.Reflection
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

[<RequireQualifiedAccess>]
type DependencyKind = Call | Storage | CapturedEnvironment | ProofSupport

type RegionDependency = { Consumer: string; Provider: string; Kind: DependencyKind; SupportNodes: Set<NodeId> }
type SupportEdge = { Consumer: string; Domain: string; Identity: string; Providers: Set<string>; SupportNodes: Set<NodeId>; Fingerprint: string }
type Region = { Identity: string; Root: NodeId; Members: Set<NodeId>; Fingerprint: string }
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
      NodeOwners: Map<NodeId, string>
      NodeFingerprints: Map<NodeId, string> }

let regions plan = plan.Regions |> Map.values |> Seq.toList
let dependencies identity plan = plan.Dependencies |> List.filter (fun edge -> edge.Consumer = identity)
let supportEdges identity plan = plan.SupportEdges |> List.filter (fun edge -> edge.Consumer = identity)
let internal hash (text: string) = Encoding.UTF8.GetBytes text |> SHA256.HashData |> Convert.ToHexString
let private flags = BindingFlags.Public ||| BindingFlags.NonPublic
let private property (ty: Type) name =
    ty.GetProperty name |> Option.ofObj |> Option.defaultWith (fun () -> invalidOp ("Missing source row field " + name))

/// Inspect source rows only; NativeType is frozen by the shared witness encoder.
let rec private references (value: objnull) : Set<NodeId> =
    match value with
    | null -> Set.empty
    | :? NodeId as id -> Set.singleton id
    | :? NativeType -> Set.empty
    | :? string -> Set.empty
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

let private label (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.ModuleDef(name, _) -> "module:" + name
    | SemanticKind.Binding(name, _, _, _) -> "binding:" + name
    | SemanticKind.TypeDef(name, _, _) -> "type:" + name
    | SemanticKind.MemberDef(name, _, _) -> "member:" + name
    | SemanticKind.Obligation info -> "claim:" + info.Id
    | _ -> "node"

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

let segment (graph: SemanticGraph) : Result<SegmentationPlan, SegmentationFailure list> =
    let errors = ResizeArray<SegmentationFailure>()
    let fail id reason = errors.Add(SegmentationFailure.InvalidGraph(id, reason))
    for KeyValue(id, node) in graph.Nodes do
        if node.Id <> id then fail (Some id) "The graph node is filed under a different identity."
        for target in node.Children @ Option.toList node.Parent @ (kindEdges id node.Kind |> List.collect (fun edge -> edge.Target :: edge.Sources)) do
            if not (graph.Nodes.ContainsKey target) then fail (Some id) "A structural or reference target is absent from the graph."
    for id, _ in graph.DeclarationRoots do
        if not (graph.Nodes.ContainsKey id) then fail (Some id) "A declaration root is absent from the graph."
    // Module and binding addresses are independent of allocation order and source ranges.
    let identities = Collections.Generic.Dictionary<NodeId, string>()
    let visiting = Collections.Generic.HashSet<NodeId>()
    let rec address id =
        match identities.TryGetValue id with
        | true, identity -> identity
        | _ when not (visiting.Add id) ->
            fail (Some id) "The lexical parent relation contains a cycle."
            "cycle"
        | _ ->
            let node = graph.Nodes[id]
            let identity =
                match node.Parent |> Option.bind graph.Nodes.TryFind with
                | Some parent ->
                    let prefix = address parent.Id
                    match node.Kind with
                    | SemanticKind.Binding _ | SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ | SemanticKind.MemberDef _ ->
                        prefix + "/" + label node
                    | _ ->
                        let index = parent.Children |> List.tryFindIndex ((=) id)
                        match index with
                        | Some index -> prefix + "/" + string index
                        | None -> prefix + "/" + label node
                | None ->
                    match node.Kind with
                    | SemanticKind.ModuleDef _ | SemanticKind.Binding _ | SemanticKind.Obligation _ -> label node
                    | _ -> "detached:" + label node + ":" + string node.Range
            visiting.Remove id |> ignore
            identities[id] <- identity
            identity
    if errors.Count = 0 then
        for id in graph.Nodes.Keys do address id |> ignore
    let names = identities |> Seq.map (fun pair -> pair.Key, pair.Value) |> Map.ofSeq
    for identity, group in names |> Map.toList |> List.groupBy snd do
        if group.Length <> 1 then errors.Add(SegmentationFailure.AmbiguousIdentity identity)
    // Every top-level declaration owns its local storage. Module containers do
    // not own sibling declarations and are never dependency providers.
    let rec owner seen id =
        if Set.contains id seen then None else
        let node = graph.Nodes[id]
        match node.Kind with
        | SemanticKind.ModuleDef _ -> None
        | _ ->
            match node.Parent |> Option.bind graph.Nodes.TryFind with
            | Some { Kind = SemanticKind.ModuleDef _ } -> Some id
            | Some parent -> owner (Set.add id seen) parent.Id
            | None -> Some id
    let owners =
        if errors.Count > 0 then Map.empty else
        graph.Nodes.Keys |> Seq.choose (fun id -> owner Set.empty id |> Option.map (fun root -> id, names[root])) |> Map.ofSeq
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
            // structural storage operands remain in the owning callable region.
            for edge in kindEdges id node.Kind do
                if Hyperedge.isReference edge && edge.Role <> EdgeRole.Member then
                    for source in edge.Sources do addDependency DependencyKind.Storage id source (Set.singleton source)
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
    if errors.Count > 0 then Result.Error(List.ofSeq errors) else
    try
        // Contract identities are relation citizens rather than executable nodes.
        let names =
            codata.CallableContracts |> Map.fold (fun (names: Map<NodeId, string>) id contract ->
                let participants = contract.Participants |> List.filter (fun p -> p.Role = ParticipantRole.CallableImplementation)
                match participants with
                | [implementation] when contract.Identity = id && implementation.Group = id &&
                                        implementation.Ordinal = 0 && names.ContainsKey implementation.Node && not (names.ContainsKey id) ->
                    names.Add(id, "contract:" + names[implementation.Node])
                | _ ->
                    fail (Some id) "A callable contract has no unique indexed implementation."
                    names) names
        let names =
            codata.CallableAggregateSlots |> Map.fold (fun (names: Map<NodeId, string>) id row ->
                let refs = references (box row) |> Set.remove id
                let identity = refs |> Seq.choose names.TryFind |> Seq.sort |> String.concat "|"
                let path = WitnessSegmentation.encoder names (box row.Path)
                names.Add(id, "callable-slot:" + identity + ":" + path)) names
        let encode = WitnessSegmentation.encoder names
        let nodeFingerprints =
            graph.Nodes |> Map.map (fun _ node ->
                let kind = match node.Kind with SemanticKind.ModuleDef(name, _) -> SemanticKind.ModuleDef(name, []) | kind -> kind
                encode (box (kind, node.Type, node.SRTPResolution, node.ArenaAffinity, node.LayoutHint,
                             (match kind with SemanticKind.ModuleDef _ -> [] | _ -> node.Children),
                             node.Parent, node.Metadata, node.IsReachable, node.EmissionStrategy, node.ValueRange))
                |> hash)
        let supports = ResizeArray<SupportEdge>()
        let addSupport domain key anchor value =
            let refs = references value
            let consumers =
                match anchor |> Option.bind owners.TryFind with
                | Some consumer -> Set.singleton consumer
                | None ->
                    let referenced = refs |> Seq.choose owners.TryFind |> Set.ofSeq
                    if referenced.IsEmpty then owners.Values |> Set.ofSeq else referenced
            let providers = refs |> Seq.choose owners.TryFind |> Set.ofSeq
            let fingerprint = encode value |> hash
            for consumer in consumers do
                let providers = providers.Remove consumer
                supports.Add { Consumer = consumer; Domain = domain; Identity = key; Providers = providers
                               SupportNodes = refs; Fingerprint = fingerprint }
                for provider in providers do
                    deps.Add { Consumer = consumer; Provider = provider; Kind = DependencyKind.ProofSupport; SupportNodes = refs }
        let mapRows domain (rows: Map<NodeId, 'a>) =
            for KeyValue(id, value) in rows do
                let anchor =
                    if owners.ContainsKey id then Some id
                    else references (box value) |> Seq.tryFind owners.ContainsKey
                addSupport domain (names.TryFind id |> Option.defaultValue domain) anchor (box value)
        mapRows "CallableContracts" codata.CallableContracts
        mapRows "MutableCallableStorage" codata.MutableCallableStorage
        mapRows "ClosureDomain.Layouts" codata.EnvironmentLayouts
        mapRows "ClosureDomain.Origins" codata.EnvironmentOrigins
        mapRows "ClosureDomain.Placement" codata.Closures
        mapRows "ClosureDomain.Callables" codata.KnownCallables
        for KeyValue(identity, entry) in codata.ProgramStorage.Entries do
            let id = match identity with ProgramStorageIdentity.Allocation id | ProgramStorageIdentity.BindingSlot id -> id
            addSupport "ProgramStorage" names[id] (Some id) (box entry)
        // Preserve every authored edge, including complete domain inventories
        // and absence observations. Domain fields are scoped at their existing
        // row boundary so unrelated declarations do not share a ModuleDef owner.
        let domainRows domain (value: objnull) =
            let value = value |> Option.ofObj |> Option.get
            for field in FSharpType.GetRecordFields(value.GetType(), flags) do
                let row = field.GetValue value
                match row with
                | :? IEnumerable as items when not (row :? string) ->
                    for item in items do
                        let refs = references item
                        let key = domain + "." + field.Name + ":" + (refs |> Seq.choose names.TryFind |> Seq.sort |> String.concat "|")
                        let ty = item |> Option.ofObj |> Option.map (fun value -> value.GetType())
                        match ty with
                        | Some ty when ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<Collections.Generic.KeyValuePair<_, _>> ->
                            let rowKey = (property ty "Key").GetValue item
                            let value = (property ty "Value").GetValue item
                            let anchor = match rowKey with :? NodeId as id -> Some id | _ -> None
                            addSupport domain key anchor (box (rowKey, value))
                        | _ -> addSupport domain key (rowAnchor item) item
                | _ ->
                    // Scalar headers/negative observations are dependencies of
                    // every declaration, but contain no sibling executable body.
                    for KeyValue(id, _) in graph.Nodes do
                        if owners.TryFind id = names.TryFind id then addSupport domain (domain + "." + field.Name) (Some id) row
        for edge in graph.Edges do
            match edge.Role with
            | EdgeRole.NumericDomain domain -> domainRows "NumericDomain" (box domain)
            | EdgeRole.MemoryDomain domain -> domainRows "MemoryDomain" (box domain)
            | EdgeRole.SpatialModuleDomain domain -> domainRows "SpatialModuleDomain" (box domain)
            | _ ->
                for source in edge.Sources do addDependency DependencyKind.ProofSupport edge.Target source (Set.ofList (edge.Target :: edge.Sources))
                addSupport "Relation" (encode (box (edge.Class, edge.Role, edge.Ordinal, edge.Target, edge.Sources))) (Some edge.Target) (box edge)
        let regionMap =
            owners |> Map.toList |> List.groupBy snd |> List.map (fun (identity, nodes) ->
                let members = nodes |> List.map fst |> Set.ofList
                let root = members |> Seq.find (fun id -> names[id] = identity)
                let inputs = members |> Seq.map (fun id -> names[id] + ":" + nodeFingerprints[id]) |> Seq.sort |> String.concat "|"
                let proofInputs = supports |> Seq.filter (fun edge -> edge.Consumer = identity)
                                  |> Seq.map (fun edge -> edge.Domain + ":" + edge.Identity + ":" + edge.Fingerprint)
                                  |> Seq.sort |> String.concat "|"
                identity, { Identity = identity; Root = root; Members = members
                            Fingerprint = hash (inputs + "|" + proofInputs + "|" + encode (box graph.Platform)) }) |> Map.ofList
        if errors.Count > 0 then Result.Error(List.ofSeq errors) else
        Result.Ok { Regions = regionMap; Dependencies = deps |> Seq.distinct |> Seq.sort |> Seq.toList
                    SupportEdges = supports |> Seq.distinct |> Seq.sort |> Seq.toList
                    NodeIdentities = names; NodeOwners = owners; NodeFingerprints = nodeFingerprints }
    with :? InvalidOperationException as error ->
        Result.Error [SegmentationFailure.UnsupportedInput error.Message]

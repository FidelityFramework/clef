// SPDX-License-Identifier: MIT
/// Exact writable program inventory. The source owns object identities, held
/// representations and declared spaces. Backend commitment supplies observed
/// placement and the complete mapped-region extent; reservation is not proof
/// that independently emitted globals fit a linked image.
module Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorage

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
module Program = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization
module Authority = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority
module Environments = Clef.Compiler.Nanopass.ClosureEnvironmentSettlement
module Lazies = Clef.Compiler.Nanopass.LazyRuntime
module Sequences = Clef.Compiler.Nanopass.SequenceProgramInstances

/// Stable source identity within a reservation; it is not a target symbol.
let identityName = function
    | ProgramStorageIdentity.Allocation id -> sprintf "allocation:%d" (NodeId.value id)
    | ProgramStorageIdentity.BindingSlot id -> sprintf "binding:%d" (NodeId.value id)

let sourceOf = function
    | ProgramStorageIdentity.Allocation id | ProgramStorageIdentity.BindingSlot id -> id

let private toSpace (space: PlatformResolution.DeclaredSpace) : BAREWire.Platform.MemorySpace =
    { Name = space.Name; Kind = space.Kind; Capacity = space.Capacity
      Alignment = space.Alignment; Granularity = space.Granularity; Growth = space.Growth
      Access = space.Access; Base = space.Base; Notes = ""; MapKind = ""; Since = ""; Until = "" }

let private viewCarrier ty =
    match applySubst ty with
    | NativeType.TFun _ | NativeType.TLazy _ | NativeType.TSeq _ | NativeType.TSeqEnumerator _ -> true
    | _ -> false

let settle (graph: SemanticGraph) : ProgramStorageInventory =
    let codata = graph.Codata.Value
    // These are retained source residence claims, not allocations selected by
    // a successful authority lookup. Losing authority must not erase a claim.
    // Earlier proposal formation remains the owning residence recipe's work.
    let staticSites =
        codata.Escapes |> Map.toList |> List.choose (fun (site, residence) ->
            match residence, graph.Nodes.TryFind site with
            // A module-level mutable callable cell is a binding slot, never a static allocation.
            | EscapeKind.StaticLifetime, Some node when node.IsReachable && not (codata.MutableCallableStorage.ContainsKey site) -> Some(site, node)
            | _ -> None)
    match Program.read graph, graph.Platform with
    | _, None -> ProgramStorageInventory.empty
    | _, Some context when PlatformContext.substrateKind context = SubstrateKind.FPGA -> ProgramStorageInventory.empty
    | None, Some _ ->
        // Without a current startup plan nothing program-long is placed, and each such
        // site says so: static allocations, and module-level callable cells (binding
        // slots, which are not among the static allocation sites).
        let cells =
            codata.Escapes |> Map.toList |> List.choose (fun (site, residence) ->
                match residence, graph.Nodes.TryFind site with
                | EscapeKind.StaticLifetime, Some node when node.IsReachable && codata.MutableCallableStorage.ContainsKey site ->
                    Some(ProgramStorageIdentity.BindingSlot site, "The mutable callable cell lacks a current program startup plan")
                | _ -> None)
        { ProgramStorageInventory.empty with
            Unresolved =
                (staticSites |> List.map (fun (site, _) ->
                    ProgramStorageIdentity.Allocation site, "The retained static allocation lacks a current program startup plan"))
                @ cells |> Map.ofList }
    | Some plan, Some _ ->
        let mutable entries: Map<ProgramStorageIdentity, ProgramStorageEntry> = Map.empty
        let mutable unresolved: Map<ProgramStorageIdentity, string> = Map.empty
        let pending identity reason = unresolved <- Map.add identity reason unresolved
        let add identity shape bytes alignment (authority: Program.ValueAuthority) participants =
            let source = sourceOf identity
            match graph.Nodes.TryFind source with
            | Some node when node.IsReachable && bytes > 0 && alignment > 0 && (alignment &&& (alignment - 1)) = 0 ->
                let dependencies =
                    Set.union participants
                        (Set.union (Set.ofList (source :: authority.Evidence.Sources))
                                   (Authority.declarationInputs graph authority.Space.Node))
                entries <- entries.Add(identity,
                    { Identity = identity; SourceType = applySubst node.Type; Shape = shape
                      Bytes = bytes; Alignment = alignment; SpaceNode = authority.Space.Node
                      Space = toSpace authority.Space; Participants = dependencies })
            | _ -> pending identity "The source allocation or its exact positive extent/alignment is unavailable"
        for binding in plan.ValueBindings do
            let identity = ProgramStorageIdentity.BindingSlot binding
            match graph.Nodes.TryFind binding, Program.tryValueAuthority graph binding with
            | Some node, Some authority when node.IsReachable && codata.MutableCallableStorage.ContainsKey binding ->
                // The callable cell's protocol is its published storage contract; the slot
                // is its program-long residence and requires that residence fact.
                let storage = codata.MutableCallableStorage[binding]
                if codata.Escapes.TryFind binding <> Some EscapeKind.StaticLifetime then
                    pending identity "The mutable callable cell lacks its published program-long residence"
                else
                    match Placement.placeCallableCell graph storage with
                    | Ok(shape, bytes, alignment) ->
                        add identity shape bytes alignment authority
                            (Set.ofList (binding :: authority.Initializer.Initializer :: authority.Evidence.Sources))
                    | Error reason -> pending identity (sprintf "%A" reason)
            | Some node, None when node.IsReachable && codata.MutableCallableStorage.ContainsKey binding ->
                pending identity "The mutable callable cell lacks exact startup and mutable-space authority"
            | Some node, Some authority when node.IsReachable ->
                if not (viewCarrier node.Type) then
                    match Placement.placeProgramSlot graph binding with
                    | Ok(shape, bytes, alignment) ->
                        let entryInputs =
                            match shape, Clef.Compiler.Baker.Recipes.BoundaryDeclarations.entryFormation graph binding with
                            | ProgramStorageShape.NativeEntry formation, Some entry when entry.Formation = formation -> entry.Transport
                            | _ -> Set.empty
                        add identity shape bytes alignment authority
                            (Set.union entryInputs (Set.ofList (binding :: authority.Initializer.Initializer :: authority.Evidence.Sources)))
                    | Error reason -> pending identity (sprintf "%A" reason)
            | Some node, _ when node.IsReachable && not (viewCarrier node.Type) ->
                pending identity "The program binding lacks exact startup and mutable-space authority"
            | _ -> ()
        let callables =
            plan.ValueBindings |> Seq.choose (fun binding -> Environments.programInstance graph binding)
            |> Seq.choose (fun value -> value.Allocation |> Option.map (fun allocation -> allocation, value)) |> Map.ofSeq
        let lazies =
            plan.ValueBindings |> Seq.choose (fun binding ->
                Lazies.programInstance graph binding |> Option.map (fun (owner, allocation) -> allocation, owner)) |> Map.ofSeq
        let sequences =
            plan.ValueBindings |> Seq.choose (fun binding -> Sequences.programInstance graph binding)
            |> Seq.map (fun value -> value.Allocation, value) |> Map.ofSeq
        for site, node in staticSites do
            let identity = ProgramStorageIdentity.Allocation site
            match Authority.authority graph site with
            | Some(authority, dependencies) ->
                let proofDependencies obligations =
                    graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && List.contains edge.Target obligations)
                    |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList |> Set.union dependencies
                match node.Kind with
                | SemanticKind.EnvironmentCreate(owner, _) | SemanticKind.EnvironmentAllocate owner ->
                    match codata.EnvironmentLayouts.TryFind owner, callables.TryFind site with
                    | Some layout, Some instance ->
                        add identity ProgramStorageShape.Bytes layout.Bytes layout.Alignment authority
                            (Set.union instance.Participants (proofDependencies layout.Obligations))
                    | _ -> pending identity "The actual static callable instance and its typed layout are not jointly established"
                | SemanticKind.LazyEnvironment(owner, _) | SemanticKind.LazyAllocate owner ->
                    match codata.LazyLayouts.TryFind owner, lazies.TryFind site with
                    | Some layout, Some actual when owner = actual && Lazies.validate graph layout ->
                        add identity ProgramStorageShape.Bytes layout.Bytes layout.Alignment authority (proofDependencies layout.Obligations)
                    | _ -> pending identity "The actual static Lazy instance and its typed layout are not jointly established"
                | SemanticKind.SeqExpr _ | SemanticKind.ContinuationAllocate _ ->
                    let owner = match node.Kind with SemanticKind.ContinuationAllocate owner -> owner | _ -> site
                    match codata.ContinuationFrames.TryFind owner, sequences.TryFind site with
                    | Some frame, Some instance when instance.Owner = owner && instance.Generator = frame.Generator ->
                        add identity ProgramStorageShape.Bytes frame.Bytes frame.Alignment authority
                            (Set.union instance.Participants (proofDependencies frame.Obligations))
                    | _ -> pending identity "The actual static continuation instance and its frame layout are not jointly established"
                | SemanticKind.RecordExpr _ | SemanticKind.TupleExpr _ | SemanticKind.DUConstruct _ ->
                    let key = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type
                    match graph.Layouts.Value.TryFind key with
                    | Some(SettledLayout.Record(_, Some bytes, Some alignment))
                    | Some(SettledLayout.Union(_, _, Some bytes, Some alignment)) ->
                        add identity ProgramStorageShape.Bytes bytes alignment authority dependencies
                    | _ -> pending identity "The program aggregate backing has no settled source layout"
                | _ -> pending identity "This static allocation requires its owning source storage contract"
            | None -> pending identity "The retained static allocation lacks exact startup and mutable-space authority"
        let mutable reservations = Map.empty
        for spaceNode, values in entries.Values |> Seq.groupBy _.SpaceNode do
            let values = List.ofSeq values
            let space = values.Head.Space
            let requests: BAREWire.Platform.StorageRequest array =
                values |> List.sortBy _.Identity |> List.map (fun value ->
                    ({ Name = identityName value.Identity; Length = int64 value.Bytes; Alignment = value.Alignment }: BAREWire.Platform.StorageRequest)) |> List.toArray
            match BAREWire.Platform.WritableStorage.reserve space requests with
            | Ok reservation -> reservations <- reservations.Add(spaceNode, reservation)
            | Error findings ->
                let reason = findings |> Array.map (fun finding -> finding.Kind + ": " + finding.Message) |> String.concat "; "
                for value in values do pending value.Identity reason
        { Entries = entries; Reservations = reservations; Unresolved = unresolved }

/// Recompute against the current graph before native consumption. Stale codata
/// may not retain a capacity/layout/startup result from a previous snapshot.
type private InventoryReading = { Current: ProgramStorageInventory; Agrees: bool }
let private readings = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, InventoryReading>()
let private reading graph =
    readings.GetValue(graph, fun currentGraph ->
        let current = settle currentGraph
        { Current = current; Agrees = current = currentGraph.Codata.Value.ProgramStorage })

/// One current source reading, shared by validation and its located failures.
/// It includes unresolved allocations and is not an admission result.
let inspect (graph: SemanticGraph) = (reading graph).Current

let read (graph: SemanticGraph) =
    let result = reading graph
    if result.Agrees then Some result.Current else None

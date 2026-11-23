// SPDX-License-Identifier: MIT
/// Pure, cone-scoped SSA assignment and NodeId reconciliation nanopass.
///
/// In the Fidelity architecture, Alex witnesses values directly from published
/// `NodeId`s and ordinals (`Alex.Traversal.Values.value nodeId k = V(NodeId.value nodeId, k)`).
/// Where graph structure is unchanged (outside the delta cone in selective rebuild),
/// `reconcileAndAssign` retains the baseline `NodeId`s and `SSAId(node, ordinal)`
/// assignments across the graph and its codata; where structure is affected or newly
/// elaborated, `NodeId`s and `SSAId(node, ordinal)` assignments advance monotonically
/// above the baseline high-water mark without reuse; and a full release rebuild
/// (`normalize`) starts cold from the freshly reset graph without carrying prior state.
module Clef.Compiler.Nanopass.SSAAssignment

open System
open System.Collections
open System.Reflection
open Microsoft.FSharp.Reflection
open Clef.Compiler.Baker.Ingredients
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

let nodeOf (SSAId(n, _)) = n
let ordinalOf (SSAId(_, k)) = k

let private flags = BindingFlags.Public ||| BindingFlags.NonPublic

let private isEmptyEnumerable (value: obj) =
    let enumerator = (value :?> IEnumerable).GetEnumerator()
    not (enumerator.MoveNext())

let private isLeafType (ty: Type) =
    ty.IsPrimitive
    || ty.IsEnum
    || ty = typeof<string>
    || ty = typeof<bigint>
    || ty = typeof<decimal>
    || ty = typeof<NativeType>
    || ty = typeof<TypeIdentity>
    || ty = typeof<NominalTypeIdentity>
    || ty = typeof<ConstructorIdentity>
    || ty = typeof<Fidelity.PSG.TypeIdentity>
    || ty = typeof<Fidelity.PSG.NominalTypeIdentity>
    || ty = typeof<Fidelity.PSG.ConstructorIdentity>
    || ty = typeof<SpecializationTrace>
    || ty.Name = "SpecializationTrace"
    || ty = typeof<SourceRange>
    || ty = typeof<Fidelity.PSG.SourceRange>
    || ty = typeof<ValueRange>
    || ty = typeof<Fidelity.PSG.ValueRange>
    || ty = typeof<PlatformContext>
    || ty = typeof<Fidelity.PSG.PlatformWidths>
    || ty = typeof<SSAAssignmentPlan>

// Legacy CLR reflection. The self-hosting core requires typed SSA correspondence.
// https://forge.spkez.dev/FidelityFramework/clef/issues/175#issuecomment-11812
let rec private remapValue (remap: NodeId -> NodeId) (ty: Type) (value: objnull) : objnull =
    match value with
    | null -> null
    | _ when ty = typeof<NodeId> ->
        box (remap (unbox<NodeId> value))
    | _ when ty = typeof<Fidelity.PSG.NodeId> ->
        let (Fidelity.PSG.NodeId n) = unbox<Fidelity.PSG.NodeId> value
        box (Fidelity.PSG.NodeId(NodeId.value (remap (NodeId n))))
    | _ when isLeafType ty ->
        value
    | _ ->
        let value = Option.ofObj value |> Option.get
        let actualTy = value.GetType()
        if isLeafType actualTy then
            box value
        elif actualTy.IsArray then
            let elemTy = actualTy.GetElementType() |> Option.ofObj |> Option.get
            let src = value :?> Array
            if src.Length = 0 then
                box value
            else
                let dst = Array.CreateInstance(elemTy, src.Length)
                for i = 0 to src.Length - 1 do
                    dst.SetValue(remapValue remap elemTy (src.GetValue i), i)
                box dst
        elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<option<_>> then
            let elemTy = ty.GetGenericArguments().[0]
            let case, fields = FSharpValue.GetUnionFields(value, ty, flags)
            if fields.Length = 0 then
                null
            else
                let mapped = remapValue remap elemTy fields.[0]
                FSharpValue.MakeUnion(case, [| mapped |], flags)
        elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<list<_>> then
            if isEmptyEnumerable value then
                box value
            else
                let elemTy = ty.GetGenericArguments().[0]
                let items =
                    (value :?> IEnumerable)
                    |> Seq.cast<objnull>
                    |> Seq.map (remapValue remap elemTy)
                    |> Seq.toArray
                let cases = FSharpType.GetUnionCases(ty, flags)
                let nilCase = cases |> Array.find (fun c -> c.GetFields().Length = 0)
                let consCase = cases |> Array.find (fun c -> c.GetFields().Length = 2)
                let mutable acc = FSharpValue.MakeUnion(nilCase, [||], flags)
                for i = items.Length - 1 downto 0 do
                    acc <- FSharpValue.MakeUnion(consCase, [| items.[i]; acc |], flags)
                acc
        elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<Set<_>> then
            if isEmptyEnumerable value then
                box value
            else
                let elemTy = ty.GetGenericArguments().[0]
                let items =
                    (value :?> IEnumerable)
                    |> Seq.cast<objnull>
                    |> Seq.map (remapValue remap elemTy)
                    |> Seq.toArray
                let arr = Array.CreateInstance(elemTy, items.Length)
                for i = 0 to items.Length - 1 do
                    arr.SetValue(items.[i], i)
                Activator.CreateInstance(ty, [| box arr |])
        elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<Map<_, _>> then
            if isEmptyEnumerable value then
                box value
            else
                let args = ty.GetGenericArguments()
                let keyTy, valTy = args.[0], args.[1]
                let tupleTy = FSharpType.MakeTupleType [| keyTy; valTy |]
                let kvpTy = typedefof<Collections.Generic.KeyValuePair<_, _>>.MakeGenericType(args)
                let propKey = kvpTy.GetProperty("Key") |> Option.ofObj |> Option.get
                let propVal = kvpTy.GetProperty("Value") |> Option.ofObj |> Option.get
                let items =
                    (value :?> IEnumerable)
                    |> Seq.cast<obj>
                    |> Seq.map (fun kvp ->
                        let k = remapValue remap keyTy (propKey.GetValue kvp)
                        let v = remapValue remap valTy (propVal.GetValue kvp)
                        FSharpValue.MakeTuple([| k; v |], tupleTy))
                    |> Seq.toArray
                let arr = Array.CreateInstance(tupleTy, items.Length)
                for i = 0 to items.Length - 1 do
                    arr.SetValue(items.[i], i)
                Activator.CreateInstance(ty, [| box arr |])
        elif FSharpType.IsTuple ty then
            let elemTys = FSharpType.GetTupleElements ty
            let fields = FSharpValue.GetTupleFields value
            let mapped = (elemTys, fields) ||> Array.map2 (remapValue remap)
            FSharpValue.MakeTuple(mapped, ty)
        elif FSharpType.IsRecord(ty, flags) then
            let props = FSharpType.GetRecordFields(ty, flags)
            let fields = FSharpValue.GetRecordFields(value, flags)
            let mapped = (props, fields) ||> Array.map2 (fun p v -> remapValue remap p.PropertyType v)
            FSharpValue.MakeRecord(ty, mapped, flags)
        elif FSharpType.IsUnion(ty, flags) then
            let case, fields = FSharpValue.GetUnionFields(value, ty, flags)
            let props = case.GetFields()
            if props.Length = 0 then
                box value
            else
                let mapped = (props, fields) ||> Array.map2 (fun p v -> remapValue remap p.PropertyType v)
                FSharpValue.MakeUnion(case, mapped, flags)
        else
            box value

let private remapTyped<'T> (remap: NodeId -> NodeId) (value: 'T) : 'T =
    remapValue remap typeof<'T> (box value) |> unbox<'T>

let private remapEdges remap (edges: Hyperedge list) =
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let domainRows (edge: Hyperedge) =
        let target = edge.Target
        match edge.Role with
        | EdgeRole.BoundaryDomain d -> Some (Boundaries.domainRow target d, Boundaries.domainRewrite target d)
        | EdgeRole.NumericDomain d -> Some (NumericValues.domainRow target d, NumericValues.domainRewrite target d)
        | EdgeRole.MemoryDomain d -> Some (MemoryValues.domainRow target d, MemoryValues.domainRewrite target d)
        | EdgeRole.SpatialModuleDomain d -> Some (SpatialValues.domainRow target d, SpatialValues.domainRewrite target d)
        | _ -> None
    let mapped = remapTyped<Hyperedge list> remap edges
    let domains =
        (Map.empty, edges, mapped)
        |||> List.fold2 (fun domains original current ->
            match domainRows original with
            | Some (row, rewrite) when key row = key original ->
                match domainRows current with
                | Some (nextRow, nextRewrite) ->
                    Map.change original.Target (function
                        | None -> Some (Some (row, rewrite, nextRow, nextRewrite))
                        | Some _ -> Some None) domains
                | None -> domains
            | _ -> domains)
    let reorder (current: Hyperedge) (expected: Hyperedge) =
        if current.Class = expected.Class && current.Role = expected.Role &&
           current.Ordinal = expected.Ordinal && current.Target = expected.Target &&
           List.sort current.Sources = List.sort expected.Sources then
            { current with Sources = expected.Sources }
        else current
    (edges, mapped)
    ||> List.map2 (fun original current ->
        match Map.tryFind original.Target domains with
        | Some (Some (row, _, next, _)) when key original = key row -> reorder current next
        | Some (Some (_, rewrite, _, next)) when key original = key rewrite -> reorder current next
        | _ -> current)

let rec private remapGraph (remap: NodeId -> NodeId) (graph: SemanticGraph) : SemanticGraph =
    { graph with
        Nodes = remapTyped<Map<NodeId, SemanticNode>> remap graph.Nodes
        DeclarationRoots = remapTyped<(NodeId * DeclRoot) list> remap graph.DeclarationRoots
        Modules = remapTyped<Map<ModulePath, NodeId list>> remap graph.Modules
        Types = lazy (remapTyped<Map<string, NodeId>> remap graph.Types.Value)
        ModuleClassifications = lazy (remapTyped<Map<NodeId, ModuleClassification>> remap graph.ModuleClassifications.Value)
        StaticStringPool = remapTyped<StaticStringPool option> remap graph.StaticStringPool
        LiteralStorage = remapTyped<Map<NodeId, LiteralStorage>> remap graph.LiteralStorage
        Escaping = lazy (remapTyped<Map<NodeId, string>> remap graph.Escaping.Value)
        Codata = lazy (remapTyped<Codata> remap graph.Codata.Value)
        Edges = remapEdges remap graph.Edges
        WitnessProvenance =
            graph.WitnessProvenance
            |> Option.map (fun p -> { PreparedRoots = remapGraph remap p.PreparedRoots })
        SequenceRangeProvenance = remapTyped<SequenceRangeAuthority option> remap graph.SequenceRangeProvenance
        RangeContextFacts = remapTyped<RangeContextFacts option> remap graph.RangeContextFacts }

let [<Literal>] Family = 512

let value (nodeId: NodeId) (ordinal: int) : SSAId =
    SSAId(NodeId.value nodeId, ordinal)

let familyValues (nodeId: NodeId) : SSAId list =
    List.init Family (value nodeId)

let private isAssignableNode (node: SemanticNode) : bool =
    match node.Kind with
    | SemanticKind.ModuleDef _
    | SemanticKind.TypeDef _
    | SemanticKind.Obligation _
    | SemanticKind.Error _ -> false
    | _ -> true

let private slotsForNode (nodeId: NodeId) (node: SemanticNode) : SSAId list =
    if not (isAssignableNode node) then
        []
    else
        familyValues nodeId

let private orderedReachableNodes (graph: SemanticGraph) : (NodeId * SemanticNode) list =
    graph.Nodes
    |> Map.toList
    |> List.filter (fun (_, node) -> node.IsReachable && isAssignableNode node)
    |> List.sortBy (fun (id, _) -> NodeId.value id)

let private occupiedHighWater (graph: SemanticGraph) : int =
    max 0 (Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.maxOccupiedNodeId graph)

/// Full-compilation cold-start SSA assignment pass.
let normalize (graph: SemanticGraph) : SemanticGraph =
    let reachable = orderedReachableNodes graph
    let assignments =
        reachable
        |> List.map (fun (id, node) -> id, slotsForNode id node)
        |> Map.ofList
    let assignedIds = assignments |> Map.keys |> Set.ofSeq
    let identityRemap =
        graph.Nodes.Keys
        |> Seq.map (fun id -> id, id)
        |> Map.ofSeq
    let codata = graph.Codata.Value
    let plan : SSAAssignmentPlan =
        { Assignments = assignments
          NodeHighWater = occupiedHighWater graph
          NodeRemap = identityRemap
          RetainedNodes = Set.empty
          ReassignedNodes = assignedIds }
    { graph with Codata = lazy { codata with SSAAssignment = Some plan } }

[<RequireQualifiedAccess>]
type ReconciliationFailure =
    | MissingBaselinePlan
    | MissingRetainedAssignment of NodeId
    | MissingRetainedCorrespondence of NodeId
    | AmbiguousRetainedCorrespondence of Diagnostic
    | InvalidCorrespondenceBaseline of SegmentationFailure list
    | InvalidCorrespondenceCandidate of SegmentationFailure list
    | InvalidReturnedIdentities of (NodeId * string) list

let private uncheckedPhysicalCorrespondence baseline candidate (correspondences: Map<NodeId, NodeId option>) =
    if correspondences.IsEmpty then None
    else
        match physicalOccurrenceAddresses baseline, physicalOccurrenceAddresses candidate with
        | Result.Error failures, _ -> Some(ReconciliationFailure.InvalidCorrespondenceBaseline failures)
        | _, Result.Error failures -> Some(ReconciliationFailure.InvalidCorrespondenceCandidate failures)
        | Result.Ok prior, Result.Ok current ->
            correspondences
            |> Map.toSeq
            |> Seq.tryPick (fun (receiving, predecessor) ->
                let address = predecessor |> Option.bind prior.TryFind
                if address.IsSome && address = current.TryFind receiving then None
                else Some(ReconciliationFailure.MissingRetainedCorrespondence receiving))

/// Cone-scoped selective-rebuild SSA reconciliation and assignment.
/// Retained structure outside the delta cone keeps its baseline `NodeId`s and
/// `SSAId(node, ordinal)` assignments across the graph and codata; affected or
/// newly elaborated nodes advance above the prior high-water mark and any
/// relation identities held in place.
let private reconcileAndAssignCore
    transportCallableRelations
    (baseline: SemanticGraph)
    (baselinePlan: SSAAssignmentPlan)
    (alignment: Map<NodeId, NodeId>)
    (retainedCandidateNodes: Set<NodeId>)
    (candidate: SemanticGraph)
    : Result<SemanticGraph * SSAAssignmentPlan, ReconciliationFailure> =
    let baselineFacts = baseline.Codata.Value
    let candidateFacts = candidate.Codata.Value
    let sameIdentityClass baseId candId =
        (baseline.Nodes.ContainsKey baseId && candidate.Nodes.ContainsKey candId)
        || (transportCallableRelations &&
            ((baselineFacts.CallableContracts.ContainsKey baseId && candidateFacts.CallableContracts.ContainsKey candId)
             || (baselineFacts.CallableAggregateSlots.ContainsKey baseId && candidateFacts.CallableAggregateSlots.ContainsKey candId)))
    let candToBase =
        alignment
        |> Map.fold (fun acc baseId candId ->
            if Set.contains candId retainedCandidateNodes && sameIdentityClass baseId candId then
                let correspondence = if Map.containsKey candId acc then None else Some baseId
                Map.add candId correspondence acc
            else
                acc) Map.empty
    // A region selected for retention already owns its exact SSA family.
    // Check that authority before remapping the graph or creating any families.
    let reachable = orderedReachableNodes candidate
    let retainedRefusal =
        retainedCandidateNodes
        |> Seq.tryPick (fun source ->
            match candToBase.TryFind source with
            | None -> Some(ReconciliationFailure.MissingRetainedCorrespondence source)
            | Some None ->
                let range = candidate.Nodes.TryFind source |> Option.map _.Range |> Option.defaultValue dummyRange
                Some(ReconciliationFailure.AmbiguousRetainedCorrespondence
                    { Severity = NativeDiagnosticSeverity.Error
                      Code = "CCS8407"
                      Message = "The retained occurrence has more than one admissible baseline identity."
                      Range = range
                      RelatedNodes = [source]
                      Reachability = ReachabilityContext.Unknown })
            | Some (Some id) ->
                match candidate.Nodes.TryFind source with
                | Some node when node.IsReachable && isAssignableNode node ->
                    match baselinePlan.Assignments.TryFind id with
                    | Some (_ :: _) -> None
                    | _ -> Some(ReconciliationFailure.MissingRetainedAssignment id)
                | _ -> None)
    let refusal =
        retainedRefusal |> Option.orElseWith (fun () ->
            if transportCallableRelations then None
            else uncheckedPhysicalCorrespondence baseline candidate candToBase)
    match refusal with
    | Some failure -> Result.Error failure
    | None ->
        // Temporary source coordinates do not contribute to destination history.
        // A callable identity left in place is an occupied destination coordinate.
        let initialHighWater =
            max baselinePlan.NodeHighWater (occupiedHighWater baseline)
        let assign (remap, highWater, retainedSet) candId =
            match candToBase.TryFind candId with
            | Some (Some baseId) ->
                Map.add candId baseId remap, highWater, Set.add baseId retainedSet
            | _ ->
                let nextId = highWater + 1
                Map.add candId (NodeId nextId) remap, nextId, retainedSet
        let relationRemap, relationHighWater =
            let ids = Seq.append candidateFacts.CallableContracts.Keys candidateFacts.CallableAggregateSlots.Keys
            if transportCallableRelations then
                let remap, highWater, _ =
                    ids
                    |> Seq.sortBy NodeId.value
                    |> Seq.fold assign (Map.empty, initialHighWater, Set.empty)
                remap, highWater
            else
                let occupied = ids |> Seq.fold (fun highWater id -> max highWater (NodeId.value id)) initialHighWater
                Map.empty, occupied
        let nodeRemap, finalHighWater, retainedReconciled =
            candidate.Nodes.Keys
            |> Seq.sortBy NodeId.value
            |> Seq.fold assign (Map.empty, relationHighWater, Set.empty)
        let remapNodeId (id: NodeId) : NodeId =
            match nodeRemap.TryFind id with
            | Some mapped -> mapped
            | None -> relationRemap.TryFind id |> Option.defaultValue id
        let assignments, retainedAssigned, reassigned =
            reachable
            |> List.fold (fun (acc, retained, fresh) (source, node) ->
                let id = nodeRemap[source]
                if Set.contains id retainedReconciled then
                    Map.add id baselinePlan.Assignments[id] acc, Set.add id retained, fresh
                else
                    Map.add id (slotsForNode id node) acc, retained, Set.add id fresh)
                (Map.empty, Set.empty, Set.empty)
        let plan : SSAAssignmentPlan =
            { Assignments = assignments
              NodeHighWater = finalHighWater
              NodeRemap = nodeRemap
              RetainedNodes = retainedAssigned
              ReassignedNodes = reassigned }
        let remappedGraph = remapGraph remapNodeId candidate
        let codata = remappedGraph.Codata.Value
        match Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.validateTypedIdentities
                  remappedGraph.Nodes codata.CallableContracts codata.CallableAggregateSlots with
        | Result.Error failures -> Result.Error(ReconciliationFailure.InvalidReturnedIdentities failures)
        | Result.Ok () ->
            let reconciledGraph =
                { remappedGraph with Codata = lazy { codata with SSAAssignment = Some plan } }
            Result.Ok(reconciledGraph, plan)

let private reconcileExistingPlan transportCallableRelations (baseline: SemanticGraph) alignment retainedCandidateNodes candidate =
    match baseline.Codata.Value.SSAAssignment with
    | Some plan -> reconcileAndAssignCore transportCallableRelations baseline plan alignment retainedCandidateNodes candidate
    | None -> Result.Error ReconciliationFailure.MissingBaselinePlan

/// Reassign structural occurrences and keep existing callable relation identities.
let reconcileAndAssign baseline alignment retainedCandidateNodes candidate =
    reconcileExistingPlan false baseline alignment retainedCandidateNodes candidate

/// Transport identities from the checked pair and its actual scoped Baker result.
let internal reconcileAndAssignWithCallableRelations scoped retainedCandidateNodes =
    let baseline, candidate, alignment, _ = scopedRebuildInputs scoped
    reconcileExistingPlan true baseline alignment retainedCandidateNodes candidate

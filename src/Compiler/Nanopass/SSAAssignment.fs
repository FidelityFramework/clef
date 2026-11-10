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
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

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
        Edges = remapTyped<Hyperedge list> remap graph.Edges
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

let private maxGraphNodeId (graph: SemanticGraph) : int =
    if graph.Nodes.IsEmpty then
        0
    else
        graph.Nodes.Keys |> Seq.map NodeId.value |> Seq.max

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
    let plan : SSAAssignmentPlan =
        { Assignments = assignments
          NodeHighWater = maxGraphNodeId graph
          NodeRemap = identityRemap
          RetainedNodes = Set.empty
          ReassignedNodes = assignedIds }
    let codata = graph.Codata.Value
    { graph with Codata = lazy { codata with SSAAssignment = Some plan } }

/// Cone-scoped selective-rebuild SSA reconciliation and assignment.
/// Retained structure outside the delta cone keeps its baseline `NodeId`s and
/// `SSAId(node, ordinal)` assignments across the graph and codata; affected or
/// newly elaborated nodes advance monotonically above `baselinePlan.NodeHighWater`
/// without reusing prior identifiers.
let reconcileAndAssign
    (baseline: SemanticGraph)
    (alignment: Map<NodeId, NodeId>)
    (retainedCandidateNodes: Set<NodeId>)
    (candidate: SemanticGraph)
    : SemanticGraph * SSAAssignmentPlan =
    let baselineWithPlan =
        match baseline.Codata.Value.SSAAssignment with
        | Some _ -> baseline
        | None -> normalize baseline
    let baselinePlan = baselineWithPlan.Codata.Value.SSAAssignment.Value
    let candToBase =
        alignment
        |> Map.fold (fun acc baseId candId ->
            if Set.contains candId retainedCandidateNodes && baselineWithPlan.Nodes.ContainsKey baseId then
                Map.add candId baseId acc
            else
                acc) Map.empty
    let initialHighWater = max baselinePlan.NodeHighWater (maxGraphNodeId baselineWithPlan)
    let orderedCandIds =
        candidate.Nodes.Keys
        |> Seq.sortBy NodeId.value
        |> Seq.toList
    let nodeRemap, finalHighWater, retainedReconciled =
        orderedCandIds
        |> List.fold (fun (remap: Map<NodeId, NodeId>, highWater: int, retainedSet: Set<NodeId>) candId ->
            match candToBase.TryFind candId with
            | Some baseId ->
                Map.add candId baseId remap, max highWater (NodeId.value baseId), Set.add baseId retainedSet
            | None ->
                let nextId = highWater + 1
                let freshNodeId = NodeId nextId
                Map.add candId freshNodeId remap, nextId, retainedSet)
            (Map.empty, initialHighWater, Set.empty)
    let remapNodeId (id: NodeId) : NodeId =
        match nodeRemap.TryFind id with
        | Some mapped -> mapped
        | None -> id
    let remappedGraph = remapGraph remapNodeId candidate
    let reachable = orderedReachableNodes remappedGraph
    let assignments, retainedAssigned, reassigned =
        reachable
        |> List.fold (fun (acc: Map<NodeId, SSAId list>, ret: Set<NodeId>, reas: Set<NodeId>) (id, node) ->
            if Set.contains id retainedReconciled then
                let slots =
                    match baselinePlan.Assignments.TryFind id with
                    | Some existing when not existing.IsEmpty -> existing
                    | _ -> slotsForNode id node
                Map.add id slots acc, Set.add id ret, reas
            else
                let slots = slotsForNode id node
                Map.add id slots acc, ret, Set.add id reas)
            (Map.empty, Set.empty, Set.empty)
    let plan : SSAAssignmentPlan =
        { Assignments = assignments
          NodeHighWater = finalHighWater
          NodeRemap = nodeRemap
          RetainedNodes = retainedAssigned
          ReassignedNodes = reassigned }
    let codata = remappedGraph.Codata.Value
    let reconciledGraph =
        { remappedGraph with Codata = lazy { codata with SSAAssignment = Some plan } }
    reconciledGraph, plan

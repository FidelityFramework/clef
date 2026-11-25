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

let private normalizeContiguousRuns (isMatch: Participant -> bool) (renumber: bool) (participants: Participant list) : Participant list =
    let flushRun (runRev: Participant list) (acc: Participant list) =
        let sorted =
            runRev
            |> List.rev
            |> List.sortBy (fun p -> p.Node, p.Group, p.Ordinal)
        let normalized =
            if renumber then sorted |> List.mapi (fun i p -> { p with Ordinal = i })
            else sorted
        List.rev normalized @ acc
    let rec loop (runRev: Participant list) (acc: Participant list) (remaining: Participant list) =
        match remaining with
        | [] ->
            let finalAcc = if runRev.IsEmpty then acc else flushRun runRev acc
            List.rev finalAcc
        | head :: tail when isMatch head ->
            loop (head :: runRev) acc tail
        | head :: tail ->
            let nextAcc = if runRev.IsEmpty then acc else flushRun runRev acc
            loop [] (head :: nextAcc) tail
    loop [] [] participants

let private normalizeRuntimeParticipants (runtime: MemoryRegionRuntime) : MemoryRegionRuntime =
    let ordered =
        runtime.Participants
        |> normalizeContiguousRuns (fun p -> p.Role = ParticipantRole.RegionRuntimeDescriptor) true
        |> normalizeContiguousRuns (fun p -> p.Role = ParticipantRole.RegionRuntimeAcquire) true
        |> normalizeContiguousRuns (fun p -> p.Role = ParticipantRole.RegionRuntimeRelease) true
    { runtime with Participants = ordered }

let private normalizeMemoryOperation (operation: MemoryWitnessOperation) : MemoryWitnessOperation =
    match operation with
    | MemoryWitnessOperation.Region witness ->
        let participants =
            witness.Participants
            |> normalizeContiguousRuns (fun p -> p.Role = ParticipantRole.RegionDeclaration) false
        let runtime = witness.Runtime |> Option.map normalizeRuntimeParticipants
        MemoryWitnessOperation.Region { witness with Participants = participants; Runtime = runtime }
    | _ -> operation

let private normalizeEdge (edge: Hyperedge) : Hyperedge =
    match edge.Role with
    | EdgeRole.BoundaryDomain d ->
        { edge with
            Role =
                EdgeRole.BoundaryDomain
                    { d with
                        Imports = List.sort d.Imports
                        Entries = List.sort d.Entries
                        Calls = List.sort d.Calls } }
    | EdgeRole.MemoryDomain d ->
        let operations = d.Operations |> List.map (fun (site, op) -> site, normalizeMemoryOperation op)
        { edge with Role = EdgeRole.MemoryDomain { d with Operations = operations } }
    | EdgeRole.MemoryOperation op ->
        { edge with Role = EdgeRole.MemoryOperation (normalizeMemoryOperation op) }
    | _ -> edge

let private remapEdges remap (edges: Hyperedge list) =
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let unorderedKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, List.sort edge.Sources, edge.Target
    let callsBySite (rows: Hyperedge list) =
        rows
        |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCall call -> Some (call.Site, call) | _ -> None)
        |> Map.ofList
    let companionRows (calls: Map<NodeId, BoundaryCall>) (edge: Hyperedge) =
        let target = edge.Target
        match edge.Role with
        | EdgeRole.BoundaryDomain d ->
            [ Boundaries.domainRow target d; Boundaries.domainRewrite target d ]
            @ (d.IntrinsicDeclarations |> List.map (fun (site, imp) -> StringBytes.abiRow site imp))
            @ (d.IntrinsicImports |> List.map StringBytes.importRow)
            @ (d.IntrinsicCalls |> List.collect StringBytes.callRows)
            @ (d.IntrinsicProofs |> List.collect StringBytes.proofRows)
        | EdgeRole.BoundaryImport import -> [ Boundaries.importRow import ]
        | EdgeRole.BoundaryResourceDeclaration row -> [ Boundaries.row (EdgeRole.BoundaryResourceDeclaration row) 0 (Set.toList row.Participants) row.Identity ]
        | EdgeRole.BoundaryWritableBufferDeclaration row -> [ Boundaries.row (EdgeRole.BoundaryWritableBufferDeclaration row) 0 (Set.toList row.Participants) row.Identity ]
        | EdgeRole.BoundaryWritableBufferUse row -> [ Boundaries.row (EdgeRole.BoundaryWritableBufferUse row) 0 (Set.toList row.Participants) row.Call ]
        | EdgeRole.BoundaryBufferAbsence row -> [ Boundaries.row (EdgeRole.BoundaryBufferAbsence row) 0 (row.DeclarationFacts |> Map.keys |> Seq.toList) row.Quote ]
        | EdgeRole.BoundaryResourceAccess row -> [ Boundaries.row (EdgeRole.BoundaryResourceAccess row) 0 (Set.toList row.Participants) row.Site ]
        | EdgeRole.BoundaryEntry entry -> [ Boundaries.row (EdgeRole.BoundaryEntry entry) 0 (Set.toList entry.Participants) entry.Formation ]
        | EdgeRole.BoundaryCallbackInvocation invocation -> [ Boundaries.row (EdgeRole.BoundaryCallbackInvocation invocation) 0 (Set.toList invocation.Participants) invocation.Identity ]
        | EdgeRole.BoundaryCallbackAbsence row -> [ Boundaries.row (EdgeRole.BoundaryCallbackAbsence row) 0 (row.DeclarationFacts |> Map.keys |> Seq.toList) row.Quote ]
        | EdgeRole.BoundaryClosedEntry entry -> [ Boundaries.row (EdgeRole.BoundaryClosedEntry entry) 0 (Set.toList entry.Participants) entry.Formation ]
        | EdgeRole.BoundaryCall call -> Boundaries.callRow call :: Boundaries.operandRows call
        | EdgeRole.BoundaryCoverage coverage ->
            match calls.TryFind coverage.Site with
            | Some call -> Boundaries.coverageRows call coverage (Boundaries.coverageOutcome coverage)
            | None -> []
        | EdgeRole.NumericDomain d -> [ NumericValues.domainRow target d; NumericValues.domainRewrite target d ]
        | EdgeRole.MemoryDomain d ->
            let operations = Map.ofList d.Operations
            [ MemoryValues.domainRow target d; MemoryValues.domainRewrite target d ]
            @ (d.Operations |> List.map (MemoryValues.operationRow operations))
            @ (d.Proofs |> List.collect MemoryValues.proofRows)
            @ (d.ArrayCopies |> List.map MemoryValues.copyRow)
            @ (d.AllocationConstructions |> List.map MemoryValues.allocationConstructionRow)
            @ (d.CopyConstructions |> List.map MemoryValues.copyConstructionRow)
        | EdgeRole.SpatialModuleDomain d -> [ SpatialValues.domainRow target d; SpatialValues.domainRewrite target d ]
        | _ -> []
    let mapped = remapTyped<Hyperedge list> remap edges |> List.map normalizeEdge
    let origCalls = callsBySite edges
    let currCalls = callsBySite mapped
    let expectedByPair =
        (Map.empty, edges, mapped)
        |||> List.fold2 (fun acc original current ->
            let origRows = companionRows origCalls original
            let currRows = companionRows currCalls current
            if origRows.IsEmpty || origRows.Length <> currRows.Length then acc
            else
                (acc, origRows, currRows)
                |||> List.fold2 (fun state origExpected currExpected ->
                    let pairKey = key origExpected, unorderedKey currExpected
                    Map.change pairKey (function
                        | None -> Some (Some currExpected)
                        | Some _ -> Some None) state))
    (edges, mapped)
    ||> List.map2 (fun original current ->
        match Map.tryFind (key original, unorderedKey current) expectedByPair with
        | Some (Some expected) when current.Sources <> expected.Sources ->
            { current with Sources = expected.Sources }
        | _ -> current)

let rec private remapGraph (remap: NodeId -> NodeId) (graph: SemanticGraph) : Result<SemanticGraph, NodeId * string> =
    let provenanceResult =
        match graph.WitnessProvenance with
        | None -> Result.Ok None
        | Some p ->
            remapGraph remap p.PreparedRoots
            |> Result.map (fun roots -> Some { PreparedRoots = roots })
    provenanceResult
    |> Result.bind (fun provenance ->
        let remappedCodata =
            lazy
                let codata = remapTyped<Codata> remap graph.Codata.Value
                match codata.WitnessEmission with
                | None -> codata
                | Some emission ->
                    let operations = emission.Memory.Operations |> Map.map (fun _ -> normalizeMemoryOperation)
                    { codata with WitnessEmission = Some { emission with Memory = { emission.Memory with Operations = operations } } }
        let remapped =
            { graph with
                Nodes = remapTyped<Map<NodeId, SemanticNode>> remap graph.Nodes
                DeclarationRoots = remapTyped<(NodeId * DeclRoot) list> remap graph.DeclarationRoots
                Modules = remapTyped<Map<ModulePath, NodeId list>> remap graph.Modules
                Types = lazy (remapTyped<Map<string, NodeId>> remap graph.Types.Value)
                ModuleClassifications = lazy (remapTyped<Map<NodeId, ModuleClassification>> remap graph.ModuleClassifications.Value)
                StaticStringPool = remapTyped<StaticStringPool option> remap graph.StaticStringPool
                LiteralStorage = remapTyped<Map<NodeId, LiteralStorage>> remap graph.LiteralStorage
                Escaping = lazy (remapTyped<Map<NodeId, string>> remap graph.Escaping.Value)
                Codata = remappedCodata
                Edges = remapEdges remap graph.Edges
                WitnessProvenance = provenance
                SequenceRangeProvenance = remapTyped<SequenceRangeAuthority option> remap graph.SequenceRangeProvenance
                RangeContextFacts = remapTyped<RangeContextFacts option> remap graph.RangeContextFacts }
        let boundaryOriginTarget =
            remapped.Edges |> List.tryPick (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDomain { StringOriginRelations = Some _ } -> Some edge.Target
                | _ -> None)
        match boundaryOriginTarget with
        | None -> Result.Ok remapped
        | Some target ->
            match StringOrigins.relations remapped with
            | Result.Error reason -> Result.Error (target, "SSAAssignment: " + reason)
            | Result.Ok fresh ->
                let reorderedEnrichedTargets =
                    remapped.Edges
                    |> List.collect (fun edge ->
                        match edge.Role with
                        | EdgeRole.BoundaryDomain d -> edge.Target :: (d.IntrinsicProofs |> List.map _.Obligation)
                        | EdgeRole.BoundaryCoverage c -> [ c.Obligation ]
                        | EdgeRole.MemoryDomain d -> edge.Target :: (d.Proofs |> List.map _.Obligation)
                        | EdgeRole.NumericDomain _ | EdgeRole.SpatialModuleDomain _ ->
                            [ edge.Target ]
                        | _ -> [])
                    |> Set.ofList
                let canonicalRelation (row: StringOriginRelation) =
                    let sources =
                        if row.Flavor = StringOriginRelationKind.Named "EnrichedWith" && reorderedEnrichedTargets.Contains row.Target then
                            List.sort row.Sources
                        else row.Sources
                    row.Recorded, row.Class, row.Flavor, row.Ordinal, row.Target, sources
                let sortedFresh = fresh |> List.map canonicalRelation |> List.sort
                let edges =
                    remapped.Edges |> List.map (fun edge ->
                        match edge.Role with
                        | EdgeRole.BoundaryDomain ({ StringOriginRelations = Some relations } as domain)
                            when relations <> fresh && (relations |> List.map canonicalRelation |> List.sort) = sortedFresh ->
                            { edge with Role = EdgeRole.BoundaryDomain { domain with StringOriginRelations = Some fresh } }
                        | _ -> edge)
                Result.Ok { remapped with Edges = edges })

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
        match remapGraph remapNodeId candidate with
        | Result.Error failure -> Result.Error(ReconciliationFailure.InvalidReturnedIdentities [ failure ])
        | Result.Ok remappedGraph ->
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

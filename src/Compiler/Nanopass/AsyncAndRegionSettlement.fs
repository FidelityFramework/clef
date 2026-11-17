// SPDX-License-Identifier: MIT
/// Baker saturation and proof settlement for async delimited continuations
/// (A-01 through A-03, Farscape#220 CCS8424/CCS8425) and scoped memory regions
/// (A-04 through A-06).
///
/// Every fact published here is settled from source structure, the selected
/// platform's declarations and the analysed value ranges. A missing premise is
/// refused at its owner with a deterministic diagnostic; no row is published
/// with a substituted identity, a default width or a default count.
///
/// The continuation frame of each settled formation is realized in the PSG
/// (clef#163): its allocation, capture and state initialization, the stores
/// before each suspension cut and the resumption dispatch are explicit nodes
/// of the formation's deferred callable, folded in before SSA assignment.
/// The join of each settled orchestration is realized the same way: each
/// child is bound once, and the join holds one explicit activation per child
/// and the store of each result into its result array.
module Clef.Compiler.Nanopass.AsyncAndRegionSettlement

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Ingredients.Obligations
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Nanopass.Recipe
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module Release = Clef.Compiler.Nanopass.RegionReleaseConstruction
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Machine = Clef.Compiler.Baker.Recipes.AsyncContinuationRecipes

type Settlement =
    { Frames: Map<NodeId, ContinuationFrame>
      Formations: Map<NodeId, AsyncFormation>
      Activations: Map<NodeId, AsyncActivation>
      Suspensions: Map<NodeId, AsyncSuspension>
      Orchestrations: Map<NodeId, AsyncOrchestration>
      RegionAllocations: Map<NodeId, RegionAllocation>
      RegionCallPassings: Map<NodeId, RegionCallPassing>
      RegionCopyEndpoints: Map<NodeId, RegionCopyEndpoint>
      Residences: Map<NodeId, EscapeKind>
      /// Frame allocation, binding and reference occurrence -> frame identity.
      Origins: Map<NodeId, NodeId>
      Diagnostics: Diagnostic list }

let empty : Settlement =
    { Frames = Map.empty
      Formations = Map.empty
      Activations = Map.empty
      Suspensions = Map.empty
      Orchestrations = Map.empty
      RegionAllocations = Map.empty
      RegionCallPassings = Map.empty
      RegionCopyEndpoints = Map.empty
      Residences = Map.empty
      Origins = Map.empty
      Diagnostics = [] }

//-------------------------------------------------------------------------
// Accrued enrichment: obligation citizens, their hyperedges, diagnostics
//-------------------------------------------------------------------------

type private Accrual =
    { Obligations: SemanticNode list
      Edges: Hyperedge list
      Diagnostics: Diagnostic list }

let private none : Accrual = { Obligations = []; Edges = []; Diagnostics = [] }

let private join (left: Accrual) (right: Accrual) : Accrual =
    { Obligations = left.Obligations @ right.Obligations
      Edges = left.Edges @ right.Edges
      Diagnostics = left.Diagnostics @ right.Diagnostics }

let private joinAll (items: Accrual list) = items |> List.fold join none

let private refusal (code: string) (range: SourceRange) (related: NodeId list) (message: string) : Accrual =
    { none with
        Diagnostics =
            [ { Severity = NativeDiagnosticSeverity.Error
                Code = code
                Message = message
                Range = range
                RelatedNodes = List.distinct related
                Reachability = ReachabilityContext.Reachable } ] }

let private claim (subject: SemanticNode) (name: string) (kind: string) (statement: string) (body: ObligationBody) (sources: NodeId list) =
    let obligation =
        obligationNode subject (NodeId.value subject.Id)
            { Id = name
              Kind = kind
              Logic = "QF_LIA"
              Statement = statement
              Source = fmtRange subject.Range
              Refs = []
              Body = body }
    obligation, { none with Obligations = [ obligation ]; Edges = [ constrains (List.distinct (subject.Id :: sources)) obligation ] }

let private layoutClaim subject name (slots: (int * int * int) list) (bytes: int) (alignment: int) sources =
    claim subject name "continuation-layout" "Frame or result-storage slots tile their exact extent with disjoint, naturally aligned fields."
        (ObligationBody.ContinuationLayout(slots, bytes, alignment)) sources

let private capacityClaim subject name (needed: int64) (capacity: int64) sources =
    claim subject name "capacity-fits" "The required byte extent fits within the settled storage capacity."
        (ObligationBody.CapacityFits(needed, capacity)) sources

//-------------------------------------------------------------------------
// Structural readers
//-------------------------------------------------------------------------

let private participants (nodes: NodeId list) : Participant list =
    nodes
    |> List.distinct
    |> List.map (fun node -> { Node = node; Role = ParticipantRole.Source; Group = node; Ordinal = 0 })

let rec private sourceIntrinsic (graph: SemanticGraph) (id: NodeId) (arguments: NodeId list) : (SemanticNode * IntrinsicInfo * NodeId list) option =
    match Map.tryFind id graph.Nodes with
    | Some ({ Kind = SemanticKind.Intrinsic info } as intrinsic) -> Some (intrinsic, info, arguments)
    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> sourceIntrinsic graph inner arguments
    | Some { Kind = SemanticKind.Application(callee, actuals) } -> sourceIntrinsic graph callee (actuals @ arguments)
    | _ -> None

let private intrinsicApplication (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Application _ -> sourceIntrinsic graph node.Id []
    | _ -> None

let private subtree (graph: SemanticGraph) (root: NodeId) : Set<NodeId> =
    let rec walk pending seen =
        match pending with
        | [] -> seen
        | head :: rest when Set.contains head seen -> walk rest seen
        | head :: rest ->
            match Map.tryFind head graph.Nodes with
            | Some node -> walk (node.Children @ rest) (Set.add head seen)
            | None -> walk rest (Set.add head seen)
    walk [ root ] Set.empty

/// Evaluation order inside one computation: a preorder over its structure.
let private evaluationOrder (graph: SemanticGraph) (root: NodeId) : Map<NodeId, int> =
    let rec walk pending (index: int) (order: Map<NodeId, int>) =
        match pending with
        | [] -> order
        | head :: rest when order.ContainsKey head -> walk rest index order
        | head :: rest ->
            let children = Map.tryFind head graph.Nodes |> Option.map _.Children |> Option.defaultValue []
            walk (children @ rest) (index + 1) (Map.add head index order)
    walk [ root ] 0 Map.empty

/// The source declarations a computation reads: references and captured slots.
let private readDeclarations (graph: SemanticGraph) (root: NodeId) : Set<NodeId> =
    subtree graph root
    |> Set.toList
    |> List.choose (fun id ->
        match Map.tryFind id graph.Nodes with
        | Some { Kind = SemanticKind.VarRef(_, Some definition) } -> Some definition
        | Some { Kind = SemanticKind.EnvironmentRead(_, slot) } -> Some slot
        | _ -> None)
    |> Set.ofList

let private readsOf (graph: SemanticGraph) (root: NodeId) (declaration: NodeId) : NodeId list =
    subtree graph root
    |> Set.toList
    |> List.filter (fun id ->
        match Map.tryFind id graph.Nodes with
        | Some { Kind = SemanticKind.VarRef(_, Some definition) } -> definition = declaration
        | Some { Kind = SemanticKind.EnvironmentRead(_, slot) } -> slot = declaration
        | _ -> false)

let rec private origin (graph: SemanticGraph) (id: NodeId) (visited: Set<NodeId>) : NodeId =
    if Set.contains id visited then id else
    let visited = Set.add id visited
    match Map.tryFind id graph.Nodes with
    | Some { Kind = SemanticKind.VarRef(_, Some definition) } -> origin graph definition visited
    | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [ value ] } -> origin graph value visited
    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> origin graph inner visited
    | _ -> id

let private isFormation (node: SemanticNode) =
    node.Metadata.TryFind "Async.Formation" = Some (MetadataValue.Bool true)

let rec private lexicalScopeDepth (graph: SemanticGraph) (id: NodeId) (visited: Set<NodeId>) : int =
    if Set.contains id visited then 1 else
    let visited = Set.add id visited
    match Map.tryFind id graph.Nodes |> Option.bind _.Parent |> Option.bind (fun parent -> Map.tryFind parent graph.Nodes) with
    | Some ({ Kind = SemanticKind.Lambda _ } as parent) ->
        1 + lexicalScopeDepth graph parent.Id visited
    | Some ({ Kind = SemanticKind.IfThenElse _ | SemanticKind.Match _ | SemanticKind.CaseElimination _ } as parent) ->
        1 + lexicalScopeDepth graph parent.Id visited
    | Some ({ Kind = SemanticKind.Sequential items } as parent) ->
        let precedingBindings =
            items
            |> List.takeWhile ((<>) id)
            |> List.filter (fun itemId ->
                match Map.tryFind itemId graph.Nodes with
                | Some { Kind = SemanticKind.Binding _ } -> true
                | _ -> false)
            |> List.length
        precedingBindings + lexicalScopeDepth graph parent.Id visited
    | Some parent -> lexicalScopeDepth graph parent.Id visited
    | None -> 1

/// The deferred callable of a formation: its final structural child, a
/// Lambda or (after closure conversion) the closure value of one.
let private formationCallable (graph: SemanticGraph) (owner: SemanticNode) =
    let rec implementation depth (id: NodeId) =
        if depth > 4 then None
        else
            match Map.tryFind id graph.Nodes with
            | Some ({ Kind = SemanticKind.Lambda(parameters, body, captures, _, _) } as lambda) -> Some (lambda, parameters, body, captures)
            | Some { Kind = SemanticKind.ClosureValue(code, _) } -> implementation (depth + 1) code
            | Some { Kind = SemanticKind.VarRef(_, Some definition) } -> implementation (depth + 1) definition
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [ value ] } -> implementation (depth + 1) value
            | _ -> None
    match List.rev owner.Children with
    | callable :: anchors ->
        implementation 0 callable
        |> Option.map (fun (lambda, parameters, body, captures) -> callable, lambda, parameters, body, captures, List.rev anchors)
    | [] -> None

let rec private resolveFormation (graph: SemanticGraph) (formations: Set<NodeId>) (id: NodeId) (visited: Set<NodeId>) : NodeId option =
    if Set.contains id visited then None else
    let visited = Set.add id visited
    if Set.contains id formations then Some id
    else
        match Map.tryFind id graph.Nodes with
        | Some { Kind = SemanticKind.VarRef(_, Some definition) } -> resolveFormation graph formations definition visited
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [ value ] } -> resolveFormation graph formations value visited
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> resolveFormation graph formations inner visited
        | Some { Kind = SemanticKind.Lambda(_, body, _, _, _) } -> resolveFormation graph formations body visited
        | Some { Kind = SemanticKind.Sequential items } when not items.IsEmpty -> resolveFormation graph formations (List.last items) visited
        | Some { Kind = SemanticKind.Application(callee, _) } -> resolveFormation graph formations callee visited
        | _ -> None

//-------------------------------------------------------------------------
// Settled layouts from the selected platform's declared widths
//-------------------------------------------------------------------------

let private widthBits (platform: PlatformContext option) (width: NTUWidth) =
    match width with
    | NTUWidth.Fixed bits -> Some bits
    | NTUWidth.Resolved dimension ->
        platform |> Option.bind (fun ctx -> PlatformContext.tryWidth ctx (WidthDimension.name dimension) |> Result.toOption)

let private pointerBytes (platform: PlatformContext option) =
    platform
    |> Option.bind (fun ctx -> PlatformContext.tryWidth ctx (WidthDimension.name WidthDimension.Pointer) |> Result.toOption)
    |> Option.filter (fun bits -> bits > 0 && bits % 8 = 0)
    |> Option.map (fun bits -> bits / 8)

/// The settled slot of a value of this type: slot, holding mode, bytes and
/// alignment. A bare integer kind is bounded by its declared dimension.
let private slotOf (platform: PlatformContext option) (ty: NativeType) : (SettledSlot * CaptureSlotKind * int * int) option =
    let ty = applySubst ty
    let scalar slot bytes = Some (slot, CaptureSlotKind.Scalar slot, bytes, bytes)
    let words count holds =
        pointerBytes platform |> Option.map (fun bytes -> SettledSlot.Pointer count, holds, count * bytes, bytes)
    let bits width make =
        widthBits platform width
        |> Option.filter (fun value -> value >= 8 && value % 8 = 0)
        |> Option.bind (fun value -> scalar (make value) (value / 8))
    match ty with
    | NativeType.TFun _ -> words 2 (CaptureSlotKind.Scalar (SettledSlot.Pointer 2))
    | NativeType.TApp(tc, _) when Types.isReadOnlyViewTypeCon tc -> words 2 (CaptureSlotKind.ValueView ty)
    | NativeType.TApp(tc, _) when Types.isAsyncTypeCon tc -> words 2 (CaptureSlotKind.Scalar (SettledSlot.Pointer 2))
    | _ ->
        match Types.tryGetNTUKind ty with
        | Some (NTUKind.NTUint width) | Some (NTUKind.NTUuint width) -> bits width (fun value -> SettledSlot.Integer(value, None))
        | Some (NTUKind.NTUfloat width) -> bits width SettledSlot.Real
        | Some NTUKind.NTUbool -> scalar SettledSlot.Bool 1
        | Some NTUKind.NTUchar -> scalar SettledSlot.Char 4
        | Some (NTUKind.NTUptr | NTUKind.NTUsize | NTUKind.NTUdiff | NTUKind.NTUfnptr) ->
            words 1 (CaptureSlotKind.Scalar (SettledSlot.Pointer 1))
        | Some (NTUKind.NTUarray | NTUKind.NTUborrowedview) -> words 2 (CaptureSlotKind.ValueView ty)
        | _ -> None

/// The byte size and alignment of a region element (scalars only).
let private elementLayout (platform: PlatformContext option) (ty: NativeType) : (int64 * int) option =
    match Types.tryGetNTUKind (applySubst ty) with
    | Some (NTUKind.NTUint _) | Some (NTUKind.NTUuint _) | Some (NTUKind.NTUfloat _)
    | Some NTUKind.NTUbool | Some NTUKind.NTUchar
    | Some NTUKind.NTUptr | Some NTUKind.NTUsize | Some NTUKind.NTUdiff ->
        slotOf platform ty |> Option.map (fun (_, _, bytes, alignment) -> int64 bytes, alignment)
    | _ -> None

let private isUnit (ty: NativeType) =
    match applySubst ty with
    | NativeType.TApp({ NTUKind = Some NTUKind.NTUunit }, []) -> true
    | _ -> false

let private arrayElement (ty: NativeType) =
    match applySubst ty with
    | NativeType.TApp(tc, [ element ]) when tc.NTUKind = Some NTUKind.NTUarray -> Some element
    | _ -> None

/// Natural-alignment tiling of slots, in order: offsets, extent and alignment.
let private tile (slots: (int * int) list) : (int * int * int) list * int * int =
    let align offset alignment = if alignment <= 1 then offset else ((offset + alignment - 1) / alignment) * alignment
    let placed, finish =
        slots |> List.mapFold (fun offset (bytes, alignment) ->
            let start = align offset alignment
            (start, bytes, alignment), start + bytes) 0
    let alignment = slots |> List.fold (fun acc (_, a) -> max acc a) 1
    placed, align finish alignment, alignment

/// A finite non-negative integer bound settled for a value: a literal or the
/// analysed range of the value's source.
let private settledBound (graph: SemanticGraph) (id: NodeId) : (bigint * bigint) option =
    let root = origin graph id Set.empty
    let ofNode nodeId =
        match Map.tryFind nodeId graph.Nodes with
        | Some { Kind = SemanticKind.Literal(NativeLiteral.Int(value, _)) } -> Some (bigint value, bigint value)
        | Some { Kind = SemanticKind.Literal(NativeLiteral.UInt(value, _)) } -> Some (bigint value, bigint value)
        | Some { ValueRange = Some(ValueRange.Bounded(lower, upper)) } -> Some (lower, upper)
        | _ -> None
    ofNode id |> Option.orElseWith (fun () -> ofNode root)

let private maxBytes = bigint System.Int64.MaxValue

//-------------------------------------------------------------------------
// Scoped memory regions (A-04, A-05, A-06)
//-------------------------------------------------------------------------

type private Allocation =
    { Site: SemanticNode
      Binding: NodeId option
      Regions: NodeId list
      Bytes: int64
      Alignment: int }

type private RegionState =
    { Allocations: Map<NodeId, RegionAllocation>
      Settled: Allocation list
      Releases: Map<NodeId, NodeId list>
      RegionsOf: NodeId -> NodeId list }

let private settleRegions (graph: SemanticGraph) (reachable: SemanticNode list) : RegionState * Map<NodeId, RegionCallPassing> * Map<NodeId, RegionCopyEndpoint> * Map<NodeId, EscapeKind> * Accrual =
    let platform = graph.Platform
    let applications name =
        reachable |> List.choose (fun node ->
            match intrinsicApplication graph node with
            | Some (intrinsic, info, arguments) when info.FullName = name -> Some (node, intrinsic, arguments)
            | _ -> None)
    let creations = applications "Region.create"
    let creationIds = creations |> List.map (fun (node, _, _) -> node.Id) |> Set.ofList
    let scopes = Release.regionScopes graph |> List.map (fun row -> row.Creation, row) |> Map.ofList

    // A region value's creation(s): directly, or through the actuals of every
    // call that supplies the formal it is read from.
    let lambdaOfFormal =
        reachable |> List.collect (fun node ->
            match node.Kind with
            | SemanticKind.Lambda(parameters, _, _, _, _) -> parameters |> List.mapi (fun ordinal (_, _, formal) -> formal, (node.Id, ordinal))
            | _ -> [])
        |> Map.ofList
    let callsOf =
        reachable |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Application(callee, arguments) when (sourceIntrinsic graph callee []).IsNone ->
                match Map.tryFind (origin graph callee Set.empty) graph.Nodes with
                | Some { Kind = SemanticKind.Lambda _; Id = lambda } -> Some (lambda, (node, arguments))
                | _ -> None
            | _ -> None)
        |> List.groupBy fst
        |> List.map (fun (lambda, calls) -> lambda, calls |> List.map snd)
        |> Map.ofList
    let rec regionsOf (visited: Set<NodeId>) (id: NodeId) : NodeId list =
        let root = origin graph id Set.empty
        if Set.contains root visited then []
        elif creationIds.Contains root then [ root ]
        else
            match Map.tryFind root lambdaOfFormal with
            | Some (lambda, ordinal) ->
                Map.tryFind lambda callsOf |> Option.defaultValue []
                |> List.collect (fun (_, arguments) ->
                    arguments |> List.tryItem ordinal |> Option.map (regionsOf (Set.add root visited)) |> Option.defaultValue [])
                |> List.distinct
            | None -> []
    let regionsOf = regionsOf Set.empty

    let space =
        Platform.resolve graph
        |> Option.map (fun declared -> declared.Spaces |> List.filter (fun space -> space.Kind = "region"))

    // Region capacity: pages of the declared region space's granularity.
    let capacities, capacityRefusals =
        creations |> List.map (fun (node, _, arguments) ->
            match space with
            | None | Some [] ->
                None, refusal "CCS8403" node.Range [ node.Id ] "Region.create requires a declared region memory space (Kind = \"region\") in the selected platform."
            | Some [ declared ] ->
                match arguments with
                | [ pages ] ->
                    match settledBound graph pages with
                    | Some (lower, upper) when lower > 0I ->
                        let page = bigint declared.Granularity
                        let guaranteed = lower * page
                        let worst = upper * page
                        if declared.Granularity <= 0 then
                            None, refusal "CCS8405" node.Range [ node.Id; declared.Node ] "The declared region memory space has no positive page granularity."
                        elif worst > bigint declared.Capacity || guaranteed > maxBytes then
                            None, refusal "CCS8405" node.Range [ node.Id; pages; declared.Node ] "Region.create requests more pages than the declared region memory space provides."
                        else Some (node.Id, (int64 guaranteed, declared)), none
                    | Some _ ->
                        None, refusal "CCS8405" node.Range [ node.Id; pages ] "Region.create requires a strictly positive page count."
                    | None ->
                        None, refusal "CCS8405" node.Range [ node.Id; pages ] "Region.create requires a settled, finite page count."
                | _ -> None, refusal "CCS8403" node.Range [ node.Id ] "Region.create requires exactly one page-count argument."
            | Some _ ->
                None, refusal "CCS8403" node.Range [ node.Id ] "The selected platform declares more than one region memory space; the region placement is ambiguous.")
        |> List.unzip
    let capacities = capacities |> List.choose id |> Map.ofList

    let bindingOfValue (node: SemanticNode) =
        node.Parent
        |> Option.bind (fun parent -> Map.tryFind parent graph.Nodes)
        |> Option.bind (fun parent ->
            match parent.Kind, parent.Children with
            | SemanticKind.Binding(_, false, _, _), [ value ] when value = node.Id -> Some parent.Id
            | _ -> None)

    // Allocation extent: a settled element count of the element's declared width.
    let allocations, allocationRefusals =
        applications "Region.alloc"
        |> List.map (fun (node, _, arguments) ->
            match arguments with
            | [ region; count ] ->
                match arrayElement node.Type |> Option.bind (elementLayout platform), settledBound graph count, regionsOf region with
                | None, _, _ ->
                    None, refusal "CCS8403" node.Range [ node.Id ] "Region.alloc requires an element type with a declared byte width."
                | _, None, _ ->
                    None, refusal "CCS8405" node.Range [ node.Id; count ] "Region.alloc requires a settled, finite element count."
                | _, Some (lower, _), _ when lower <= 0I ->
                    None, refusal "CCS8405" node.Range [ node.Id; count ] "Region.alloc requires a strictly positive element count and byte extent."
                | _, _, [] ->
                    None, refusal "CCS8403" node.Range [ node.Id; region ] "Region.alloc does not draw from a settled region creation."
                | Some (elementBytes, alignment), Some (_, upper), regions ->
                    let bytes = upper * bigint elementBytes
                    if bytes > maxBytes then
                        None, refusal "CCS8405" node.Range [ node.Id; count ] "Region.alloc byte extent exceeds the finite layout model."
                    else
                        Some { Site = node; Binding = bindingOfValue node; Regions = regions; Bytes = int64 bytes; Alignment = alignment }, none
            | _ -> None, refusal "CCS8403" node.Range [ node.Id ] "Region.alloc requires a region and an element count.")
        |> List.unzip
    let allocations = allocations |> List.choose id
    let allocationOf (id: NodeId) =
        let root = origin graph id Set.empty
        allocations |> List.tryFind (fun allocation -> allocation.Site.Id = root || allocation.Binding = Some root)

    // Region.copyTo destinations are storage of the destination region.
    let copyTos =
        applications "Region.copyTo"
        |> List.choose (fun (node, intrinsic, arguments) ->
            match arguments with
            | [ source; destination; count ] -> Some (node, intrinsic, source, destination, count)
            | _ -> None)
    let copyOuts =
        applications "Region.copyOut"
        |> List.choose (fun (node, intrinsic, arguments) ->
            match arguments with
            | [ source; count ] -> Some (node, intrinsic, source, count)
            | _ -> None)
    let copyBytes (node: SemanticNode) count =
        match arrayElement node.Type |> Option.bind (elementLayout platform), settledBound graph count with
        | Some (elementBytes, alignment), Some (lower, upper) when lower > 0I && upper * bigint elementBytes <= maxBytes ->
            Some (int64 (upper * bigint elementBytes), alignment)
        | _ -> None
    let copyIns =
        copyTos |> List.choose (fun (node, _, _, destination, count) ->
            match regionsOf destination, copyBytes node count with
            | [ region ], Some (bytes, alignment) -> Some (region, (node, bytes, alignment))
            | _ -> None)

    // Releases: explicit source releases and constructed scope-exit releases.
    let releaseApplications =
        applications "Region.release" |> List.choose (fun (node, _, arguments) ->
            match arguments with
            | [ region ] -> Some (node, regionsOf region)
            | _ -> None)

    let statementOf (scope: NodeId) (id: NodeId) =
        let rec climb (current: NodeId) =
            match Map.tryFind current graph.Nodes |> Option.bind _.Parent with
            | Some parent when parent = scope -> Some (current, parent)
            | Some parent ->
                match Map.tryFind parent graph.Nodes with
                | Some { Kind = SemanticKind.Sequential _ } -> Some (current, parent)
                | Some _ -> climb parent
                | None -> None
            | None -> None
        climb id
    let ancestorsWithin (scope: NodeId) (id: NodeId) =
        let rec climb (current: NodeId) acc =
            if current = scope then current :: acc
            else
                match Map.tryFind current graph.Nodes |> Option.bind _.Parent with
                | Some parent -> climb parent (current :: acc)
                | None -> current :: acc
        climb id []
    // An explicit release covers an exit when the exit is (or is inside) the
    // release, or when the release is sequenced before a computation that
    // contains the exit.
    let covers (scope: NodeId) (release: NodeId) (tail: NodeId) =
        let chain = ancestorsWithin scope tail
        List.contains release chain ||
        (match statementOf scope release with
         | Some (statement, block) ->
             match Map.tryFind block graph.Nodes with
             | Some { Kind = SemanticKind.Sequential items } ->
                 let position item = items |> List.tryFindIndex ((=) item)
                 chain |> List.exists (fun ancestor ->
                     match position statement, position ancestor with
                     | Some before, Some after -> before < after
                     | _ -> false)
             | _ -> false
         | None -> false)

    let regionRows, regionRefusals =
        creations
        |> List.choose (fun (node, intrinsic, _) -> Map.tryFind node.Id capacities |> Option.map (fun capacity -> node, intrinsic, capacity))
        |> List.map (fun (node, intrinsic, (capacity, _)) ->
            let drawn = allocations |> List.filter (fun allocation -> List.contains node.Id allocation.Regions)
            let received = copyIns |> List.filter (fun (region, _) -> region = node.Id) |> List.map snd
            let extent = (drawn |> List.sumBy _.Bytes) + (received |> List.sumBy (fun (_, bytes, _) -> bytes))
            let alignment =
                (drawn |> List.map _.Alignment) @ (received |> List.map (fun (_, _, alignment) -> alignment))
                |> List.fold max 1
            let values =
                (drawn |> List.collect (fun allocation -> allocation.Site.Id :: Option.toList allocation.Binding))
                @ (received |> List.map (fun (copy, _, _) -> copy.Id))
                |> List.distinct
            match Map.tryFind node.Id scopes with
            | None ->
                None, refusal "CCS8405" node.Range [ node.Id ] "A region requires a binding in an owning lexical scope so that every scope exit can release it."
            | Some _ when values.IsEmpty ->
                None, refusal "CCS8405" node.Range [ node.Id ] "A region requires at least one allocation with a positive byte extent."
            | Some _ when extent > capacity ->
                None, refusal "CCS8405" node.Range ([ node.Id ] @ values) (sprintf "The region's settled allocation extent (%d bytes) exceeds its page capacity (%d bytes)." extent capacity)
            | Some scope ->
                let tails = Release.exitTails graph scope.Scope
                let constructed =
                    reachable |> List.choose (fun candidate ->
                        match candidate.Metadata.TryFind Release.ScopeExitReleaseOf, candidate.Metadata.TryFind Release.ScopeExitPath with
                        | Some (MetadataValue.NodeId creation), Some (MetadataValue.NodeId path) when creation = node.Id -> Some (path, candidate.Id)
                        | _ -> None)
                let explicitReleases =
                    releaseApplications
                    |> List.filter (fun (release, regions) -> regions = [ node.Id ] && not (release.Metadata.ContainsKey Release.ScopeExitReleaseOf))
                    |> List.map fst
                let pairs, uncovered =
                    if not constructed.IsEmpty then
                        let paths = constructed |> List.map fst |> Set.ofList
                        let originalTails =
                            tails |> List.map (fun tail ->
                                match Map.tryFind tail graph.Nodes |> Option.bind _.Parent with
                                | Some parent when paths.Contains parent -> parent
                                | _ -> tail)
                            |> List.distinct
                        constructed, originalTails |> List.filter (fun tail -> not (paths.Contains tail) && not (constructed |> List.exists (fun (_, release) -> release = tail)))
                    else
                        let paired =
                            tails |> List.map (fun tail ->
                                tail, explicitReleases |> List.tryFind (fun release -> covers scope.Scope release.Id tail))
                        paired |> List.choose (fun (tail, release) -> release |> Option.map (fun release -> tail, release.Id)),
                        paired |> List.choose (fun (tail, release) -> if release.IsNone then Some tail else None)
                if pairs.IsEmpty || not uncovered.IsEmpty then
                    None, refusal "CCS8405" node.Range ([ node.Id ] @ uncovered)
                            "The region is not released on every exit path of its owning scope, and no release can be constructed where the exit value reads region storage."
                else
                    match intrinsic.Children with
                    | [] ->
                        None, refusal "CCS8403" node.Range [ node.Id ] "Region.create lacks its placement anchor."
                    | placement :: _ ->
                        let paths = pairs |> List.map fst |> List.distinct
                        let releases = pairs |> List.map snd
                        let depth = lexicalScopeDepth graph scope.Binding Set.empty |> max 2
                        let lifetimeScope = scope.Binding
                        let sources = [ node.Id; placement; lifetimeScope ] @ values @ paths @ releases
                        let obligation, accrued =
                            capacityClaim node (sprintf "region_%d_budget" (NodeId.value node.Id)) extent capacity sources
                        let row : RegionAllocation =
                            { Region = node.Id
                              SpacePlacement = placement
                              LifetimeScope = lifetimeScope
                              LifetimeDepth = depth
                              ByteExtent = extent
                              Capacity = capacity
                              Alignment = alignment
                              AllocatedValues = values
                              ScopeExitPaths = paths
                              ScopeExitReleases = pairs
                              Obligations = [ obligation.Id ]
                              Participants = participants sources }
                        Some (node.Id, row), accrued)
        |> List.unzip
    let regionRows = regionRows |> List.choose id |> Map.ofList
    let releasesByRegion =
        regionRows |> Map.map (fun _ row -> row.ScopeExitReleases |> List.map snd |> List.distinct)

    // A-06: a region value never leaves its owning scope uncopied: through
    // any exit path, a returned closure capturing it, or an outer mutable cell.
    let storageOf (region: NodeId) =
        match Map.tryFind region regionRows with
        | Some row -> row.AllocatedValues |> Set.ofList
        | None ->
            allocations |> List.filter (fun allocation -> List.contains region allocation.Regions)
            |> List.collect (fun allocation -> allocation.Site.Id :: Option.toList allocation.Binding) |> Set.ofList
    let escapeRefusals =
        creations |> List.choose (fun (node, _, _) ->
            Map.tryFind node.Id scopes |> Option.map (fun scope -> node, scope, storageOf node.Id))
        |> List.collect (fun (node, scope, storage) ->
            let isStorage id =
                let root = origin graph id Set.empty
                storage.Contains root || storage.Contains id
            let scopeNodes = subtree graph scope.Scope
            let returned =
                Release.exitTails graph scope.Scope
                |> List.filter (fun tail ->
                    isStorage tail ||
                    (match Map.tryFind (origin graph tail Set.empty) graph.Nodes with
                     | Some { Kind = SemanticKind.Lambda(_, body, _, _, _) } -> readDeclarations graph body |> Set.exists isStorage
                     | _ -> false))
            let stored =
                scopeNodes |> Set.toList |> List.choose (fun id ->
                    match Map.tryFind id graph.Nodes with
                    | Some { Kind = SemanticKind.Set(target, value) } ->
                        match Map.tryFind target graph.Nodes with
                        | Some { Kind = SemanticKind.VarRef(_, Some cell) } when not (scopeNodes.Contains cell) && isStorage value -> Some id
                        | _ -> None
                    | _ -> None)
            (returned @ stored) |> List.map (fun site ->
                refusal "CCS8406" (Map.tryFind site graph.Nodes |> Option.map _.Range |> Option.defaultValue node.Range) [ site; node.Id ]
                    "A region-allocated value cannot escape its owning region scope without an explicit Region.copyOut or Region.copyTo transfer."))

    // A-05: every region argument of every call borrows the caller's region;
    // the callee (or any function it forwards the formal to) cannot release it.
    let rec releasesThrough (visited: Set<NodeId * int>) (lambda: NodeId) (ordinal: int) : SemanticNode list =
        if Set.contains (lambda, ordinal) visited then [] else
        let visited = Set.add (lambda, ordinal) visited
        match Map.tryFind lambda graph.Nodes with
        | Some { Kind = SemanticKind.Lambda(parameters, body, _, _, _) } ->
            match List.tryItem ordinal parameters with
            | Some (_, _, formal) ->
                let inside = subtree graph body
                let direct =
                    releaseApplications |> List.choose (fun (release, _) ->
                        if inside.Contains release.Id then
                            match sourceIntrinsic graph release.Id [] with
                            | Some (_, _, [ argument ]) when origin graph argument Set.empty = formal -> Some release
                            | _ -> None
                        else None)
                let forwarded =
                    callsOf |> Map.toList |> List.collect (fun (callee, calls) ->
                        calls |> List.collect (fun (call, arguments) ->
                            if inside.Contains call.Id then
                                arguments |> List.indexed |> List.collect (fun (position, argument) ->
                                    if origin graph argument Set.empty = formal then releasesThrough visited callee position else [])
                            else []))
                direct @ forwarded
            | None -> []
        | _ -> []
    let passings, passingRefusals =
        callsOf |> Map.toList |> List.collect (fun (lambda, calls) ->
            match Map.tryFind lambda graph.Nodes with
            | Some { Kind = SemanticKind.Lambda(parameters, body, _, _, _) } ->
                calls |> List.collect (fun (call, arguments) ->
                    arguments |> List.indexed |> List.choose (fun (ordinal, argument) ->
                        let isRegionFormal =
                            match List.tryItem ordinal parameters with
                            | Some (_, ty, _) ->
                                match applySubst ty with
                                | NativeType.TApp(tc, _) -> Types.isRegionTypeCon tc
                                | _ -> false
                            | None -> false
                        if not isRegionFormal then None
                        else
                            match regionsOf argument with
                            | [ region ] ->
                                match Map.tryFind region regionRows with
                                | Some regionRow ->
                                    let illegal = releasesThrough Set.empty lambda ordinal |> List.distinctBy _.Id
                                    let refused =
                                        illegal |> List.map (fun release ->
                                            refusal "CCS8405" release.Range [ release.Id; call.Id; argument ]
                                                "A borrowed region parameter cannot be released by the callee; region lifetime is owned by the caller scope.")
                                    let sources = [ argument; call.Id; region; regionRow.LifetimeScope; body ]
                                    let obligation, accrued =
                                        capacityClaim call (sprintf "region_pass_%d_%d" (NodeId.value call.Id) ordinal) regionRow.ByteExtent regionRow.Capacity sources
                                    let row : RegionCallPassing =
                                        { Site = argument
                                          Call = call.Id
                                          ParameterOrdinal = ordinal
                                          Region = region
                                          Mode = RegionOwnershipMode.Borrowed
                                          AllocationProvenance = region
                                          CallerLifetimeScope = regionRow.LifetimeScope
                                          CallerLifetimeDepth = regionRow.LifetimeDepth
                                          CalleeLifetimeScope = body
                                          CalleeLifetimeDepth = regionRow.LifetimeDepth + 1
                                          PermitCalleeRelease = false
                                          CalleeReleases = []
                                          Obligations = [ obligation.Id ]
                                          Participants = participants sources }
                                    Some (Some (argument, row), joinAll (accrued :: refused))
                                | None -> None
                            | [] -> None
                            | _ ->
                                Some (None, refusal "CCS8403" call.Range [ call.Id; argument ] "A region argument has more than one possible creation; the borrowed region is ambiguous.")))
            | _ -> [])
        |> List.unzip
    let passings = passings |> List.choose id |> Map.ofList

    // A-06: settled copy endpoints with the actual count, element width and
    // destination; the copied extent fits its source allocation and destination.
    let copyOutRows =
        copyOuts |> List.map (fun (node, _, source, count) ->
            match allocationOf source, copyBytes node count with
            | Some allocation, Some (bytes, alignment) ->
                match allocation.Regions |> List.tryExactlyOne |> Option.bind (fun region -> Map.tryFind region regionRows) with
                | Some sourceRow when bytes <= allocation.Bytes ->
                    match Map.tryFind sourceRow.Region scopes with
                    | Some regionScope ->
                        let dstScope = regionScope.Scope
                        let dstDepth = min (sourceRow.LifetimeDepth - 1) (lexicalScopeDepth graph dstScope Set.empty) |> max 1
                        let sources = [ node.Id; allocation.Site.Id; sourceRow.Region; source ]
                        let obligation, accrued =
                            capacityClaim node (sprintf "region_copyout_%d" (NodeId.value node.Id)) bytes allocation.Bytes sources
                        let row : RegionCopyEndpoint =
                            { Site = node.Id
                              Kind = RegionCopyKind.CopyOut
                              EscapingValue = allocation.Site.Id
                              SourceRegion = sourceRow.Region
                              SourceView = source
                              SourceLifetimeScope = sourceRow.LifetimeScope
                              SourceLifetimeDepth = sourceRow.LifetimeDepth
                              SourceByteExtent = bytes
                              SourceCapacity = sourceRow.Capacity
                              SourceAlignment = sourceRow.Alignment
                              DestinationRegion = None
                              DestinationStorage = node.Id
                              DestinationLifetimeScope = dstScope
                              DestinationLifetimeDepth = dstDepth
                              DestinationByteExtent = bytes
                              DestinationCapacity = bytes
                              DestinationAlignment = max alignment sourceRow.Alignment
                              EscapeDischargeObligation = obligation.Id
                              Participants = participants (sources @ [ sourceRow.LifetimeScope; dstScope ]) }
                        Some (node.Id, row), accrued
                    | None ->
                        None, refusal "CCS8406" node.Range [ node.Id; source ] "Region.copyOut requires a source region with a settled owning lexical scope."
                | Some _ ->
                    None, refusal "CCS8405" node.Range [ node.Id; count; allocation.Site.Id ] "Region.copyOut copies more bytes than its source allocation holds."
                | None ->
                    None, refusal "CCS8406" node.Range [ node.Id; source ] "Region.copyOut requires a source allocated in exactly one settled region."
            | None, _ ->
                None, refusal "CCS8406" node.Range [ node.Id; source ] "Region.copyOut requires a region-allocated source value."
            | _, None ->
                None, refusal "CCS8405" node.Range [ node.Id; count ] "Region.copyOut requires a settled, positive element count of a declared element width.")
    let copyToRows =
        copyTos |> List.map (fun (node, _, source, destination, count) ->
            match allocationOf source, regionsOf destination, copyBytes node count with
            | Some allocation, [ destinationRegion ], Some (bytes, alignment) ->
                match allocation.Regions |> List.tryExactlyOne |> Option.bind (fun region -> Map.tryFind region regionRows), Map.tryFind destinationRegion regionRows with
                | Some sourceRow, Some destinationRow when destinationRegion = sourceRow.Region || destinationRow.LifetimeDepth >= sourceRow.LifetimeDepth ->
                    None, refusal "CCS8406" node.Range [ node.Id; source; destination ] "Region.copyTo requires a distinct destination region whose lifetime outlives the source region."
                | Some sourceRow, Some destinationRow when bytes <= allocation.Bytes && bytes <= destinationRow.Capacity ->
                    let sources = [ node.Id; allocation.Site.Id; sourceRow.Region; source; destinationRegion ]
                    let obligation, accrued =
                        capacityClaim node (sprintf "region_copyto_%d" (NodeId.value node.Id)) destinationRow.ByteExtent destinationRow.Capacity sources
                    let row : RegionCopyEndpoint =
                        { Site = node.Id
                          Kind = RegionCopyKind.CopyTo
                          EscapingValue = allocation.Site.Id
                          SourceRegion = sourceRow.Region
                          SourceView = source
                          SourceLifetimeScope = sourceRow.LifetimeScope
                          SourceLifetimeDepth = sourceRow.LifetimeDepth
                          SourceByteExtent = bytes
                          SourceCapacity = sourceRow.Capacity
                          SourceAlignment = sourceRow.Alignment
                          DestinationRegion = Some destinationRegion
                          DestinationStorage = node.Id
                          DestinationLifetimeScope = destinationRow.LifetimeScope
                          DestinationLifetimeDepth = destinationRow.LifetimeDepth
                          DestinationByteExtent = bytes
                          DestinationCapacity = destinationRow.Capacity
                          DestinationAlignment = max alignment destinationRow.Alignment
                          EscapeDischargeObligation = obligation.Id
                          Participants = participants (sources @ [ sourceRow.LifetimeScope; destinationRow.LifetimeScope ]) }
                    Some (node.Id, row), accrued
                | Some _, Some _ ->
                    None, refusal "CCS8405" node.Range [ node.Id; count; destination ] "Region.copyTo copies more bytes than its source allocation or destination region capacity holds."
                | _ -> None, refusal "CCS8406" node.Range [ node.Id; source; destination ] "Region.copyTo requires a settled source region and a distinct settled destination region."
            | None, _, _ -> None, refusal "CCS8406" node.Range [ node.Id; source ] "Region.copyTo requires a region-allocated source value."
            | _, _, None -> None, refusal "CCS8405" node.Range [ node.Id; count ] "Region.copyTo requires a settled, positive element count of a declared element width."
            | _ -> None, refusal "CCS8406" node.Range [ node.Id; destination ] "Region.copyTo requires exactly one settled destination region.")
    let copyRows, copyAccruals = (copyOutRows @ copyToRows) |> List.unzip
    let copyRows = copyRows |> List.choose id |> Map.ofList

    // A copied-out value is fresh storage outside every region; where it
    // reaches an exit of its owning scope it escapes by return.
    let residences =
        copyOutRows |> List.choose (fst >> Option.map fst) |> List.choose (fun copy ->
            let rec lambdaBody (id: NodeId) (visited: Set<NodeId>) =
                if Set.contains id visited then None else
                match Map.tryFind id graph.Nodes |> Option.bind _.Parent |> Option.bind (fun parent -> Map.tryFind parent graph.Nodes) with
                | Some { Kind = SemanticKind.Lambda(_, body, _, _, _) } -> Some body
                | Some parent -> lambdaBody parent.Id (Set.add id visited)
                | None -> None
            lambdaBody copy Set.empty
            |> Option.filter (fun body -> Release.exitTails graph body |> List.exists (fun tail -> origin graph tail Set.empty = copy))
            |> Option.map (fun _ -> copy, EscapeKind.EscapesViaReturn))
        |> Map.ofList

    let state =
        { Allocations = regionRows
          Settled = allocations
          Releases = releasesByRegion
          RegionsOf = regionsOf }
    state, passings, copyRows, residences,
    joinAll (capacityRefusals @ allocationRefusals @ regionRefusals @ escapeRefusals @ passingRefusals @ copyAccruals)

//-------------------------------------------------------------------------
// Async formations, frames, suspensions, activations, orchestrations
//-------------------------------------------------------------------------

type private Cut =
    { Site: SemanticNode
      Intrinsic: SemanticNode
      Awaited: NodeId
      Bound: NodeId option
      Continuation: NodeId
      /// Every item the cut's block evaluates after its statement: the
      /// computation the continuation recipe places in the cut's dispatch region.
      Resumed: NodeId list
      Delimiter: NodeId
      BindResume: NodeId
      Completion: NodeId
      Cleanup: NodeId
      Order: int }

/// The settled frame operations of one formation's deferred callable.
type private Realization =
    { Frame: NodeId
      Callable: NodeId
      Elaboration: Machine.Elaboration }

/// One settled elaboration to fold into the graph.
type private Fold =
    { /// The edited occurrence whose recipe carries the created nodes.
      Carrier: NodeId
      /// Every created node and the current version of every edited node.
      Nodes: SemanticNode list
      Edited: Set<NodeId>
      Provenance: Hyperedge list
      /// The source array accesses the elaboration introduces, each with the
      /// settled extent of the array it addresses.
      Accesses: (NodeId * int) list }

let private settleAsync (graph: SemanticGraph) (reachable: SemanticNode list) (regions: RegionState)
        : Map<NodeId, ContinuationFrame> * Map<NodeId, AsyncFormation> * Map<NodeId, AsyncSuspension> * Map<NodeId, AsyncActivation> * Map<NodeId, AsyncOrchestration> * Realization list * Fold list * Accrual =
    let platform = graph.Platform
    let owners = reachable |> List.filter isFormation |> List.sortBy (fun node -> NodeId.value node.Id)
    let ownerSpanByFormation =
        owners
        |> List.map (fun owner ->
            let span =
                match formationCallable graph owner with
                | Some (_, _, _, body, _, _) -> Set.union (subtree graph owner.Id) (subtree graph body)
                | None -> subtree graph owner.Id
            owner.Id, span)
    let enclosingOwnerOf (id: NodeId) : NodeId option =
        ownerSpanByFormation
        |> List.filter (fun (ownerId, span) -> ownerId <> id && span.Contains id)
        |> List.sortBy (fun (_, span) -> span.Count)
        |> List.tryHead
        |> Option.map fst
    let awaitResolution =
        reachable
        |> List.choose (fun node ->
            match intrinsicApplication graph node with
            | Some (intrinsic, info, [ awaited ]) when info.FullName = "Async.Await" ->
                match enclosingOwnerOf node.Id with
                | Some owner -> Some (Choice1Of2 (owner, (node, intrinsic, awaited)))
                | None -> Some (Choice2Of2 (refusal "CCS8403" node.Range [ node.Id ] "Async.Await appears outside an enclosing async formation."))
            | _ -> None)
    let awaitsByOwner =
        awaitResolution
        |> List.choose (function Choice1Of2 pair -> Some pair | Choice2Of2 _ -> None)
        |> List.groupBy fst
        |> List.map (fun (owner, cuts) -> owner, cuts |> List.map snd)
        |> Map.ofList
    let orphanAwaitAccruals =
        awaitResolution
        |> List.choose (function Choice2Of2 accrued -> Some accrued | Choice1Of2 _ -> None)

    let settleOwner (owner: SemanticNode) =
        match formationCallable graph owner with
        | Some (_, lambda, (_, _, formal) :: _, body, captures, [ resultStorage; lifetimeScope; completion; frame; state; current ]) ->
            let callable = lambda.Id
            let ownerNodes = Set.union (subtree graph owner.Id) (subtree graph body)
            let bodyNodes = subtree graph body
            let order = evaluationOrder graph body
            let orderOf id = Map.tryFind id order |> Option.defaultValue System.Int32.MaxValue
            let isLocalDeclaration (declaration: NodeId) =
                match Map.tryFind declaration graph.Nodes with
                | Some { Kind = SemanticKind.PatternBinding _ } -> true
                | Some ({ Kind = SemanticKind.Binding _ } as binding) ->
                    match binding.Parent |> Option.bind (fun parent -> Map.tryFind parent graph.Nodes) with
                    | Some { Kind = SemanticKind.ModuleDef _ } -> false
                    | _ -> true
                | _ -> false
            let captured =
                ((captures |> List.choose _.SourceNodeId)
                 @ (readDeclarations graph body |> Set.toList |> List.filter (fun declaration -> not (ownerNodes.Contains declaration) && isLocalDeclaration declaration)))
                |> List.filter (fun declaration -> graph.Nodes.ContainsKey declaration && (Map.tryFind declaration graph.Nodes |> Option.exists _.IsReachable))
                |> List.distinct
                |> List.sortBy NodeId.value
            let locals =
                bodyNodes |> Set.toList |> List.filter (fun id ->
                    match Map.tryFind id graph.Nodes with
                    | Some ({ Kind = SemanticKind.Binding _ } as binding) when binding.IsReachable -> enclosingOwnerOf id = Some owner.Id
                    | _ -> false)
                |> List.sortBy orderOf
            let cuts =
                Map.tryFind owner.Id awaitsByOwner |> Option.defaultValue []
                |> List.choose (fun (site, intrinsic, awaited) ->
                    match intrinsic.Children with
                    | delimiter :: bindResume :: completionTarget :: cleanup :: _ ->
                        let parent = site.Parent |> Option.bind (fun parent -> Map.tryFind parent graph.Nodes)
                        let bound = match parent with Some ({ Kind = SemanticKind.Binding _ } as binding) -> Some binding.Id | _ -> None
                        let statement =
                            match bound with
                            | Some binding -> binding
                            | None -> site.Id
                        // One definition of the resumed computation, shared with the
                        // recipe that moves it into the cut's dispatch region.
                        let resumed = Machine.resumed graph statement
                        let continuation =
                            match resumed with
                            | next :: _ -> next
                            | [] -> completionTarget
                        Some { Site = site; Intrinsic = intrinsic; Awaited = awaited; Bound = bound
                               Continuation = continuation; Resumed = resumed
                               Delimiter = delimiter; BindResume = bindResume; Completion = completionTarget; Cleanup = cleanup
                               Order = orderOf site.Id }
                    | _ -> None)
                |> List.sortBy _.Order
            // Liveness and initialization are read over every resumed item, not
            // the first one: a value read by any later item of the block is live.
            let resumedReads (cut: Cut) =
                cut.Resumed |> List.fold (fun reads item -> Set.union reads (readDeclarations graph item)) Set.empty
            let resumedNodes (cut: Cut) =
                cut.Resumed |> List.fold (fun nodes item -> Set.union nodes (subtree graph item)) Set.empty
            let live (cut: Cut) =
                let reads = resumedReads cut
                let continuationNodes = resumedNodes cut
                let capturedLive = captured |> List.filter reads.Contains
                let localLive =
                    locals |> List.filter (fun binding ->
                        not (continuationNodes.Contains binding) && cut.Bound <> Some binding &&
                        orderOf binding < cut.Order && reads.Contains binding)
                capturedLive @ localLive |> List.distinct
            let liveByCut = cuts |> List.map (fun cut -> cut, live cut)
            let hasValue (id: NodeId) =
                Map.tryFind id graph.Nodes |> Option.exists (fun node -> not (isUnit node.Type))
            let statementOf (cut: Cut) =
                match cut.Bound with
                | Some binding -> binding
                | None -> cut.Site.Id
            let captureSlots = captured |> List.filter hasValue
            let retainedLocals =
                liveByCut |> List.collect snd |> List.filter (fun id -> not (List.contains id captured)) |> List.distinct |> List.filter hasValue
            // The value of each resumed computation leaves its dispatch region
            // through a frame slot of its own.
            let resultSlots =
                cuts |> List.choose (fun cut -> Machine.resumedValue graph (statementOf cut)) |> List.filter hasValue |> List.distinct
            // A retained value is stored and reloaded by value. A binding that
            // is assigned after its declaration requires a cell slot, which this
            // frame does not settle.
            let mutableSlots =
                (captureSlots @ retainedLocals) |> List.filter (fun id ->
                    match Map.tryFind id graph.Nodes with
                    | Some { Kind = SemanticKind.Binding(_, true, _, _) } -> true
                    | _ -> captures |> List.exists (fun capture -> capture.SourceNodeId = Some id && capture.IsMutable))
            let captureInfos : (NodeId * CaptureInfo option) list =
                captureSlots |> List.map (fun id ->
                    match captures |> List.tryFind (fun capture -> capture.SourceNodeId = Some id), Map.tryFind id graph.Nodes with
                    | Some capture, _ -> id, Some capture
                    | None, Some ({ Kind = SemanticKind.Binding(name, isMutable, _, _) } as node) ->
                        id, Some { Name = name; Type = node.Type; IsMutable = isMutable; SourceNodeId = Some id }
                    | None, Some ({ Kind = SemanticKind.PatternBinding name } as node) ->
                        id, Some { Name = name; Type = node.Type; IsMutable = false; SourceNodeId = Some id }
                    | None, _ -> id, None)
            // Retention of region-backed and borrowed values across each cut. A
            // refused retention leaves the frame without a settled slot set.
            let retentionOf (cut: Cut) (liveSlots: NodeId list) =
                liveSlots |> List.map (fun binding ->
                    let node = graph.Nodes[binding]
                    let ty = applySubst node.Type
                    let isView =
                        match ty with
                        | NativeType.TApp(tc, _) -> Types.isReadOnlyViewTypeCon tc || tc.NTUKind = Some NTUKind.NTUborrowedview
                        | _ -> false
                    let isRegionHandle =
                        match ty with
                        | NativeType.TApp(tc, _) -> Types.isRegionTypeCon tc
                        | _ -> false
                    let allocation =
                        regions.Settled |> List.tryFind (fun allocation -> allocation.Binding = Some binding || allocation.Site.Id = origin graph binding Set.empty)
                    let ownedRegion region = bodyNodes.Contains region
                    match isView, isRegionHandle, allocation with
                    | true, _, _ ->
                        None, refusal "CCS8424" cut.Site.Range [ cut.Site.Id; binding ]
                            "Borrowed region or view handle cannot be retained across an async suspension point without a dominating buffer retention or lifetime scope proof."
                    | _, true, _ when not (regions.RegionsOf binding |> List.forall ownedRegion) || List.contains binding captured ->
                        None, refusal "CCS8424" cut.Site.Range [ cut.Site.Id; binding ]
                            "A borrowed region handle cannot be retained across an async suspension point; its lifetime belongs to a scope outside the suspended computation."
                    | _, _, Some allocation ->
                        match allocation.Regions with
                        | [ region ] when ownedRegion region && not (List.contains binding captured) ->
                            // A region without a settled release is refused below.
                            let releases =
                                match Map.tryFind region regions.Releases with
                                | Some settled -> settled
                                | None -> []
                            let reads = cut.Resumed |> List.collect (fun item -> readsOf graph item binding) |> List.distinct
                            let readOrders = reads |> List.map orderOf
                            let releaseOrders = releases |> List.map orderOf
                            let allocationOrder = orderOf allocation.Site.Id
                            if releases.IsEmpty || reads.IsEmpty then
                                None, refusal "CCS8424" cut.Site.Range [ cut.Site.Id; binding; region ]
                                    "A region-allocated value live across an async suspension point has no settled region release frontier to prove retention against."
                            elif releaseOrders |> List.exists (fun release -> release > allocationOrder && readOrders |> List.exists (fun read -> release < read)) then
                                None, refusal "CCS8425" cut.Site.Range ([ cut.Site.Id; binding; region ] @ releases)
                                    "Borrowed region or view handle is invalidated or released before its post-resumption use across an async suspension point."
                            else
                                let lastRead = reads |> List.maxBy orderOf
                                let model : BorrowedResultViewScopeModel =
                                    { Call = allocation.Site.Id
                                      Declaration = cut.Site.Id
                                      Owner = region
                                      View = binding
                                      CallOrder = allocationOrder
                                      InvalidationOrders = releaseOrders
                                      ReadOrders = readOrders
                                      NullToNoneBoundary = true }
                                let obligation, accrued =
                                    claim cut.Site (sprintf "async_retention_%d_%d" (NodeId.value cut.Site.Id) (NodeId.value binding))
                                        "region-retention-scope"
                                        "The backing region is acquired before, and released only after, every post-resumption read across the suspension cut."
                                        (ObligationBody.BorrowedResultViewScope model)
                                        ([ cut.Site.Id; binding; region; allocation.Site.Id; lastRead ] @ releases @ reads)
                                Some { Binding = binding
                                       BackingRegion = region
                                       RetainedUntil = lastRead
                                       InvalidatedBy = releases
                                       RetirementCheck = obligation.Id }, accrued
                        | _ ->
                            None, refusal "CCS8424" cut.Site.Range [ cut.Site.Id; binding ]
                                "Borrowed region or view handle cannot be retained across an async suspension point without a dominating buffer retention or lifetime scope proof."
                    | _ -> None, none)
            let retentionByCut =
                liveByCut |> List.map (fun (cut, liveSlots) -> cut.Site.Id, retentionOf cut (liveSlots |> List.filter hasValue))
            let retentionAccruals = retentionByCut |> List.collect (fun (_, rows) -> rows |> List.map snd)
            // Frame placement follows the sequence frame: the state field, the
            // captures and the retained values take their range-selected
            // representations from the declared platform.
            let framePlacement =
                match retentionAccruals |> List.exists (fun accrued -> not accrued.Diagnostics.IsEmpty), mutableSlots, captureInfos |> List.filter (fun (_, info) -> info.IsNone), Map.tryFind state graph.Nodes with
                | true, _, _, _ -> Result.Error (joinAll retentionAccruals)
                | false, cell :: _, _, _ ->
                    Result.Error (refusal "CCS8403" owner.Range [ owner.Id; cell ] "A binding declared for assignment is retained in an async continuation frame, which has no settled cell slot for it.")
                | false, [], (undeclared, _) :: _, _ ->
                    Result.Error (refusal "CCS8403" owner.Range [ owner.Id; undeclared ] "An async formation capture has no named source declaration.")
                | false, [], [], None ->
                    Result.Error (refusal "CCS8403" owner.Range [ owner.Id ] "The async formation lacks its state anchor.")
                | false, [], [], Some anchor ->
                    // The formation's state anchor declares the frame's state field: an
                    // occurrence of the published graph holding the state before any
                    // suspension cut (-1), with the range of every settled state.
                    let stateSlot : SemanticNode =
                        { anchor with
                            Kind = SemanticKind.Literal (NativeLiteral.Int(-1L, NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register)))
                            Type = Types.intType
                            ValueRange = Some (ValueRange.bounded -1I (bigint (cuts.Length - 1))) }
                    let placementGraph = { graph with Nodes = graph.Nodes.Add(state, stateSlot) }
                    match Placement.placeAsyncContinuationWithRanges placementGraph state (captureInfos |> List.choose snd) (retainedLocals @ resultSlots) Map.empty with
                    | Result.Error error ->
                        Result.Error (refusal "CCS8403" owner.Range [ owner.Id ] ("The async continuation frame has no settled placement: " + Placement.describeContinuationPlacementError error))
                    | Result.Ok (SettledLayout.Record(_, Some frameBytes, Some frameAlignment), fields) ->
                        let slots : ContinuationSlot list =
                            fields |> List.choose (fun field ->
                                Map.tryFind field.Source placementGraph.Nodes |> Option.map (fun source ->
                                    { Source = field.Source
                                      ValueType = source.Type
                                      Field = field.Field
                                      Holds = field.Holds
                                      IsCapture = field.Role = Placement.ContinuationRole.Capture }))
                        let extents =
                            slots |> List.choose (fun slot ->
                                match slot.Field.Offset, slot.Field.Size, slot.Field.Align with
                                | Some offset, Some bytes, Some alignment -> Some (slot.Source, (offset, bytes, alignment))
                                | _ -> None)
                        if slots.Length <> fields.Length || extents.Length <> fields.Length then
                            Result.Error (refusal "CCS8403" owner.Range [ owner.Id ] "The async continuation frame has a slot without a complete placement.")
                        else
                            let placedSources = slots |> List.map _.Source |> Set.ofList
                            let machineCuts : Machine.Cut list =
                                liveByCut |> List.mapi (fun ordinal (cut, liveSlots) ->
                                    let machineCut : Machine.Cut =
                                        { Site = cut.Site.Id
                                          Statement = statementOf cut
                                          Ordinal = ordinal
                                          Retained = liveSlots |> List.filter placedSources.Contains }
                                    machineCut)
                            let plan : Machine.Plan =
                                { Formation = owner.Id
                                  Frame = frame
                                  Callable = callable
                                  Body = body
                                  State = state
                                  Captures = captureSlots |> List.filter placedSources.Contains
                                  Cuts = machineCuts
                                  Results = Set.ofList resultSlots }
                            match Machine.build placementGraph plan with
                            | Result.Error pending ->
                                Result.Error (refusal "CCS8403" owner.Range [ owner.Id; pending.Site ] ("The async continuation frame operations are not settled: " + pending.Reason))
                            | Result.Ok elaboration ->
                                Result.Ok (slots, Map.ofList extents, frameBytes, frameAlignment, elaboration)
                    | Result.Ok _ ->
                        Result.Error (refusal "CCS8403" owner.Range [ owner.Id ] "The declared target has no concrete async continuation frame extent and alignment.")
            match framePlacement with
            | Result.Error accrued -> [], [], accrued
            | Result.Ok (slots, extents, frameBytes, frameAlignment, elaboration) ->
                let placed = slots |> List.choose (fun slot -> Map.tryFind slot.Source extents)
                let frameSet = slots |> List.map _.Source |> Set.ofList
                let anchors = [ owner.Id; callable; body; frame; resultStorage; lifetimeScope; completion ] @ captured
                let frameClaim, frameAccrual =
                    layoutClaim owner (sprintf "async_frame_%d" (NodeId.value frame)) placed frameBytes frameAlignment anchors
                let resultType =
                    match applySubst owner.Type with
                    | NativeType.TApp(tc, [ element ]) when Types.isAsyncTypeCon tc -> applySubst element
                    | other -> other
                let resultLayout =
                    if isUnit resultType then Some ([], 0, 1)
                    else slotOf platform resultType |> Option.map (fun (_, _, bytes, alignment) -> [ (0, bytes, alignment) ], bytes, alignment)
                match resultLayout with
                | None ->
                    [], [], refusal "CCS8403" owner.Range [ owner.Id; resultStorage ] "The async formation's result type has no settled storage layout."
                | Some (resultSlots, resultBytes, resultAlignment) ->
                    let formationClaim, formationAccrual =
                        layoutClaim owner (sprintf "async_result_%d" (NodeId.value owner.Id)) resultSlots resultBytes resultAlignment anchors
                    let frameRow : ContinuationFrame =
                        { Owner = frame
                          Generator = callable
                          Formal = formal
                          State = state
                          Current = current
                          Slots = slots
                          Bytes = frameBytes
                          Alignment = frameAlignment
                          ScratchSlots = []
                          ScratchBytes = 0
                          ScratchAlignment = 1
                          Initializers = elaboration.CaptureInitializers
                          ResumeStates = cuts |> List.mapi (fun index _ -> index)
                          Obligations = [ frameClaim.Id ] }
                    let formationRow : AsyncFormation =
                        { Formation = owner.Id
                          Callable = callable
                          Body = body
                          CapturedBindings = captured
                          ResultType = resultType
                          ResultStorage = resultStorage
                          Frame = frame
                          LifetimeScope = lifetimeScope
                          CompletionProtocol = completion
                          Obligations = [ formationClaim.Id ]
                          Participants = participants anchors }
                    let suspensions =
                        liveByCut |> List.mapi (fun ordinal (cut, liveSlots) ->
                            let liveSlots = liveSlots |> List.filter frameSet.Contains
                            let continuationNodes = resumedNodes cut
                            let initialized =
                                (captured @ (locals |> List.filter (fun binding ->
                                    not (continuationNodes.Contains binding) && cut.Bound <> Some binding && orderOf binding < cut.Order)))
                                |> List.filter frameSet.Contains |> Set.ofList
                            let retained =
                                match retentionByCut |> List.tryFind (fun (site, _) -> site = cut.Site.Id) with
                                | Some (_, rows) -> rows
                                | None -> []
                            let spanning = retained |> List.choose fst
                            let retainedAccrual = retained |> List.map snd |> joinAll
                            let liveLayout =
                                liveSlots |> List.choose (fun id ->
                                    Map.tryFind id extents |> Option.map (fun (_, bytes, alignment) -> bytes, alignment))
                            let livePlaced, liveBytes, liveAlignment = tile liveLayout
                            let sources =
                                [ cut.Site.Id; owner.Id; frame; cut.Delimiter; cut.Continuation; cut.Awaited; cut.BindResume; cut.Completion; cut.Cleanup ] @ liveSlots
                            let suspensionClaim, suspensionAccrual =
                                layoutClaim cut.Site (sprintf "async_suspension_%d" (NodeId.value cut.Site.Id)) livePlaced liveBytes liveAlignment sources
                            let edge sources target role : Hyperedge = { Sources = sources; Target = target; Class = EdgeClass.Suspension; Role = role; Ordinal = 0 }
                            let edges =
                                [ edge [ owner.Id; callable; cut.Site.Id ] cut.Delimiter EdgeRole.Delimiter
                                  edge [ owner.Id; frame; cut.Awaited ] cut.Site.Id (EdgeRole.SuspensionCut ordinal)
                                  edge [ owner.Id; frame; cut.Site.Id; cut.BindResume ] cut.Continuation (EdgeRole.SuspensionResume ordinal)
                                  edge [ owner.Id; frame; cut.Site.Id; cut.Awaited ] cut.BindResume (EdgeRole.SuspensionResumeAction ordinal)
                                  edge [ owner.Id; frame; cut.Site.Id ] cut.Completion EdgeRole.SuspensionCompleted
                                  edge [ owner.Id; frame; cut.Site.Id ] cut.Cleanup EdgeRole.Cleanup ]
                                @ (if liveSlots.IsEmpty then [] else [ edge ([ owner.Id; frame ] @ liveSlots) cut.Site.Id EdgeRole.SuspensionLiveAcross ])
                            let retentionNodes =
                                spanning |> List.collect (fun retention -> [ retention.Binding; retention.BackingRegion; retention.RetainedUntil; retention.RetirementCheck ] @ retention.InvalidatedBy)
                            let row : AsyncSuspension =
                                { Site = cut.Site.Id
                                  Formation = owner.Id
                                  Frame = frame
                                  StateOrdinal = ordinal
                                  Delimiter = cut.Delimiter
                                  Continuation = cut.Continuation
                                  AwaitedSource = cut.Awaited
                                  LiveSlots = liveSlots
                                  InitializedSlots = initialized
                                  BindResumeTarget = cut.BindResume
                                  CompletionTarget = cut.Completion
                                  CleanupTarget = cut.Cleanup
                                  SpanningRetentions = spanning
                                  Obligations = [ suspensionClaim.Id ]
                                  Participants = participants (sources @ retentionNodes) }
                            (cut.Site.Id, row), joinAll [ retainedAccrual; suspensionAccrual; { none with Edges = edges } ])
                    [ (frame, frameRow), (owner.Id, formationRow), suspensions |> List.map fst ],
                    [ { Frame = frame; Callable = callable; Elaboration = elaboration } ],
                    joinAll ([ frameAccrual; formationAccrual ] @ (suspensions |> List.map snd))
        | _ ->
            [], [], refusal "CCS8403" owner.Range [ owner.Id ] "The async formation lacks its deferred callable or its protocol anchors."

    let settledOwners = owners |> List.map settleOwner
    let ownerRows = settledOwners |> List.collect (fun (rows, _, _) -> rows)
    let realizations = settledOwners |> List.collect (fun (_, machines, _) -> machines)
    let frames = ownerRows |> List.map (fun (frame, _, _) -> frame) |> Map.ofList
    let formations = ownerRows |> List.map (fun (_, formation, _) -> formation) |> Map.ofList
    let suspensions = ownerRows |> List.collect (fun (_, _, suspensions) -> suspensions) |> Map.ofList
    let formationSet = formations |> Map.keys |> Set.ofSeq
    let resolve id = resolveFormation graph formationSet id Set.empty

    let resultLayout (formation: AsyncFormation) =
        if isUnit formation.ResultType then Some ([], 0, 1)
        else slotOf platform formation.ResultType |> Option.map (fun (_, _, bytes, alignment) -> [ (0, bytes, alignment) ], bytes, alignment)

    let isOrchestration id =
        match Map.tryFind (origin graph id Set.empty) graph.Nodes with
        | Some node ->
            match intrinsicApplication graph node with
            | Some (_, info, _) -> info.FullName = "Async.Parallel" || info.FullName = "Async.Sequential"
            | None -> false
        | None -> false

    // A-01: activations of a settled formation; an activation of a settled
    // orchestration is that orchestration's join. Anything else is refused.
    let activations, activationAccruals =
        reachable |> List.choose (fun node ->
            match intrinsicApplication graph node with
            | Some (intrinsic, info, [ computation ])
                when info.FullName = "Async.RunSynchronously" || info.FullName = "Async.Start" || info.FullName = "Async.StartImmediate" ->
                match resolve computation |> Option.bind (fun id -> Map.tryFind id formations), intrinsic.Children with
                | Some formation, resultTarget :: _ :: completionTarget :: _ ->
                    match resultLayout formation with
                    | Some (slots, bytes, alignment) ->
                        let sources = [ node.Id; formation.Formation; resultTarget; completionTarget ]
                        let obligation, accrued =
                            layoutClaim node (sprintf "async_activation_%d" (NodeId.value node.Id)) slots bytes alignment sources
                        let row : AsyncActivation =
                            { Site = node.Id
                              Formation = formation.Formation
                              ResultTarget = resultTarget
                              CompletionTarget = completionTarget
                              Obligations = [ obligation.Id ]
                              Participants = participants sources }
                        Some (Some (node.Id, row), accrued)
                    | None -> Some (None, refusal "CCS8403" node.Range [ node.Id; formation.Formation ] "The activated formation's result type has no settled storage layout.")
                | None, _ when isOrchestration computation -> None
                | None, _ ->
                    Some (None, refusal "CCS8403" node.Range [ node.Id; computation ] (info.FullName + " does not activate a settled async formation or orchestration."))
                | Some _, _ ->
                    Some (None, refusal "CCS8403" node.Range [ node.Id ] (info.FullName + " lacks its result and completion targets."))
            | _ -> None)
        |> List.unzip

    // A-03: orchestrations over a settled array of child formations. The
    // child work items are explicit operations. Each child computation is
    // bound once ahead of the child array, and the orchestration's join is
    // elaborated into one activation per child, each applied to the child
    // read through its binding, and the store of each result into the
    // join's result array.
    let enclosingCallable (id: NodeId) =
        let rec climb (current: NodeId) (visited: Set<NodeId>) =
            if Set.contains current visited then None else
            match Map.tryFind current graph.Nodes |> Option.bind _.Parent |> Option.bind (fun parent -> Map.tryFind parent graph.Nodes) with
            | Some { Kind = SemanticKind.Lambda _; Id = lambda } -> Some lambda
            | Some parent -> climb parent.Id (Set.add current visited)
            | None -> None
        climb id Set.empty
    // The immutable binding an operand names.
    let rec namedBinding (id: NodeId) (visited: Set<NodeId>) =
        if Set.contains id visited then None else
        match Map.tryFind id graph.Nodes with
        | Some { Kind = SemanticKind.VarRef(_, Some definition) } ->
            match Map.tryFind definition graph.Nodes with
            | Some { Kind = SemanticKind.Binding(_, false, _, _) } -> Some definition
            | _ -> None
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> namedBinding inner (Set.add id visited)
        | _ -> None
    // The intrinsic applications that consume an orchestration's value.
    let consumersOf (site: NodeId) =
        reachable |> List.choose (fun node ->
            match intrinsicApplication graph node with
            | Some (_, info, [ computation ]) when node.Id <> site && origin graph computation Set.empty = site -> Some (node, info)
            | _ -> None)
    let orchestrationSites =
        reachable |> List.choose (fun node ->
            match intrinsicApplication graph node with
            | Some (intrinsic, info, [ tasks ]) when info.FullName = "Async.Parallel" || info.FullName = "Async.Sequential" -> Some (node, intrinsic, info, tasks)
            | _ -> None)
    // The child arrays: each is an array expression bound directly to an
    // immutable name outside every async formation. Its children are bound
    // once, whatever number of orchestrations read the array.
    let childArrayOf (tasks: NodeId) =
        match namedBinding tasks Set.empty, Map.tryFind (origin graph tasks Set.empty) graph.Nodes with
        | Some binding, Some ({ Kind = SemanticKind.ArrayExpr _ } as array)
            when (Map.tryFind binding graph.Nodes |> Option.map _.Children) = Some [ array.Id ] && (enclosingOwnerOf binding).IsNone ->
            Some (array.Id, binding)
        | _ -> None
    let childArrays =
        orchestrationSites
        |> List.choose (fun (_, _, _, tasks) -> childArrayOf tasks)
        |> List.distinctBy fst
        |> List.map (fun (array, binding) ->
            let plan : Machine.ChildArrayPlan = { Array = array; Tasks = binding }
            array, Machine.bindChildren graph plan)
        |> Map.ofList
    let orchestrations =
        orchestrationSites |> List.map (fun (node, intrinsic, info, tasks) ->
            let mode = if info.FullName = "Async.Parallel" then AsyncOrchestrationMode.Parallel else AsyncOrchestrationMode.Sequential
            let unsettled related message = None, [], None, refusal "CCS8403" node.Range (node.Id :: related) (info.FullName + message)
            match Map.tryFind (origin graph tasks Set.empty) graph.Nodes, intrinsic.Children with
            | Some { Kind = SemanticKind.ArrayExpr elements }, joinCondition :: resultStorage :: lifetimeScope :: _ when not elements.IsEmpty ->
                let children = elements |> List.map (fun element -> element, resolve element |> Option.bind (fun id -> Map.tryFind id formations))
                match children |> List.tryFind (fun (_, formation) -> formation.IsNone) with
                | Some (child, _) -> unsettled [ child ] " has a child that is not a settled async formation."
                | None ->
                    let children = children |> List.map (fun (element, formation) -> element, Option.get formation)
                    let childIds = children |> List.map fst
                    match childIds |> List.distinct |> List.length = childIds.Length, children |> List.map (snd >> resultLayout) with
                    | false, _ -> unsettled [] " requires distinct child computations."
                    | true, layouts when layouts |> List.forall Option.isSome && (layouts |> List.choose id |> List.map (fun (_, bytes, alignment) -> bytes, alignment) |> List.distinct |> List.length) = 1 ->
                        let _, stride, alignment = layouts |> List.head |> Option.get
                        match stride > 0, childArrayOf tasks |> Option.bind (fun (array, _) -> Map.tryFind array childArrays), consumersOf node.Id with
                        | false, _, _ -> unsettled [] " requires a child result with positive storage."
                        | true, None, _ ->
                            unsettled [ tasks ] " requires its child array bound directly to an immutable name outside an async formation, so that each child activation reads its child through a binding."
                        | true, Some (Result.Error pending), _ ->
                            unsettled [ pending.Site ] (" has no settled child bindings: " + pending.Reason)
                        | true, Some (Result.Ok _), [] ->
                            unsettled [] " has no Async.RunSynchronously join; its child activations have no settled site."
                        | true, Some (Result.Ok bound), [ (joinSite, joinInfo) ]
                            when joinInfo.FullName = "Async.RunSynchronously" && enclosingCallable joinSite.Id = enclosingCallable node.Id
                                 && (enclosingOwnerOf joinSite.Id).IsNone && bound.Children.Length = children.Length ->
                            match Clef.Compiler.Baker.Recipes.ArrayConstructionRecipes.uninitialized graph node joinSite.Type children.Length with
                            | Result.Error reason -> unsettled [joinSite.Id] (" has no result allocation: " + reason)
                            | Result.Ok storage ->
                                let plan : Machine.JoinPlan =
                                    { Orchestration = node.Id
                                      Join = joinSite.Id
                                      Storage = storage.Value
                                      Children =
                                        List.zip children bound.Children |> List.map (fun ((_, formation), child) ->
                                            let work : Machine.ChildPlan =
                                                { Child = child
                                                  Result = formation.ResultType
                                                  Range = Map.tryFind formation.Body graph.Nodes |> Option.bind _.ValueRange }
                                            work) }
                                match Machine.join graph plan with
                                | Result.Error pending ->
                                    unsettled [ pending.Site ] (" has no settled child activations: " + pending.Reason)
                                | Result.Ok elaboration ->
                                    // All consumers were settled above. The source
                                    // orchestration is now a marker; the join owns
                                    // explicit storage and child activations.
                                    let anchors = [joinCondition;resultStorage;lifetimeScope]
                                    let marker = { node with Kind=SemanticKind.Sequential anchors; Type=Types.unitType; Children=anchors }
                                    let elaboration = { elaboration with Nodes=marker :: storage.Nodes @ elaboration.Nodes }
                                    // The explicit child activations are the orchestration's work items.
                                    let workItems = elaboration.Activations |> List.map (fun child -> child.Site.Id)
                                    let deliveries = elaboration.Activations |> List.map _.Delivery
                                    let workDependencies =
                                        match mode with
                                        | AsyncOrchestrationMode.Parallel -> []
                                        | AsyncOrchestrationMode.Sequential -> List.pairwise workItems
                                    let slots = workItems |> List.mapi (fun index _ -> index * stride, stride, alignment)
                                    // The join owns its guarded allocation and every child
                                    // delivery. The original orchestration remains a marker.
                                    let sources =
                                        [ node.Id; joinCondition; resultStorage; lifetimeScope; elaboration.Storage; elaboration.Results; storage.Allocation ] @ (storage.Nodes |> List.map _.Id) @ workItems @ deliveries
                                        |> List.distinct
                                    let obligation, accrued =
                                        layoutClaim node (sprintf "async_orchestration_%d" (NodeId.value node.Id)) slots (workItems.Length * stride) alignment sources
                                    let row : AsyncOrchestration =
                                        { Site = node.Id
                                          Mode = mode
                                          Children = workItems
                                          WorkDependencies = workDependencies
                                          ResultOrdering = workItems |> List.mapi (fun index child -> index, child)
                                          JoinCondition = joinCondition
                                          ResultStorage = storage.Allocation
                                          ResultCapacity = workItems.Length
                                          ElementStride = stride
                                          LifetimeScope = lifetimeScope
                                          SynchronizationObligations = [ obligation.Id ]
                                          Participants = participants (sources @ childIds @ (bound.Children |> List.map _.Binding)) }
                                    // Each child activation is an activation of its child's formation.
                                    let childRows =
                                        List.zip3 children bound.Children elaboration.Activations |> List.map (fun ((element, formation), binding, child) ->
                                            let sources =
                                                [ child.Site.Id; formation.Formation; child.ResultTarget; child.CompletionTarget
                                                  child.Computation; child.Delivery; binding.Binding; element; node.Id ]
                                            let claimed, childAccrual =
                                                layoutClaim child.Site (sprintf "async_child_activation_%d" (NodeId.value child.Site.Id)) [ (0, stride, alignment) ] stride alignment sources
                                            let activation : AsyncActivation =
                                                { Site = child.Site.Id
                                                  Formation = formation.Formation
                                                  ResultTarget = child.ResultTarget
                                                  CompletionTarget = child.CompletionTarget
                                                  Obligations = [ claimed.Id ]
                                                  Participants = participants sources }
                                            (child.Site.Id, activation), childAccrual)
                                    Some (node.Id, row), childRows |> List.map fst, Some (bound, elaboration),
                                    joinAll ({ accrued with Edges=accrued.Edges @ storage.Edges } :: (childRows |> List.map snd))
                        | true, Some (Result.Ok _), consumers ->
                            unsettled (consumers |> List.map (fun (consumer, _) -> consumer.Id))
                                " requires exactly one Async.RunSynchronously join in the callable that forms it, outside an async formation; no other consumer has settled child activations."
                    | true, _ -> unsettled [] " requires children whose results share one settled storage layout."
            | _ -> unsettled [ tasks ] " requires a settled array of child async computations.")
    // The elaborations of the settled orchestrations: the child bindings of
    // each child array, once, and each join. Every edited occurrence has one
    // current version under all the rewrites that name it.
    let elaborated = orchestrations |> List.choose (fun (_, _, elaboration, _) -> elaboration)
    let boundArrays = elaborated |> List.map fst |> List.distinctBy (fun bound -> bound.Rewrite)
    let rewrites =
        (boundArrays |> List.map (fun bound -> bound.Rewrite, bound.Nodes, bound.Edited, []))
        @ (elaborated |> List.map (fun (_, join) ->
            // The result array holds one element per child.
            let edited = join.Nodes |> List.choose (fun node -> if graph.Nodes.ContainsKey node.Id then Some node.Id else None) |> Set.ofList
            join.Rewrite, join.Nodes, edited, join.Activations |> List.map (fun child -> child.Delivery, join.Activations.Length)))
    let joins, joinRefusals =
        rewrites
        |> List.groupBy (fun (edit, _, _, _) -> edit.Target)
        |> List.map (fun (target, group) ->
            let previous = graph.Nodes[target]
            match Machine.rewrite previous (group |> List.map (fun (edit, _, _, _) -> edit)) with
            | Result.Ok version ->
                let fold : Fold =
                    { Carrier = target
                      Nodes = version :: (group |> List.collect (fun (_, nodes, _, _) -> nodes))
                      Edited = group |> List.fold (fun edited (_, _, ids, _) -> Set.union edited ids) (Set.singleton target)
                      Provenance = []
                      Accesses = group |> List.collect (fun (_, _, _, accesses) -> accesses) }
                Some fold, none
            | Result.Error reason ->
                None, refusal "CCS8403" previous.Range [ target ] ("The orchestration elaboration has no settled structure: " + reason))
        |> List.unzip
    let joins = joins |> List.choose id
    let orchestrationRows = orchestrations |> List.choose (fun (row, _, _, _) -> row) |> Map.ofList
    let childActivations = orchestrations |> List.collect (fun (_, rows, _, _) -> rows)
    // A-02: a settled suspension cut activates the formation it awaits. The
    // Async.Await application is published as an activation of that
    // formation, with the result and completion targets of its own protocol
    // anchors.
    let awaitActivations, awaitAccruals =
        awaitsByOwner |> Map.toList |> List.collect snd
        |> List.choose (fun (site, intrinsic, awaited) ->
            match suspensions.ContainsKey site.Id, resolve awaited |> Option.bind (fun id -> Map.tryFind id formations), intrinsic.Children with
            | true, Some formation, resultTarget :: _ :: completionTarget :: _ ->
                resultLayout formation |> Option.map (fun (slots, bytes, alignment) ->
                    let sources = [ site.Id; formation.Formation; resultTarget; completionTarget; awaited ]
                    let obligation, accrued =
                        layoutClaim site (sprintf "async_await_activation_%d" (NodeId.value site.Id)) slots bytes alignment sources
                    let row : AsyncActivation =
                        { Site = site.Id
                          Formation = formation.Formation
                          ResultTarget = resultTarget
                          CompletionTarget = completionTarget
                          Obligations = [ obligation.Id ]
                          Participants = participants sources }
                    (site.Id, row), accrued)
            | _ -> None)
        |> List.unzip
    let activationRows = (activations |> List.choose id) @ childActivations @ awaitActivations |> Map.ofList
    frames, formations, suspensions, activationRows, orchestrationRows, realizations, joins,
    joinAll (orphanAwaitAccruals @ (settledOwners |> List.map (fun (_, _, accrued) -> accrued)) @ activationAccruals @ awaitAccruals @ (orchestrations |> List.map (fun (_, _, _, accrued) -> accrued)) @ joinRefusals)

//-------------------------------------------------------------------------
// Frame realization: fan the settled elaborations out and fold them in
//-------------------------------------------------------------------------

/// The provenance of every frame read of one formation: the slot it reads
/// and the stores of that slot through the formation's frame allocation.
let private frameProvenance (machine: Realization) : Hyperedge list =
    let writers =
        machine.Elaboration.Writes
        |> List.groupBy (fun (_, slot, _) -> slot)
        |> List.map (fun (slot, rows) ->
            slot, rows |> List.sortBy (fun (writer, _, _) -> NodeId.value writer) |> List.collect (fun (writer, _, value) -> [ writer; value ]))
        |> Map.ofList
    machine.Elaboration.Reads |> List.collect (fun (read, slot) ->
        let stores =
            match writers.TryFind slot with
            | Some rows -> rows
            | None -> []
        [ { Sources = [ slot ]; Target = read; Class = EdgeClass.Provenance; Role = EdgeRole.ContinuationValue; Ordinal = 0 }
          { Sources = [ machine.Frame; machine.Callable; machine.Elaboration.Allocation; slot ] @ stores
            Target = read; Class = EdgeClass.Provenance; Role = EdgeRole.ContinuationSlotAccess; Ordinal = 0 } ])

let private frameFold (machine: Realization) : Fold =
    { Carrier = machine.Callable
      Nodes = machine.Elaboration.Nodes
      Edited = machine.Elaboration.Edited
      Provenance = frameProvenance machine
      Accesses = [] }

/// Fold every settled elaboration into the graph: the frame operations of
/// each formation and the child activations of each orchestration join. Each
/// edited occurrence keeps its identity; replaced structural incidence is
/// retired and the incidence of every current node is recorded with the
/// provenance its elaboration settled.
let private realize (graph: SemanticGraph) (folds: Fold list) : SemanticGraph =
    match folds with
    | [] -> graph
    | _ ->
        let nodes = folds |> List.collect _.Nodes
        let edited = folds |> List.fold (fun ids fold -> Set.union ids fold.Edited) Set.empty
        let versions =
            nodes |> List.filter (fun node -> edited.Contains node.Id) |> List.map (fun node -> node.Id, node) |> Map.ofList
        let created =
            folds
            |> List.groupBy _.Carrier
            |> List.map (fun (carrier, group) ->
                carrier, group |> List.collect (fun fold -> fold.Nodes |> List.filter (fun node -> not (fold.Edited.Contains node.Id))))
            |> Map.ofList
        let create (source: SemanticNode) (_: SemanticGraph) =
            match versions.TryFind source.Id with
            | Some version ->
                let fresh =
                    match created.TryFind source.Id with
                    | Some nodes -> nodes
                    | None -> []
                RecipeCreated
                    { OriginalNodeId = source.Id
                      NewNodes = version :: fresh
                      NewEdges = []
                      ReplacementRootId = source.Id
                      ElaborationKind = "Baker"
                      ElaborationSource = "Async.frame" }
            | None -> NotApplicable "The occurrence has no async continuation or orchestration elaboration."
        let folded = FoldIn.foldIn (FanOut.fanOut "AsyncContinuation" (fun node -> versions.ContainsKey node.Id) create graph) graph
        let key (edge: Hyperedge) = edge.Target, edge.Class, edge.Role, edge.Ordinal, edge.Sources
        let retired =
            edited
            |> Set.toList
            |> List.collect (fun id ->
                match graph.Nodes.TryFind id with
                | Some previous -> structuralIncidence previous
                | None -> [])
            |> List.map key
            |> Set.ofList
        let incidence = nodes |> List.collect structuralIncidence
        let provenance = folds |> List.collect _.Provenance
        let current = { folded with Edges = (folded.Edges |> List.filter (fun edge -> not (retired.Contains(key edge)))) @ incidence @ provenance }
        // The child reads and result stores of an orchestration join are source
        // array accesses. Each receives its bounds guard from the memory access
        // elaboration, as every source access does. The guard's zero endpoint
        // and its extent read hold the ranges this settlement establishes: the
        // extent of the addressed array is the orchestration's child count.
        let extents = folds |> List.collect _.Accesses |> Map.ofList
        let guarded =
            if extents.IsEmpty then current
            else MemoryAccessElaboration.normalize current
        let endpoints =
            guarded.Edges |> List.collect (fun edge ->
                match edge.Role, edge.Sources with
                | EdgeRole.MemoryAccessGuard, [ _; _; length; zero; _; _; _; _; source ] ->
                    match extents.TryFind source with
                    | Some extent -> [ length, ValueRange.bounded (bigint extent) (bigint extent); zero, ValueRange.bounded 0I 0I ]
                    | None -> []
                | _ -> [])
            |> Map.ofList
        let ranged =
            guarded.Nodes |> Map.map (fun id node ->
                match endpoints.TryFind id with
                | Some range when node.ValueRange.IsNone -> { node with ValueRange = Some range }
                | _ -> node)
        // The fold keeps every node identity. The tables settled before this
        // representation-only recipe remain keyed by those identities.
        { guarded with
            Nodes = ranged
            FieldRanges = graph.FieldRanges
            ElementRanges = graph.ElementRanges
            Layouts = graph.Layouts
            StaticStringPool = graph.StaticStringPool
            LiteralStorage = graph.LiteralStorage
            Escaping = graph.Escaping
            Codata = graph.Codata
            RangeContextFacts = graph.RangeContextFacts
            SequenceRangeProvenance = graph.SequenceRangeProvenance }
        |> Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable
        |> RepresentationRanges.preserve graph

/// Result arrays use the numeric owner's complete-write element carrier.
/// Renew orchestration geometry after the explicit join deliveries have entered
/// that domain; a child's activation result layout is a separate contract.
let settleResultStorage (graph: SemanticGraph) =
    let facts = graph.Codata.Value
    if facts.AsyncOrchestrations.IsEmpty then graph else
    match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
    | Result.Error _ -> graph
    | Result.Ok numeric ->
        let updates =
            facts.AsyncOrchestrations |> Map.toList |> List.choose(fun (site,row) ->
                numeric.Elements.TryFind row.ResultStorage
                |> Option.bind (Placement.extentOfSlot graph)
                |> Option.map(fun (bytes,alignment) ->
                    let slots = row.ResultOrdering |> List.map(fun (ordinal,_) -> ordinal*bytes,bytes,alignment)
                    let citizens = row.SynchronizationObligations |> List.choose(fun id ->
                        graph.Nodes.TryFind id |> Option.bind(fun node ->
                            match node.Kind with
                            | SemanticKind.Obligation info ->
                                Some {node with Kind=SemanticKind.Obligation {info with Body=ObligationBody.ContinuationLayout(slots,row.ResultCapacity*bytes,alignment)}}
                            | _ -> None))
                    site,{row with ElementStride=bytes},citizens))
        let graph = ObligationElaboration.foldIn
                        {NewNodes=[];NewEdges=[];Annotated=updates |> List.collect(fun (_,_,citizens) -> citizens)} graph
        let rows = updates |> List.fold(fun rows (site,row,_) -> Map.add site row rows) facts.AsyncOrchestrations
        {graph with Codata=lazy {facts with AsyncOrchestrations=rows;WitnessEmission=None}}

//-------------------------------------------------------------------------
// Entry
//-------------------------------------------------------------------------

let private settleCore (admitted: bool) (graph: SemanticGraph) : SemanticGraph * Settlement =
    if not admitted || graph.Platform.IsNone then
        graph, empty
    else
        let reachable =
            graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.sortBy (fun node -> NodeId.value node.Id) |> Seq.toList
        let relevant =
            reachable |> List.exists (fun node ->
                isFormation node ||
                (match node.Kind with
                 | SemanticKind.Intrinsic info ->
                     info.FullName.StartsWith("Async.", System.StringComparison.Ordinal)
                     || info.FullName.StartsWith("Region.", System.StringComparison.Ordinal)
                 | _ -> false))
        if not relevant then
            graph, empty
        else
            let regions, passings, copies, residences, regionAccrual = settleRegions graph reachable
            let frames, formations, suspensions, activations, orchestrations, machines, joins, asyncAccrual = settleAsync graph reachable regions
            let accrued = join regionAccrual asyncAccrual
            let enrichment : Enrichment =
                { NewNodes = accrued.Obligations
                  NewEdges = accrued.Edges
                  Annotated = [] }
            let enrichedGraph = ObligationElaboration.foldIn enrichment graph
            let realized = realize enrichedGraph ((machines |> List.map frameFold) @ joins)
            let origins =
                machines
                |> List.collect (fun machine -> machine.Elaboration.FrameReferences |> List.map (fun reference -> reference, machine.Frame))
                |> Map.ofList
            // The frame is storage of the deferred callable's own activation.
            let frameResidences =
                machines |> List.fold (fun facts machine -> Map.add machine.Elaboration.Allocation EscapeKind.StackScoped facts) residences
            realized,
            { Frames = frames
              Formations = formations
              Activations = activations
              Suspensions = suspensions
              Orchestrations = orchestrations
              RegionAllocations = regions.Allocations
              RegionCallPassings = passings
              RegionCopyEndpoints = copies
              Residences = frameResidences
              Origins = origins
              Diagnostics = accrued.Diagnostics }

let settleWhenSourceAdmitted (admitted: bool) (graph: SemanticGraph) : SemanticGraph * Settlement =
    Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> settleCore admitted graph)

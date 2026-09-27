// SPDX-License-Identifier: MIT
/// Source-owned array access and actual mutable-place elaboration. Bounds are
/// ordinary guarded source computations before numeric and demand settlement.
module Clef.Compiler.Baker.Recipes.MemoryAccessRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.Obligations
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module Requirements = Clef.Compiler.PSGSaturation.SemanticGraph.Requirements
module Memory = Clef.Compiler.Baker.Ingredients.MemoryValues
module TypeIdentity = Clef.Compiler.NativeTypedTree.TypeIdentities

type Expansion = { Structure: Result; Edges: Hyperedge list }

let private isArray (graph: SemanticGraph) id =
    match graph.Nodes.TryFind id |> Option.map (fun node -> applySubst node.Type) with
    | Some(NativeType.TApp(tc, [_])) -> tc.NTUKind = Some NTUKind.NTUarray
    | _ -> false

let rec private sourceIntrinsic (graph: SemanticGraph) id arguments =
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.Intrinsic info } -> Some(info, arguments)
    | Some { Kind = SemanticKind.Application(callee, actuals) } -> sourceIntrinsic graph callee (actuals @ arguments)
    | _ -> None

let private access (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.IndexGet(buffer, index) when isArray graph buffer -> Some(buffer, index, None)
    | SemanticKind.IndexSet(buffer, index, value) when isArray graph buffer -> Some(buffer, index, Some value)
    | SemanticKind.ElementAddress(buffer, index) when isArray graph buffer -> Some(buffer, index, None)
    | SemanticKind.AddressOf(expression, _) ->
        match graph.Nodes.TryFind expression with
        | Some { Kind = SemanticKind.IndexGet(buffer, index) } when isArray graph buffer -> Some(buffer, index, None)
        | _ -> None
    | SemanticKind.Application _ ->
        match sourceIntrinsic graph node.Id [] with
        | Some(info, [buffer; index])
            when info.Module = IntrinsicModule.Array && info.Operation = "get" && isArray graph buffer -> Some(buffer, index, None)
        | Some(info, [buffer; index; value])
            when info.Module = IntrinsicModule.Array && info.Operation = "set" && isArray graph buffer -> Some(buffer, index, Some value)
        | _ -> None
    | _ -> None

let private address (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.AddressOf(expression, _) ->
        match graph.Nodes.TryFind expression with
        | Some inner ->
            match applySubst inner.Type, inner.Kind with
            | NativeType.TByref _, _ -> Some(SemanticKind.Reborrow expression, [expression])
            | _, SemanticKind.VarRef(_, Some binding) ->
                match graph.Nodes.TryFind binding with
                | Some { Kind = SemanticKind.Binding(_, true, _, _) } -> Some(SemanticKind.CellAddress binding, [])
                | _ -> None
            | _, SemanticKind.FieldGet(receiver, field) ->
                match graph.Nodes.TryFind receiver |> Option.map (fun node -> applySubst node.Type) with
                | Some(NativeType.TApp(tc, _)) ->
                    Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances.tryDefinition (NominalTypeIdentity.ofConstructor tc) graph
                    |> Option.bind (fun declaration ->
                        match declaration.Metadata.TryFind "TypeDef.MutableFields" with
                        | Some(MetadataValue.StringList fields) when List.contains field fields -> Some(SemanticKind.FieldAddress(receiver, field), [receiver])
                        | _ -> None)
                | _ -> None
            | _ -> None
        | None -> None
    | _ -> None

let candidates (graph: SemanticGraph) =
    let placeInputs =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind, node.Metadata.TryFind "Baker.MemoryPlaceSource" with
            | SemanticKind.AddressOf(input, _), _ | _, Some(MetadataValue.NodeId input) -> Some input
            | _ -> None) |> Set.ofSeq
    graph.Nodes.Values |> Seq.filter (fun node ->
        node.IsReachable && not (placeInputs.Contains node.Id) &&
        not (node.Metadata.ContainsKey "Baker.MemoryGuarded") &&
        ((access graph node).IsSome || (address graph node).IsSome))
    |> Seq.toList

let materialize (ctx: Context) (graph: SemanticGraph) (source: SemanticNode) : Expansion =
    let state = SaturationState.create source.Range ctx.OriginalHOF ctx.ExpansionId source.Id graph.Platform
    let evidence = ResizeArray<Hyperedge>()
    let recipe =
      match address graph source with
      | Some(kind, children) -> saturation {
            do! enrich source kind source.Type children source.EmissionStrategy false
            return source.Id
        }
      | None -> saturation {
        let buffer, index, stored = access graph source |> Option.defaultWith (fun () -> invalidOp "No source array access at memory recipe site")
        let indexType = graph.Nodes[index].Type
        let bufferType = graph.Nodes[buffer].Type
        let! zero = numLit 0L indexType
        let intrinsic =
            { Module = IntrinsicModule.Array; Operation = "length"; Category = IntrinsicCategory.Pure; FullName = "Array.length" }
        let! lengthFunction = createWithChildren (SemanticKind.Intrinsic intrinsic) (NativeType.TFun(bufferType, Types.intType)) []
        let! length = app lengthFunction [buffer] Types.intType
        let! lower = ge index zero indexType
        let! upper = lt index length indexType
        let! predicate = andAlso lower upper
        let diagnostic = sprintf "Array index out of bounds at %s:%d:%d" source.Range.File source.Range.Start.Line source.Range.Start.Column
        let! required = createWithChildren (SemanticKind.Require(predicate, diagnostic)) Types.unitType [predicate]
        let! current = getUserState
        let kind, children =
            match source.Kind, stored with
            | SemanticKind.AddressOf _, _ | SemanticKind.ElementAddress _, _ -> SemanticKind.ElementAddress(buffer, index), [buffer; index]
            | _, None -> SemanticKind.IndexGet(buffer, index), [buffer; index]
            | _, Some value -> SemanticKind.IndexSet(buffer, index, value), [buffer; index; value]
        let operation =
            { mkNode current kind source.Type children with
                Metadata = source.Metadata.Add("Baker.MemoryGuarded", MetadataValue.Bool true)
                Parent = Some source.Id; ArenaAffinity = source.ArenaAffinity }
        do! emit operation
        do! enrich source (SemanticKind.Sequential [required; operation.Id]) source.Type [required; operation.Id] source.EmissionStrategy false
        evidence.Add { Class = EdgeClass.Provenance; Role = EdgeRole.MatchRequirement; Ordinal = 1
                       Sources = [required; predicate; operation.Id]; Target = source.Id }
        evidence.Add { Class = EdgeClass.Provenance; Role = EdgeRole.MemoryAccessGuard; Ordinal = 0
                       Sources = [buffer; index; length; zero; lower; upper; predicate; required; source.Id]; Target = operation.Id }
        if stored.IsNone then
            match graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringByteView view when view.Site=buffer -> Some view | _ -> None) with
            | [view] ->
                evidence.Add { Class=EdgeClass.Range; Role=EdgeRole.StringByteRange(0I,255I); Ordinal=0
                               Sources=[buffer;view.Source;view.RepresentationDeclaration;index;length;lower;upper;predicate;required;source.Id]
                               Target=operation.Id }
            | _ ->
                match Clef.Compiler.PSGSaturation.SemanticGraph.StringByteStorage.evidence graph buffer with
                | Some(_,lo,hi,participants) ->
                    evidence.Add { Class=EdgeClass.Range;Role=EdgeRole.StringByteRange(lo,hi);Ordinal=0
                                   Sources=[buffer;index;length;lower;upper;predicate;required;source.Id]@Set.toList participants
                                   Target=operation.Id }
                | None -> ()
        return source.Id
      }
    let outcome, nodes = run state recipe
    match outcome with
    | NoMatch reason -> invalidOp ("Array bounds source elaboration failed: " + reason)
    | Matched root ->
        let nodes = nodes |> List.map (fun node ->
            let metadata = node.Metadata.Add("Baker.MemoryOwned", MetadataValue.Bool true)
            let metadata =
                match source.Kind with
                | SemanticKind.AddressOf(input, _) when node.Id = source.Id -> metadata.Add("Baker.MemoryPlaceSource", MetadataValue.NodeId input)
                | _ -> metadata
            { node with Metadata = metadata })
        let key (edge: Hyperedge) = edge.Target, edge.Class, edge.Role, edge.Ordinal, edge.Sources
        let replaced = structuralIncidence source |> List.map key |> Set.ofList
        { Structure = mkResultNoShadow nodes root []
          Edges = (graph.Edges |> List.filter (fun edge -> not (replaced.Contains(key edge))))
                  @ (nodes |> List.collect structuralIncidence) @ List.ofSeq evidence }

exception private MissingContract of string
let private needed reason = function Some value -> value | None -> raise (MissingContract reason)
let private demand condition reason = if not condition then raise (MissingContract reason)
let private live (graph: SemanticGraph) id = graph.Nodes.TryFind id |> Option.filter _.IsReachable |> needed "A memory premise is not a live source occurrence."

let private intrinsic = sourceIntrinsic

let private arrayLength (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.FieldGet(buffer, "Length") when isArray graph buffer -> Some buffer
    | SemanticKind.Application _ ->
        match intrinsic graph node.Id [] with
        | Some(info, [buffer]) when info.Module = IntrinsicModule.Array && info.Operation = "length" && isArray graph buffer -> Some buffer
        | _ -> None
    | _ -> None

let private pendingArrayConstruction (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Application _ ->
        match sourceIntrinsic graph node.Id [] with
        | Some(info, arguments) when info.Module = IntrinsicModule.Array ->
            let requiredArity =
                match info.Operation with "zeroCreate" -> Some 1 | "sub" -> Some 3 | "blit" -> Some 5 | _ -> None
            requiredArity |> Option.bind (fun arity -> if arguments.Length = arity then Some info.Operation else None)
        | _ -> None
    | _ -> None

let private carrier (numeric: NumericWitnessProjection) id =
    numeric.Values.TryFind id |> needed "The source numeric owner did not settle this memory scalar carrier."

let private element (numeric: NumericWitnessProjection) id =
    numeric.Elements.TryFind id |> needed "The source numeric owner did not settle the complete-write element slot."

let private size (graph: SemanticGraph) slot =
    Placement.extentOfSlot graph slot |> needed "The declared target has no admitted physical extent for this element slot."

let private pointerBits (graph: SemanticGraph) =
    let context = graph.Platform |> needed "An address requires a declared target Pointer dimension."
    match PlatformContext.pointerSize context with
    | Ok bytes when bytes > 0 -> bytes * 8
    | _ -> raise (MissingContract "An address requires a positive declared target Pointer dimension.")

let private callIs graph operation arguments id =
    match intrinsic graph id [] with
    | Some(info, actuals) -> info.Module = IntrinsicModule.Operators && info.Operation = operation && actuals = arguments
    | _ -> false

/// A guard fact cites actual executable source expressions. Changing a term,
/// bypassing Require, or reusing another access's requirement invalidates it.
let private bounds (graph: SemanticGraph) (numeric: NumericWitnessProjection) site buffer index =
    let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard && edge.Target = site)
    match rows with
    | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [actualBuffer; actualIndex; length; zero; lower; upper; predicate; required; frontier] }]
        when actualBuffer = buffer && actualIndex = index ->
        demand (arrayLength graph (live graph length) = Some buffer) "The bounds guard does not read this exact buffer's extent."
        demand (match (live graph zero).Kind with SemanticKind.Literal(NativeLiteral.Int(0L, _)) -> true | _ -> false)
               "The bounds guard has no exact zero lower endpoint."
        demand (callIs graph "op_GreaterThanOrEqual" [index;zero] lower && callIs graph "op_LessThan" [index;length] upper)
               "The bounds guard does not establish 0 <= index < this buffer's extent."
        demand (match (live graph predicate).Kind with
                | SemanticKind.IfThenElse(condition, yes, Some no) when condition = lower && yes = upper ->
                    match (live graph no).Kind with SemanticKind.Literal(NativeLiteral.Bool false) -> true | _ -> false
                | _ -> false) "The bounds conjunction is absent or changed."
        let requirement = Requirements.tryRequirement graph required |> needed "The bounds guard has no admitted always-active source failure frontier."
        demand (requirement.Condition = predicate && requirement.Frontier = frontier && requirement.Continuation = site)
               "The bounds requirement does not guard this exact access continuation."
        let indexCarrier, extentCarrier = carrier numeric index, carrier numeric length
        demand (match indexCarrier.Slot, extentCarrier.Slot with SettledSlot.Integer _, SettledSlot.Integer _ -> true | _ -> false)
               "Array bounds require settled integer index and extent carriers."
        let participants = Set.ofList (site :: requirement.Participants @ [buffer;index;length;zero;lower;upper;predicate])
                           |> Set.union indexCarrier.Participants |> Set.union extentCarrier.Participants
        { Buffer = buffer; Index = index; IndexCarrier = indexCarrier; ExtentCarrier = extentCarrier
          IndexUnsigned = ValueRange.isNonNegative indexCarrier.Range; Length = length; Lower = lower; Upper = upper
          Requirement = { Site = requirement.Site; Condition = requirement.Condition; Diagnostic = requirement.Diagnostic
                          Frontier = requirement.Frontier; Continuation = requirement.Continuation
                          PatternTest = requirement.PatternTest; Participants = requirement.Participants }
          Participants = participants }
    | _ -> raise (MissingContract "An array access requires its own source-elaborated bounds guard and failure continuation.")

let rec private valueSite graph id =
    match (live graph id).Kind with
    | SemanticKind.Sequential items when not items.IsEmpty -> valueSite graph (List.last items)
    | SemanticKind.TypeAnnotation(inner, _) -> valueSite graph inner
    | _ -> id

/// Read the common source meet, validating the selected storage/result slots.
/// The recipe never manufactures an adaptation in place of the numeric owner.
let private adaptation graph consumer operand fromSlot intoSlot =
    let operand = valueSite graph operand
    let rows = graph.Codata.Value.Meets.TryFind consumer |> Option.defaultValue [] |> List.filter (fun meet -> meet.Operand = operand)
    match fromSlot, intoSlot with
    | SettledSlot.Integer(fromBits, _), SettledSlot.Integer(intoBits, _)
    | SettledSlot.Real fromBits, SettledSlot.Real intoBits ->
        if fromBits = intoBits then
            demand rows.IsEmpty "A memory operand has an unexpected adaptation despite identical settled widths."
            None
        else
            match rows with
            | [meet] when meet.Consumer = consumer && meet.From = fromBits && meet.To = intoBits -> Some meet
            | _ -> raise (MissingContract "The exact source meet between the memory element and value carrier is absent or ambiguous.")
    | a, b when a = b ->
        demand rows.IsEmpty "A memory operand has an adaptation incompatible with its identical settled slots."
        None
    | _ -> raise (MissingContract "Memory value and element storage have incompatible settled representations.")

let nearestLambda graph id =
    let rec walk seen current =
        if Set.contains current seen then None else
        match graph.Nodes.TryFind current with
        | Some { Kind = SemanticKind.Lambda _ } -> Some current
        | Some node -> node.Parent |> Option.bind (walk (Set.add current seen))
        | None -> None
    walk Set.empty id

let private usesOf (graph: SemanticGraph) family =
    let liveNodes = graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.toList
    (liveNodes |> List.collect structuralIncidence) @ graph.Edges
    |> List.filter (fun edge ->
        (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) &&
        (graph.Nodes.TryFind edge.Target |> Option.exists _.IsReachable) &&
        (edge.Sources |> List.exists (fun id -> Set.contains id family)))
    |> List.distinctBy (fun edge -> edge.Class,edge.Role,edge.Ordinal,edge.Target,edge.Sources)

let private closedLocalReference graph scope root =
    let nodes = graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.toList
    let rec close seen =
        let next =
            nodes |> List.choose (fun node ->
                match node.Kind, node.Children with
                | SemanticKind.Binding(_,false,_,_), [source] when Set.contains source seen -> Some node.Id
                | SemanticKind.VarRef(_,Some source), _ | SemanticKind.TypeAnnotation(source,_), _
                | SemanticKind.EagerExpr source, _ | SemanticKind.Reborrow source, _ when Set.contains source seen -> Some node.Id
                | SemanticKind.Sequential items, _ when List.tryLast items |> Option.exists (fun source -> Set.contains source seen) -> Some node.Id
                | _ -> None) |> Set.ofList |> Set.union seen
        if next = seen then seen else close next
    let family = close (Set.singleton root)
    let uses = usesOf graph family
    let safe =
        uses |> List.forall (fun edge ->
            let target = live graph edge.Target
            nearestLambda graph target.Id = Some scope &&
            (family.Contains target.Id ||
             match target.Kind with
             | SemanticKind.Deref reference when family.Contains reference -> true
             | SemanticKind.Sequential items -> List.tryLast items |> Option.exists (fun id -> not (family.Contains id))
             | _ -> false))
    safe, Set.union family (uses |> List.map _.Target |> Set.ofList)

/// Close the exact identity-preserving aliases, then classify every live use.
/// A store prevents image sharing; an unknown call, capture, return or address
/// escape prevents this finite local residence proof.
let arrayUses graph site =
    let nodes = graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.toList
    let internalView (node:SemanticNode) =
        match intrinsic graph node.Id [] with
        | Some({Module=IntrinsicModule.String;Operation="fromBytes"},[input]) when
            graph.Edges |> List.exists(fun edge ->
                edge.Role=EdgeRole.StringByteSnapshot &&
                (match edge.Sources with [_;snapshot] -> snapshot=input | _ -> false)) -> Some input
        | Some({Module=IntrinsicModule.String;Operation="toBytes"},[input]) when
            graph.Edges |> List.exists(fun edge ->
                edge.Role=EdgeRole.StringToBytesSnapshot &&
                (match edge.Sources with [_;view;_] -> view=node.Id | _ -> false)) -> Some input
        | _ -> None
    let rec close aliases =
        let more =
            nodes |> List.choose (fun node ->
                let aliasesInput =
                    match node.Kind, node.Children with
                    | SemanticKind.Binding(_, false, _, _), [value] -> Set.contains value aliases
                    | SemanticKind.VarRef(_, Some definition), _ -> Set.contains definition aliases
                    | SemanticKind.TypeAnnotation(value, _), _ | SemanticKind.EagerExpr value, _
                    | SemanticKind.StringByteBorrow value, _ -> Set.contains value aliases
                    | SemanticKind.Sequential items, _ -> List.tryLast items |> Option.exists (fun value -> Set.contains value aliases)
                    | _ -> internalView node |> Option.exists(fun value -> Set.contains value aliases)
                if aliasesInput then Some node.Id else None) |> Set.ofList |> Set.union aliases
        if more = aliases then aliases else close more
    let aliases = close (Set.singleton site)
    let uses = usesOf graph aliases
    let mutable readonly = true
    let mutable closed = true
    let mutable participants = aliases
    for edge in uses do
        let target = live graph edge.Target
        participants <- Set.add target.Id participants
        if not (aliases.Contains target.Id) then
            match target.Kind with
            | SemanticKind.ModuleDef _ when edge.Class = EdgeClass.Reference && edge.Role = EdgeRole.Member -> ()
            | SemanticKind.IndexGet(buffer, _) when aliases.Contains buffer -> ()
            | SemanticKind.IndexSet(buffer, _, _) when aliases.Contains buffer -> readonly <- false
            | SemanticKind.ElementAddress(buffer, _) when aliases.Contains buffer ->
                readonly <- false
                match nearestLambda graph site with
                | Some scope ->
                    let safe, referenceUses = closedLocalReference graph scope target.Id
                    participants <- Set.union participants referenceUses
                    closed <- closed && safe
                | None -> closed <- false
            | SemanticKind.FieldGet(buffer, "Length") when aliases.Contains buffer -> ()
            | SemanticKind.Sequential items when items |> List.tryLast |> Option.exists (fun last -> not (aliases.Contains last)) -> ()
            | SemanticKind.Application _ ->
                match intrinsic graph target.Id [] with
                | Some(info, [buffer]) when (info.Module = IntrinsicModule.Array || info.Module = IntrinsicModule.String) && info.Operation = "length" && aliases.Contains buffer -> ()
                | _ -> readonly <- false; closed <- false
            | _ -> readonly <- false; closed <- false
    readonly && closed, closed, participants

let private literal graph id =
    match (live graph id).Kind with
    | SemanticKind.Literal((NativeLiteral.Int _ | NativeLiteral.UInt _ | NativeLiteral.Bool _ | NativeLiteral.Char _) as value) -> Some value
    | _ -> None

let private proofHolds = function
    | ObligationBody.CapacityFits(capacity, available) -> 0L <= capacity && capacity <= available
    | ObligationBody.ContinuationLayout(slots, extent, alignment) ->
        let rec ordered endOfPrevious = function
            | [] -> endOfPrevious = extent
            | (offset, bytes, aligned) :: rest ->
                aligned > 0 && offset >= endOfPrevious && offset % aligned = 0 && bytes > 0 &&
                alignment >= aligned && alignment % aligned = 0 && ordered (offset + bytes) rest
        extent >= 0 && alignment > 0 && ordered 0 slots
    | _ -> false

/// Final source settlement follows ranges, complete-write element selection,
/// storage and canonical meets. It returns explicit failures for unsupported
/// residence and places rather than asking an emission Pattern to infer them.
let settle (graph: SemanticGraph) (numeric: NumericWitnessProjection)
    : Enrichment * (NodeId * MemoryWitnessOperation) list * Map<NodeId,string> * Set<NodeId> =
    let mutable enrichment = Enrichment.empty
    let mutable operations = []
    let mutable unresolved = Map.empty
    let mutable required = Set.empty
    let excluded = Memory.excluded graph
    let platform = lazy (Platform.resolve graph |> needed "A memory residence requires the selected source platform declaration.")
    let settleNode (node: SemanticNode) =
        let mutable proofs = Enrichment.empty
        let enrichmentId = Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()
        let proof body participants label =
            let proven = proofHolds body
            demand proven ("The source memory " + label + " proof is refuted.")
            let info = { Id = sprintf "memory_%d_%s" (NodeId.value node.Id) label; Kind = "memory-" + label; Logic = "QF_LIA"
                         Statement = "Source memory " + label + " for the exact published residence and element layout."
                         Source = fmtRange node.Range; Refs = []; Body = body }
            let citizen = obligationNode node enrichmentId info |> Memory.markOwned
            let evidence: MemoryProof = { Site = node.Id; Obligation = citizen.Id; Body = body; Participants = participants; Proven = proven }
            proofs <- Enrichment.combine proofs { NewNodes = [citizen]; NewEdges = Memory.proofRows evidence; Annotated = [] }
            citizen.Id
        let operation =
          match node.Kind with
          | SemanticKind.ArrayExpr elements ->
            let slot = element numeric node.Id
            let bytes, alignment = size graph slot
            demand (bytes > 0 && alignment > 0) "Array storage needs positive settled element extent and alignment."
            let initializers = elements |> List.map (literal graph)
            demand (initializers |> List.forall Option.isSome) "Ordinary array elements require source demand and memoization placement; effectful or nonliteral initializers are not admitted as eager stores."
            let values = initializers |> List.map Option.get
            let adapted = elements |> List.map (fun id -> id, adaptation graph node.Id id (carrier numeric (valueSite graph id)).Slot slot)
            let readonly, closed, uses = arrayUses graph node.Id
            let participants = Set.union uses (Set.ofList elements) |> Set.add node.Id
            let extent = bigint elements.Length * bigint bytes
            demand (extent <= bigint System.Int32.MaxValue) "Array storage extent exceeds the admitted finite layout model."
            let residence, space, authority =
                if readonly then
                    let declared = Platform.immutableProgramSpace platform.Value |> needed "A readonly constant array requires an explicitly designated immutable program space."
                    MemoryResidence.ImmutableProgram declared.Node, declared, Platform.immutableProgramAuthority platform.Value
                else
                    demand closed "The array's complete use family escapes or observes address identity; a source residence contract is required."
                    let scope = nearestLambda graph node.Id |> needed "A mutable array has no source lexical activation scope."
                    demand (uses |> Set.forall (fun id ->
                        match (live graph id).Kind with SemanticKind.ModuleDef _ -> true | _ -> nearestLambda graph id = Some scope))
                        "An array alias or access crosses its proposed stack activation."
                    let declared = platform.Value.Spaces |> List.filter (fun space -> space.Kind = "stack" && space.Access.Contains("w"))
                    let stack = match declared with [stack] -> stack | _ -> raise (MissingContract "A local mutable array requires one declared writable stack space.")
                    MemoryResidence.Stack(scope, stack.Node), stack, [platform.Value.Node;stack.Node;scope]
            let participants = Set.union participants (Set.ofList authority)
            demand (space.Alignment >= alignment && space.Alignment % alignment = 0) "The declared memory space does not satisfy the array element alignment."
            let slots = elements |> List.mapi (fun ordinal _ -> ordinal * bytes, bytes, alignment)
            let layoutProof = proof (ObligationBody.ContinuationLayout(slots, int extent, alignment)) participants "array_layout"
            let capacityProof = proof (ObligationBody.CapacityFits(int64 extent, space.Capacity)) participants "array_capacity"
            MemoryWitnessOperation.ArrayLiteral
                { Site = node.Id; Elements = adapted; Element = slot; Length = elements.Length; Residence = residence
                  Initializers = Some values; Alignment = alignment; ElementBytes = bytes
                  Participants = participants |> Set.add layoutProof |> Set.add capacityProof }
          | SemanticKind.IndexGet(buffer,index) | SemanticKind.IndexSet(buffer,index,_) ->
            let stored = match node.Kind with SemanticKind.IndexSet(_,_,value) -> Some value | _ -> None
            let bounds = bounds graph numeric node.Id buffer index
            let slot = element numeric buffer
            let adapted = match stored with
                          | Some value -> adaptation graph node.Id value (carrier numeric (valueSite graph value)).Slot slot
                          | None -> adaptation graph node.Id node.Id slot (carrier numeric node.Id).Slot
            MemoryWitnessOperation.ArrayAccess
                { Site = node.Id; Buffer = buffer; Index = index; Value = stored; Element = slot; Adaptation = adapted
                  Bounds = bounds; Participants = Set.union bounds.Participants (Set.ofList (Option.toList stored)) }
          | SemanticKind.ElementAddress(buffer,index) ->
            let bounds = bounds graph numeric node.Id buffer index
            let slot = element numeric buffer
            let bytes, _ = size graph slot
            MemoryWitnessOperation.Address
                { Site = node.Id; Place = MemoryPlace.ArrayElement(buffer,index,bounds); Element = Some slot; ElementBytes = Some bytes
                  PointerBits = pointerBits graph; Participants = bounds.Participants }
          | SemanticKind.CellAddress binding ->
            let cell = live graph binding
            demand (match cell.Kind with SemanticKind.Binding(_,true,_,_) -> true | _ -> false) "AddressOf requires the actual mutable binding cell."
            let scalar = carrier numeric binding
            let bytes, _ = size graph scalar.Slot
            MemoryWitnessOperation.Address
                { Site = node.Id; Place = MemoryPlace.MutableCell binding; Element = Some scalar.Slot; ElementBytes = Some bytes
                  PointerBits = pointerBits graph; Participants = scalar.Participants |> Set.add node.Id |> Set.add binding }
          | SemanticKind.Reborrow source ->
            let input = live graph source
            demand (match applySubst input.Type, applySubst node.Type with NativeType.TByref _, NativeType.TByref _ -> applySubst input.Type = applySubst node.Type | _ -> false)
                   "Reborrowing must preserve the existing typed reference exactly."
            MemoryWitnessOperation.Address
                { Site = node.Id; Place = MemoryPlace.ExistingReference source; Element = None; ElementBytes = None
                  PointerBits = pointerBits graph; Participants = Set.ofList [node.Id;source] }
          | SemanticKind.FieldAddress(receiver, name) ->
            let input = live graph receiver
            let declaration =
                match applySubst input.Type with
                | NativeType.TApp(tc, _) ->
                    Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances.tryDefinition (NominalTypeIdentity.ofConstructor tc) graph
                    |> needed "The addressed record has no exact source type declaration."
                | _ -> raise (MissingContract "A field address requires a concrete nominal record receiver.")
            demand (match declaration.Metadata.TryFind "TypeDef.MutableFields" with
                    | Some(MetadataValue.StringList fields) -> List.contains name fields | _ -> false)
                   "The source record declaration does not mark this exact field mutable."
            let fields, total, alignment =
                match numeric.Layouts.TryFind (TypeIdentity.ofType input.Type) with
                | Some(SettledLayout.Record(fields, Some total, Some alignment)) -> fields,total,alignment
                | _ -> raise (MissingContract "The addressed record lacks its complete settled byte storage layout.")
            let field = fields |> List.tryFind (fun field -> field.Name = name) |> needed "The addressed field is absent from the exact source record layout."
            let bytes, fieldAlignment = size graph field.Slot
            demand (total > 0 && alignment > 0 && field.Size = Some bytes && field.Align = Some fieldAlignment &&
                    field.Offset |> Option.exists (fun offset -> offset >= 0 && offset % fieldAlignment = 0 && offset + bytes <= total))
                   "The addressed field's exact offset, extent and alignment are not contained in its receiver storage."
            MemoryWitnessOperation.Address
                { Site = node.Id; Place = MemoryPlace.RecordField(receiver,total,field); Element = Some field.Slot; ElementBytes = Some bytes
                  PointerBits = pointerBits graph; Participants = Set.ofList [node.Id;receiver;declaration.Id] }
          | SemanticKind.AddressOf _ -> raise (MissingContract "AddressOf has no admitted actual mutable place; defensive copies cannot supply that place.")
          | SemanticKind.FieldGet(_, "Pointer") ->
            raise (MissingContract "The current source member contract does not admit .Pointer; an actual mutable place uses the documented AddressOf operation.")
          | _ ->
            match pendingArrayConstruction graph node with
            | Some operation ->
                let reason=match node.Metadata.TryFind "Baker.ArrayConstructionError" with
                           | Some(MetadataValue.String reason) -> reason
                           | _ -> "Array." + operation + " requires source-owned construction, range guards, demand and storage residence; no such operation is settled."
                raise (MissingContract reason)
            | None -> ()
            let buffer = arrayLength graph node |> needed "The memory operation has no source settlement recipe."
            let result = carrier numeric node.Id
            MemoryWitnessOperation.ArrayExtent
                { Site = node.Id; Source = buffer; Element = element numeric buffer; Result = result
                  Participants = result.Participants |> Set.add node.Id |> Set.add buffer }
        enrichment <- Enrichment.combine enrichment proofs
        operation
    for node in graph.Nodes.Values do
        if node.IsReachable && not (excluded.Contains node.Id) then
            let needs =
                match node.Kind with
                | SemanticKind.ArrayExpr _ | SemanticKind.AddressOf _ | SemanticKind.CellAddress _
                | SemanticKind.ElementAddress _ | SemanticKind.FieldAddress _ | SemanticKind.Reborrow _ -> true
                | SemanticKind.IndexGet(buffer,_) | SemanticKind.IndexSet(buffer,_,_) -> isArray graph buffer
                | SemanticKind.FieldGet(buffer,"Pointer") -> isArray graph buffer
                | _ -> (arrayLength graph node).IsSome || (pendingArrayConstruction graph node).IsSome
            if needs then
                required <- Set.add node.Id required
                try operations <- (node.Id, settleNode node) :: operations
                with MissingContract reason -> unresolved <- Map.add node.Id reason unresolved
    enrichment, List.rev operations, unresolved, required

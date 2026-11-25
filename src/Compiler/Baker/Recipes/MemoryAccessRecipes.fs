// SPDX-License-Identifier: MIT
// Source-owned array access and actual mutable-place elaboration. Bounds are
// ordinary guarded source computations before numeric and demand settlement.
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

type private ResultBuilder() =
    member _.Bind(value, next) = Result.bind next value
    member _.Return(value) = Ok value
    member _.ReturnFrom(value: Result<'T, 'E>) = value
    member _.Zero() = Ok ()
    member _.Delay(f: unit -> Result<'T, 'E>) = f
    member _.Run(f: unit -> Result<'T, 'E>) = f ()
    member _.Combine(first: Result<unit, 'E>, second: unit -> Result<'T, 'E>) =
        match first with
        | Ok () -> second ()
        | Result.Error err -> Result.Error err
    member _.For(items: seq<'T>, body: 'T -> Result<unit, 'E>) =
        use enumerator = items.GetEnumerator()
        let rec loop () =
            if not (enumerator.MoveNext()) then Ok ()
            else
                match body enumerator.Current with
                | Ok () -> loop ()
                | Result.Error err -> Result.Error err
        loop ()

let private result = ResultBuilder()

let private mapResult (fn: 'T -> Result<'U, 'E>) (items: 'T list) : Result<'U list, 'E> =
    let rec loop acc remaining =
        match remaining with
        | [] -> Ok (List.rev acc)
        | head :: tail ->
            match fn head with
            | Ok value -> loop (value :: acc) tail
            | Result.Error err -> Result.Error err
    loop [] items

type Expansion = { Structure: Result; Edges: Hyperedge list }

let rec private sourceIntrinsic (graph: SemanticGraph) id arguments =
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.Intrinsic info } -> Some(info, arguments)
    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> sourceIntrinsic graph inner arguments
    | Some { Kind = SemanticKind.Application(callee, actuals) } -> sourceIntrinsic graph callee (actuals @ arguments)
    | _ -> None

/// An array of async computations is an orchestration operand, never
/// element storage; every other array keeps its ordinary bounds and residence.
let private isArray (graph: SemanticGraph) id =
    match graph.Nodes.TryFind id |> Option.map (fun node -> applySubst node.Type) with
    | Some(NativeType.TApp(tc, [elemTy])) when tc.NTUKind = Some NTUKind.NTUarray ->
        match applySubst elemTy with
        | NativeType.TApp(etc, _) -> not (Types.isAsyncTypeCon etc)
        | _ -> true
    | _ -> false

let private isReadOnlyView (graph: SemanticGraph) id =
    match graph.Nodes.TryFind id |> Option.map (fun node -> applySubst node.Type) with
    | Some(NativeType.TApp(tc, [_])) -> Types.isReadOnlyViewTypeCon tc
    | _ -> false

let private isReadableBuffer (graph: SemanticGraph) id =
    isArray graph id || isReadOnlyView graph id

[<RequireQualifiedAccess>]
type private ReadOnlyViewConversion =
    | OfArray of source: NodeId
    | OfString of source: NodeId
    | Slice of source: NodeId * offset: NodeId * count: NodeId

let private readOnlyViewConversion (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Application _ ->
        match sourceIntrinsic graph node.Id [] with
        | Some((info: IntrinsicInfo), [source]) when info.Module = IntrinsicModule.Array && info.FullName = "ReadOnlyView.ofArray" ->
            Some(ReadOnlyViewConversion.OfArray source)
        | Some((info: IntrinsicInfo), [source]) when info.Module = IntrinsicModule.Array && info.FullName = "ReadOnlyView.ofString" ->
            Some(ReadOnlyViewConversion.OfString source)
        | Some((info: IntrinsicInfo), [source; offset; count]) when info.Module = IntrinsicModule.Array && info.FullName = "ReadOnlyView.slice" ->
            Some(ReadOnlyViewConversion.Slice(source, offset, count))
        | _ -> None
    | _ -> None

let private access (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.IndexGet(buffer, index) when isReadableBuffer graph buffer -> Some(buffer, index, None)
    | SemanticKind.IndexSet(buffer, index, value) when isArray graph buffer -> Some(buffer, index, Some value)
    | SemanticKind.ElementAddress(buffer, index) when isArray graph buffer -> Some(buffer, index, None)
    | SemanticKind.AddressOf(expression, _) ->
        match graph.Nodes.TryFind expression with
        | Some { Kind = SemanticKind.IndexGet(buffer, index) } when isArray graph buffer -> Some(buffer, index, None)
        | _ -> None
    | SemanticKind.Application _ ->
        match sourceIntrinsic graph node.Id [] with
        | Some(info, [buffer; index])
            when info.Module = IntrinsicModule.Array && info.Operation = "get" && isReadableBuffer graph buffer -> Some(buffer, index, None)
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

// Derive the byte-read range and its storage sources from the access guard.
let byteRange (graph: SemanticGraph) (guard: Hyperedge) : Hyperedge option =
    match guard.Role, guard.Sources with
    | EdgeRole.MemoryAccessGuard, [buffer; index; length; _; lower; upper; predicate; required; source] ->
        let range lo hi sources =
            { Class = EdgeClass.Range; Role = EdgeRole.StringByteRange(lo, hi)
              Ordinal = 0; Sources = sources; Target = guard.Target }
        match graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringByteView view when view.Site = buffer -> Some view | _ -> None) with
        | [view] ->
            Some (range 0I 255I [buffer; view.Source; view.RepresentationDeclaration; index; length; lower; upper; predicate; required; source])
        | _ ->
            Clef.Compiler.PSGSaturation.SemanticGraph.StringByteStorage.evidence graph buffer
            |> Option.map (fun (_, lo, hi, participants) ->
                range lo hi ([buffer; index; length; lower; upper; predicate; required; source] @ Set.toList participants))
    | _ -> None

let private materializeCore (ctx: Context) (graph: SemanticGraph) (source: SemanticNode) : Result<Expansion, string> =
    let state = SaturationState.create source.Range ctx.OriginalHOF ctx.ExpansionId source.Id graph.Platform
    let evidence = ResizeArray<Hyperedge>()
    let recipe =
      match address graph source with
      | Some(kind, children) -> saturation {
            do! enrich source kind source.Type children source.EmissionStrategy false
            return source.Id
        }
      | None ->
        match access graph source with
        | None -> fail (XParsec.ErrorType.Message "No source array access at memory recipe site")
        | Some(buffer, index, stored) -> saturation {
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
                    // The guarded operation has only transient claims; the
                    // original source access retains the ordered operand evaluation.
                    Metadata = source.Metadata.Remove("Source.ObligationSite").Remove("Source.DeclarationIncarnation").Add("Baker.MemoryGuarded", MetadataValue.Bool true)
                    Parent = Some source.Id; ArenaAffinity = source.ArenaAffinity }
            do! emit operation
            let ordered = children @ [required; operation.Id]
            do! enrich source (SemanticKind.Sequential ordered) source.Type ordered source.EmissionStrategy false
            evidence.Add { Class = EdgeClass.Provenance; Role = EdgeRole.MatchRequirement; Ordinal = 1
                           Sources = [required; predicate; operation.Id]; Target = source.Id }
            let guard =
                { Class = EdgeClass.Provenance; Role = EdgeRole.MemoryAccessGuard; Ordinal = 0
                  Sources = [buffer; index; length; zero; lower; upper; predicate; required; source.Id]; Target = operation.Id }
            evidence.Add guard
            if stored.IsNone then
                byteRange graph guard |> Option.iter evidence.Add
            return source.Id
          }
    let outcome, nodes = run state recipe
    match outcome with
    | NoMatch reason -> Result.Error ("Array bounds source elaboration failed: " + reason)
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
        Ok { Structure = mkResultNoShadow nodes root []
             Edges = (graph.Edges |> List.filter (fun edge -> not (replaced.Contains(key edge))))
                     @ (nodes |> List.collect structuralIncidence) @ List.ofSeq evidence }

let materialize ctx graph source =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> materializeCore ctx graph source)

let private needed reason = function Some value -> Ok value | None -> Result.Error reason
let private demand condition reason = if condition then Ok () else Result.Error reason
let private live (graph: SemanticGraph) id =
    graph.Nodes.TryFind id |> Option.filter _.IsReachable |> needed "A memory premise is not a live source occurrence."

let private intrinsic = sourceIntrinsic

let private arrayLength (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.FieldGet(buffer, "Length") when isReadableBuffer graph buffer -> Some buffer
    | SemanticKind.Application _ ->
        match intrinsic graph node.Id [] with
        | Some(info, [buffer]) when info.Module = IntrinsicModule.Array && info.Operation = "length" && isReadableBuffer graph buffer -> Some buffer
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

let private viewElementSlot (graph: SemanticGraph) (numeric: NumericWitnessProjection) (node: SemanticNode) =
    match numeric.OccurrenceRepresentations.TryFind node.Id with
    | Some(Result.Error reason) -> Result.Error reason
    | _ ->
    match numeric.Elements.TryFind node.Id with
    | Some slot -> Ok slot
    | None ->
        match applySubst node.Type with
        | NativeType.TApp(tc, [element]) when Types.isReadOnlyViewTypeCon tc || tc.NTUKind = Some NTUKind.NTUarray ->
            match numeric.Layouts.TryFind (TypeIdentity.ofType element) with
            | Some(SettledLayout.Record(_, Some bytes, Some align))
            | Some(SettledLayout.Union(_, _, Some bytes, Some align)) when bytes > 0 && align > 0 ->
                Ok (SettledSlot.InlineBytes(bytes, align))
            | _ ->
                match Types.tryGetNTUKind element with
                | Some(NTUKind.NTUfloat(NTUWidth.Fixed bits)) when bits > 0 -> Ok (SettledSlot.Real bits)
                | Some(NTUKind.NTUfloat(NTUWidth.Resolved dimension)) ->
                    Platform.resolve graph
                    |> Option.bind _.Core
                    |> Option.bind (fun core ->
                        match core.Widths |> List.filter (fun w -> w.Name = WidthDimension.name dimension) with
                        | [w] when w.Bits > 0 -> Some w.Bits
                        | _ -> None)
                    |> needed "ReadOnlyView real element lacks a unique declared platform width."
                    |> Result.map SettledSlot.Real
                | _ -> Result.Error "ReadOnlyView lacks a settled element slot."
        | _ -> Result.Error "The source numeric owner did not settle the complete-write element slot."

let private size (graph: SemanticGraph) slot =
    Placement.extentOfSlot graph slot |> needed "The declared target has no admitted physical extent for this element slot."

let private pointerBits (graph: SemanticGraph) =
    result {
        let! context = graph.Platform |> needed "An address requires a declared target Pointer dimension."
        match PlatformContext.pointerSize context with
        | Ok bytes when bytes > 0 -> return bytes * 8
        | _ -> return! Result.Error "An address requires a positive declared target Pointer dimension."
    }

let private callIs graph operation arguments id =
    match intrinsic graph id [] with
    | Some(info, actuals) -> info.Module = IntrinsicModule.Operators && info.Operation = operation && actuals = arguments
    | _ -> false

// A guard fact cites actual executable source expressions. Changing a term,
// bypassing Require, or reusing another access's requirement invalidates it.
let private bounds (graph: SemanticGraph) (numeric: NumericWitnessProjection) site buffer index =
    let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard && edge.Target = site)
    match rows with
    | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [actualBuffer; actualIndex; length; zero; lower; upper; predicate; required; frontier] }]
        when actualBuffer = buffer && actualIndex = index ->
        result {
            let! lengthNode = live graph length
            do! demand (arrayLength graph lengthNode = Some buffer) "The bounds guard does not read this exact buffer's extent."
            let! zeroNode = live graph zero
            do! demand (match zeroNode.Kind with SemanticKind.Literal(NativeLiteral.Int(0L, _)) -> true | _ -> false)
                   "The bounds guard has no exact zero lower endpoint."
            do! demand (callIs graph "op_GreaterThanOrEqual" [index;zero] lower && callIs graph "op_LessThan" [index;length] upper)
                   "The bounds guard does not establish 0 <= index < this buffer's extent."
            let! predNode = live graph predicate
            let! isConjunction =
                match predNode.Kind with
                | SemanticKind.IfThenElse(condition, yes, Some no) when condition = lower && yes = upper ->
                    result {
                        let! noNode = live graph no
                        match noNode.Kind with
                        | SemanticKind.Literal(NativeLiteral.Bool false) -> return true
                        | _ -> return false
                    }
                | _ -> Ok false
            do! demand isConjunction "The bounds conjunction is absent or changed."
            let! requirement = Requirements.tryRequirement graph required |> needed "The bounds guard has no admitted always-active source failure frontier."
            do! demand (requirement.Condition = predicate && requirement.Frontier = frontier && requirement.Continuation = site)
                   "The bounds requirement does not guard this exact access continuation."
            let! indexCarrier = carrier numeric index
            let! extentCarrier = carrier numeric length
            do! demand (match indexCarrier.Slot, extentCarrier.Slot with SettledSlot.Integer _, SettledSlot.Integer _ -> true | _ -> false)
                   "Array bounds require settled integer index and extent carriers."
            let participants = Set.ofList (site :: requirement.Participants @ [buffer;index;length;zero;lower;upper;predicate])
                               |> Set.union indexCarrier.Participants |> Set.union extentCarrier.Participants
            return { Buffer = buffer; Index = index; IndexCarrier = indexCarrier; ExtentCarrier = extentCarrier
                     IndexUnsigned = ValueRange.isNonNegative indexCarrier.Range; Length = length; Lower = lower; Upper = upper
                     Requirement = { Site = requirement.Site; Condition = requirement.Condition; Diagnostic = requirement.Diagnostic
                                     Frontier = requirement.Frontier; Continuation = requirement.Continuation
                                     PatternTest = requirement.PatternTest; Participants = requirement.Participants }
                     Participants = participants }
        }
    | _ -> Result.Error "An array access requires its own source-elaborated bounds guard and failure continuation."

let rec private valueSite graph id =
    result {
        let! node = live graph id
        match node.Kind with
        | SemanticKind.Sequential items when not items.IsEmpty -> return! valueSite graph (List.last items)
        | SemanticKind.TypeAnnotation(inner, _) -> return! valueSite graph inner
        | _ -> return id
    }

let rec private tryValueSite (graph: SemanticGraph) id =
    match graph.Nodes.TryFind id |> Option.filter _.IsReachable with
    | Some { Kind = SemanticKind.Sequential items } when not items.IsEmpty -> tryValueSite graph (List.last items)
    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> tryValueSite graph inner
    | Some _ -> Some id
    | None -> None

// Read the common source meet, validating the selected storage/result slots.
// The recipe never manufactures an adaptation in place of the numeric owner.
let private adaptation graph consumer operand fromSlot intoSlot =
    result {
        let! operand = valueSite graph operand
        let rows = graph.Codata.Value.Meets.TryFind consumer |> Option.defaultValue [] |> List.filter (fun meet -> meet.Operand = operand)
        match fromSlot, intoSlot with
        | SettledSlot.Integer(fromBits, _), SettledSlot.Integer(intoBits, _)
        | SettledSlot.Real fromBits, SettledSlot.Real intoBits ->
            if fromBits = intoBits then
                do! demand rows.IsEmpty "A memory operand has an unexpected adaptation despite identical settled widths."
                return None
            else
                match rows with
                | [meet] when meet.Consumer = consumer && meet.From = fromBits && meet.To = intoBits -> return Some meet
                | _ -> return! Result.Error "The exact source meet between the memory element and value carrier is absent or ambiguous."
        | a, b when a = b ->
            do! demand rows.IsEmpty "A memory operand has an adaptation incompatible with its identical settled slots."
            return None
        | _ -> return! Result.Error "Memory value and element storage have incompatible settled representations."
    }

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

let private closedLocalReference (graph: SemanticGraph) scope root =
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
            match graph.Nodes.TryFind edge.Target |> Option.filter _.IsReachable with
            | None -> false
            | Some target ->
                nearestLambda graph target.Id = Some scope &&
                (family.Contains target.Id ||
                 match target.Kind with
                 | SemanticKind.Deref reference when family.Contains reference -> true
                 | SemanticKind.Sequential items -> List.tryLast items |> Option.exists (fun id -> not (family.Contains id))
                 | _ -> false))
    safe, Set.union family (uses |> List.map _.Target |> Set.ofList)

// Close the exact identity-preserving aliases, then classify every live use.
// A store prevents image sharing; an unknown call, capture, return or address
// escape prevents this finite local residence proof.
let arrayUses (graph: SemanticGraph) site =
    let liveOpt id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
    let nodes = graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.toList
    let checkedStrings = graph.Edges |> List.choose(fun edge ->
        match edge.Role with
        | EdgeRole.StringCheckedConstruction construction when edge.Target=construction.Owner -> Some construction
        | _ -> None)
    let checkedOption id =
        match liveOpt id |> Option.map (fun n -> applySubst n.Type) with
        | Some(NativeType.TApp(constructor,[element])) -> constructor=Types.voptionTyCon && element=Types.stringType
        | _ -> false
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
        | Some(info, input :: _) when info.Module = IntrinsicModule.Array && (info.FullName = "ReadOnlyView.ofArray" || info.FullName = "ReadOnlyView.slice") -> Some input
        | _ -> None
    let isBoundaryBinding id =
        graph.Edges |> List.exists (fun e ->
            match e.Role with
            | EdgeRole.BoundaryDeclaration d -> d.Binding = id
            | _ -> false)
    let lambdaParams callee =
        let rec resolve seen id =
            if Set.contains id seen then None else
            match liveOpt id with
            | None -> None
            | Some node ->
                match node.Kind, node.Children with
                | SemanticKind.VarRef(_, Some defId), _ -> resolve (Set.add id seen) defId
                | SemanticKind.Binding(_, false, _, _), [bodyId] when not (isBoundaryBinding id) ->
                    resolve (Set.add id seen) bodyId
                | SemanticKind.Lambda(parameters, _, _, _, _), _ -> Some parameters
                | _ -> None
        resolve Set.empty callee
    // A descriptor stored in an async continuation frame slot stays in the
    // deferred callable's activation; a validated read of that slot is the
    // same descriptor. The reading is built only when a frame access is met.
    let ingress = lazy (Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze graph)
    let rec close aliases =
        let more =
            nodes |> List.choose (fun node ->
                let aliasesInput =
                    match node.Kind, node.Children with
                    | SemanticKind.Binding(_, false, _, _), [value] -> Set.contains value aliases
                    | SemanticKind.FrameRead _, _ ->
                        Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryActivationFrameRead ingress.Value node.Id
                        |> Option.exists (fun access -> access.Inputs |> List.exists (fun (_, value) -> Set.contains value aliases))
                    | SemanticKind.VarRef(_, Some definition), _ -> Set.contains definition aliases
                    | SemanticKind.TypeAnnotation(value, _), _ | SemanticKind.EagerExpr value, _
                    | SemanticKind.StringByteBorrow value, _ -> Set.contains value aliases
                    | SemanticKind.Sequential items, _ -> List.tryLast items |> Option.exists (fun value -> Set.contains value aliases)
                    // A checked native value contains this backing; it is not
                    // a second allocation or permission to escape the scope.
                    | SemanticKind.DUConstruct("ValueSome",1,Some text,None), _ ->
                        aliases.Contains text && checkedStrings |> List.exists(fun construction -> construction.Success=node.Id && construction.Text=text)
                    | SemanticKind.IfThenElse(guard,success,Some failure), _ ->
                        let contained id =
                            aliases.Contains id ||
                            (match liveOpt id with
                             | Some { Kind = SemanticKind.Sequential items } -> List.tryLast items |> Option.exists aliases.Contains
                             | _ -> false)
                        (contained success || contained failure) &&
                        ((Types.tryGetReadOnlyViewElement node.Type |> Option.isSome) ||
                         checkedStrings |> List.exists(fun construction -> construction.Decision=node.Id && construction.Validation=guard && construction.Success=success))
                    | SemanticKind.DUEliminate(value,1,"ValueSome",_), _ -> aliases.Contains value
                    | SemanticKind.CaseElimination(value,arms), _ when aliases.Contains value && checkedOption value ->
                        arms |> List.exists(fun arm -> aliases.Contains arm.Body)
                    | SemanticKind.PatternBinding _, _ when (Types.tryGetReadOnlyViewElement node.Type |> Option.isSome) || isArray graph node.Id ->
                        nodes |> List.exists (fun callNode ->
                            match callNode.Kind with
                            | SemanticKind.Application(callee, actuals) ->
                                match lambdaParams callee with
                                | Some parameters when parameters.Length = actuals.Length ->
                                    List.zip actuals parameters
                                    |> List.exists (fun (actual, (_, _, paramId)) -> paramId = node.Id && Set.contains actual aliases)
                                | _ -> false
                            | _ -> false)
                    | _ -> internalView node |> Option.exists(fun value -> Set.contains value aliases)
                if aliasesInput then Some node.Id else None) |> Set.ofList |> Set.union aliases
        if more = aliases then aliases else close more
    let aliases = close (Set.singleton site)
    let uses = usesOf graph aliases
    let mutable readonly = true
    let mutable closed = true
    let mutable participants = aliases
    for edge in uses do
        match liveOpt edge.Target with
        | None ->
            readonly <- false
            closed <- false
        | Some target ->
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
                | SemanticKind.FrameWrite(_, _, value)
                    when aliases.Contains value &&
                         (Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryActivationFrameStore ingress.Value target.Id).IsSome -> ()
                | SemanticKind.DUGetTag(value,_) when aliases.Contains value -> ()
                | SemanticKind.CaseElimination(value,arms) when aliases.Contains value && checkedOption value &&
                                                              arms |> List.forall(fun arm -> arm.Guard.IsNone) -> ()
                | SemanticKind.Sequential items when items |> List.tryLast |> Option.exists (fun last -> not (aliases.Contains last)) -> ()
                | SemanticKind.Lambda(parameters, body, _, _, _) when not (aliases.Contains body) && parameters |> List.exists (fun (_, _, pid) -> aliases.Contains pid) -> ()
                | SemanticKind.Application(callee,actuals) ->
                    match intrinsic graph target.Id [] with
                    | Some(info, [buffer]) when (info.Module = IntrinsicModule.Array || info.Module = IntrinsicModule.String) && info.Operation = "length" && aliases.Contains buffer -> ()
                    | Some({Module=IntrinsicModule.String;Operation=("validateUtf8" | "retireSnapshot")},[buffer])
                        when aliases.Contains buffer && checkedStrings |> List.exists(fun construction ->
                            construction.Snapshot=buffer && (construction.Validation=target.Id || construction.Retirement=target.Id)) -> ()
                    | Some({Module=IntrinsicModule.Sys;Operation="write"},[_;buffer;_])
                        when aliases.Contains buffer &&
                             (match liveOpt buffer with Some { Kind = SemanticKind.StringByteBorrow _ } -> true | _ -> false) &&
                             nearestLambda graph target.Id = nearestLambda graph site &&
                             (nearestLambda graph site).IsSome -> ()
                    | _ ->
                        let hypotheses=Platform.writableReferenceArguments graph callee actuals
                        match hypotheses with
                        | [buffer, _, bufferOrd] when aliases.Contains buffer &&
                            (actuals |> List.mapi(fun ordinal actual->ordinal=bufferOrd || not(aliases.Contains actual)) |> List.forall id) ->
                            readonly <- false
                            let scope=nearestLambda graph site
                            closed <- closed && scope.IsSome && nearestLambda graph target.Id=scope
                        | _ ->
                            match Platform.readOnlyBufferArguments graph callee actuals with
                            | [buffer, _, sourceOrdinal] when aliases.Contains buffer &&
                                actuals |> List.mapi(fun ordinal actual -> ordinal = sourceOrdinal || not(aliases.Contains actual)) |> List.forall id ->
                                let scope = nearestLambda graph site
                                closed <- closed && scope.IsSome && nearestLambda graph target.Id = scope
                            | _ ->
                                let passesToReadOnlyViewParam =
                                    match lambdaParams callee with
                                    | Some parameters when parameters.Length = actuals.Length ->
                                        List.zip actuals parameters
                                        |> List.forall (fun (actual, (_, _, paramId)) ->
                                            not (aliases.Contains actual) || aliases.Contains paramId)
                                    | _ -> false
                                if not passesToReadOnlyViewParam then
                                    readonly <- false
                                    closed <- false
                | _ -> readonly <- false; closed <- false
    readonly && closed, closed, participants

let private literal graph id =
    result {
        let! node = live graph id
        match node.Kind with
        | SemanticKind.Literal((NativeLiteral.Int _ | NativeLiteral.UInt _ | NativeLiteral.Bool _ | NativeLiteral.Char _) as value) -> return Some value
        | _ -> return None
    }

let private proofHolds = function
    | ObligationBody.CapacityFits(capacity, available) -> 0L <= capacity && capacity <= available
    | ObligationBody.ContinuationLayout(slots, extent, alignment) ->
        let rec ordered endOfPrevious = function
            | [] -> endOfPrevious = extent
            | (offset, bytes, aligned) :: rest ->
                aligned > 0 && offset >= endOfPrevious && offset % aligned = 0 && bytes > 0 &&
                alignment >= aligned && alignment % aligned = 0 && ordered (offset + bytes) rest
        extent >= 0 && alignment > 0 && ordered 0 slots
    | ObligationBody.IntegerRepresentationCoverage(lower, upper, minimum, maximum) ->
        minimum <= lower && lower <= upper && upper <= maximum
    | _ -> false

// Final source settlement follows ranges, complete-write element selection,
// storage and canonical meets. It returns explicit failures for unsupported
// residence and places rather than asking an emission Pattern to infer them.
let private settleCore (graph: SemanticGraph) (numeric: NumericWitnessProjection)
    : Enrichment * (NodeId * MemoryWitnessOperation) list * Map<NodeId,string> * Set<NodeId> =
    let mutable enrichment = Enrichment.empty
    let mutable operations = []
    let mutable unresolved = Map.empty
    let mutable required = Set.empty
    let excluded = Memory.excluded graph
    let platformResolved = lazy (Platform.resolve graph |> needed "A memory residence requires the selected source platform declaration.")
    let getPlatform () = platformResolved.Value
    let regionMemoryContracts = lazy (Platform.readRegionMemory graph)
    let boundaryImports = lazy (
        graph.Edges
        |> List.choose (function { Role = EdgeRole.BoundaryImport imported } -> Some imported | _ -> None)
        |> List.distinctBy _.Identity)
    let regionOperation (node: SemanticNode) =
        match sourceIntrinsic graph node.Id [] with
        | Some(info, arguments) when info.FullName.StartsWith("Region.", System.StringComparison.Ordinal) ->
            Some(info.FullName, arguments)
        | _ -> None
    let regionAt site =
        graph.Codata.Value.RegionAllocations.Values
        |> Seq.filter (fun row -> row.Region=site || List.contains site row.AllocatedValues
                                 || row.ScopeExitReleases |> List.exists (fun (_,release) -> release=site))
        |> Seq.toList
        |> function [row] -> Ok row | _ -> Result.Error "Region memory requires one settled owning region."
    let exactCount id = result {
        let! count = carrier numeric id
        match count.Range with
        | ValueRange.Bounded(lo,hi) when lo=hi && lo>0I && hi<=bigint System.Int32.MaxValue -> return int lo
        | _ -> return! Result.Error "Region storage requires a positive exact source allocation count."
    }
    let regionRuntime (owner:RegionAllocation) = result {
        let! contracts=regionMemoryContracts.Value
        let! declared=getPlatform ()
        let! space=declared.Spaces |> List.tryFind(fun space -> space.Node=owner.SpacePlacement)
                   |> needed "The region storage space was withdrawn."
        match contracts |> List.filter(fun contract -> contract.Descriptor.Space=space.Name) with
        | [] -> return None
        | [contract] ->
            let imports=boundaryImports.Value
            let imported name =
                imports |> List.filter(fun imported -> graph.Nodes.TryFind imported.Binding |> Option.bind (Platform.qualifiedExportName graph)=Some name)
                |> function [imported] -> Ok imported | _ -> Result.Error("Region memory lacks its exact generated import: " + name)
            let! acquire=imported contract.Descriptor.Acquire
            let! release=imported contract.Descriptor.Release
            let role group kind ordinal occurrence : Participant =
                { Node = occurrence; Role = kind; Ordinal = ordinal; Group = group }
            let ordered group kind (members: Set<NodeId>) =
                members |> Set.toList |> List.sort |> List.mapi (role group kind)
            let sourceImportSupport (imported: BoundaryImport) =
                let source =
                    Set.add imported.Scope
                        (Set.union (Set.ofSeq imported.SourceTypes.Keys) (Set.ofSeq imported.DeclarationFacts.Keys))
                Set.intersect imported.Participants source
            let participants =
                ordered contract.Node ParticipantRole.RegionRuntimeDescriptor contract.Participants
                @ ordered acquire.Identity ParticipantRole.RegionRuntimeAcquire (sourceImportSupport acquire)
                @ ordered release.Identity ParticipantRole.RegionRuntimeRelease (sourceImportSupport release)
            let runtime : MemoryRegionRuntime =
                { Declaration=contract.Node; Acquire=acquire.Identity; Release=release.Identity
                  Contract=contract.Descriptor; Participants=participants }
            return Some (contract.Binding, runtime)
        | _ -> return! Result.Error "Region memory has ambiguous runtime declarations."
    }
    let reservedBytes site = result {
        let! value = live graph site
        let! count =
            match regionOperation value with
            | Some("Region.alloc",[_;count]) | Some("Region.copyTo",[_;_;count]) -> exactCount count
            | _ -> Result.Error "Region reservation is not an allocation or copyTo occurrence."
        let! slot = viewElementSlot graph numeric value
        let! bytes,alignment = size graph slot
        return int64 count * int64 bytes,alignment
    }
    let regionOffset (row: RegionAllocation) site = result {
        let allocations =
            row.AllocatedValues |> List.filter (fun id ->
                match graph.Nodes.TryFind id |> Option.bind regionOperation with
                | Some("Region.alloc",_) | Some("Region.copyTo",_) -> true
                | _ -> false) |> List.distinct |> List.sort
        let! reservations = allocations |> mapResult (fun id -> reservedBytes id |> Result.map (fun (bytes,align) -> id,bytes,align))
        let placed,_ = reservations |> List.mapFold (fun offset (id,bytes,alignment) ->
            let align = int64 alignment
            let start = ((offset+align-1L)/align)*align
            (id,start),start+bytes) 0L
        return! placed |> List.tryPick (fun (id,offset) -> if id=site then Some offset else None)
                |> needed "Region allocation has no source-owned reservation."
    }
    let checkedCase site =
        graph.Edges |> List.choose(fun edge ->
            match edge.Role with
            | EdgeRole.StringCheckedConstruction row when edge.Target=row.Owner && (row.Success=site || row.Failure=site) -> Some row
            | _ -> None) |> function [row] -> Some row | _ -> None
    let emitProof (siteNode: SemanticNode) enrichmentId body participants label =
        result {
            let proven = proofHolds body
            do! demand proven ("The source memory " + label + " proof is refuted.")
            let info = { Id = sprintf "memory_%d_%s" (NodeId.value siteNode.Id) label; Kind = "memory-" + label; Logic = "QF_LIA"
                         Statement = "Source memory " + label + " for the exact published residence and element layout."
                         Source = fmtRange siteNode.Range; Refs = []; Body = body }
            let citizen = obligationNode siteNode enrichmentId info |> Memory.markOwned
            let evidence: MemoryProof = { Site = siteNode.Id; Obligation = citizen.Id; Body = body; Participants = participants; Proven = proven }
            return citizen.Id, { NewNodes = [citizen]; NewEdges = Memory.proofRows evidence; Annotated = [] }
        }
    let settleNode (node: SemanticNode) =
        let mutable proofs = Enrichment.empty
        let enrichmentId = Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()
        let proof body participants label =
            result {
                let! citizenId, added = emitProof node enrichmentId body participants label
                proofs <- Enrichment.combine proofs added
                return citizenId
            }
        result {
            let! operation =
                match node.Kind with
                | SemanticKind.Application _ when (regionOperation node).IsSome ->
                    result {
                        let name,arguments = regionOperation node |> Option.get
                        let facts=graph.Codata.Value
                        let participant group role ordinal occurrence : Participant =
                            { Node = occurrence; Role = role; Ordinal = ordinal; Group = group }
                        let atSite = participant node.Id
                        let! kind,row,operand,source,count,copyOwner,ports =
                            match name,arguments with
                            | "Region.create",[_] -> regionAt node.Id |> Result.map (fun row -> MemoryRegionKind.Create,row,None,None,None,None,[])
                            | "Region.alloc",[region;count] ->
                                let ports = [atSite ParticipantRole.RegionHandleOperand 0 region; atSite ParticipantRole.RegionElementCount 1 count]
                                regionAt node.Id |> Result.map (fun row -> MemoryRegionKind.Allocate,row,Some region,None,Some count,None,ports)
                            | "Region.release",[region] ->
                                let ports = [atSite ParticipantRole.RegionHandleOperand 0 region]
                                regionAt node.Id |> Result.map (fun row -> MemoryRegionKind.Release,row,Some region,None,None,None,ports)
                            | "Region.copyOut",[source;count] ->
                                let ports = [atSite ParticipantRole.RegionCopySource 0 source; atSite ParticipantRole.RegionElementCount 1 count]
                                facts.RegionCopyEndpoints.TryFind node.Id |> needed "copyOut lacks its source escape contract."
                                |> Result.bind (fun copy -> facts.RegionAllocations.TryFind copy.SourceRegion |> needed "copyOut source region is absent.")
                                |> Result.map (fun row -> MemoryRegionKind.CopyOut,row,None,Some source,Some count,Some node.Id,ports)
                            | "Region.copyTo",[source;region;count] ->
                                let ports =
                                    [ atSite ParticipantRole.RegionCopySource 0 source
                                      atSite ParticipantRole.RegionHandleOperand 1 region
                                      atSite ParticipantRole.RegionElementCount 2 count ]
                                facts.RegionCopyEndpoints.TryFind node.Id |> needed "copyTo lacks its source escape contract."
                                |> Result.bind (fun copy -> copy.DestinationRegion |> Option.bind facts.RegionAllocations.TryFind |> needed "copyTo destination region is absent.")
                                |> Result.map (fun row -> MemoryRegionKind.CopyTo,row,Some region,Some source,Some count,None,ports)
                            | "Region.retireCopy",[value] ->
                                result {
                                    let copies =
                                        facts.RegionCopyEndpoints.Values |> Seq.filter(fun copy ->
                                            copy.Returned |> Option.exists(fun life -> life.Retirements |> List.exists(fun (_,site) -> site=node.Id)))
                                        |> Seq.toList
                                    let! copy =
                                        match copies with
                                        | [copy] -> Ok copy
                                        | _ -> Result.Error "Independent-copy retirement has no unique source lifetime."
                                    let! owner=facts.RegionAllocations.TryFind copy.SourceRegion |> needed "The copy source region is absent."
                                    let! count=
                                        match graph.Nodes.TryFind copy.Site |> Option.bind regionOperation with
                                        | Some("Region.copyOut",[_;count]) -> Ok count
                                        | _ -> Result.Error "Copy retirement lost its original copy count."
                                    let ports = [atSite ParticipantRole.RegionRetiredValue 0 value; participant copy.Site ParticipantRole.RegionElementCount 1 count]
                                    return MemoryRegionKind.RetireCopy,owner,Some value,None,Some count,Some copy.Site,ports
                                }
                            | _ -> Result.Error "Unsupported region memory occurrence."
                        let! slot,bytes,alignment,length =
                            match count with
                            | None ->
                                demand (row.Capacity<=int64 System.Int32.MaxValue) "Region capacity exceeds the finite storage model."
                                |> Result.map (fun () -> SettledSlot.Integer(8,None),1,row.Alignment,int row.Capacity)
                            | Some count -> result {
                                let! length=exactCount count
                                let! valueNode =
                                    if kind=MemoryRegionKind.RetireCopy then operand |> Option.bind graph.Nodes.TryFind |> needed "Copy retirement lost its operand."
                                    else Ok node
                                let! slot=viewElementSlot graph numeric valueNode
                                let! bytes,alignment=size graph slot
                                return slot,bytes,alignment,length
                              }
                        let! offset =
                            match kind with
                            | MemoryRegionKind.Allocate | MemoryRegionKind.CopyTo -> regionOffset row node.Id
                            | _ -> Ok 0L
                        let capacity = if kind=MemoryRegionKind.CopyOut || kind=MemoryRegionKind.RetireCopy then int64 length*int64 bytes else row.Capacity
                        do! demand (offset>=0L && offset+int64 length*int64 bytes<=capacity)
                                "The source region reservation exceeds its settled capacity."
                        let copyClaims = facts.RegionCopyEndpoints.TryFind node.Id |> Option.map (fun copy -> [copy.EscapeDischargeObligation]) |> Option.defaultValue []
                        let operands =
                            [atSite ParticipantRole.Site 0 node.Id; atSite ParticipantRole.RegionOwner 0 row.Region
                             atSite ParticipantRole.RegionAllocationSpace 0 row.SpacePlacement] @ row.Participants @ ports
                        let participants = operands |> Seq.map _.Node |> Set.ofSeq
                        let finish = offset + int64 length * int64 bytes
                        // Include the preceding reserved bytes so this layout tiles
                        // the region prefix instead of claiming a gap at offset zero.
                        let slots = (if offset=0L then [] else [0,int offset,1]) @ [int offset,length*bytes,alignment]
                        let! layout = proof (ObligationBody.ContinuationLayout(slots,int finish,alignment)) participants "region_layout"
                        let! capacityProof = proof (ObligationBody.CapacityFits(finish,capacity)) participants "region_capacity"
                        let obligations = layout::capacityProof::(row.Obligations @ copyClaims)
                        let lifetime=copyOwner |> Option.bind facts.RegionCopyEndpoints.TryFind |> Option.bind _.Returned
                        let! selectedRuntime=regionRuntime row
                        let runtime=selectedRuntime |> Option.map snd
                        let space=match lifetime with Some life -> life.Space | None -> row.SpacePlacement
                        let declarationRoots=row.SpacePlacement::space::(selectedRuntime |> Option.map fst |> Option.toList)
                        let! declarations=declarationRoots |> List.distinct |> List.fold(fun state root ->
                            state |> Result.bind(fun facts ->
                                Clef.Compiler.Baker.Ingredients.Boundaries.declarationFacts graph root
                                |> Result.map(fun current -> Map.fold(fun facts id value -> Map.add id value facts) facts current))) (Ok Map.empty)
                        let! obligations =
                            match lifetime with
                            | None -> Ok obligations
                            | Some life -> result {
                                do! demand ((graph.Platform |> Option.bind _.ProjectMemoryPolicy)=Some(life.Policy.ProjectPath,life.Policy.SourceVersion,life.Policy.Model,true))
                                        "Independent copy lost its captured project allocation permission."
                                let! platform=getPlatform ()
                                let! heap=platform.Spaces |> List.tryFind(fun selected -> selected.Node=life.Space && selected.Kind="heap" && selected.Access.Contains("w"))
                                          |> needed "Independent copy lost its selected writable heap space."
                                do! demand (runtime |> Option.forall(fun selected -> selected.Contract.EscapeSpace=heap.Name)) "Independent copy differs from its declared destination space."
                                let support=Set.union participants (Set.ofList(life.Application::platform.Node::heap.Node::(life.Retirements |> List.map snd)))
                                let! heapCapacity=proof (ObligationBody.CapacityFits(capacity,heap.Capacity)) support "region_copy_capacity"
                                return heapCapacity::obligations
                              }
                        let support =
                            operands @ [atSite ParticipantRole.RegionStorageSpace 0 space]
                            @ (copyOwner |> Option.map (atSite ParticipantRole.RegionCopyOwner 0) |> Option.toList)
                            @ (declarations |> Map.toList |> List.map (fst >> atSite ParticipantRole.RegionDeclaration 0))
                            @ (obligations |> List.mapi (atSite ParticipantRole.RegionProof))
                        return MemoryWitnessOperation.Region {
                            Site=node.Id; Region=row.Region; Kind=kind; Operand=operand; Source=source
                            Count=(if kind=MemoryRegionKind.RetireCopy then None else count)
                            Element=slot; ElementBytes=bytes; Length=length; Offset=offset; Capacity=capacity
                            Alignment=alignment; Space=space; Runtime=runtime;CopyOwner=copyOwner;Declarations=declarations;Obligations=obligations
                            Participants=support }
                    }
                | SemanticKind.Binding(_,true,_,_) ->
                    result {
                        let! scope = nearestLambda graph node.Id |> needed "A scalar cell lacks a lexical activation."
                        let! initial = match node.Children with [value] -> Ok value | _ -> Result.Error "A scalar cell requires one initializer."
                        let! nodeCarrier = carrier numeric node.Id
                        let slot = nodeCarrier.Slot
                        do! demand (match slot with SettledSlot.Bool -> true | SettledSlot.Integer(bits,_) -> List.contains bits [8;16;32;64] | _ -> false)
                               "Local scalar storage requires a settled Boolean or byte-addressable integer."
                        let! bytes,alignment = size graph slot
                        let nodes = graph.Nodes.Values |> Seq.filter (fun candidate -> candidate.IsReachable && not(excluded.Contains candidate.Id)) |> Seq.toList
                        let reads = nodes |> List.choose (fun candidate -> match candidate.Kind with SemanticKind.VarRef(_,Some binding) when binding=node.Id -> Some candidate.Id | _ -> None) |> Set.ofList
                        do! demand (reads |> Set.forall (fun site -> nearestLambda graph site=Some scope)) "A scalar cell is captured outside its activation."
                        do! demand (nodes |> List.forall (fun candidate -> match candidate.Kind with SemanticKind.CellAddress binding when binding=node.Id -> false | _ -> true))
                               "An addressed scalar cell requires a separate lifetime contract."
                        let writes = nodes |> List.choose (fun candidate ->
                            match candidate.Kind with
                            | SemanticKind.Set(target,value) when reads.Contains target -> Some(candidate.Id,value)
                            | _ -> None)
                        do! demand (writes |> List.forall (fun (site,_) -> nearestLambda graph site=Some scope)) "A scalar write crosses its activation."
                        let! declared = getPlatform ()
                        let! space =
                            match declared.Spaces |> List.filter (fun space -> space.Kind="stack" && space.Access.Contains("w")) with
                            | [space] -> Ok space
                            | _ -> Result.Error "A local scalar requires one declared writable stack space."
                        do! demand (space.Alignment>=alignment && space.Alignment%alignment=0) "Declared stack alignment cannot satisfy the scalar."
                        let participants = Set.unionMany [reads; nodeCarrier.Participants; Set.ofList [node.Id;initial;scope;declared.Node;space.Node]
                                                          writes |> List.collect (fun (site,value)->[site;value]) |> Set.ofList]
                        let! layout = proof (ObligationBody.ContinuationLayout([0,bytes,alignment],bytes,alignment)) participants "scalar_layout"
                        let! capacity = proof (ObligationBody.CapacityFits(int64 bytes,space.Capacity)) participants "scalar_capacity"
                        return MemoryWitnessOperation.LocalScalar {Site=node.Id;Initializer=initial;Element=slot;Bytes=bytes;Alignment=alignment
                                                                   Residence=MemoryResidence.Stack(scope,space.Node);Reads=reads;Writes=writes
                                                                   Platform=declared.Node;Layout=layout;Capacity=capacity}
                    }
                | SemanticKind.DUConstruct _ when (checkedCase node.Id).IsSome ->
                    result {
                        let construction=checkedCase node.Id |> Option.get
                        do! demand (match node.Kind with
                                    | SemanticKind.DUConstruct("ValueSome",1,Some text,None) -> node.Id=construction.Success && text=construction.Text
                                    | SemanticKind.DUConstruct("ValueNone",0,None,None) -> node.Id=construction.Failure
                                    | _ -> false) "The checked carrier allocation changed its exact native case."
                        do! demand (applySubst node.Type=NativeType.TApp(Types.voptionTyCon,[Types.stringType]))
                                "The checked carrier allocation lacks its native value-option source type."
                        let sourceType=TypeIdentity.ofType node.Type
                        let! bytes,alignment =
                            match numeric.Layouts.TryFind sourceType with
                            | Some(SettledLayout.Union(_,_,Some bytes,Some alignment)) when bytes>0 && alignment>0 -> Ok(bytes,alignment)
                            | _ -> Result.Error "The constructed value lacks its complete settled union storage layout."
                        let! returned = StringByteStorageRecipes.returnedLifetime graph construction
                        let _,closed,uses=arrayUses graph node.Id
                        let! declared = getPlatform ()
                        let! scope,stack,residence,uses =
                            match returned with
                            | Some(life,space) ->
                                // Uses names program consumers. The exact logical capacity
                                // target is supported separately through its named role.
                                let executableUses=Set.union uses (Set.ofList life.Uses) |> Set.remove life.Capacity
                                Ok(life.Application,space,MemoryResidence.Heap(life.Application,space.Node),executableUses)
                            | None ->
                                result {
                                    do! demand closed "The constructed value's complete use family escapes or has an unsupported consumer."
                                    let! scope = nearestLambda graph node.Id |> needed "The constructed value has no source lexical activation scope."
                                    for useId in uses do
                                        let! useNode = live graph useId
                                        let inScope =
                                            match useNode.Kind with
                                            | SemanticKind.ModuleDef _ -> true
                                            | _ -> nearestLambda graph useId = Some scope
                                        do! demand inScope "A constructed-value alias or access crosses its proposed stack activation."
                                    let! stack =
                                        match declared.Spaces |> List.filter(fun space -> space.Kind="stack" && space.Access.Contains("w")) with
                                        | [stack] -> Ok stack
                                        | _ -> Result.Error "A local constructed value requires one declared writable stack space."
                                    return (scope,stack,MemoryResidence.Stack(scope,stack.Node),uses)
                                }
                        do! demand (stack.Alignment>=alignment && stack.Alignment%alignment=0)
                                "The declared stack space does not satisfy the constructed-value layout alignment."
                        let incidence=[construction.Owner;construction.Input;construction.Snapshot;construction.Length;construction.Validation
                                       construction.Decision;construction.Text;construction.Success;construction.Failure;construction.Retirement]
                        let participants=Set.union uses (Set.ofList(declared.Node::stack.Node::scope::incidence))
                        let! layoutProof = proof (ObligationBody.ContinuationLayout([0,bytes,alignment],bytes,alignment)) participants "constructed_layout"
                        let! capacityProof = proof (ObligationBody.CapacityFits(int64 bytes,stack.Capacity)) participants "constructed_capacity"
                        return MemoryWitnessOperation.ConstructedValue
                            {Site=node.Id;Owner=construction.Owner;SourceType=sourceType;Residence=residence
                             Uses=uses;Construction=construction;Platform=declared.Node;Layout=layoutProof;Capacity=capacityProof}
                    }
                | SemanticKind.ArrayExpr elements ->
                    result {
                        let! slot = viewElementSlot graph numeric node
                        let! bytes, alignment = size graph slot
                        do! demand (bytes > 0 && alignment > 0) "Array storage needs positive settled element extent and alignment."
                        let! initializersOpt, adapted =
                            match slot with
                            | SettledSlot.InlineBytes _ ->
                                Ok((if elements.IsEmpty then Some [] else None), elements |> List.map (fun id -> id, None))
                            | _ ->
                                result {
                                    let! initializers = elements |> mapResult (literal graph)
                                    do! demand (initializers |> List.forall Option.isSome) "Ordinary array elements require source demand and memoization placement; effectful or nonliteral initializers are not admitted as eager stores."
                                    let! adaptedList =
                                        elements
                                        |> mapResult (fun id ->
                                            result {
                                                let! valSite = valueSite graph id
                                                let! valCarrier = carrier numeric valSite
                                                let! adapt = adaptation graph node.Id id valCarrier.Slot slot
                                                return (id, adapt)
                                            })
                                    return (Some(initializers |> List.map Option.get), adaptedList)
                                }
                        let readonly, closed, uses = arrayUses graph node.Id
                        let participants = Set.union uses (Set.ofList elements) |> Set.add node.Id
                        let extent = bigint elements.Length * bigint bytes
                        do! demand (extent <= bigint System.Int32.MaxValue) "Array storage extent exceeds the admitted finite layout model."
                        let! declaredPlatform = getPlatform ()
                        let! residence, space, authority =
                            if readonly then
                                result {
                                    let! declared = Platform.immutableProgramSpace declaredPlatform |> needed "A readonly constant array requires an explicitly designated immutable program space."
                                    return (MemoryResidence.ImmutableProgram declared.Node, declared, Platform.immutableProgramAuthority declaredPlatform)
                                }
                            else
                                result {
                                    do! demand closed "The array's complete use family escapes or observes address identity; a source residence contract is required."
                                    let! scope = nearestLambda graph node.Id |> needed "A mutable array has no source lexical activation scope."
                                    for useId in uses do
                                        let! useNode = live graph useId
                                        let inScope =
                                            match useNode.Kind with
                                            | SemanticKind.ModuleDef _ -> true
                                            | _ -> nearestLambda graph useId = Some scope
                                        do! demand inScope "An array alias or access crosses its proposed stack activation."
                                    let declared = declaredPlatform.Spaces |> List.filter (fun space -> space.Kind = "stack" && space.Access.Contains("w"))
                                    let! stack =
                                        match declared with
                                        | [stack] -> Ok stack
                                        | _ -> Result.Error "A local mutable array requires one declared writable stack space."
                                    return (MemoryResidence.Stack(scope, stack.Node), stack, [declaredPlatform.Node;stack.Node;scope])
                                }
                        let participants = Set.union participants (Set.ofList authority)
                        do! demand (space.Alignment >= alignment && space.Alignment % alignment = 0) "The declared memory space does not satisfy the array element alignment."
                        let slots = elements |> List.mapi (fun ordinal _ -> ordinal * bytes, bytes, alignment)
                        let! layoutProof = proof (ObligationBody.ContinuationLayout(slots, int extent, alignment)) participants "array_layout"
                        let! capacityProof = proof (ObligationBody.CapacityFits(int64 extent, space.Capacity)) participants "array_capacity"
                        return MemoryWitnessOperation.ArrayLiteral
                            { Site = node.Id; Elements = adapted; Element = slot; Length = elements.Length; Residence = residence
                              Initializers = initializersOpt; Alignment = alignment; ElementBytes = bytes
                              Participants = participants |> Set.add layoutProof |> Set.add capacityProof }
                    }
                | SemanticKind.IndexGet(buffer,index) | SemanticKind.IndexSet(buffer,index,_) ->
                    result {
                        let evaluation = match node.Kind with SemanticKind.IndexSet(_,_,value) -> Some value | _ -> None
                        if evaluation.IsSome then
                            do! demand (isArray graph buffer) "ReadOnlyView elements are read-only and cannot be mutated."
                        else
                            do! demand (isReadableBuffer graph buffer) "The array read target lacks a readable buffer contract."
                        // The source operation retains the whole evaluation (including its
                        // guards). The memory operand and its numeric meet both name the
                        // resulting value; a transparent block is not a second value.
                        let! stored =
                            match evaluation with
                            | Some evalId -> valueSite graph evalId |> Result.map Some
                            | None -> Ok None
                        let! bounds = bounds graph numeric node.Id buffer index
                        let! bufNode = live graph buffer
                        let! slot = viewElementSlot graph numeric bufNode
                        let! adapted =
                            match stored, slot with
                            | _, SettledSlot.InlineBytes _ -> Ok None
                            | Some value, _ ->
                                result {
                                    let! valCarrier = carrier numeric value
                                    return! adaptation graph node.Id value valCarrier.Slot slot
                                }
                            | None, _ ->
                                result {
                                    let! nodeCarrier = carrier numeric node.Id
                                    return! adaptation graph node.Id node.Id slot nodeCarrier.Slot
                                }
                        return MemoryWitnessOperation.ArrayAccess
                            { Site = node.Id; Buffer = buffer; Index = index; Value = stored; Element = slot; Adaptation = adapted
                              Bounds = bounds; Participants = Set.union bounds.Participants (Set.ofList (Option.toList evaluation @ Option.toList stored)) }
                    }
                | SemanticKind.ElementAddress(buffer,index) ->
                    result {
                        do! demand (isArray graph buffer) "ReadOnlyView elements are read-only and cannot have their mutable element address taken."
                        let! bounds = bounds graph numeric node.Id buffer index
                        let! bufNode = live graph buffer
                        let! slot = viewElementSlot graph numeric bufNode
                        let! bytes, _ = size graph slot
                        let! ptrBits = pointerBits graph
                        return MemoryWitnessOperation.Address
                            { Site = node.Id; Place = MemoryPlace.ArrayElement(buffer,index,bounds); Element = Some slot; ElementBytes = Some bytes
                              PointerBits = ptrBits; Participants = bounds.Participants }
                    }
                | SemanticKind.CellAddress binding ->
                    result {
                        let! cell = live graph binding
                        do! demand (match cell.Kind with SemanticKind.Binding(_,true,_,_) -> true | _ -> false) "AddressOf requires the actual mutable binding cell."
                        let! scalar = carrier numeric binding
                        let! bytes, _ = size graph scalar.Slot
                        let! ptrBits = pointerBits graph
                        return MemoryWitnessOperation.Address
                            { Site = node.Id; Place = MemoryPlace.MutableCell binding; Element = Some scalar.Slot; ElementBytes = Some bytes
                              PointerBits = ptrBits; Participants = scalar.Participants |> Set.add node.Id |> Set.add binding }
                    }
                | SemanticKind.Reborrow source ->
                    result {
                        let! input = live graph source
                        do! demand (match applySubst input.Type, applySubst node.Type with NativeType.TByref _, NativeType.TByref _ -> applySubst input.Type = applySubst node.Type | _ -> false)
                               "Reborrowing must preserve the existing typed reference exactly."
                        let! ptrBits = pointerBits graph
                        return MemoryWitnessOperation.Address
                            { Site = node.Id; Place = MemoryPlace.ExistingReference source; Element = None; ElementBytes = None
                              PointerBits = ptrBits; Participants = Set.ofList [node.Id;source] }
                    }
                | SemanticKind.FieldAddress(receiver, name) ->
                    result {
                        let! input = live graph receiver
                        let! declaration =
                            match applySubst input.Type with
                            | NativeType.TApp(tc, _) ->
                                Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances.tryDefinition (NominalTypeIdentity.ofConstructor tc) graph
                                |> needed "The addressed record has no exact source type declaration."
                            | _ -> Result.Error "A field address requires a concrete nominal record receiver."
                        do! demand (match declaration.Metadata.TryFind "TypeDef.MutableFields" with
                                    | Some(MetadataValue.StringList fields) -> List.contains name fields | _ -> false)
                               "The source record declaration does not mark this exact field mutable."
                        let! fields, total, alignment =
                            match numeric.Layouts.TryFind (TypeIdentity.ofType input.Type) with
                            | Some(SettledLayout.Record(fields, Some total, Some alignment)) -> Ok(fields,total,alignment)
                            | _ -> Result.Error "The addressed record lacks its complete settled byte storage layout."
                        let! field = fields |> List.tryFind (fun field -> field.Name = name) |> needed "The addressed field is absent from the exact source record layout."
                        let! bytes, fieldAlignment = size graph field.Slot
                        do! demand (total > 0 && alignment > 0 && field.Size = Some bytes && field.Align = Some fieldAlignment &&
                                    field.Offset |> Option.exists (fun offset -> offset >= 0 && offset % fieldAlignment = 0 && offset + bytes <= total))
                               "The addressed field's exact offset, extent and alignment are not contained in its receiver storage."
                        let! ptrBits = pointerBits graph
                        return MemoryWitnessOperation.Address
                            { Site = node.Id; Place = MemoryPlace.RecordField(receiver,total,field); Element = Some field.Slot; ElementBytes = Some bytes
                              PointerBits = ptrBits; Participants = Set.ofList [node.Id;receiver;declaration.Id] }
                    }
                | SemanticKind.AddressOf _ ->
                    Result.Error "AddressOf has no admitted actual mutable place; defensive copies cannot supply that place."
                | SemanticKind.FieldGet(_, "Pointer") ->
                    Result.Error "The current source member contract does not admit .Pointer; an actual mutable place uses the documented AddressOf operation."
                | _ ->
                    result {
                        do! match pendingArrayConstruction graph node with
                            | Some operation ->
                                let reason =
                                    match node.Metadata.TryFind "Baker.ArrayConstructionError" with
                                    | Some(MetadataValue.String reason) -> reason
                                    | _ -> "Array." + operation + " requires source-owned construction, range guards, demand and storage residence; no such operation is settled."
                                Result.Error reason
                            | None -> Ok ()
                        let! buffer = arrayLength graph node |> needed "The memory operation has no source settlement recipe."
                        let! resultCarrier = carrier numeric node.Id
                        let! bufNode = live graph buffer
                        let! elemSlot = viewElementSlot graph numeric bufNode
                        return MemoryWitnessOperation.ArrayExtent
                            { Site = node.Id; Source = buffer; Element = elemSlot; Result = resultCarrier
                              Participants = resultCarrier.Participants |> Set.add node.Id |> Set.add buffer }
                    }
            enrichment <- Enrichment.combine enrichment proofs
            return operation
        }
    let isImmutableBinding id =
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Binding(_, false, _, _) }
        | Some { Kind = SemanticKind.PatternBinding _ } -> true
        | _ -> false
    let rec canonicalRoot seen id =
        if Set.contains id seen then id else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some inner) } when isImmutableBinding inner -> canonicalRoot seen inner
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
        | Some { Kind = SemanticKind.EagerExpr inner } -> canonicalRoot seen inner
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> canonicalRoot seen value
        | Some { Kind = SemanticKind.Sequential items } when not items.IsEmpty -> canonicalRoot seen (List.last items)
        | _ -> id
    let dominatingLengthLowerBound (siteNode: SemanticNode) (sourceId: NodeId) : (bigint * NodeId list) option =
        let sourceRoot = canonicalRoot Set.empty sourceId
        let isSourceLength id =
            let targetId = canonicalRoot Set.empty id
            let checkNode candidate =
                match graph.Nodes.TryFind candidate with
                | Some { Kind = SemanticKind.FieldGet(buf, "Length") } -> canonicalRoot Set.empty buf = sourceRoot
                | Some { Kind = SemanticKind.Application _ } ->
                    match intrinsic graph candidate [] with
                    | Some(info, [buf]) when info.Module = IntrinsicModule.Array && info.Operation = "length" ->
                        canonicalRoot Set.empty buf = sourceRoot
                    | _ -> false
                | _ -> false
            checkNode id || checkNode targetId
        let lowerBoundOf id =
            match tryValueSite graph id |> Option.bind numeric.Values.TryFind with
            | Some c ->
                match c.Range with
                | ValueRange.Bounded(lo, hi) when lo <= hi -> Some lo
                | _ -> None
            | None -> None
        let rec extractFromCond condId =
            match graph.Nodes.TryFind condId with
            | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
            | Some { Kind = SemanticKind.EagerExpr inner } -> extractFromCond inner
            | Some { Kind = SemanticKind.VarRef(_, Some inner) } when isImmutableBinding inner -> extractFromCond inner
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [inner] } -> extractFromCond inner
            | Some { Kind = SemanticKind.Sequential items } when not items.IsEmpty -> extractFromCond (List.last items)
            | Some { Kind = SemanticKind.IfThenElse(a, b, Some falseId) } ->
                match graph.Nodes.TryFind falseId with
                | Some { Kind = SemanticKind.Literal(NativeLiteral.Bool false) } -> extractFromCond a @ extractFromCond b
                | _ -> []
            | Some { Kind = SemanticKind.Application _ } ->
                match intrinsic graph condId [] with
                | Some(info, [lhs; rhs]) when info.Module = IntrinsicModule.Operators ->
                    let emitLower kOpt =
                        match kOpt with
                        | Some k -> [k, [condId; lhs; rhs]]
                        | None -> []
                    match info.Operation with
                    | "op_GreaterThan" when isSourceLength lhs ->
                        emitLower (lowerBoundOf rhs |> Option.map (fun k -> k + 1I))
                    | "op_GreaterThanOrEqual" when isSourceLength lhs ->
                        emitLower (lowerBoundOf rhs)
                    | "op_LessThan" when isSourceLength rhs ->
                        emitLower (lowerBoundOf lhs |> Option.map (fun k -> k + 1I))
                    | "op_LessThanOrEqual" when isSourceLength rhs ->
                        emitLower (lowerBoundOf lhs)
                    | _ -> []
                | _ -> []
            | _ -> []
        let rec climb seen childId acc =
            match graph.Nodes.TryFind childId |> Option.bind _.Parent with
            | Some parentId when not (Set.contains parentId seen) ->
                let seen = Set.add parentId seen
                let acc =
                    match graph.Nodes.TryFind parentId with
                    | Some { Kind = SemanticKind.IfThenElse(cond, yes, _) } when yes = childId ->
                        extractFromCond cond @ acc
                    | Some { Kind = SemanticKind.Sequential items } ->
                        let preceding =
                            items
                            |> List.takeWhile (fun item -> item <> childId)
                            |> List.collect (fun item ->
                                match graph.Nodes.TryFind item with
                                | Some { Kind = SemanticKind.Require(cond, _) } -> extractFromCond cond
                                | _ -> [])
                        preceding @ acc
                    | _ -> acc
                climb seen parentId acc
            | _ -> acc
        match climb Set.empty siteNode.Id [] with
        | [] -> None
        | bounds ->
            let bestLo = bounds |> List.map fst |> List.max
            let nodes = bounds |> List.collect snd
            Some(bestLo, nodes)
    let shapeReader = lazy (Clef.Compiler.Baker.Ingredients.ArrayShapes.reader graph)
    let validateReadOnlyViewConversion (node: SemanticNode) = function
        | ReadOnlyViewConversion.OfArray source ->
            result {
                let! input = live graph source
                let! _ = viewElementSlot graph numeric node
                let! callee =
                    match node.Kind with
                    | SemanticKind.Application(callee, [actual]) when actual = source && node.Children = [callee; source] -> Ok callee
                    | _ -> Result.Error "ReadOnlyView.ofArray lost its exact source operand."
                let! _ =
                    match applySubst input.Type, Types.tryGetReadOnlyViewElement (applySubst node.Type) with
                    | NativeType.TApp(array, [element]), Some target
                        when array.NTUKind = Some NTUKind.NTUarray && applySubst element = applySubst target -> Ok ()
                    | _ -> Result.Error "ReadOnlyView.ofArray requires its exact array element type."
                let! sourceCarrier = numeric.OccurrenceRepresentations.TryFind source |> Option.bind Result.toOption
                                     |> needed "ReadOnlyView.ofArray source lacks its settled descriptor."
                let! resultCarrier = numeric.OccurrenceRepresentations.TryFind node.Id |> Option.bind Result.toOption
                                     |> needed "ReadOnlyView.ofArray result lacks its settled descriptor."
                do! demand
                        (match sourceCarrier, resultCarrier with
                         | ValueRepresentation.Buffer(_, element), ValueRepresentation.Buffer(None, target) -> element = target
                         | _ -> false)
                        "ReadOnlyView.ofArray must preserve the source element representation."
                let participant role occurrence : Participant =
                    { Node = occurrence; Role = role; Ordinal = 0; Group = node.Id }
                let view =
                    { Site = node.Id; Source = source; SourceCarrier = sourceCarrier; ResultCarrier = resultCarrier
                      Participants = [ participant ParticipantRole.Site node.Id
                                       participant ParticipantRole.ReadOnlyViewCallee callee
                                       participant ParticipantRole.ReadOnlyViewArraySource source ] }
                operations <- (node.Id, MemoryWitnessOperation.ReadOnlyArrayView view) :: operations
                required <- Set.add node.Id required
                return Enrichment.empty
            }
        | ReadOnlyViewConversion.Slice(source, offset, count) ->
            result {
                let! _ = live graph source
                let! offsetSite = valueSite graph offset
                let! offsetCarrier = carrier numeric offsetSite
                let! countSite = valueSite graph count
                let! countCarrier = carrier numeric countSite
                let! offLo, offHi =
                    match offsetCarrier.Range with
                    | ValueRange.Bounded(lo, hi) when lo >= 0I && lo <= hi -> Ok(lo, hi)
                    | _ -> Result.Error "ReadOnlyView.slice requires a finite non-negative settled offset range."
                let! cntLo, cntHi =
                    match countCarrier.Range with
                    | ValueRange.Bounded(lo, hi) when lo >= 0I && lo <= hi -> Ok(lo, hi)
                    | _ -> Result.Error "ReadOnlyView.slice requires a finite non-negative settled count range."
                let! shapeExtentOpt =
                    match shapeReader.Value source with
                    | Some extent when not extent.Sources.IsEmpty ->
                        result {
                            let! resolved =
                                extent.Sources
                                |> mapResult (function
                                    | Clef.Compiler.Baker.Ingredients.ArrayShapes.Length.Constant n ->
                                        result {
                                            do! demand (n >= 0I) "ReadOnlyView.slice requires a non-negative source extent."
                                            return (n, Set.empty)
                                        }
                                    | Clef.Compiler.Baker.Ingredients.ArrayShapes.Length.Count cid ->
                                        result {
                                            let! cidSite = valueSite graph cid
                                            let! c = carrier numeric cidSite
                                            match c.Range with
                                            | ValueRange.Bounded(lo, hi) when lo >= 0I && lo <= hi -> return (lo, c.Participants)
                                            | _ -> return! Result.Error "ReadOnlyView.slice requires a finite non-negative settled source extent."
                                        })
                            let minExtent = resolved |> List.map fst |> List.min
                            let ps = resolved |> List.map snd |> Set.unionMany |> Set.union extent.Participants
                            return Some(minExtent, ps)
                        }
                    | _ -> Ok None
                let guardExtentOpt =
                    match dominatingLengthLowerBound node source with
                    | Some(minExtent, guardNodes) when minExtent >= 0I ->
                        Some(minExtent, Set.ofList guardNodes)
                    | _ -> None
                let! srcExtentLo, extentParticipants =
                    match shapeExtentOpt, guardExtentOpt with
                    | Some(shapeLo, shapePs), Some(guardLo, guardPs) ->
                        if guardLo > shapeLo then Ok(guardLo, Set.union shapePs guardPs)
                        else Ok(shapeLo, shapePs)
                    | Some(shapeLo, shapePs), None -> Ok(shapeLo, shapePs)
                    | None, Some(guardLo, guardPs) -> Ok(guardLo, guardPs)
                    | None, None ->
                        Result.Error "ReadOnlyView.slice requires a settled source extent or dominating length guard proving slice bounds."
                do! demand (offLo >= 0I && cntLo >= 0I && offHi + cntHi <= srcExtentLo)
                        (sprintf "ReadOnlyView.slice bounds [%s..%s) exceed settled source extent %s." (string offHi) (string (offHi + cntHi)) (string srcExtentLo))
                let participants =
                    Set.unionMany [ offsetCarrier.Participants; countCarrier.Participants; extentParticipants; Set.ofList [node.Id; source; offset; count] ]
                let! _, sliceProofEnrich =
                    emitProof node (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ())
                        (ObligationBody.IntegerRepresentationCoverage(0I, offHi + cntHi, 0I, srcExtentLo))
                        participants "slice_bounds"
                let! _ = viewElementSlot graph numeric node
                return sliceProofEnrich
            }
        | ReadOnlyViewConversion.OfString source ->
            result {
                let! _ =
                    numeric.OccurrenceRepresentations.TryFind source
                    |> Option.bind (function Ok rep -> Some rep | Result.Error _ -> None)
                    |> needed "ReadOnlyView source lacks a settled physical representation."
                let! _ =
                    numeric.OccurrenceRepresentations.TryFind node.Id
                    |> Option.bind (function Ok rep -> Some rep | Result.Error _ -> None)
                    |> needed "ReadOnlyView lacks a settled physical representation."
                let! _ = element numeric node.Id
                let! _ =
                    Clef.Compiler.Baker.Ingredients.StringBytes.byteRepresentation graph
                    |> needed "ReadOnlyView requires a declared unsigned byte representation."
                return Enrichment.empty
            }
    for node in graph.Nodes.Values do
        if node.IsReachable && not (excluded.Contains node.Id) then
            let needs =
                match node.Kind with
                | SemanticKind.ArrayExpr _ -> isArray graph node.Id
                | SemanticKind.Application _ when (regionOperation node).IsSome -> true
                | SemanticKind.AddressOf _ | SemanticKind.CellAddress _
                | SemanticKind.ElementAddress _ | SemanticKind.FieldAddress _ | SemanticKind.Reborrow _ -> true
                | SemanticKind.DUConstruct _ when (checkedCase node.Id).IsSome -> true
                | SemanticKind.IndexGet(buffer,_) | SemanticKind.IndexSet(buffer,_,_) -> isReadableBuffer graph buffer
                | SemanticKind.FieldGet(buffer,"Pointer") -> isReadableBuffer graph buffer
                | _ -> (arrayLength graph node).IsSome || (pendingArrayConstruction graph node).IsSome
            if needs then
                required <- Set.add node.Id required
                match settleNode node with
                | Ok op -> operations <- (node.Id, op) :: operations
                | Result.Error reason -> unresolved <- Map.add node.Id reason unresolved
            elif (match node.Kind with SemanticKind.Binding(_,true,_,_) -> true | _ -> false) && (nearestLambda graph node.Id).IsSome then
                // This optional permission does not replace existing specialized
                // storage families. An absent account grants no artifact admission.
                match settleNode node with
                | Ok op ->
                    operations <- (node.Id, op) :: operations
                    required <- Set.add node.Id required
                | Result.Error _ -> ()
            else
                match readOnlyViewConversion graph node with
                | Some conversion ->
                    match validateReadOnlyViewConversion node conversion with
                    | Ok convEnrich -> enrichment <- Enrichment.combine enrichment convEnrich
                    | Result.Error reason -> unresolved <- Map.add node.Id reason unresolved
                | None -> ()
    enrichment, List.rev operations, unresolved, required

// Finalize the source-authored logical live budget after the existing numeric
// owner has settled the exact element and native union layouts.
let finalizeReturned (graph:SemanticGraph) (numeric:NumericWitnessProjection) =
    let mutable nodes=graph.Nodes
    let mutable proofEdges=[]
    let finish (edge: Hyperedge) =
        match edge.Role with
        | EdgeRole.StringCheckedConstruction construction ->
            match construction.Returned with
            | None -> edge
            | Some lifetime ->
                let pending reason = Result.Error reason
                let outcome =
                    result {
                        let! platform = Platform.resolve graph |> needed "The returned checked platform was withdrawn."
                        let! space =
                            platform.Spaces |> List.tryFind(fun space->space.Node=lifetime.Space && space.Kind="heap" && space.Access.Contains("w"))
                            |> needed "The returned checked heap declaration was withdrawn."
                        let! allocation =
                            graph.Edges |> List.choose(fun row->
                                match row.Role with
                                | EdgeRole.ArrayAllocationConstruction row when row.Owner=construction.Snapshot -> Some row
                                | _ -> None)
                            |> function
                               | [row] -> Ok row
                               | _ -> pending "The returned checked snapshot has no unique source allocation."
                        let! maximum =
                            match numeric.Values.TryFind allocation.Count.Reference with
                            | Some countCarrier ->
                                match countCarrier.Range with
                                | ValueRange.Bounded(lo,hi) when lo>0I -> Ok hi
                                | ValueRange.Bounded(lo,hi) when lo=0I && hi=0I -> Ok 0I
                                | _ -> pending "The returned checked snapshot requires a positive or exactly zero count."
                            | None -> pending "The returned checked snapshot lacks its settled count carrier."
                        let! bytes =
                            match numeric.Elements.TryFind allocation.Site |> Option.bind(Clef.Compiler.PSGSaturation.SemanticGraph.Placement.extentOfSlot graph) with
                            | Some(bytes,_) -> Ok(bigint bytes)
                            | None -> pending "The returned checked element extent is missing."
                        let! carrierBytes =
                            match numeric.Layouts.TryFind(Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[construction.Success].Type) with
                            | Some(SettledLayout.Union(_,_,Some bytes,_)) -> Ok(bigint bytes)
                            | _ -> pending "The returned checked native carrier layout is missing."
                        let total = maximum*bytes+carrierBytes
                        do! if total>bigint space.Capacity || total>bigint System.Int64.MaxValue then
                                pending "The combined returned checked live extent exceeds its declared heap capacity."
                            else Ok ()
                        let lifetime = {lifetime with MaximumLiveBytes=int64 total}
                        let construction = {construction with Returned=Some lifetime}
                        let sources =
                            [lifetime.Application;lifetime.Callee;lifetime.Declaration;lifetime.Implementation;lifetime.Argument;lifetime.Formal;lifetime.Body
                             lifetime.Caller;lifetime.Actual;lifetime.Elimination;lifetime.SomeUse;lifetime.NoneUse;lifetime.SomeBackingRetirement
                             lifetime.SomeCarrierRetirement;lifetime.NoneCarrierRetirement;lifetime.Platform;lifetime.Space]@lifetime.Uses
                        let citizen = nodes[lifetime.Capacity]
                        let! info =
                            match citizen.Kind with
                            | SemanticKind.Obligation info -> Ok info
                            | _ -> pending "The returned checked capacity citizen was withdrawn."
                        nodes<-nodes.Add(citizen.Id,{citizen with Kind=SemanticKind.Obligation{info with Body=ObligationBody.CapacityFits(int64 total,space.Capacity)}})
                        proofEdges<-constrains sources {citizen with Kind=SemanticKind.Obligation{info with Body=ObligationBody.CapacityFits(int64 total,space.Capacity)}}::proofEdges
                        return {edge with Role=EdgeRole.StringCheckedConstruction construction;Sources=List.distinct(edge.Sources@sources@[lifetime.Capacity])}
                    }
                match outcome with
                | Ok updatedEdge -> updatedEdge
                | Result.Error reason ->
                    match nodes.TryFind lifetime.Capacity with
                    | Some citizen ->
                        match citizen.Kind with
                        | SemanticKind.Obligation info ->
                            nodes<-nodes.Add(citizen.Id,{citizen with Kind=SemanticKind.Obligation{info with Body=ObligationBody.Pending[reason]}})
                        | _ -> ()
                    | None -> ()
                    edge
        | _ -> edge
    let edges=graph.Edges |> List.map finish
    {graph with Nodes=nodes;Edges=edges@proofEdges}

let settle graph numeric =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> settleCore graph numeric)

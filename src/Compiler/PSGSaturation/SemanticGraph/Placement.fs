// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Placement: the settled layouts of the graph's aggregate types (Dimensional_Range_Design.md §3.3
/// and ruling 2; Layout_As_Joint_Constraint.md §3; native-type-universe.md §2.3; CS-11 slice 0).
///
/// A record's layout is the consequence of its fields' selections, settled in the graph. CCS
/// preserves a type's layout identity at type checking (`TypeConRef.Layout`, symbolic) and
/// resolves its size here, at saturation, because that is where the platform is: the pass runs
/// after `PlatformDeclaration.fill` has read the description's width dimensions and
/// representations into the context and after `RangeAnalysis.run` has settled every field's
/// range (`FieldRanges`) and every node's. For every reachable record and union type, and every
/// reachable tuple, option and Result type, it writes one `SettledLayout` to `SemanticGraph.Layouts`:
/// each integer field at the representation its range selects (`RangeAnalysis.heldWidthOf`; an
/// `Empty` range, a field nothing constructs, selects the smallest declared representation and
/// never zero bytes; a width-named carrier its own representation, which is what keeps a wire or
/// FFI struct's field widths declared until CS-12's boundary rows take over), a bool at one byte,
/// a char at its code-point representation, a real at its declared bits, every pointer-sized field
/// at the declared Pointer width times the words of the leg's realisation (`SettledSlot.Pointer`),
/// a union's payload slot at its widest case; alignment follows the selected representation and
/// offsets tile in declaration order. On a context declaring no representations (fabric) the
/// layout records widths only and no byte offsets. Composer reads a field's representation,
/// offset and size here and computes none of them (§8.3: one size model, the settled layout for
/// aggregates and the selected width for scalars).
module Clef.Compiler.PSGSaturation.SemanticGraph.Placement

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.Expressions.Intrinsics
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

/// The words of the CPU leg's pointer-sized realisations (`SettledSlot.Pointer`): an address, a
/// function value's closure pair, and a view of a buffer (a memref descriptor: two addresses, an
/// offset, a size and a stride). Read here into the layout; never summed below the graph.
let [<Literal>] private HandleWords = 1
let [<Literal>] private ClosureWords = 2
let [<Literal>] private ViewWords = 5

/// The aggregate types the graph reaches, each with the key `Layouts` holds it under.
[<RequireQualifiedAccess>]
type private Aggregate =
    | Record of name: string * fields: (string * NativeType) list
    | Union of name: string * cases: (string * (string option * NativeType) list) list
    | Tuple of key: string * elements: NativeType list
    | Option of key: string * inner: NativeType
    | Result of key: string * ok: NativeType * error: NativeType

/// What the pass reads of the graph once.
type private Placer = {
    Graph: SemanticGraph
    Context: PlatformContext option
    /// The declared Pointer width in bytes; None on fabric or where the description declares none.
    PointerBytes: int option
    /// Per tuple type (rendered), per position: the join of the element's range over every
    /// reachable construction of a tuple of that type; a position nothing constructs is Empty.
    TupleRanges: Map<string, ValueRange list>
}

/// The rendered key of a type (as `ElementRanges` keys an element type).
let private keyOf (ty: NativeType) : string = formatType (applySubst ty)

/// The union cases a type constructor's definition declares, if it is a union.
let private unionCasesOf (graph: SemanticGraph) (name: string) : (string * (string option * NativeType) list) list option =
    match SemanticGraph.recallType name graph |> Option.bind (fun id -> SemanticGraph.tryGetNode id graph) with
    | Some { Kind = SemanticKind.TypeDef (_, TypeDefKind.UnionDef cases, _) } -> Some cases
    | _ -> None

/// The aggregate a type is, if it is one the pass places.
let private aggregateOf (graph: SemanticGraph) (ty: NativeType) : Aggregate option =
    match applySubst ty with
    | NativeType.TTuple (elements, _) as t -> Some (Aggregate.Tuple (keyOf t, elements))
    | NativeType.TApp (tycon, [ inner ]) as t when tycon.Name = "option" || tycon.Name = "voption" -> Some (Aggregate.Option (keyOf t, inner))
    | NativeType.TApp (tycon, [ ok; err ]) as t when tycon.Name = "Result" || tycon.Name = "result" -> Some (Aggregate.Result (keyOf t, ok, err))
    | NativeType.TApp (tycon, _) ->
        match SemanticGraph.tryGetRecordFields tycon.Name graph with
        | Some fields -> Some (Aggregate.Record (tycon.Name, fields))
        | None ->
            match unionCasesOf graph tycon.Name with
            | Some cases -> Some (Aggregate.Union (tycon.Name, cases))
            | None -> None
    | NativeType.TUnion (tycon, cases) ->
        Some (Aggregate.Union (tycon.Name, cases |> List.map (fun c -> c.Name, c.Fields)))
    | _ -> None

let private aggregateKey (a: Aggregate) : string =
    match a with
    | Aggregate.Record (name, _) | Aggregate.Union (name, _) -> name
    | Aggregate.Tuple (key, _) | Aggregate.Option (key, _) | Aggregate.Result (key, _, _) -> key

/// The types an aggregate's placement reads: its fields, elements or payloads.
let private constituents (a: Aggregate) : NativeType list =
    match a with
    | Aggregate.Record (_, fields) -> fields |> List.map snd
    | Aggregate.Union (_, cases) -> cases |> List.collect (fun (_, fields) -> fields |> List.map snd)
    | Aggregate.Tuple (_, elements) -> elements
    | Aggregate.Option (_, inner) -> [ inner ]
    | Aggregate.Result (_, ok, err) -> [ ok; err ]

/// Every aggregate a type mentions, itself included, through its arguments, fields, elements and
/// payloads; keyed, so a recursive type is visited once.
let rec private collect (graph: SemanticGraph) (acc: Map<string, Aggregate>) (ty: NativeType) : Map<string, Aggregate> =
    let ty = applySubst ty
    let acc =
        match aggregateOf graph ty with
        | Some a when not (Map.containsKey (aggregateKey a) acc) ->
            constituents a |> List.fold (collect graph) (Map.add (aggregateKey a) a acc)
        | _ -> acc
    match ty with
    | NativeType.TApp (_, args) -> args |> List.fold (collect graph) acc
    | NativeType.TFun (d, r) -> collect graph (collect graph acc d) r
    | NativeType.TTuple (elements, _) -> elements |> List.fold (collect graph) acc
    | NativeType.TByref (e, _) | NativeType.TNativePtr e | NativeType.TLazy e | NativeType.TSeq e
    | NativeType.TSeqEnumerator e | NativeType.TList e | NativeType.TSet e -> collect graph acc e
    | NativeType.TMap (k, v) -> collect graph (collect graph acc k) v
    | NativeType.TForall (_, body) -> collect graph acc body
    | NativeType.TAnon (fields, _) -> fields |> List.fold (fun acc (_, t) -> collect graph acc t) acc
    | _ -> acc

//-------------------------------------------------------------------------
// Slots
//-------------------------------------------------------------------------

/// The slot of an integer of the bare kind with the given range: the representation its range
/// selects (`RangeAnalysis.heldWidthOf`, the one site for an unobservable range on a core), with
/// the declared representation's name on a core; on fabric the range's own width.
let private integerSlot (p: Placer) (range: ValueRange) : SettledSlot =
    match RangeAnalysis.heldWidthOf p.Graph range with
    | Some bits -> SettledSlot.Integer (bits, RangeAnalysis.selectedRepresentationOf p.Graph range |> Option.map (fun r -> r.Name))
    | None -> SettledSlot.Opaque (sprintf "an integer of the unobservable range %s" (ValueRange.render range))

/// The slot of a width-named integer carrier: its own representation (interim, CS-12).
let private carrierSlot (p: Placer) (kind: NTUKind) (bits: int) : SettledSlot =
    match p.Context |> Option.bind (fun ctx -> RangeSources.representationOfKind ctx kind) with
    | Some r -> SettledSlot.Integer (r.Bits, Some r.Name)
    | None -> SettledSlot.Integer (bits, None)

/// The slot of a value of the given kind; `range` is the settled range of the field or position
/// for an integer of the bare kind.
let private slotOfKind (p: Placer) (range: ValueRange) (kind: NTUKind) : SettledSlot =
    match kind with
    | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)
    | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register) -> integerSlot p range
    | NTUKind.NTUint (NTUWidth.Fixed bits) | NTUKind.NTUuint (NTUWidth.Fixed bits) -> carrierSlot p kind bits
    | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer)
    | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer)
    | NTUKind.NTUsize | NTUKind.NTUdiff | NTUKind.NTUptr | NTUKind.NTUfnptr -> SettledSlot.Pointer HandleWords
    | NTUKind.NTUfloat (NTUWidth.Fixed bits) | NTUKind.NTUposit (NTUWidth.Fixed bits, _) -> SettledSlot.Real bits
    | NTUKind.NTUfloat (NTUWidth.Resolved dim) | NTUKind.NTUposit (NTUWidth.Resolved dim, _) ->
        match p.Context |> Option.bind (fun ctx -> PlatformContext.tryWidth ctx (WidthDimension.name dim) |> Result.toOption) with
        | Some bits -> SettledSlot.Real bits
        | None -> SettledSlot.Opaque (sprintf "a real at the undeclared dimension '%s'" (WidthDimension.name dim))
    | NTUKind.NTUbool -> SettledSlot.Bool
    | NTUKind.NTUchar -> SettledSlot.Char
    | NTUKind.NTUunit -> SettledSlot.Unit
    | NTUKind.NTUstring | NTUKind.NTUarray | NTUKind.NTUlazy | NTUKind.NTUseq -> SettledSlot.Pointer ViewWords
    | NTUKind.NTUlist | NTUKind.NTUmap | NTUKind.NTUset -> SettledSlot.Pointer HandleWords
    | NTUKind.NTUdecimal | NTUKind.NTUuuid | NTUKind.NTUdatetime | NTUKind.NTUtimespan ->
        SettledSlot.Opaque (sprintf "the kind %A, which the CPU leg does not place" kind)

/// The slot of a value of the given type; `range` is the settled range of the field or position.
let rec private slotOf (p: Placer) (range: ValueRange) (ty: NativeType) : SettledSlot =
    let ty = applySubst ty
    match ty with
    | NativeType.TVar _ -> SettledSlot.Opaque (sprintf "the unresolved type variable %s" (formatType ty))
    | NativeType.TForall (_, body) -> slotOf p range body
    | NativeType.TFun _ -> SettledSlot.Pointer ClosureWords
    | NativeType.TTuple _ | NativeType.TAnon _ | NativeType.TUnion _
    | NativeType.TLazy _ | NativeType.TSeq _ | NativeType.TSeqEnumerator _ -> SettledSlot.Pointer ViewWords
    | NativeType.TNativePtr _ | NativeType.TByref _ | NativeType.TList _ | NativeType.TMap _ | NativeType.TSet _ -> SettledSlot.Pointer HandleWords
    | NativeType.TMeasure _ | NativeType.TError _ -> SettledSlot.Opaque (formatType ty)
    | NativeType.TNum _ | NativeType.TApp _ ->
        match Types.tryGetNTUKind ty with
        | Some kind -> slotOfKind p range kind
        | None ->
            match ty with
            | NativeType.TApp (tycon, _) ->
                match aggregateOf p.Graph ty with
                | Some _ -> SettledSlot.Pointer ViewWords
                | None ->
                    // a handle or a compound of words, by the layout family the type declares
                    match TypeLayout.baseLayout tycon.Layout with
                    | TypeLayout.PlatformWord -> SettledSlot.Pointer HandleWords
                    | TypeLayout.FatPointer -> SettledSlot.Pointer 2
                    | TypeLayout.NTUCompound n -> SettledSlot.Pointer n
                    | TypeLayout.Record | TypeLayout.Union -> SettledSlot.Pointer ViewWords
                    | _ -> SettledSlot.Opaque (formatType ty)
            | _ -> SettledSlot.Opaque (formatType ty)

/// The size and alignment of a slot on a core, in bytes: an integer's representation, a
/// pointer-sized field's words at the declared Pointer width (alignment one word), a bool one
/// byte, a char and the unit four, a real its bits. None on fabric or for an opaque slot.
let private extentOf (p: Placer) (slot: SettledSlot) : (int * int) option =
    match p.PointerBytes, slot with
    | None, _ -> None
    | _, SettledSlot.Opaque _ -> None
    | _, SettledSlot.Integer (bits, _) -> let b = max 1 ((bits + 7) / 8) in Some (b, b)
    | _, SettledSlot.Bool -> Some (1, 1)
    | _, SettledSlot.Char -> Some (4, 4)
    | _, SettledSlot.Unit -> Some (4, 4)
    | _, SettledSlot.Real bits -> let b = max 1 ((bits + 7) / 8) in Some (b, b)
    | Some ptr, SettledSlot.Pointer words -> Some (words * ptr, ptr)

let private alignUp (offset: int) (align: int) : int =
    if align <= 1 then offset else ((offset + align - 1) / align) * align

/// The fields of a record or tuple tiled in declaration order: each at the next offset aligned
/// to its slot's alignment, the aggregate aligned to its widest field, its size rounded up to
/// that alignment. A field with no extent (fabric, an opaque slot) leaves every offset and the
/// size unsettled.
let private tile (p: Placer) (fields: (string * SettledSlot) list) : SettledLayout =
    let extents = fields |> List.map (fun (_, slot) -> extentOf p slot)
    if extents |> List.exists Option.isNone then
        SettledLayout.Record (fields |> List.map (fun (name, slot) -> { Name = name; Slot = slot; Offset = None; Size = None; Align = None }), None, None)
    else
        let placed, cursor, maxAlign =
            List.zip fields extents
            |> List.fold (fun (acc, cursor, maxAlign) ((name, slot), extent) ->
                let (size, align) = Option.get extent
                let offset = alignUp cursor align
                ({ Name = name; Slot = slot; Offset = Some offset; Size = Some size; Align = Some align } :: acc, offset + size, max maxAlign align)) ([], 0, 1)
        SettledLayout.Record (List.rev placed, Some (alignUp cursor maxAlign), Some maxAlign)

/// A union's layout: one byte of tag at offset zero, the payload slot of the widest case at
/// offset one, alignment one (the leg's byte-buffer realisation, its payloads read through typed
/// views). A case with several fields carries them as one tuple payload.
let private union (p: Placer) (cases: (string * SettledSlot option) list) : SettledLayout =
    let payloads = cases |> List.choose snd
    let extents = payloads |> List.map (extentOf p)
    if extents |> List.exists Option.isNone then SettledLayout.Union (cases, None, None, None)
    else
        let widest = extents |> List.choose id |> List.map fst |> List.fold max 0
        SettledLayout.Union (cases, Some 1, Some (1 + widest), Some 1)

/// The range a field or position of the bare integer kind holds; Empty where nothing constructs it.
let private fieldRange (p: Placer) (typeName: string) (field: string) : ValueRange =
    p.Graph.FieldRanges.Value
    |> Map.tryFind typeName
    |> Option.bind (Map.tryFind field)
    |> Option.defaultValue ValueRange.Empty

let private tupleRange (p: Placer) (key: string) (index: int) : ValueRange =
    Map.tryFind key p.TupleRanges
    |> Option.bind (List.tryItem index)
    |> Option.defaultValue ValueRange.Empty

/// The payload slot of a union case: one field's slot, several fields' as one tuple payload
/// (a view), none for a case without a payload. A union payload of the bare integer kind has no
/// settled range in this changeset (a DU payload is unobservable, CS-10 owed) and is held through
/// the interim word.
let private payloadSlot (p: Placer) (fields: (string option * NativeType) list) : SettledSlot option =
    match fields with
    | [] -> None
    | [ (_, ty) ] -> Some (slotOf p ValueRange.Unbounded ty)
    | _ -> Some (SettledSlot.Pointer ViewWords)

let private place (p: Placer) (a: Aggregate) : SettledLayout =
    match a with
    | Aggregate.Record (name, fields) ->
        tile p (fields |> List.map (fun (field, ty) -> field, slotOf p (fieldRange p name field) ty))
    | Aggregate.Tuple (key, elements) ->
        tile p (elements |> List.mapi (fun i ty -> sprintf "Item%d" (i + 1), slotOf p (tupleRange p key i) ty))
    | Aggregate.Union (_, cases) ->
        union p (cases |> List.map (fun (caseName, fields) -> caseName, payloadSlot p fields))
    | Aggregate.Option (_, inner) ->
        union p [ ("None", None); ("Some", payloadSlot p [ (None, inner) ]) ]
    | Aggregate.Result (_, ok, err) ->
        union p [ ("Ok", payloadSlot p [ (None, ok) ]); ("Error", payloadSlot p [ (None, err) ]) ]

//-------------------------------------------------------------------------
// Entry
//-------------------------------------------------------------------------

/// Settle the layout of every aggregate type the reachable graph mentions and write the map to
/// `Layouts`. Runs after `PlatformDeclaration.fill` and `RangeAnalysis.run`, on every substrate.
let settle (context: PlatformContext option) (graph: SemanticGraph) : SemanticGraph =
    let reachable = graph.Nodes |> Map.toList |> List.map snd |> List.filter (fun n -> n.IsReachable)
    let tupleRanges =
        reachable
        |> List.fold (fun (acc: Map<string, ValueRange list>) node ->
            match node.Kind, applySubst node.Type with
            | SemanticKind.TupleExpr elements, (NativeType.TTuple (elementTypes, _) as t) when elements.Length = elementTypes.Length ->
                let key = keyOf t
                let ranges =
                    elements |> List.map (fun e ->
                        SemanticGraph.tryGetNode e graph |> Option.bind (fun n -> n.ValueRange) |> Option.defaultValue ValueRange.Empty)
                let joined =
                    match Map.tryFind key acc with
                    | Some existing when existing.Length = ranges.Length -> List.map2 ValueRange.join existing ranges
                    | _ -> ranges
                Map.add key joined acc
            | _ -> acc) Map.empty
    let placer = {
        Graph = graph
        Context = context
        PointerBytes =
            context
            |> Option.filter (fun ctx -> PlatformContext.substrateKind ctx <> SubstrateKind.FPGA)
            |> Option.bind (fun ctx -> PlatformContext.pointerSize ctx |> Result.toOption)
        TupleRanges = tupleRanges
    }
    let aggregates =
        reachable
        |> List.fold (fun acc node ->
            let acc = collect graph acc node.Type
            match node.Kind with
            | SemanticKind.Lambda (parameters, _, _, _, _) -> parameters |> List.fold (fun acc (_, ty, _) -> collect graph acc ty) acc
            | SemanticKind.TypeDef (_, TypeDefKind.RecordDef fields, _) -> fields |> List.fold (fun acc (_, ty) -> collect graph acc ty) acc
            | SemanticKind.TypeDef (_, TypeDefKind.UnionDef cases, _) ->
                cases |> List.fold (fun acc (_, fields) -> fields |> List.fold (fun acc (_, ty) -> collect graph acc ty) acc) acc
            | _ -> acc) Map.empty
    let layouts = aggregates |> Map.map (fun _ a -> place placer a)
    { graph with Layouts = lazy layouts }

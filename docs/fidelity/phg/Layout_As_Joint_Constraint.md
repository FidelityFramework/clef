# Bringing Layout Up: Memory Layout as a Joint Constraint in the PSG

> Design of record. Companion to `PSG_to_PHG_Plan.md` (which places this work at
> Phase 2) and `Composer/docs/Witness_Boundary_Audit.md` (which measures the
> state this replaces).

## 1. The problem, stated as it actually is

Layout is computed in Alex, at final witnessing to emission as MLIR, by five unrelated pieces of code that
disagree with each other.

| Site | What it decides | Model |
|---|---|---|
| `LambdaWitness.fs:546-632` | closure slot byte offsets (construction) | mutable accumulator over `mlirTypeSizeForArch` |
| `ClosurePatterns.fs:226-268` | closure slot byte offsets (extraction) | a **second, independent** walk |
| `RecordPatterns.fs:28-29` | record field offsets | `mlirTypeSize` (arch-blind) |
| `OptionWitness.fs:38` | option representation | `1 + mlirTypeSize` |
| `TypeMapping.fs:368-470` | DU, tuple, lazy, seq, enumerator offsets | `mlirTypeSizeForArch`, plus estimation at `:260-267` |

Three size models are live at once (`mlirTypeSize` says a memref is 40 bytes,
`mlirTypeSizeForArch` says 5 words, the dead `computeSize` says 32). Records and
closures containing the same field type get different sizes for it. The DU path
takes `List.tryHead` of case payloads where it needs `max` (`TypeMapping.fs:387`,
against `max` at `:244`), so any union whose first payload case is not its
largest is under-allocated.

None of this is visible to a proof. `CaptureSlot` carries no offset, so there is
nothing for an obligation to cite. Callsheet families 8, 9, 10 and 11 are all
blocked on the same sentence: *"`ClosureLayout`/`DULayout` heap sequences into
graph structure."*

The clef side is not innocent. `computeRecordLayout` (`NativeTypes.fs:1196`)
opens with `let wordSize = 8` — *"64-bit platform constants"* — and takes no
`PlatformContext`, though the graph carries one. `SemanticNode.LayoutHint` exists
and is set at exactly one construction site; Alex never reads it.

## 2. What replaces it

**One hyperedge per aggregate, whose annotation is simultaneously the layout and
the proposition about the layout.** This is invariant I3: deciding a placement
and proving it sound are the same act at saturation.

### 2.1 The edge

For every aggregate node — closure environment, record, DU case, tuple, lazy
thunk, seq frame, continuation frame:

```
f_layout = (S_f, t_f, lambda_f)

  S_f      the constituent nodes in slot order
           closure  -> the captured bindings
           record   -> the field value nodes
           DU       -> the case payload nodes
           frame    -> the live-across set of the segment
  t_f      the aggregate node
  lambda_f a LayoutAnnotation (2.2)
```

`S_f` is the field list. It is finite and fixed at elaboration, which is exactly
invariant **I1** — the finiteness lemma DTS/DMM §3.2.1 names. A linked
environment would forfeit it; a flat one is what makes every obligation below
quantifier-free.

Arity is `|S_f|`, genuinely > 1. A closure over four captures is one edge of
arity 4, not four edges — the extent and disjointness claims are joint over all
four and do not decompose into pairwise facts.

### 2.2 The annotation

```fsharp
/// How a slot is held. Mirrors CaptureInfo.IsMutable, decided in CCS.
[<RequireQualifiedAccess>]
type SlotMode = ByValue | ByRef

/// A fixed prefix the aggregate carries before its slots.
/// The literal shapes clef-lang-spec closure-representation.md 7 already fixes.
[<RequireQualifiedAccess>]
type PrefixShape =
    | None                       // record, tuple, closure environment: {slots...}
                                 //   (the function value is the other half of the pair, never a slot)
    | LazyThunk                  // lazy:       {computed, value, slots...}
    | SeqFrame                   // seq:        {state, current, slots...}
    | Discriminant of states:int // suspension: {state, slots...}
    | Tag of caseCount:int       // DU:         {tag, payload}

/// One settled slot. Every field is a literal at saturation.
type SlotPlacement = {
    Source: NodeId
    Ordinal: int
    ByteOffset: int
    ByteSize: int
    Align: int
    Mode: SlotMode
}

/// The layout of one aggregate on one target. This value IS the layout and IS
/// the proposition; 3 reads it as the latter.
type LayoutAnnotation = {
    Prefix: PrefixShape
    PrefixBytes: int          // settled, not "// Approximate"
    Slots: SlotPlacement list
    Extent: int               // total bytes including tail padding
    Align: int
    Padding: (int * int) list // (offset, length) runs, so coverage is checkable
}
```

**Multi-target.** DTS/DMM §4.3 already puts a per-target reachability bitvector
on the edge. Layout follows the same rule rather than inventing another: `lambda_f`
carries `Map<TargetId, LayoutAnnotation>`. A single-target build has a
one-entry map. Alex reads the entry for the target it is emitting.

### 2.3 The one function that computes it

```fsharp
/// The single definition of placement. Replaces computeRecordLayout,
/// mlirTypeSize, mlirTypeSizeForArch, computeSize, structFieldByteOffset,
/// calculateFieldOffsetForArch, the two closure offset walks, and
/// OptionWitness's `1 + size`.
placeSlots
    : PlatformContext
   -> PrefixShape
   -> (NodeId * NativeType * SlotMode) list
   -> LayoutAnnotation
```

Sizes come from `PlatformContext.Dimensions` and `PointerAlign`, never from a
constant. `TypeLayout.PlatformWord`, `FatPointer` and `NTUCompound` resolve
**here**, at saturation, against the platform the graph carries.

DU payload size is `max` over case payloads by construction, so
`TypeMapping.fs:387`'s `tryHead` bug cannot be re-expressed. Records and
closures cannot disagree about a field's size because there is one function.

### 2.4 The joint constraint

The same `LayoutAnnotation`, read as a proposition. All QF_LIA over literals with
an enumerated source set, so all decidable in bounded time — callsheet family 9
verbatim, plus families 8 and 10.

| VC | Assertion | Guards |
|---|---|---|
| **VC-EXT** | `PrefixBytes + sum(ByteSize) + sum(padding) = Extent` | CWE-131 |
| **VC-DIS** | slot ranges pairwise disjoint | CWE-787 |
| **VC-COV** | slots + padding tile `[0, Extent)` exactly, no gap unaccounted | CWE-125 |
| **VC-ALIGN** | each `ByteOffset mod Align = 0`; each `Align` a power of two | CWE-787 |
| **VC-IDX** | extraction indices lie in `[PrefixBytes, Extent)` | CWE-125 |
| **VC-TAG** | (DU) `tag` in `[0, caseCount)`, payload within the case struct | CWE-787 |
| **VC-ARENA** | (escaping) `pos + Extent <= arena capacity` | CWE-122 |

VC-DIS at arity *n* is `n(n-1)/2` pairwise claims asserted **jointly**; it is the
same shape as HelloProof's `layout_user_strings`, which quantifies over five
storages and ten pairs and is irreducible to a clique.

### 2.5 Projection onto alpha, and what Alex witnesses via the zipper

Invariant **I4** governs the crossing: a hyperedge is never a query target for
the emission traversal. Its consequence reaches Alex only as saturated
annotations on the nodes it governs.

So each `SlotPlacement` projects onto its `Source` node, and `Extent`/`Align`
project onto `t_f`. The carrier already exists and is unread:
`SemanticNode.LayoutHint: TypeLayout option`. It widens to hold a
`SlotPlacement` and an aggregate `LayoutAnnotation`.

`LambdaWitness`'s construction loop becomes a read:

```fsharp
// before: a mutable accumulator, and a second independent walk on extraction
let mutable captureByteOffset = sizeOf codePtrTy
...
captureByteOffset <- captureByteOffset + sizeOf cap.SlotType

// after: one settled list, read by both sides
for slot in layout.Slots do
    emit (MemRefOp.ReinterpretCast(view, envMemref, slot.ByteOffset, slot.ByteSize))
    emit (MemRefOp.Store(valueOf slot.Source, view))
```

No `sizeOf`. No accumulator. Construction and extraction read the same list, so
they cannot disagree — today they are two independent computations with nothing
holding them together.

## 3. The structural change this forces

`computeRecordLayout` runs today during **type checking**, in `NativeService`,
before the graph exists and before `PlatformContext` is reachable. Placement
cannot stay there: it needs the platform, and it needs the constituent *nodes*
to hang slots on.

So the settled placement moves to cross-application via **saturation**, and `TypeConRef.Layout` becomes
what its neighbours already claim to be — provisional and symbolic, an identity
fact, not a byte count. `TypeLayout.PlatformWord` and `FatPointer` are already
written that way; `Inline(size, align)` computed against a hardcoded 8 is the
anomaly, not the rule.

That resolves the contradiction the audit found. `NativeTypes.fs:655-656` says
*"CCS preserves type identity; Alex resolves to concrete size"*;
`CCS_Architecture.md:205` says Alex does not compute or decide. Both can hold
once the resolution point is named: **CCS preserves identity at type-check time
and resolves size at saturation, because that is where the platform is.** Alex
resolves nothing. The `NativeTypes.fs` comments are corrected as this lands.

## 4. The two dispatches

One annotation, read twice against one set of anchor names:

1. **Design time.** Saturation closes the layout edge; its VCs emit SMT-LIB2;
   cvc5 discharges. Continuous, in Lattice, as source is edited.
2. **Build time.** The artifact-side re-check reads the emitted
   `memref.view`/`reinterpret_cast` offsets out of the witnessed MLIR and
   re-derives the same VCs under the same anchor names. Agreement is twin
   pairing (a hyperedge of arity 2); a design-time VC with no build-time twin is
   a detected leak by the same mechanism that discharges the proof.

This is what `layout_user_strings` already does for rodata and what nothing does
for closures, records or DUs.

## 5. Sequencing

1. `placeSlots` in CCS, taking `PlatformContext`. Land it beside the existing
   code and assert it reproduces today's offsets for the single x86_64 target —
   the DU `max`/`tryHead` divergence is the one expected difference, and it is a
   fix.
2. Layout hyperedge in `F`; project `SlotPlacement` onto `LayoutHint`.
3. Alex reads: `LambdaWitness`, `ClosurePatterns`, `RecordPatterns`,
   `OptionWitness`, `TypeMapping` offset paths become lookups. Delete
   `TypeSizing.fs` (dead), collapse `mlirTypeSize` and `mlirTypeSizeForArch`.
4. VC emission at saturation; ledger entry per aggregate.
5. Build-time re-derivation and twin pairing.

Steps 1–3 are the drain and are checkable by transcript identity. Steps 4–5 add
obligations and are checkable by the ledger growing where the callsheet says it
should — families 9 and 10 moving from *a priori-pending* to *generated*.

## 6. Verification

- **Transcript identity** on the samples through step 3: layout moved, output
  unchanged. The DU case is the deliberate exception.
- **A DU whose first payload case is not its largest** must round-trip. Today it
  is under-sized. This is the regression test the bug never had.
- **A record and a closure sharing a field type** must agree on that field's
  size. Today they do not.
- **cvc5 `unsat`** on every emitted layout VC; **`sat`** on a deliberately
  corrupted annotation (overlapping slots, wrong extent), so the obligations are
  shown to have teeth.

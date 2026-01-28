# Collection Witness Compositional Design

**Date:** January 28, 2026  
**Context:** Clean-room witness rebuild following Elements→Patterns→Witnesses architecture

---

## Architectural Principle

Witnesses are **thin compositional layers** that observe PSG structure and delegate to shared Patterns.

```
PSG Structure (from FNCS + Baker + PSGElaboration)
    ↓
Witness (XParsec match, ~15-25 lines)
    ↓
Pattern (shared MLIR emission, ~50 lines)
    ↓
Elements (atomic MLIR ops, module internal)
    ↓
MLIR Output
```

**Key Insight:** Elements and Patterns are **shared infrastructure**. Collection witnesses don't build primitives; they **compose existing patterns**.

---

## PSG Structure for Collection Primitives

### Empty Collections (List/Map/Set.empty)

**PSG Structure:**
```
Node: Intrinsic { Module = List/Map/Set; Operation = "empty" }
Children: None
Type: TList<T> / TMap<K,V> / TSet<T>
SSAs: 1 (the result)
```

**Witness Pattern:** `pFlatClosure` with zero captures
**MLIR Result:** `{code_ptr}` struct via Undef

### Structural Access (List.head, Map.key, Set.value)

**PSG Structure:**
```
Node: Intrinsic { Operation = "head"/"key"/"value" }
Children: [collectionNodeId]
SSAs: 2 (GEP result, Load result)
```

**Witness Pattern:** `pFieldAccess` on field index
**MLIR Result:** GEP + Load extracting field

### Structural Construction (List.cons, Map.node, Set.node)

**PSG Structure:**
```
Node: Intrinsic { Operation = "cons"/"node" }
Children: [field values...]
SSAs: N+1 (Undef + N InsertValues)
```

**Witness Pattern:** 
- `List.cons` → `pFlatClosure` with captures (head, tail)
- `Map.node`/`Set.node` → `pRecordStruct` with fields

**MLIR Result:** Struct construction via Undef + InsertValue chain

### isEmpty Operations

**PSG Structure:** Baker-decomposed (varies)
- May be: IfThenElse checking structure
- May be: Function call through code_ptr
- Depends on Baker's decomposition strategy

**Witness Behavior:** Returns `TRError` - this structure is witnessed by other patterns (IfThenElse, Application)

---

## Existing Pattern Coverage

From `ElisionPatterns.fs`:

| Collection Op | Pattern | Status |
|--------------|---------|--------|
| empty | `pFlatClosure` | ✅ Exists |
| cons | `pFlatClosure` | ✅ Exists |
| head/tail/key/value | `pFieldAccess` | ✅ Exists |
| node | `pRecordStruct` | ✅ Exists |
| isEmpty | N/A | Baker decomposes |

**Result:** No new Patterns needed! All collection primitives compose from existing patterns.

---

## Witness Structure Template

Following `LazyWitness.fs` canonical pattern (~120 lines total):

```fsharp
module Alex.Witnesses.MapWitness

open XParsec
open Alex.XParsec.PSGCombinators
open Alex.Patterns.ElisionPatterns
open Alex.Traversal.TransferTypes
open Alex.Dialects.Core.Types

module SSAAssign = PSGElaboration.SSAAssignment

// ═══════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════

let private getNodeSSAs (nodeId: NodeId) (ssa: SSAAssign.SSAAssignment) : SSA list =
    match SSAAssign.lookupSSAs nodeId ssa with
    | Some ssas -> ssas
    | None -> []

// ═══════════════════════════════════════════════════════════
// CATEGORY-SELECTIVE WITNESS
// ═══════════════════════════════════════════════════════════

let private witnessMap (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    // Match intrinsic operations via XParsec
    match tryMatch pIntrinsic ctx.Graph node ctx.Zipper ctx.Coeffects.Platform with
    | Some (info, _) when info.Module = IntrinsicModule.Map ->
        match info.Operation with
        | "empty" -> witnessMapEmpty ctx node
        | "key" -> witnessMapKey ctx node
        | "value" -> witnessMapValue ctx node
        // ... other primitives
        | _ -> WitnessOutput.skip
    | _ -> WitnessOutput.skip

// Each primitive is ~15-25 lines, delegates to Pattern
let private witnessMapEmpty ctx node = ...
let private witnessMapKey ctx node = ...

// ═══════════════════════════════════════════════════════════
// PUBLIC API
// ═══════════════════════════════════════════════════════════

let nanopass : Nanopass = {
    Name = "Map"
    Witness = witnessMap
}
```

---

## SSA Contract from PSGElaboration

From `SSAAssignment.fs` (lines 507-519):

```fsharp
| IntrinsicModule.Map, "empty" -> 1      // Undef
| IntrinsicModule.Map, "isEmpty" -> 2    // Baker decomposes
| IntrinsicModule.Map, "key" -> 2        // GEP + Load
| IntrinsicModule.Map, "value" -> 2      // GEP + Load
| IntrinsicModule.Map, "left" -> 2       // GEP + Load
| IntrinsicModule.Map, "right" -> 2      // GEP + Load
| IntrinsicModule.Map, "height" -> 2     // GEP + Load
| IntrinsicModule.Map, "node" -> 6       // Undef + 5 InsertValues
```

Witnesses read pre-assigned SSAs via `lookupSSAs`.

---

## XParsec Combinators Needed

All exist in `PSGCombinators.fs`:
- `pIntrinsic` → Match any intrinsic node
- `pIntrinsicModule` → Match specific module
- `getUserState` → Access platform info
- `tryMatch` → Run parser with state

**No new combinators needed.**

---

## Implementation Plan

1. **MapWitness.fs** (8 primitives × 20 lines = ~160 lines)
   - empty, isEmpty, key, value, left, right, height, node

2. **ListWitness.fs** (5 primitives × 20 lines = ~100 lines)
   - empty, isEmpty, head, tail, cons

3. **SetWitness.fs** (7 primitives × 20 lines = ~140 lines)
   - empty, isEmpty, value, left, right, height, node

**Total:** ~400 lines (down from 5,773 lines - 93% reduction)

---

## Key Architectural Decisions

### Decision 1: isEmpty Returns TRError

**Rationale:** Baker decomposes isEmpty into control flow (IfThenElse) or function calls. These structures are witnessed by OTHER witnesses (ControlFlowWitness, ApplicationWitness). Collection witnesses don't need to handle decomposed operations.

### Decision 2: No Direct Element Usage

**Enforcement:** Witnesses import only:
- `Alex.XParsec.PSGCombinators`
- `Alex.Patterns.ElisionPatterns`
- `Alex.Traversal.TransferTypes`

Elements are `module internal` to Patterns - witnesses physically cannot import them.

### Decision 3: Flat Closures for Empty

**Rationale:** Everything is a flat closure. Empty collections = `{code_ptr}` with zero captures. No null pointers, no special cases, one universal pattern.

### Decision 4: SSAs from Coeffects

**Rationale:** PSGElaboration pre-computed SSAs. Witnesses are **observers**, not **computers**. Read what's there, don't recompute.

---

## Validation Strategy

1. **Compile sample 13a_SimpleCollections**
2. **Inspect MLIR output** - verify canonical structure:
   - Empty → Undef with struct type
   - Field access → GEP + Load
   - Construction → Undef + InsertValue chain
3. **Execute binary** - verify correct behavior
4. **Line count check** - MapWitness < 200 lines

---

## Sources

- `src/MiddleEnd/Alex/Witnesses/LazyWitness.fs` - Canonical witness pattern
- `src/MiddleEnd/Alex/Witnesses/SeqWitness.fs` - Recent compositional example
- `src/MiddleEnd/Alex/Patterns/ElisionPatterns.fs` - Shared pattern library
- `src/MiddleEnd/PSGElaboration/SSAAssignment.fs` - SSA cost table
- `~/repos/fsnative/src/Compiler/Baker/Ingredients/Primitives.fs` - Baker primitive definitions
- `docs/PRDs/C-04-CoreCollections.md` - Collection type specifications
- Memory: `flat_closure_universal_pattern` - Architectural foundation
- Memory: `baker_collection_primitives_architecture` - Pipeline understanding
- Memory: `alex_compositional_architecture_elements_patterns_witnesses` - Three-tier model

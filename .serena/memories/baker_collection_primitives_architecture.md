# Baker Collection Primitives - The Three-Stage Pipeline

**Date:** January 28, 2026  
**Critical:** This describes what Alex actually witnesses for collections

---

## The Complete Pipeline

### Stage 1: FNCS FrontEnd

**PSG Construction:** FCS → Basic PSG structure

**Baker Saturation:** Decomposes high-level collection operations to primitives

Examples:
- `Map.add key value map` → Recursive lambda using `Map.isEmpty`, `Map.key`, `Map.node` primitives
- `List.map f xs` → Recursive lambda using `List.isEmpty`, `List.head`, `List.tail`, `List.cons`
- `Set.union s1 s2` → Recursive lambda using `Set.isEmpty`, `Set.value`, `Set.node`
- `Option.map f opt` → Pattern matching using `Option.none`, `Option.some`, `Option.isSome`

**Output:** Fully saturated PSG containing ONLY primitives (no high-level operations)

### Stage 2: Firefly MiddleEnd (PSGElaboration)

**SSAAssignment:** Computes SSA counts for ALL nodes, including Baker primitive intrinsics

**Other coeffects:** Mutability analysis, capture analysis, closure layouts, etc.

**Output:** Enriched PSG + TransferCoeffects

### Stage 3: Firefly Alex

**Three-tier witness structure:**
- Elements (module internal): Atomic MLIR ops
- Patterns (public): Composable semantic operations
- Witnesses (public): Thin observers using XParsec

**XParsec API:** Pattern-match the fully elaborated PSG

**Witnesses traverse:** The FULL PSG structure using XParsec patterns, including Baker primitive intrinsics, PSG structure from F# source, and elaborated nodes. NOT limited to just Baker primitives.

---

## Baker Primitive Intrinsics

These are what Alex witnesses. High-level operations are decomposed by Baker to primitives.

### Map Primitives

**Baker decomposes:** `Map.add`, `Map.tryFind`, `Map.containsKey`, `Map.remove`, `Map.keys`, `Map.values`

**Alex witnesses:**
- `Map.empty` → **flat closure with zero captures** (1 SSA: Undef { code_ptr })
- `Map.isEmpty` → **Baker decomposes to structural check** (SSA cost varies by Baker's decomposition)
- `Map.key` → GEP + load to extract key from AVL struct (2 SSAs)
- `Map.value` → GEP + load to extract value (2 SSAs)
- `Map.left` → GEP + load to extract left subtree (2 SSAs)
- `Map.right` → GEP + load to extract right subtree (2 SSAs)
- `Map.node` → undef + insertvalue chain to construct AVL node (5 SSAs)

**AVL struct layout:** `{key: K, value: V, left: ptr, right: ptr, height: i32}`

**CRITICAL:** Alex will NEVER see `Map.add`, `Map.tryFind`, etc. These are decomposed by Baker into recursive lambdas that use the primitives above.

### List Primitives

**Baker decomposes:** `List.map`, `List.filter`, `List.fold`, `List.rev`, `List.append`, `List.length`

**Alex witnesses:**
- `List.empty` → **flat closure with zero captures** (1 SSA: Undef { code_ptr })
- `List.isEmpty` → **Baker decomposes to structural check**
- `List.head` → GEP + load to extract head element (2 SSAs)
- `List.tail` → GEP + load to extract tail pointer (2 SSAs)
- `List.cons` → **flat closure with captures** (alloca + store code_ptr + store head + store tail)

**List cons layout:** `{code_ptr: ptr, head: T, tail: List<T>}`

**CRITICAL:** Alex will NEVER see `List.map`, `List.filter`, etc. These are decomposed by Baker.

### Set Primitives

**Baker decomposes:** `Set.add`, `Set.contains`, `Set.remove`, `Set.union`, `Set.intersect`, `Set.difference`

**Alex witnesses:**
- `Set.empty` → **flat closure with zero captures** (1 SSA: Undef { code_ptr })
- `Set.isEmpty` → **Baker decomposes to structural check**
- `Set.value` → GEP + load to extract value from AVL struct (2 SSAs)
- `Set.left` → GEP + load to extract left subtree (2 SSAs)
- `Set.right` → GEP + load to extract right subtree (2 SSAs)
- `Set.height` → GEP + load to extract height field (2 SSAs)
- `Set.node` → undef + insertvalue chain to construct AVL node (5 SSAs)

**AVL struct layout:** `{value: T, left: ptr, right: ptr, height: i32}`

**CRITICAL:** Alex will NEVER see `Set.union`, `Set.intersect`, etc. These are decomposed by Baker.

### Option Primitives

**Baker decomposes:** `Option.map`, `Option.bind`, `Option.defaultValue`, `Option.filter`

**Alex witnesses:**
- `Option.none` → DU with tag=0, no payload (3 SSAs: undef + tagConst + withTag)
- `Option.some` → DU with tag=1 + payload (4 SSAs: undef + tagConst + withTag + withPayload)
- `Option.isSome` → tag extraction + comparison (3 SSAs: extract + const + icmp)
- `Option.isNone` → tag extraction + comparison (3 SSAs: extract + const + icmp)

**CRITICAL:** Alex will NEVER see `Option.map`, `Option.bind`, etc. These are decomposed by Baker into pattern matching using the primitives above.

---

## What This Means for Witness Implementation

### WRONG Witness Structure (Current MapWitness.fs)

```fsharp
// ❌ WRONG - Has stubs for high-level operations that will never be witnessed
let witnessEmpty ... // ✅ Correct - this is a primitive
let witnessIsEmpty ... // ✅ Correct - this is a primitive

let witnessAdd ... // ❌ WRONG - Baker already decomposed this!
let witnessTryFind ... // ❌ WRONG - Will never be called!
let witnessContainsKey ... // ❌ WRONG - Already gone!
```

### CORRECT Witness Structure

```fsharp
// ✅ CORRECT - Witness ONLY Baker primitives
let witnessEmpty ... // primitive: null pointer
let witnessIsEmpty ... // primitive: null check
let witnessKey ... // primitive: field extraction
let witnessValue ... // primitive: field extraction
let witnessLeft ... // primitive: field extraction
let witnessRight ... // primitive: field extraction
let witnessNode ... // primitive: struct construction

// NO stubs for witnessAdd, witnessTryFind, etc.
// Those operations are GONE - decomposed by Baker
```

### Implementation Pattern

All collection witnesses should follow this structure:

1. **Witness Baker primitives** (empty, isEmpty, structural operations)
2. **Use XParsec** to pattern-match `SemanticKind.Intrinsic` nodes
3. **Delegate to Patterns** for MLIR emission
4. **Read SSAs** from pre-computed coeffects (via `requireSSA`/`requireSSAs`)

**DO NOT:**
- Have stubs for high-level operations (add, map, filter, etc.)
- Return `TRError "complex implementation pending"` for operations
- Try to "implement" operations that Baker already decomposed

---

## Sources

**Baker Primitives Definitions:**
- `/home/hhh/repos/fsnative/src/Compiler/Baker/Ingredients/Primitives.fs`
  - Lines 86-136: List primitives
  - Lines 142-176: Option primitives
  - Lines 400-449: Map primitives
  - Lines 480-548: Set primitives

**Baker Recipes (How high-level ops are decomposed):**
- `/home/hhh/repos/fsnative/src/Compiler/Baker/Recipes/MapRecipes.fs`
  - Lines 478-551: `binarySearchMap` (used by Map.tryFind)
  - Lines 566-649: `avlInsertMap` (used by Map.add)
  - Lines 369-448: `inOrderTraversalMap` (used by Map.toList)

**PSGElaboration SSA Assignment:**
- `/home/hhh/repos/Firefly/src/MiddleEnd/PSGElaboration/SSAAssignment.fs`
  - Lines 493-504: List intrinsic SSA costs
  - Lines 507-519: Map intrinsic SSA costs (NOTE: primitives like Map.key default to 20, should be 2)
  - Lines 522-533: Set intrinsic SSA costs
  - Lines 536-541: Option intrinsic SSA costs

---

## User Quote

"The entire point of PSG Elaboration and Saturation in FNCS is to provide a complete compute graph from the FrontEnd that is then fed into the MiddleEnd where the SSA assignment and other coeffects are handled to then go into Alex which is a three-tier witness structure using XParsec API to cleanly witness that fully enriched and elaborated PSG."

**Key Insight:** By the time Alex sees the PSG, Baker saturation has already decomposed ALL high-level collection operations into primitives. Alex witnesses the primitives, not the user-facing API.

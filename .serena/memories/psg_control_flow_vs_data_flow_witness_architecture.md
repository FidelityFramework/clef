# PSG Control Flow vs Data Flow: Witness Architecture

**Date:** 2026-02-03
**Context:** String.concat2 Orphaned Nodes Investigation
**Status:** Architectural Insight for Future Blog Entry

---

## The Problem

String.concat2 elaboration creates a recipe with side-effecting operations (memcpy) that must execute before the result (RecordExpr) is valid. Initial implementation resulted in 16 out of 29 recipe nodes being orphaned after fold-in - not reachable from entry points via Children edges.

**Key Error:**
```Error: [Intrinsic Fold-In] Recipe nodes not reachable from entry points! Created 29 new nodes but 16 are orphaned.```

---

## Root Cause: Representational Duality

The issue reveals a fundamental architectural insight about PSG's fluid representation model:

### PSG Expresses BOTH Control Flow AND Data Flow

From "Doubling Down on DMM and DTS":
> "The Program Semantic Graph to represent both control-flow (for CPU/sequential targets) and data-flow (for FPGA/spatial targets) interpretations of the same source program. Dimensional constraints are invariant across both interpretations. The pivot between representations preserves semantic meaning because dimensions survive the transformation."

### The Zipper Witnesses, It Does Not Decide

From "Learning to Walk":
> "The zipper witnesses, it does not decide... the photographer didn't choose the route. The path through the landscape was planned before the walk began... All decisions about ordering, about emission strategy, about what depends on what, were made during PSG construction. The walk simply witnesses those decisions and emits accordingly."

---

## The concat2 Recipe Structure

### Operations Created:
1. `fieldGet` operations to extract ptr/len from lhs and rhs strings
2. `add` operation to compute combined length
3. `stackAlloc` operation to allocate result buffer
4. **`memcpy` operation to copy lhs data** (side effect!)
5. `ptrAdd` operation to compute offset pointer
6. **`memcpy` operation to copy rhs data** (side effect!)
7. `RecordExpr` to build result fat pointer: `{ptr, len}`

### The Tension:

**Data Flow View:**
- RecordExpr depends on: resultPtr (data), combinedLen (data)
- Those are the "inputs" to construct the struct

**Control Flow View:**
- memcpy operations are imperative side effects
- They MUST execute before RecordExpr is valid
- But they return `unit` (no data dependency)

### Initial Bug:
```fsharp
let! _ = memcpy resultPtr lhsPtr lhsLen Types.uint8Type  // Bound to _, discarded!return! buildRecord [("ptr", resultPtr); ("len", combinedLen)] stringType
```

RecordExpr's Children = `[resultPtr, combinedLen]` (data dependencies only).
memcpy nodes orphaned because they're not in the data dependency graph!

---

## The Solution: Semantic Edges Establish Witnessing Order

### Children Field = Semantic Edges

The `Children` field in SemanticNode isn't just for data dependencies - it's the mechanism that establishes traversal order for the zipper witness!

From "Learning to Walk":
> "When the traversal encounters a VarRef node... It follows the edge to the definition and ensures that definition has been witnessed first. This is semantic edge following..."

The PSG zipper traverses post-order: visit Children before witnessing the parent. This works for BOTH:
- **Data dependencies:** RecordExpr needs resultPtr's value
- **Control dependencies:** RecordExpr needs memcpy side effects to complete

### Fixed Implementation:
```fsharp
let! memcpy1 = memcpy resultPtr lhsPtr lhsLen Types.uint8Type  // CAPTURE ID!
let! memcpy2 = memcpy offsetPtr rhsPtr rhsLen Types.uint8Type  // CAPTURE ID!return! buildRecordWithPrereqs
    [("ptr", resultPtr); ("len", combinedLen)]  // Field values (data flow)
    [memcpy1; memcpy2]                          // Prerequisites (control flow)
    stringType
```

RecordExpr's Children = `[memcpy1, memcpy2, resultPtr, combinedLen]`.

This means:
- **Reachability:** All nodes reachable from RecordExpr via transitive Children closure
- **Witnessing Order:** memcpy operations witnessed before RecordExpr
- **Correctness:** Side effects execute before result is constructed

---

## Architectural Principles Revealed

### 1. PSG is Fluid

PSG doesn't "decide" whether it's control flow or data flow. It can express BOTH simultaneously:
- Data dependencies via value-producing operations
- Control dependencies via Children edges to side-effecting operations

### 2. Children Edges = Witnessing Guarantees

The Children field isn't metadata - it's the architectural mechanism that ensures:
- Post-order traversal (children before parents)
- Reachability from entry points
- Correct execution ordering when witnessed by Alex/MLIR

### 3. Coeffects Pre-Compute, Zipper Witnesses

From the blog entries:
- **Before traversal:** Coeffects analysis establishes requirements, emission strategies, SSA assignments
- **During traversal:** Zipper navigates following semantic edges, emitting MLIR
- **Semantic edges:** Children relationships that survive as MLIR dependencies

### 4. Recipe Structure = Internal Connectivity

Recipes are **pure subgraphs** with:
- **Internal connectivity:** Correct Children relationships within the recipe
- **No external connections:** Parent = None for all recipe nodes
- **Replacement root:** The node that replaces the original application

**Fold-In's Job:**
- Update references in Kind and Children fields (cross-recipe dependencies)
- Establish Parent edges (back-pointers for bidirectional navigation)
- Validate reachability (all recipe nodes must be reachable)

---

## The buildRecordWithPrereqs Primitive

### Signature:
```fsharp
let buildRecordWithPrereqs
    (fields: (string * NodeId) list)
    (prereqs: NodeId list)
    (recordType: NativeType)
    : SaturationParser<NodeId>
```

### Semantics:
- `fields`: Data dependencies - the values for struct fields
- `prereqs`: Control dependencies - operations that must complete first
- Result: RecordExpr with Children = `prereqs @ fieldValues`

### Children Order:
Prerequisites FIRST, then field values. This ensures:
1. Side effects witnessed before result
2. All transitive dependencies reachable
3. Correct MLIR emission order (SSA form requires defs before uses)

---

## Cross-Recipe Dependencies

**Interesting Case:** Recipe #2 uses Recipe #1's result!

Sample 02 has TWO String.concat2 operations:
1. Node 585: `"Hello, " + name`
2. Node 588: `result_of_585 + "!"`

Recipe #2 creates:
```fsharp
let! lhsPtr = fieldGet lhsId "ptr" Types.nintType  // lhsId = 585 (replaced by 630!)
```

**After fold-in:**
- Original: `fieldGet 585 "ptr"` → Creates node 603 referencing 585
- Updated: `fieldGet 630 "ptr"` → Node 603 now references 630 (Recipe #1's result)

The updateKindRefs function (FoldIn.fs:81-82) handles this:
```fsharp
| SemanticKind.FieldGet (expr, fieldName) ->
    SemanticKind.FieldGet (update expr, fieldName)  // Rewrites 585 → 630
```

---

## Validation and Reachability

### collectReachableNodes Algorithm:
```fsharp
let rec traverse (visited: Set<NodeId>) (nodeId: NodeId) : Set<NodeId> =
    if Set.contains nodeId visited then
        visited
    else
        match Map.tryFind nodeId nodes with
        | None -> visited  // Node doesn't exist
        | Some node ->
            let visited' = Set.add nodeId visited
            node.Children |> List.fold traverse visited'  // Transitive closure

entryPoints |> List.fold traverse Set.empty
```

**Post-order traversal via Children edges:**
- Starts from entry points
- Recursively visits all Children (transitive closure)
- Returns set of all reachable nodes

**Validation:**
- Check: Are all recipe-created nodes in the reachable set?
- If not: Orphaned nodes indicate broken Children relationships
- Fail fast: Catch architectural bugs immediately

---

## MLIR Witnessing (Alex)

When Alex witnesses the PSG via Zipper:

1. **Navigate:** Zipper moves through graph (down to children, up to parents, lateral to siblings)
2. **Observe:** At each node, zipper observes coeffects (emission strategy, SSA ID, etc.)
3. **Emit:** Generate appropriate MLIR based on node kind and coeffects
4. **Order:** Post-order traversal ensures definitions before uses (SSA form)

**For concat2:**
- Witness memcpy1 → `llvm.call @memcpy(...)`
- Witness memcpy2 → `llvm.call @memcpy(...)`
- Witness RecordExpr → `llvm.mlir.undef` + `llvm.insertvalue` (build struct)

**Critical:** The Children edges ensure memcpy MLIR is emitted BEFORE the insertvalue instructions!

---

## Implications for Other Recipes

### When to Use buildRecordWithPrereqs:

**Use when:**
- Side-effecting operations must execute before result construction
- Examples: memcpy, memory writes, I/O operations, mutation

**Don't use when:**
- Pure data dependencies only
- Examples: arithmetic, field extraction, type conversions

### General Pattern:

```fsharp
saturation {
    // 1. Pure data dependencies
    let! dataValue1 = pureOperation x
    let! dataValue2 = pureOperation y
    
    // 2. Side-effecting operations (CAPTURE IDs!)
    let! sideEffect1 = impureOperation a b
    let! sideEffect2 = impureOperation c d
    
    // 3. Build result with prerequisites
    return! buildRecordWithPrereqs
        [("field1", dataValue1); ("field2", dataValue2)]  // Data deps
        [sideEffect1; sideEffect2]                         // Control deps
        resultType
}
```

---

## Key Takeaways

1. **PSG is fluid:** Can express BOTH control flow AND data flow simultaneously
2. **Children = Witnessing order:** Semantic edges establish traversal guarantees
3. **Zipper witnesses:** Doesn't decide order, observes pre-computed structure
4. **Coeffects before traversal:** All decisions made during PSG construction
5. **Recipes are subgraphs:** Internal connectivity correct, external connections via fold-in
6. **Validation is architectural:** Orphaned nodes = broken semantic edges

---

## Future Work

### Blog Entry: "Control Flow Meets Data Flow"

**Outline:**
1. The Mars Climate Orbiter vs The memcpy Orphan
2. PSG's Fluid Representation: Not Either/Or, But Both/And
3. The Photographer's Walk: Witnessing vs Deciding
4. Semantic Edges: More Than Parent/Child
5. Recipe Architecture: Pure Subgraphs with Guarantees
6. buildRecordWithPrereqs: Making Imperative Side Effects Explicit
7. Cross-Recipe Dependencies: Composing Subgraph Transformations
8. The Zipper's Gift: Traversal Without Central Dispatch

### Related Concepts:
- Dimensional types (preserve through compilation)
- Coeffects (requirements from context)
- Nanopass architecture (phase separation)
- SSA form via functional programming (Appel's equivalence)

---

## References

- Blog: "Doubling Down on DMM and DTS" - PSG fluid representation
- Blog: "Learning to Walk" - Zipper witness pattern, coeffects
- File: FoldIn.fs - Recipe fold-in and validation
- File: StringRecipes.fs - concat2 recipe implementation
- File: Primitives.fs - buildRecordWithPrereqs primitive


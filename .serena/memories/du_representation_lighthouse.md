# DU Representation Lighthouse

> **Purpose**: This memory is a "lighthouse" reference for building discriminated union (DU) representation with architectural integrity. It captures the design philosophy and specific implementation requirements.

## The Core Principle: Decisions in Baker, Not Alex

**Philosophy**: The PSG that flows from FNCS to Firefly/Alex should be "right" - Alex performs 1:1 translation to MLIR. Alex should NEVER make representation decisions or transform structure.

```
WRONG:  FNCS emits generic DU → Alex decides representation at emission time
RIGHT:  Baker decomposes DU → PSG contains explicit structure → Alex translates 1:1
```

This is the same principle behind the entire Firefly architecture: upstream components (FNCS/Baker) make semantic decisions, downstream components (Alex) perform mechanical translation.

## The Heterogeneous Payload Challenge

The critical architectural challenge for DUs like `Result<'T, 'E>`:

```fsharp
type Result<'T, 'E> =
    | Ok of 'T      // Payload: 'T (e.g., int → i64)
    | Error of 'E   // Payload: 'E (e.g., string → struct<ptr, i64>)
```

**The problem**: These payloads have incompatible shapes:
- `Ok(42)` → payload is `i64`  
- `Error("msg")` → payload is `struct<ptr, i64>`

**Why Alex can't fix this**: LLVM's `bitcast` only works for same-size compatible types (int↔float, ptr↔ptr). It CANNOT convert `struct<ptr, i64>` ↔ `i64`. Attempting this produces:

```
error: 'llvm.bitcast' op result #0 must be non-aggregate LLVM type, 
but got '!llvm.struct<(!llvm.ptr, i64)>'
```

**The insight**: This isn't a bug to patch - it's a signal that the structure must be decomposed UPSTREAM in Baker, not handled downstream in Alex witnesses.

## The Correct Architectural Approach

Baker decomposes implied structure through:

1. **Ingredients** - Intrinsics that create atomic operations
2. **Recipes** - XParsec combinators that pattern-match and rewrite

For heterogeneous DUs, Baker must:

1. **Recognize** the DU type and its case payloads
2. **Calculate** the representation (max-sized slot, tag width per platform policy)
3. **Emit** explicit structure into PSG that Alex can translate directly

### Example: Result Decomposition

Baker should transform:
```fsharp
match result with
| Ok value -> ... use value as int ...
| Error msg -> ... use msg as string ...
```

Into explicit PSG structure:
```
- Extract tag from result struct
- Branch on tag == 0 (Ok case):
    - Extract payload slot
    - Interpret as int (direct, no conversion needed)
- Branch on tag == 1 (Error case):
    - Extract payload slot  
    - Interpret as string (may need extraction from max-sized slot)
```

The key is that Baker knows the TYPES at decomposition time and can emit the correct extraction/interpretation operations.

## Platform-Aware Tag Width

DU tag width is a platform policy decision made in FNCS, not Alex:

```fsharp
// In PlatformTypes.fs
let duTagWidth (arch: Architecture) (caseCount: int) : IntBitWidth =
    let minWidth =
        if caseCount <= 256 then I8
        elif caseCount <= 65536 then I16
        else I32
    // Platform may choose larger for alignment (future optimization)
    minWidth
```

**Critical**: Tag is NEVER `i1`. Tags are case indices (0, 1, 2, ...), not booleans. Even a 2-case DU uses `i8` minimum because bits aren't addressable.

## Why This Matters: Option and Result

Option and Result are "bread and butter" types - they appear constantly in F# code. Getting their representation wrong cascades through everything:

- **Option**: Simple case (homogeneous - Some and None both have single-slot payload or unit)
- **Result**: Complex case (heterogeneous - Ok and Error may have different payload shapes)

If we get Result right with architectural purity, the pattern extends to ALL user-defined DUs.

## The Four Pillars of Transfer (Baker → Alex)

1. **Coeffects** - SSA analysis, mutability, yields, patterns, strings
2. **Active Patterns + XParsec** - Recognition and decomposition
3. **Zipper** - Traversal state and position
4. **Templates** - MLIR generation patterns

Baker uses Pillars 1-2 to decompose. Alex uses Pillars 3-4 to emit.

## Anti-Patterns to Avoid

### ❌ Alex-side type introspection
```fsharp
// WRONG: Alex deciding representation at emission time
match getPayloadType case with
| StructType _ -> emitStructExtraction()
| IntType -> emitIntExtraction()
```

### ❌ LLVM transform reliance
```fsharp
// WRONG: Hoping LLVM will fix our representation
// "LLVM's mem2reg will optimize this away"
```

### ❌ Runtime type tags
```fsharp
// WRONG: Boxing everything to avoid the problem
// Result becomes struct { tag: i8, payload: ptr }
```

### ✅ Baker decomposition
```fsharp
// RIGHT: Baker emits explicit structure
// PSG contains: ExtractTag, BranchOnTag, ExtractPayloadAs<T>
// Alex translates 1:1 to MLIR
```

## Implementation Path

1. **Define DU intrinsics in Baker** (Ingredients)
   - `DU.getTag` - extract tag from DU struct
   - `DU.getPayload<'T>` - extract and interpret payload as specific type
   - `DU.construct<Case>` - create DU with tag and payload

2. **Create DU decomposition recipes** (Recipes)
   - Pattern match on `match expr with | Case1 x -> ... | Case2 y -> ...`
   - Rewrite to explicit tag check + payload extraction

3. **Ensure platform-aware representation**
   - Tag width from `duTagWidth`
   - Payload slot from max of all case payloads

4. **Alex translates 1:1**
   - `DU.getTag` → `llvm.extractvalue`
   - `DU.getPayload<int>` → `llvm.extractvalue` (direct for matching types)
   - `DU.getPayload<string>` → extraction from max-sized slot

## Success Criteria

When this is implemented correctly:

1. Sample 08 (Option) passes ✅ (already working - simple case)
2. Sample 09 (Result) passes - heterogeneous payloads handled
3. User-defined DUs with any payload combination work
4. Alex contains NO type-based decision logic for DUs
5. All DU representation decisions are visible in PSG before Alex

---

*This memory serves as the architectural north star for DU representation work. When in doubt, ask: "Is Baker making this decision, or am I pushing it to Alex?"*

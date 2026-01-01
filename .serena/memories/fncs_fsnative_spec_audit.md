# FNCS vs fsnative-spec Audit

## Audit Date: 2025-01-01

## Purpose

Bidirectional audit comparing FNCS implementation against fsnative-spec normative requirements. Neither source is treated as fully authoritative - this identifies divergences requiring reconciliation.

---

## CRITICAL DIVERGENCES

### 1. `int` and `uint` Type Size

| Aspect | fsnative-spec | FNCS Implementation |
|--------|---------------|---------------------|
| `int` type | `isize` (platform word: 4/8 bytes) | `TypeLayout.Inline(4, 4)` - fixed 32-bit |
| `uint` type | `usize` (platform word: 4/8 bytes) | `TypeLayout.Inline(4, 4)` - fixed 32-bit |

**Location**: `NativeGlobals.fs:66-72`

**Resolution Required**: This is a fundamental semantic divergence. Either:
- A. Implementation should use platform-sized integers (matches spec philosophy)
- B. Spec should be updated if there's a deliberate reason for fixed 32-bit

**Recommendation**: Update implementation. The spec philosophy is clear about native compilation targeting different platforms. Fixed 32-bit integers would be surprising for bare-metal ARM64.

---

### 2. Error Code Range

| Aspect | fsnative-spec | FNCS Implementation |
|--------|---------------|---------------------|
| Error codes | FS8xxx range for native-specific | Uses FS0001, FS0002 (standard F# codes) |
| FS8100 | "Cannot use 'null' in F# Native" | Not implemented |
| FS8101 | "Cannot use 'null' in F# Native; all values must be initialized" | Not implemented |
| FS8102 | Warning for exception-style patterns | Not implemented |
| FS8103 | "Type does not support 'null'" | Not implemented |
| FS8104 | Warning for Unchecked.defaultof | Not implemented |

**Location**: `CheckExpressions.fs:104, 114`

**Resolution Required**: Create proper error code infrastructure.

```fsharp
// Current (wrong)
Code = "FS0001"

// Should be
Code = "FS8100"  // For null-specific errors
```

---

### 3. Null Handling

| Aspect | fsnative-spec | FNCS Implementation |
|--------|---------------|---------------------|
| Null detection | SHALL emit FS8100/FS8101 | Creates Error node but NO diagnostic |
| Error reporting | Diagnostic with proper code | Just TError value |

**Location**: `CheckExpressions.fs:558-562`

```fsharp
// Current (incomplete)
| SynExpr.Null _ ->
    builder.Create(
        SemanticKind.Error "null is not supported in native F#",
        NativeType.TError "null not supported",
        range)

// Should be
| SynExpr.Null m ->
    addError m "Cannot use 'null' in F# Native; use 'ValueNone' for optional values" env
    // Also update addError to use "FS8100"
    builder.Create(...)
```

---

### 4. `obj` Elimination

| Aspect | fsnative-spec | FNCS Implementation |
|--------|---------------|---------------------|
| obj usage | SHALL reject any code referencing `obj` | No validation exists |
| Internal usage | Presumably should not use obj | `SemanticGraph.fs:307` uses `Map<string, obj>` |
| Quotation types | No obj allowed | Comment says "Raw quotation has type Expr<obj>" |

**Locations**:
- `SemanticGraph.fs:307` - `Metadata: Map<string, obj>`
- `CheckExpressions.fs:570` - Comment about `Expr<obj>`

**Resolution Required**:
1. Add validation in CheckExpressions to reject `obj` type references
2. Replace internal `obj` usage with typed alternatives (e.g., discriminated union for metadata)
3. Fix quotation type handling - raw quotations should NOT have `Expr<obj>`

---

## IMPLEMENTATION GAPS

These are spec requirements with no implementation:

### 5. No Type Validation for obj/System.Object

The spec says:
> "The compiler SHALL reject any code that references `obj` or `System.Object`"

No such validation exists in CheckExpressions.fs.

### 6. No Reflection Rejection

The spec says:
> "NORMATIVE: `System.Reflection` and all reflection-based APIs SHALL NOT be available"

No validation exists.

### 7. No box/unbox Handling

The spec says box/unbox are not available. No specific handling or rejection in implementation.

---

## SPEC GAPS

These are implementation details that the spec doesn't document:

### 8. Union-Find Type Substitution

`UnionFind.fs` implements path compression and type variable unification. The spec doesn't detail the constraint solving algorithm.

**Recommendation**: Add section to spec on type inference algorithm (or reference standard HM inference).

### 9. SRTP Resolution During Type Checking

`SRTPResolution.fs` and `SemanticKind.TraitCall` handle SRTP. Spec mentions SRTP conceptually but doesn't specify the resolution mechanism.

**Recommendation**: Document how SRTP constraints become `Constraint.HasMember` and how witnesses are resolved.

### 10. Memory Region Tracking in TypeEnv

`TypeEnv.CurrentArena: ArenaAffinity` tracks memory affinity during checking. Spec mentions memory regions but doesn't detail how they propagate through type checking.

---

## ALIGNMENT CONFIRMED

These areas match between spec and implementation:

| Feature | Status |
|---------|--------|
| `char` = 4 bytes (UTF-32) | ✅ Aligned |
| `string` = UTF-8 fat pointer (16 bytes) | ✅ Aligned |
| `voption` type defined | ✅ Aligned |
| Memory regions (stack, arena, peripheral, sram, flash, dma) | ✅ Aligned in NativeGlobals.fs |
| Access modes (ro, wo, rw) | ✅ Aligned in NativeGlobals.fs |
| Option as value type | ✅ Aligned (`TypeLayout.Inline(-1,-1)`) |
| SRTP constraint collection | ✅ Aligned (`Constraint.HasMember`) |

---

## RECONCILIATION PRIORITIES

### Priority 1 (Semantic Correctness)

1. **Fix int/uint to be platform-sized** - Core type semantics
2. **Add null rejection with FS8100** - Null-freedom is fundamental
3. **Add obj rejection** - obj elimination is fundamental

### Priority 2 (Error Reporting)

4. **Implement FS8xxx error code infrastructure** - Tooling integration
5. **Add FS8102 warning for exception patterns** - Migration guidance
6. **Add FS8104 warning for Unchecked.defaultof** - Safety

### Priority 3 (Internal Cleanup)

7. **Replace Metadata: Map<string, obj>** - Dogfooding
8. **Fix quotation type comment** - Accuracy

### Priority 4 (Spec Updates)

9. **Document Union-Find algorithm** - Implementation detail
10. **Document SRTP resolution mechanism** - Implementation detail
11. **Document memory region propagation** - Implementation detail

---

## DISCOVERED DURING IMPLEMENTATION

These are things the implementation had to resolve that may need spec updates:

### A. TraitCall as SemanticKind

Implementation added `SemanticKind.TraitCall` which wasn't in original design. This captures SRTP dispatch at the semantic level.

**Spec Impact**: Consider documenting TraitCall in the semantic graph section.

### B. NamedIndexedPropertySet

Implementation distinguishes `obj.Prop[idx] <- v` from `obj.[idx] <- v`. 

**Spec Impact**: Consider documenting this distinction in expressions chapter.

### C. Anonymous Record isStruct Tracking

`NativeType.TAnon` now includes `isStruct: bool` to distinguish struct vs reference anonymous records.

**Spec Impact**: Ensure anonymous records section covers both forms.

---

## FILES TO MODIFY

| Priority | File | Changes |
|----------|------|---------|
| P1 | `NativeGlobals.fs:66-72` | Change int/uint to platform-sized |
| P1 | `CheckExpressions.fs:558-562` | Add proper FS8100 diagnostic |
| P1 | `CheckExpressions.fs` | Add obj type rejection |
| P2 | `CheckExpressions.fs:100-118` | Implement FS8xxx error codes |
| P3 | `SemanticGraph.fs:307` | Replace `Map<string, obj>` with typed alternative |
| P3 | `CheckExpressions.fs:570` | Fix quotation type comment |

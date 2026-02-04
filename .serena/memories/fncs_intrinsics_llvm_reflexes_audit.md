# FNCS Intrinsics LLVM Reflexes Audit

**Date:** 2026-02-04  
**Context:** Systematic audit following discovery of LLVM reflexes in FNCS type system  
**Goal:** Identify ALL intrinsic signatures that assume LLVM fat pointer mechanics instead of MLIR memref semantics

---

## Audit Methodology

**Search criteria:**
1. Intrinsics with explicit `count` or `length` parameters where memref provides this intrinsically
2. Operations taking `nativeptr<byte> + int` where memref would be a single parameter
3. String operations assuming `{ptr, len}` fat pointer representation
4. Array operations with explicit index/count parameters that memref.dim could provide

**File audited:** `/home/hhh/repos/fsnative/src/Compiler/NativeTypedTree/Expressions/Intrinsics.fs`

---

## Critical Violations (Require Signature Changes)

### 1. Sys.write - Syscall FFI Boundary

**Lines:** 133-138

**Current signature (LLVM-style):**
```fsharp
// fd:int -> buffer:nativeptr<byte> -> count:int -> int
let ty = NativeType.TFun(Types.intType,
    NativeType.TFun(NativeType.TNativePtr Types.uint8Type,
        NativeType.TFun(Types.intType, Types.intType)))
```

**Problem:**
- Takes 3 parameters: fd, buffer pointer, explicit count
- Assumes buffer has NO intrinsic length information
- This is LLVM `i8*` thinking - raw pointer with no metadata
- In MLIR, buffers ARE memrefs with intrinsic dimension information

**Memref-aligned signature:**
```fsharp
// fd:int -> buffer:memref<?xi8> -> int
// Count extracted via memref.dim inside Firefly pattern
let ty = NativeType.TFun(Types.intType,
    NativeType.TFun(memrefByteType, Types.intType))
```

**Impact:**
- Firefly `PlatformPatterns.fs` pSysWrite pattern must extract BOTH pointer AND length
- Current workaround: Pattern performs extraction, expects 3 SSAs
- Proper fix: Signature takes 2 params, pattern extracts length via memref.dim

**Status:** ⚠️ WORKAROUND IMPLEMENTED (Firefly extracts length)

---

### 2. Sys.read - Syscall FFI Boundary

**Lines:** 139-144

**Current signature (LLVM-style):**
```fsharp
// fd:int -> buffer:nativeptr<byte> -> maxCount:int -> int
let ty = NativeType.TFun(Types.intType,
    NativeType.TFun(NativeType.TNativePtr Types.uint8Type,
        NativeType.TFun(Types.intType, Types.intType)))
```

**Problem:**
- Same issue as Sys.write
- Takes explicit `maxCount` parameter instead of getting buffer capacity from memref

**Memref-aligned signature:**
```fsharp
// fd:int -> buffer:memref<?xi8> -> int
// maxCount = memref.dim (buffer capacity)
let ty = NativeType.TFun(Types.intType,
    NativeType.TFun(memrefByteType, Types.intType))
```

**Impact:**
- Firefly `PlatformPatterns.fs` pSysRead pattern must extract BOTH pointer AND length
- Same workaround pattern as Sys.write

**Status:** ⚠️ WORKAROUND IMPLEMENTED

---

### 3. NativeStr.fromPointer - String Construction

**Lines:** 348-353

**Current signature (LLVM-style):**
```fsharp
// ptr:nativeptr<byte> -> len:int -> string
let ty = NativeType.TFun(NativeType.TNativePtr Types.uint8Type,
    NativeType.TFun(Types.intType, Types.stringType))
```

**Problem:**
- Takes pointer + length to "construct" a string fat pointer struct
- Assumes string = `{ptr, len}` representation (LLVM fat pointer)
- In MLIR, buffer IS ALREADY a string (memref<?xi8>)
- This operation should be **identity** (buffer -> buffer) or **not exist**

**Memref-aligned approach:**
```fsharp
// Option A: Remove entirely - buffer IS string, no construction needed
// Option B: Make it identity function (for backward compat)
// buffer:memref<?xi8> -> string (where string = memref<?xi8>)
let ty = NativeType.TFun(memrefByteType, Types.stringType)
```

**Impact:**
- Fidelity.Platform Console.fs used this in Console.readln to "construct" string from buffer
- Firefly Phase 1 SSA remediation already worked around this
- ApplicationWitness.fs currently simplifies to return buffer directly

**Status:** ✅ WORKAROUND IMPLEMENTED (returns buffer identity)

---

## Medium Priority Violations (Impact String Operations)

### 4. String.toBytes - String Serialization

**Lines:** 212-214

**Current signature:**
```fsharp
// string -> byte[] (UTF-8 encoding)
let ty = NativeType.TFun(stringType, NativeType.TApp(Types.arrayTyCon, [Types.uint8Type]))
```

**Analysis:**
- Signature looks OK (string -> array)
- BUT: Implementation likely assumes string has `.Pointer` and `.Length` fields
- In memref world: string IS memref<?xi8>, just needs type cast to array

**Memref semantics:**
- String and byte array are BOTH memref<?xi8>
- Operation should be **identity cast** or **memref.cast**
- No copying, no field extraction

**Status:** ⚠️ NEEDS INVESTIGATION (implementation may have LLVM reflexes)

---

### 5. String.fromBytes - String Deserialization

**Lines:** 215-217

**Current signature:**
```fsharp
// byte[] -> string (UTF-8 decoding)
let ty = NativeType.TFun(NativeType.TApp(Types.arrayTyCon, [Types.uint8Type]), stringType)
```

**Analysis:**
- Same as String.toBytes - likely assumes fat pointer construction
- In memref: byte array IS memref<?xi8>, same as string
- Should be identity cast

**Status:** ⚠️ NEEDS INVESTIGATION

---

### 6. String.concat2 - String Concatenation

**Lines:** 185-187

**Current signature:**
```fsharp
// string -> string -> string
let ty = NativeType.TFun(stringType, NativeType.TFun(stringType, stringType))
```

**Analysis:**
- Signature looks clean
- BUT: Firefly StringPatterns.fs implementation uses pExtractValue to get `{ptr, len}` fields
- This is documented in SSA remediation plan as Phase 5.2 work item

**Impact:**
- Firefly `StringPatterns.fs` pStringConcat2 currently extracts fat pointer fields
- Should use memref.dim for length, memref.extract_aligned_pointer_as_index for pointers

**Status:** 🔄 DOCUMENTED IN PLAN (Phase 5.2 - refactor to pure memref)

---

## Low Priority (Array Operations)

### 7. NativePtr.copy - Memory Copy

**Lines:** 121-125

**Current signature:**
```fsharp
// nativeptr<'T> -> nativeptr<'T> -> int -> unit
let ty = NativeType.TForall([tyParamSpec],
    NativeType.TFun(NativeType.TNativePtr tyParam,
        NativeType.TFun(NativeType.TNativePtr tyParam,
            NativeType.TFun(Types.intType, Types.unitType))))
```

**Analysis:**
- Takes dest pointer, src pointer, explicit count
- Signature is appropriate for **raw pointer operations**
- This is intentionally low-level, not a string/array operation
- Caller must provide count explicitly

**Verdict:** ✅ NO CHANGE NEEDED - This is intentionally raw pointer arithmetic

---

### 8. Array.blit - Array Block Copy

**Lines:** 260-267

**Current signature:**
```fsharp
// 'T[] -> int -> 'T[] -> int -> int -> unit
// (source, sourceIndex, target, targetIndex, count)
```

**Analysis:**
- Takes explicit indices and count
- This is a **partial array copy** operation (not full array)
- Indices specify WHERE in arrays, count specifies HOW MUCH
- Cannot be inferred from memref dimensions

**Verdict:** ✅ NO CHANGE NEEDED - Explicit indices/count are semantically required

---

## Summary of Findings

### Critical (Must Fix in FNCS)

| Intrinsic | Current Params | Memref-Aligned Params | Impact |
|-----------|----------------|----------------------|---------|
| Sys.write | fd, ptr, count | fd, buffer (count via memref.dim) | FFI boundary extraction |
| Sys.read  | fd, ptr, maxCount | fd, buffer (maxCount via memref.dim) | FFI boundary extraction |
| NativeStr.fromPointer | ptr, len | buffer (identity or remove) | String construction |

**Recommendation:** Change FNCS signatures to take memref types, remove explicit length parameters.

### Medium (Investigate Implementation)

| Intrinsic | Issue | Action |
|-----------|-------|--------|
| String.toBytes | May assume fat pointer | Check implementation, use memref.cast |
| String.fromBytes | May assume fat pointer | Check implementation, use memref.cast |
| String.concat2 | Implementation extracts fields | Refactor Firefly pattern (Phase 5.2) |

**Recommendation:** Audit FNCS Baker saturation recipes for these operations.

### No Change Needed

| Intrinsic | Reason |
|-----------|--------|
| NativePtr.copy | Intentionally raw pointer arithmetic |
| Array.blit | Explicit indices/count semantically required for partial copy |

---

## Architectural Impact

### The Two-Pronged Problem

**Prong 1: FNCS Type System**
- `NativeTypes.fs` line 1193: `stringTyCon` defined with `TypeLayout.FatPointer`
- This causes `String.length s` to generate FieldGet("len") PSG nodes
- Incorrect type layout infects all downstream operations

**Prong 2: FNCS Intrinsic Signatures**
- Sys.write/read expect explicit count parameters
- NativeStr.fromPointer expects to "construct" fat pointers
- String operations may assume field access

**Combined effect:**
- FNCS generates PSG nodes assuming fat pointer representation
- Firefly witnesses try to handle memrefs
- Mismatch creates orphaned nodes, compilation failures, or complex workarounds

---

## Recommended Fixes

### Option A: Full MLIR Alignment (Architectural)

**Change FNCS:**
1. Update `NativeTypes.fs` line 1193:
   ```fsharp
   // OLD: TypeLayout.FatPointer
   // NEW: TypeLayout.MemRef or appropriate memref layout
   let stringTyCon = mkNTUTypeConRef "string" NTUKind.NTUstring TypeLayout.MemRef
   ```

2. Update Sys.write/read signatures (2 params instead of 3):
   ```fsharp
   | "write" ->
       // fd:int -> buffer:memref<?xi8> -> int
       // Length extracted via memref.dim in Firefly pattern
       let ty = NativeType.TFun(Types.intType,
           NativeType.TFun(memrefByteType, Types.intType))
   ```

3. Remove NativeStr.fromPointer or make it identity:
   ```fsharp
   | "fromPointer" ->
       // In MLIR: buffer IS string, no construction
       // Just return the buffer type directly
       let ty = NativeType.TFun(memrefByteType, Types.stringType)
   ```

**Pros:**
- Clean architecture matching MLIR semantics
- Eliminates orphaned FieldGet nodes at source
- No workarounds needed in Firefly

**Cons:**
- Requires FNCS changes (affects multiple repos)
- May impact FNCS LLVM backend (if it still exists)

---

### Option B: Firefly Workarounds (Tactical - Current Approach)

**Keep FNCS signatures unchanged, handle in Firefly:**
1. String.length witness generates memref.dim (DONE)
2. Sys.write/read patterns extract length via memref.dim (DONE)
3. StringPatterns.fs refactored to use pure memref ops (PHASE 5.2)

**Pros:**
- No FNCS changes required
- Unblocks Firefly development immediately

**Cons:**
- Witnesses operations that shouldn't exist in memref world
- PSG still generates orphaned FieldGet nodes (workaround witnesses them)
- Architectural debt accumulates

---

## Decision Matrix

| Criterion | Option A (Fix FNCS) | Option B (Workaround) |
|-----------|--------------------|-----------------------|
| **Architectural purity** | ✅ Clean | ❌ Workarounds |
| **Development speed** | ❌ Slow (cross-repo) | ✅ Fast (Firefly only) |
| **Long-term maintenance** | ✅ No debt | ❌ Accumulates debt |
| **Risk** | ⚠️ May break LLVM backend | ✅ Isolated to MLIR |
| **Recommended for** | Production release | Prototyping phase |

---

## Next Steps

**Immediate (Firefly Phase 5 completion):**
1. ✅ Complete String.length witness (DONE)
2. ✅ Complete Sys.write/read FFI extraction (DONE)
3. 🔄 Refactor StringPatterns.fs String.concat2 (PHASE 5.2)
4. ⏳ Investigate String.toBytes/fromBytes implementations
5. ⏳ Verify samples compile and execute

**Strategic (FNCS alignment):**
1. ⏳ Discuss with FNCS maintainers about memref-aligned type system
2. ⏳ Audit FNCS Baker saturation recipes for LLVM reflexes
3. ⏳ Propose TypeLayout.MemRef for string type
4. ⏳ Propose 2-param signatures for Sys.write/read
5. ⏳ Remove or deprecate NativeStr.fromPointer

---

## Related Context

**Memories:**
- `mlir_memref_strings_no_llvm_cruft` - Core memref principle and FFI boundary policy
- `fncs_architecture` - FNCS overall architecture
- `alex_compositional_architecture_elements_patterns_witnesses` - Firefly witness architecture

**Files:**
- FNCS: `NativeTypes.fs` line 1193 (TypeLayout.FatPointer)
- FNCS: `Intrinsics.fs` (this audit)
- Firefly: `PlatformPatterns.fs` (Sys.write/read workarounds)
- Firefly: `StringPatterns.fs` (String operations)
- Firefly: `ApplicationWitness.fs` (Intrinsic witnesses)

**Plan:**
- `/home/hhh/.claude/plans/golden-floating-spring.md` - SSA remediation Phase 5

---

## Audit Completion

**Date:** 2026-02-04  
**Audited by:** Claude (automated analysis)  
**Files analyzed:** 1 (FNCS Intrinsics.fs)  
**Violations found:** 6 critical/medium  
**Violations resolved:** 3 (workarounds)  
**Violations pending:** 3 (Phase 5 work)

**Next audit targets:**
- FNCS Baker saturation recipes (check for fat pointer field access in string operations)
- FNCS NativeTypes.fs TypeLayout definitions
- Fidelity.Platform library code (verify no remaining .Pointer/.Length accesses)

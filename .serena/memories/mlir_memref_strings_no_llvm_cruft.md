# MLIR Memref Strings - No LLVM Cruft

**Date:** 2026-02-04  
**Context:** Phase 5 of SSA remediation - LLVM vestigial code removal  
**Principle:** Strings ARE memrefs. ONLY memref. No fat pointer structs in MLIR backend.

---

## The Architectural Divide

### LLVM Backend (Historical)
```fsharp
// String representation: Fat pointer struct {ptr: nativeptr<byte>, len: int}
type string = { Pointer: nativeptr<byte>; Length: int }

// Access pattern (LLVM)
let write (s: string) : unit =
    let _ = Sys.write STDOUT s.Pointer s.Length
    ()
```

In LLVM:
- Strings are `{i8*, i64}` structs
- Field access via `llvm.extractvalue`
- Explicit struct construction via `llvm.insertvalue`

### MLIR Backend (Current - Correct)
```fsharp
// String representation: Direct memref
// string = memref<?xi8>  (NO struct wrapper)

// Access pattern (MLIR)
let write (s: string) : unit =
    // String IS memref - pass directly
    // Sys.write extracts pointer at FFI boundary using:
    //   memref.extract_aligned_pointer_as_index : memref<?xi8> -> index
    //   index.casts : index -> i64
    let len = String.length s
    let _ = Sys.write STDOUT s len
    ()
```

In MLIR:
- Strings ARE `memref<?xi8>` directly (no wrapper)
- Length via `memref.dim` operation
- Pointer extraction ONLY at FFI boundaries (syscalls)
- Uses MLIR standard dialects: `memref.*`, `index.*`, `arith.*`

---

## The Cruft Pattern (WRONG)

**Symptom:** Member access on strings (`.Pointer`, `.Length`)

**Example from Fidelity.Platform Console.fs (before fix):**
```fsharp
let write (s: string) : unit =
    // WRONG: This is LLVM fat pointer thinking
    let _ = Sys.write STDOUT s.Pointer s.Length
    ()
```

**What this generates in MLIR (INCORRECT):**
1. Firefly witnesses `.Pointer` as FieldGet operation
2. Pattern emits `memref.extract_aligned_pointer_as_index` (extraction #1)
3. Result is `i64` pointer
4. Firefly witnesses Sys.write call
5. Sys.write pattern sees memref parameter, emits ANOTHER extraction (extraction #2)
6. Result: **Double extraction bug** - trying to extract from already-extracted i64

**MLIR error:**
```
error: custom op 'memref.extract_aligned_pointer_as_index' invalid kind of type specified
    %v12 = memref.extract_aligned_pointer_as_index %v6 : i64 -> index
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
           Cannot extract from i64 - it's not a memref!
```

---

## The Correct Pattern (RIGHT)

**Library code (Fidelity.Platform) must use memref semantics:**
```fsharp
let write (s: string) : unit =
    // In MLIR: string IS memref<?xi8>
    // Pass memref directly - Sys.write extracts pointer at FFI boundary
    let len = String.length s
    let _ = Sys.write STDOUT s len
    ()
```

**What this generates in MLIR (CORRECT):**
1. `String.length s` → witnesses as intrinsic → generates `memref.dim`
2. `Sys.write STDOUT s len` → witnesses Sys.write intrinsic
3. Sys.write pattern sees `s` is memref, emits **single extraction** at FFI boundary
4. Result: Clean MLIR using only standard dialects

**Generated MLIR:**
```mlir
func.func @Console.write(%arg0: memref<?xi8>) -> i32 {
  %v1 = arith.constant 1 : i64                              // STDOUT
  %v4 = memref.extract_aligned_pointer_as_index %arg0 : memref<?xi8> -> index
  %v6 = index.casts %v4 : index to i64                      // Pointer for syscall
  %v9 = arith.constant 0 : index
  %v10 = memref.dim %arg0, %v9 : memref<?xi8>              // Length
  %v11 = index.casts %v10 : index to i64
  %v14 = func.call @write(%v1, %v6, %v11) : (i64, i64, i64) -> i64
  %v18 = arith.constant 0 : i32
  func.return %v18 : i32
}
```

Single extraction (lines 4-6), clean memref operations, NO llvm.* operations.

---

## FFI Boundary Policy (Unambiguous)

**WHERE extraction happens:** ONLY at FFI boundaries (syscall intrinsics)

**ALLOWED in MiddleEnd (MLIR):**
- `memref.*` - Memory reference operations
- `arith.*` - Arithmetic operations  
- `scf.*` - Structured control flow
- `func.*` - Function operations
- `index.*` - Index type operations
- `builtin.*` - Builtin types and operations

**FORBIDDEN in MiddleEnd:**
- `llvm.*` - ALL LLVM dialect operations (LLVM is backend-only, in 08_output.ll)
- Fat pointer struct access (`.Pointer`, `.Length`)
- `llvm.extractvalue`, `llvm.insertvalue`, `llvm.undef`

**Extraction pattern (ONLY at syscall boundaries):**
```fsharp
// PlatformPatterns.fs - pSysWrite pattern
let pSysWrite (ssas: SSA list) (fdSSA: SSA) (bufferSSA: SSA) (bufferType: MLIRType) (countSSA: SSA) =
    parser {
        // Buffer is ALWAYS memref at syscall boundary
        // Extract to i64 for C ABI compatibility
        let buf_ptr_index = ssas.[0]
        let buf_ptr_i64 = ssas.[1]
        let resultSSA = ssas.[2]
        
        // Extract: memref<?xi8> -> index -> i64
        let! extractOp = pExtractBasePtr buf_ptr_index bufferSSA bufferType
        let! castOp = pIndexCastS buf_ptr_i64 buf_ptr_index platformWordTy
        
        // Syscall with extracted i64 pointer
        let vals = [
            { SSA = fdSSA; Type = platformWordTy }
            { SSA = buf_ptr_i64; Type = platformWordTy }  // i64 pointer
            { SSA = countSSA; Type = platformWordTy }
        ]
        let! writeCall = pFuncCall (Some resultSSA) "write" vals platformWordTy
        
        return ([extractOp; castOp; writeCall], TRValue { SSA = resultSSA; Type = platformWordTy })
    }
```

---

## Type Mapping (FNCS → MLIR)

FNCS defines abstract intrinsic types. Backend mapping:

| FNCS Type | LLVM Backend | MLIR Backend |
|-----------|--------------|--------------|
| `string` | `{i8*, i64}` struct | `memref<?xi8>` directly |
| `nativeptr<byte>` | `i8*` | `i64` (at FFI) OR `memref<?>` (internal) |
| `int` | `i64` | `i64` |
| `byte` | `i8` | `i8` |

**Key insight:** FNCS `nativeptr<byte>` is ABSTRACT. In MLIR, it maps to:
- **Internal:** `memref<?xi8>` (memref all the way)
- **FFI boundary:** `i64` (extracted via `memref.extract_aligned_pointer_as_index + index.casts`)

---

## Detection and Removal Protocol

### How to Detect LLVM Cruft

**In library code (Fidelity.Platform, user code):**
```bash
# Search for fat pointer field access
grep -r '\.Pointer\|\.Length' /home/hhh/repos/Fidelity.Platform
```

**In MLIR output:**
```bash
# Check for llvm.* operations (should be ZERO)
grep "llvm\." samples/*/target/intermediates/07_output.mlir

# Check for double extraction (same SSA used twice in extract ops)
grep "memref.extract_aligned_pointer_as_index.*%v[0-9]" 07_output.mlir
```

**In Firefly MiddleEnd:**
```bash
# Should have ZERO llvm.* imports
grep "open.*LLVM" src/MiddleEnd/**/*.fs
```

### How to Remove LLVM Cruft

**Step 1:** Identify fat pointer field access
```fsharp
// BEFORE (WRONG)
let _ = Sys.write fd s.Pointer s.Length
```

**Step 2:** Replace with memref semantics
```fsharp
// AFTER (CORRECT)
let len = String.length s  // Uses memref.dim internally
let _ = Sys.write fd s len  // Passes memref, extraction at FFI
```

**Step 3:** Verify MLIR output
```bash
# Compile with intermediates
Firefly compile Project.fidproj -k

# Check MLIR - should see single extraction per syscall
grep -A5 "func.func @Console.write" target/intermediates/07_output.mlir
```

---

## Episode: Deep LLVM Reflexes in FNCS (2026-02-04)

### The Discovery

After fixing Fidelity.Platform Console.fs to remove `.Pointer` and `.Length` field accesses, attempted to compile Sample 01 (HelloWorldDirect). Expected it to work. It didn't.

**Error:**
```
[Intrinsic Fold-In] Recipe nodes not reachable from entry points!
Created 1 new nodes but 1 are orphaned.
Orphaned nodes: 498 (FieldGet (NodeId 122, "len"))
```

**Initial reaction:** "We fixed the library code, why is there still a FieldGet for 'len'?"

### Tracing the Root Cause

**Question:** Where is this FieldGet coming from?

**Hypothesis 1:** Maybe Console.fs still has cruft?
- **Check:** Reviewed Console.fs - confirmed NO `.Length` accesses remain
- **Status:** Hypothesis rejected

**Hypothesis 2:** Maybe FNCS intrinsic elaboration generates it?
- **Investigation:** Examined FNCS Intrinsics.fs Sys.write signature
- **Discovery:**
  ```fsharp
  | "write" ->
      // fd:int -> buffer:nativeptr<byte> -> count:int -> int
      let ty = NativeType.TFun(Types.intType,
          NativeType.TFun(NativeType.TNativePtr Types.uint8Type,
              NativeType.TFun(Types.intType, Types.intType)))
  ```
- **Insight:** Sys.write signature expects 3 parameters: `fd`, `buffer`, `count`
- **Status:** Promising but doesn't explain FieldGet

**Hypothesis 3:** Maybe string type definition itself has LLVM reflexes?
- **Investigation:** Examined FNCS NativeTypes.fs
- **Discovery (LINE 1193):**
  ```fsharp
  let stringTyCon = mkNTUTypeConRef "string" NTUKind.NTUstring TypeLayout.FatPointer
  //                                                              ^^^^^^^^^^^^^^^
  //                                                              THERE IT IS!
  ```
- **Status:** **ROOT CAUSE IDENTIFIED**

### The Architectural Trap

**The trap:** FNCS type system defines strings with `TypeLayout.FatPointer` layout. This means:

1. When FNCS sees `String.length s`, it treats it as **field access** on a fat pointer struct
2. PSG Builder creates a **FieldGet("len")** node (semantic: get the `len` field)
3. FNCS intrinsic fold-in tries to witness this node
4. **Problem:** No witness exists because Firefly MiddleEnd uses pure memref semantics
5. **Result:** Orphaned FieldGet node, compilation fails

**The realization:** LLVM reflexes exist at EVERY layer:
- ✅ **Library code** (Fidelity.Platform) - FIXED by removing `.Pointer`/`.Length` accesses
- ⚠️ **Intrinsic signatures** (FNCS Intrinsics.fs) - 3-param Sys.write signature
- ⚠️ **Type system** (FNCS NativeTypes.fs) - `TypeLayout.FatPointer` for strings
- ✅ **MiddleEnd patterns** (Firefly) - Already uses memref semantics

### The Options

**Option A: Architectural Fix (Long-term)**
- Change FNCS Sys.write signature to 2 parameters: `fd -> buffer -> int`
- Length is **intrinsic** to memref, extracted via `memref.dim` inside Sys.write pattern
- Removes FieldGet generation at source
- **Pros:** Clean, matches MLIR semantics exactly
- **Cons:** Requires FNCS changes, affects signature compatibility

**Option B: Workaround Witness (Short-term)**
- Keep FNCS signatures unchanged
- Implement String.length witness in Firefly
- Generates `memref.dim` operation when FieldGet("len") witnessed
- **Pros:** No FNCS changes needed, unblocks compilation immediately
- **Cons:** Witnesses an operation that shouldn't exist in memref world

### The Implementation (Option B)

**Decision:** Implement Option B as interim fix to unblock Sample 01 compilation.

**Files modified:**

1. **StringPatterns.fs** - Added pStringLength pattern:
```fsharp
/// String.length: get memref length via memref.dim
/// SSA layout (3 total):
///   [0] = dimIndexSSA (constant 0 for dimension index)
///   [1] = lengthIndexSSA (memref.dim result, index type)
///   [2] = resultSSA (length cast to int)
let pStringLength (ssas: SSA list) (strSSA: SSA) (strType: MLIRType) : PSGParser<MLIROp list * TransferResult> =
    parser {
        do! ensure (ssas.Length >= 3) $"pStringLength: Expected 3 SSAs, got {ssas.Length}"
        
        let dimIndexSSA = ssas.[0]
        let lengthIndexSSA = ssas.[1]
        let resultSSA = ssas.[2]
        
        // Get length via memref.dim
        let! dimConstOp = pConstI dimIndexSSA 0L TIndex  // Dimension 0 (strings are 1D)
        let! dimOp = pMemRefDim lengthIndexSSA strSSA dimIndexSSA strType
        let! castOp = pIndexCastS resultSSA lengthIndexSSA intTy  // Cast index -> int
        
        return ([dimConstOp; dimOp; castOp], TRValue { SSA = resultSSA; Type = intTy })
    }
```

2. **ApplicationWitness.fs** - Added String.length witness:
```fsharp
| IntrinsicModule.String, "length", [strSSA] ->
    let strType = argTypes.[0]
    match SSAAssign.lookupSSAs node.Id ctx.Coeffects.SSA with
    | Some ssas ->
        match tryMatch (pStringLength ssas strSSA strType) ctx.Graph node ctx.Zipper ctx.Coeffects ctx.Accumulator with
        | Some ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
        | None -> WitnessOutput.error "String.length pattern failed"
    | None -> WitnessOutput.error "String.length: No SSAs assigned"
```

3. **SSAAssignment.fs** - Allocated 3 SSAs for String.length:
```fsharp
| IntrinsicModule.String, "length" -> 3    // dim const + dim + cast
```

### The Lesson

**Key insight:** Fixing library code (Fidelity.Platform) was necessary but NOT sufficient. LLVM reflexes permeate the stack:

```
Layer                    LLVM Reflex                         Status
─────────────────────────────────────────────────────────────────────
User Code                ❌ NONE expected                    ✅ N/A
Library (Fid.Platform)   ❌ .Pointer, .Length accesses       ✅ FIXED
Intrinsic Signatures     ⚠️ 3-param Sys.write (count)        🔄 WORKAROUND
Type System              ⚠️ TypeLayout.FatPointer            🔄 WORKAROUND
MiddleEnd (Firefly)      ❌ llvm.* operations                ✅ CLEAN
```

**The workaround witnesses an operation (String.length as FieldGet) that shouldn't exist in a pure memref world.**

The correct long-term fix is changing FNCS type system and intrinsic signatures to match MLIR semantics:
- String type should have `TypeLayout.MemRef` (NOT FatPointer)
- Sys.write should take 2 params: `fd -> buffer -> int` (count extracted inside pattern)

**For now:** Option B unblocks compilation. Option A is the architectural fix for future work.

---

## Related Context

**Phase 5 Work (Firefly SSA Remediation):**
- Plan: `/home/hhh/.claude/plans/golden-floating-spring.md`
- Goal: Complete LLVM removal from MiddleEnd
- Three issues:
  1. FFI boundaries (DONE - this memory documents the solution)
  2. String concatenation (TODO - remove fat pointer extraction)
  3. Intrinsic references (TODO - witness or eliminate)

**Firefly Files Modified:**
- `PlatformPatterns.fs` - FFI extraction using MLIR standard dialects
- `StringPatterns.fs` - Added pStringLength pattern (workaround for TypeLayout.FatPointer)
- `ApplicationWitness.fs` - Added String.length witness (workaround)
- `SSAAssignment.fs` - Updated Sys.write/read SSA counts (3 SSAs), String.length (3 SSAs)

**Fidelity.Platform Files Modified:**
- `Linux_x86_64/Console.fs` - Removed `.Pointer`, `.Length` cruft from write/writeln/error/errorln

**FNCS Files (Read-Only - Discoveries):**
- `NativeTypes.fs` line 1193 - `TypeLayout.FatPointer` for string type
- `Intrinsics.fs` lines 133-138 - Sys.write 3-param signature

---

## Golden Rules

1. **Strings ARE memrefs** - No struct wrapper, no field access
2. **Extraction ONLY at FFI** - Use `memref.extract_aligned_pointer_as_index + index.casts`
3. **MLIR standard dialects ONLY** - Zero llvm.* operations in MiddleEnd
4. **Library code follows backend** - Fidelity.Platform must use memref semantics
5. **Verification mandatory** - Check 07_output.mlir for llvm.* (should be 0 matches)
6. **LLVM reflexes go DEEP** - Don't assume library fixes are sufficient, check type system and signatures

---

## Memory Cross-References

- `fncs_architecture` - FNCS intrinsic type system (abstract types)
- `mlir_errors_trace_to_fncs_elaboration` - Error tracing from MLIR to FNCS
- `alex_compositional_architecture_elements_patterns_witnesses` - Witness/Pattern/Element architecture
- `coeffect_compilation_strategy` - SSA pre-allocation via coeffects

**When resuming this work:** Read this memory FIRST to stay on the beam. The memref principle is absolute - no compromises, no conditionals, no "one if i64" logic. And remember: LLVM reflexes hide in type systems and signatures, not just library code.
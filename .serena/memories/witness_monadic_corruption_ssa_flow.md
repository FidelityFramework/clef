# Witness Monadic Corruption - SSA Flow Violations

**Date:** 2026-02-04  
**Context:** Sample 02 compilation failure - SSA value reuse causing type errors  
**Principle:** Coeffect pattern prevents monadic corruption - witnesses observe, never transform

---

## The Architectural Violation

### Symptom: SSA "Overlap" or "Reuse"
```mlir
%v16 = arith.constant 0 : i64          // Node 29: Literal Int 0
memref.store %v93, %v16[%v141] ...     // Using %v16 as memref (WRONG!)
```

**Error**: Same SSA value used with incompatible types (i64 vs memref)

### Root Cause: Monadic Corruption in Witness

**THE BUG**:
```fsharp
// ApplicationWitness.fs - NativePtr.add (BEFORE FIX)
| IntrinsicModule.NativePtr, "add", [basePtrSSA; offsetSSA] ->
    // VIOLATION: Returns offsetSSA instead of basePtrSSA
    { InlineOps = []; TopLevelOps = []; Result = TRValue { SSA = offsetSSA; Type = TIndex } }
```

**What happened**:
1. Source: `NativePtr.write (NativePtr.add buffer pos) b`
2. NativePtr.add witness receives `basePtrSSA` (%v12, memref) and `offsetSSA` (%v16, int)
3. **CORRUPTION**: Returns `offsetSSA` (%v16) instead of `basePtrSSA`
4. NativePtr.write witness receives %v16 (int) as `ptrSSA`
5. Pattern tries to use %v16 as memref → **TYPE ERROR**

---

## The Coeffect/Codata Pattern (Correct Architecture)

### Golden Rule: Witnesses Observe, Never Transform

**Coeffect Pattern**:
1. SSAAssignment.fs PRE-ALLOCATES SSAs to nodes BEFORE witnessing
2. Each node gets its OWN SSAs from coeffects
3. Witnesses USE pre-allocated SSAs, NEVER create or pick SSAs manually
4. Monadic flow: each witness receives SSAs from arguments, returns result SSA

**The Design Prevents**:
- SSA reuse (each node has unique SSAs)
- Type confusion (SSAs flow with correct types)
- Monadic corruption (witnesses can't break the chain)

**IF SSA OVERLAP OCCURS**: The witness violated the coeffect pattern by:
- Returning the wrong argument SSA
- Manually picking SSAs instead of using pre-allocated ones
- Breaking the monadic SSA flow chain

---

## The Fix: Maintain Monadic SSA Flow

### NativePtr.add (FIXED)
```fsharp
| IntrinsicModule.NativePtr, "add", [basePtrSSA; offsetSSA] ->
    // CORRECT: Return basePtrSSA to maintain monadic flow
    // The offset is tracked separately and extracted later
    let baseType = argTypes.[0]
    { InlineOps = []; TopLevelOps = []; Result = TRValue { SSA = basePtrSSA; Type = baseType } }
```

### NativePtr.write (FIXED)
```fsharp
| IntrinsicModule.NativePtr, "write", [ptrSSA; valueSSA] ->
    // Detect compound pattern: NativePtr.write (NativePtr.add base offset) value
    let ptrNodeId = argIds.[0]
    match SemanticGraph.tryGetNode ptrNodeId ctx.Graph with
    | Some ptrNode ->
        match ptrNode.Kind with
        | SemanticKind.Application (funcId, innerArgIds) ->
            match SemanticGraph.tryGetNode funcId ctx.Graph with
            | Some funcNode when funcNode.Kind matches NativePtr.add ->
                // Extract offset from add's second argument
                let offsetArgId = innerArgIds.[1]
                // Get offset SSA from coeffects (NOT by re-witnessing)
                match SSAAssign.lookupSSA offsetArgId ctx.Coeffects.SSA with
                | Some offsetSSA ->
                    // baseSSA = ptrSSA (returned by add witness)
                    // Generate: memref.store value, base[offset]
                    pMemRefStoreIndexed ptrSSA valueSSA offsetSSA elemType
```

**Key insight**: Use `SSAAssign.lookupSSA` to get offset SSA from coeffects, NOT by recursively witnessing. This maintains the recursion-free coeffect pattern.

---

## Detection Protocol

### When You See "SSA Overlap" Errors

**Step 1: Check SSA Assignment (6_coeffects.json)**
```bash
jq -r '.ssaAssignment.NodeSSAAssignments[] | select(.SSAs[]?.Index == 16) | "Node \(.NodeId) (\(.NodeKind)): SSAs = \(.SSAs | map(.Display) | join(", "))"' 06_coeffects.json
```

**Verify**:
- ✅ Each SSA (e.g., %v16) appears in only ONE node's allocation
- ✅ SSA ranges are monotonically increasing per function
- ❌ If same SSA appears in multiple nodes → SSAAssignment.fs bug (rare)

**Step 2: Check MLIR Output (07_output.mlir)**
```bash
grep -n "v16" 07_output.mlir
```

**Look for**:
- ❌ Same SSA defined with one type, used with another type
- ❌ SSA used as operand before being defined
- ❌ SSA used in incompatible operations (i64 as memref)

**Step 3: Trace SSA Flow Through Witnesses**

**Question**: Which witness is returning the wrong SSA?

**Method**:
1. Find the node that produces the problematic SSA
2. Find the node that incorrectly uses that SSA
3. Trace the argument flow between witnesses
4. Identify which witness broke the monadic chain

**Example** (from this bug):
- Node 29 produces %v16 (Literal Int 0)
- NativePtr.write uses %v16 as memref
- **Chain**: add receives [buffer=%v12, pos=%v16] → returns %v16 → write receives %v16 as ptr
- **Break**: add should return %v12, not %v16

---

## Common Monadic Corruption Patterns

### Pattern 1: Returning Wrong Argument

**Violation**:
```fsharp
| Operation, [arg1SSA; arg2SSA] ->
    // WRONG: Returns arg2 instead of result
    { Result = TRValue { SSA = arg2SSA; ... } }
```

**Fix**: Return the correct SSA for the operation's semantic meaning.

### Pattern 2: Manually Picking SSAs

**Violation**:
```fsharp
| Operation, [argSSA] ->
    // WRONG: Creating SSA manually instead of using coeffects
    let resultSSA = SSA.V 42
    { Result = TRValue { SSA = resultSSA; ... } }
```

**Fix**: Use pre-allocated SSAs from coeffects:
```fsharp
match SSAAssign.lookupSSA node.Id ctx.Coeffects.SSA with
| Some resultSSA -> ...
```

### Pattern 3: Recursively Witnessing Arguments

**Violation**:
```fsharp
| Operation, [argSSA] ->
    // WRONG: Re-witnessing argument node
    let argResult = witnessNode argNode ctx
    match argResult.Result with ...
```

**Fix**: Arguments already witnessed - get SSAs from coeffects:
```fsharp
match SSAAssign.lookupSSA argNodeId ctx.Coeffects.SSA with
| Some argSSA -> ...
```

---

## Verification After Fix

### Test 1: SSA Uniqueness
```bash
# No SSA should appear in multiple node allocations
jq -r '.ssaAssignment.NodeSSAAssignments[].SSAs[].Display' 06_coeffects.json | sort | uniq -d
```
Expected: Empty output (no duplicates per function)

### Test 2: MLIR Type Consistency
```bash
# All uses of %vN should have same type
mlir-opt --verify-diagnostics 07_output.mlir
```
Expected: No type mismatch errors

### Test 3: Monadic Flow Audit

For each compound operation (like NativePtr.write with NativePtr.add):
- ✅ Base pointer flows through correctly
- ✅ Offset extracted from coeffects, not re-witnessed
- ✅ Each witness uses only its pre-allocated SSAs
- ✅ No manual SSA creation or picking

---

## Memory Cross-References

- `coeffect_compilation_strategy` - SSA pre-allocation via coeffects
- `alex_compositional_architecture_elements_patterns_witnesses` - Witness architecture
- `mlir_memref_strings_no_llvm_cruft` - MLIR type system (index vs i64)

---

## Summary

**The Rule**: If you see SSA "overlap" or "reuse" errors, it's ALWAYS a monadic corruption in a witness.

**The Fix**: Find which witness is returning the wrong SSA or manually picking SSAs, then fix it to maintain the monadic flow using coeffects.

**The Prevention**: Witnesses observe and return. Never transform. Never pick SSAs. Use coeffects for everything.

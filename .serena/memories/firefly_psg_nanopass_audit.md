# Firefly PSG Nanopass Audit for FNCS Migration

## Session Update: January 3, 2026

### Completed Work
1. **BCL Rejection Enhanced**: Added hard-stop FS8104 diagnostic for `Unchecked.defaultof`
2. **FNCS Intrinsics Added**:
   - `NativeStr.fromPointer`: ptr:nativeptr<byte> -> len:int -> string
   - `NativeDefault.zeroed`: unit -> 'T (polymorphic zero initialization)
3. **Alloy Cleaned Up**: Removed all `Unchecked.defaultof` and `box`/`unbox` patterns
   - Primitives.fs, Core.fs, Memory.fs, NativeBuffer.fs, Span.fs, Platform.fs, Math.fs
4. **FNCSTransfer Updated**: Added MLIR emission for new intrinsics
5. **Sample 01**: Compiles and runs correctly ✅

### Remaining Work
- **String Interpolation**: Sample 02 uses `$"Hello, {name}!"` which needs lowering
  - Should be handled in FNCS (semantic transform, not emission logic)
  - Lower to string concatenation calls

---

# Firefly PSG Nanopass Audit for FNCS Migration

> **Date**: January 3, 2026
> **Status**: Audit complete, migration pending
> **Principle**: FNCS owns SemanticGraph; Firefly is "dumb emission"

## Executive Summary

Firefly's `src/Core/PSG/Nanopass/` folder should be **REMOVED** entirely. All nanopasses are semantic transformations that belong in FNCS, not Firefly. The FNCS SemanticGraph should be complete and normalized by the time Firefly consumes it.

## Audit Results

| Nanopass | Purpose | Target | Migration Notes |
|----------|---------|--------|-----------------|
| **ConstantPropagation.fs** | Evaluate constant expressions (string.Length → int) | FNCS | Constant folding during type checking |
| **DetectInlineFunctions.fs** | Mark inline function bindings | FNCS | Already known during type checking |
| **FlattenApplications.fs** | Normalize curried apps to flat form | FNCS | SemanticGraph should be normalized at construction |
| **IntermediateEmission.fs** | Dump PSG state for debugging | FNCS | PhaseEmitter infrastructure exists |
| **LowerInterpolatedStrings.fs** | Transform $"..." to String.concat calls | FNCS | Semantic transformation during checking |
| **LowerStringLength.fs** | Transform string.Length to fidelity_strlen | FNCS | Native type resolution |
| **LowerStructConstructors.fs** | Transform App(struct ctor) to Record | FNCS | Value type handling |
| **ParameterAnnotation.fs** | Annotate function parameters with index | FNCS | SemanticGraph carries this from construction |
| **ReduceAlloyOperators.fs** | Beta reduce Alloy's $ operator | FNCS | SRTP resolution / inlining |
| **ReducePipeOperators.fs** | Beta reduce F# pipe operators | FNCS | Semantic transformation during inlining |

## Architectural Principle

```
FNCS Responsibility:
  - Parse F# source
  - Type check
  - Build complete SemanticGraph with:
    - Types resolved
    - SRTP resolved  
    - Intrinsics lowered
    - Operators reduced
    - Constants folded
    - Applications normalized
    - Parameters annotated

Firefly Responsibility:
  - Read platform triple from fidproj TOML
  - Walk complete SemanticGraph
  - Emit MLIR via platform-specific Bindings
  - Invoke LLVM toolchain
```

## Migration Order

1. **First**: Add FNCS infrastructure for intrinsic lowering
   - `NativeStr.fromPointer(ptr, len)` → struct construction
   - `NativeDefault.zeroed<'T>()` → zero constant

2. **Second**: Port semantic transforms to FNCS
   - ReducePipeOperators (beta reduction)
   - ReduceAlloyOperators ($ operator)
   - FlattenApplications (normalize apps)

3. **Third**: Port native-specific transforms
   - LowerInterpolatedStrings
   - LowerStringLength
   - LowerStructConstructors

4. **Fourth**: Verify and remove
   - Run all FidelityHelloWorld samples (01-04)
   - Remove Firefly PSG folder

## Key Insight: Platform Triple Flow

The platform triple (e.g., `x86_64-unknown-linux-gnu`) comes from:
1. `fidproj` TOML file → `[compilation].target`
2. Passed to FNCS for platform-aware type sizing
3. Passed to Alex for platform-specific MLIR generation

FNCS needs the platform triple for:
- Pointer size (32 vs 64 bit)
- Type alignments
- Platform-specific intrinsic selection

## Files to Remove After Migration

```
/home/hhh/repos/Firefly/src/Core/PSG/Nanopass/
  ConstantPropagation.fs
  DetectInlineFunctions.fs
  FlattenApplications.fs
  IntermediateEmission.fs
  LowerInterpolatedStrings.fs
  LowerStringLength.fs
  LowerStructConstructors.fs
  ParameterAnnotation.fs
  ReduceAlloyOperators.fs
  ReducePipeOperators.fs
```

Also evaluate:
- `/home/hhh/repos/Firefly/src/Core/PSG/Types.fs` - PSG type definitions (if duplicating FNCS)
- `/home/hhh/repos/Firefly/src/Core/PSG/NavigationUtils.fs` - PSG navigation (if duplicating FNCS)

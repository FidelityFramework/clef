# NTU Type Flow in PRD Development (January 2026)

## The Principle

**ALL type information in code generation MUST flow from FNCS through the NTU (Native Type Universe) mapping infrastructure. NEVER hardcode types like `MLIRTypes.i32` or `MLIRTypes.i64`.**

## The Architecture

```
FNCS (NativeType)
    ↓
mapNativeTypeWithGraphForArch (using Platform.TargetArch)
    ↓
MLIRType (platform-appropriate)
    ↓
MLIR operations
```

## Key Functions

### `mapNativeTypeWithGraphForArch`
The PRIMARY type mapping function. Takes:
- `arch: Architecture` - from `z.State.Platform.TargetArch`
- `graph: SemanticGraph` - for type alias resolution
- `nativeType: NativeType` - from FNCS

Returns `MLIRType` appropriate for the platform.

### Usage Pattern

```fsharp
// CORRECT: Get type from FNCS node, map through NTU
let nodeType = someNode.Type  // NativeType from FNCS
let mlirType = mapNativeTypeWithGraphForArch z.State.Platform.TargetArch graph nodeType

// WRONG: Hardcode type
let mlirType = MLIRTypes.i32  // DON'T DO THIS
```

## Anti-Pattern: Hardcoded Types

```fsharp
// WRONG - hardcoding i32 for "int"
let cmpOp = ArithOp.CmpI (cmpSSA, pred, leftSSA, rightSSA, MLIRTypes.i32)

// WRONG - hardcoding i64 for "int64"
let constOp = ArithOp.ConstI (ssa, value, MLIRTypes.i64)
```

Note: With width-as-dimension, `NTUint(Resolved Register)` may be i32 OR i64 depending on platform.
Only `NTUint(Fixed 32)` is truly always i32. This makes hardcoding even more dangerous.

## Correct Pattern: Flow Types Through

```fsharp
// Get operand's type from FNCS (already has NativeType.TInt, TInt64, etc.)
let operandNode = SemanticGraph.tryGetNode operandId graph
let operandType = 
    match operandNode with
    | Some node -> mapNativeTypeWithGraphForArch z.State.Platform.TargetArch graph node.Type
    | None -> mapNativeTypeWithGraphForArch z.State.Platform.TargetArch graph NativeType.TInt

// Use mapped type for operations
let cmpOp = ArithOp.CmpI (cmpSSA, pred, leftSSA, rightSSA, operandType)
```

## Platform Properties Flow

```
Fidelity.Platform (binding library)
    ↓ extracted via Firefly orchestration
Platform context (word size, endianness, etc.)
    ↓ passed to FNCS
z.State.Platform.TargetArch
    ↓ used in mapNativeTypeWithGraphForArch
Platform-appropriate MLIRType
```

## Why This Matters

1. **Platform Portability**: `int` is i32 on some platforms, i64 on others
2. **Correctness**: Type mismatches cause MLIR validation errors
3. **Architecture Integrity**: Types flow from FNCS (source of truth), not guesswork

## PRD Checklist

When implementing new features, verify:

- [ ] No hardcoded `MLIRTypes.i32`, `MLIRTypes.i64`, etc. except for truly fixed types (like i1 for booleans)
- [ ] All operation types derived from `mapNativeTypeWithGraphForArch`
- [ ] Platform properties accessed via `z.State.Platform.TargetArch`
- [ ] Literal types inferred from FNCS node type, not assumed

## Related Memories

- `mlir_dialect_architecture` - Dialect layering (func/cf/scf vs llvm)
- `ntu_type_system` - NTU type universe details
- `fncs_platform_aware_type_resolution` - Platform type staging

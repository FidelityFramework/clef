# SRTP and Operator Architecture in FNCS

## Core Tension

FNCS has two mechanisms for operator resolution that can conflict:

### Mechanism 1: Built-in Bindings (NativeGlobals.fs)
```fsharp
("op_Addition", type_signature)
```
Provides a fixed type for the operator at lookup time.

### Mechanism 2: SRTP Witnesses (SRTPResolution.fs)
```fsharp
numericOpWitness : string -> NativeType -> WitnessResolution option
```
Provides dynamic resolution based on the actual type being operated on.

## The Conflict

If NativeGlobals defines:
```fsharp
("op_Addition", TFun(intType, TFun(intType, intType)))  // Fixed to int!
```

Then SRTP never gets a chance to resolve for `int64`, `uint8`, etc.
The type checker sees "expected int, got int64" and fails.

If NativeGlobals defines:
```fsharp
("op_Addition", mkPolymorphicBinaryOp())  // forall 'a. 'a -> 'a -> 'a
```

Then SRTP CAN resolve, but we need proper witness lookup and constraint solving.

## Correct Architecture

### For NTU with SRTP (F# Compatible)
1. Operators in NativeGlobals are POLYMORPHIC with constraints
2. Type inference determines concrete types
3. SRTP resolution provides witnesses
4. Witnesses map to type-specific MLIR operations

### For Pure ML Style (No SRTP)
1. Standard operators (`+`, `-`) work on `int` (platform word) ONLY
2. Other types use MODULE operators: `Int64.add`, `UInt8.add`
3. No polymorphic operators for arithmetic
4. Simpler but requires source changes

## Current Status (Jan 2026)

The codebase is in a broken hybrid state:
- Arithmetic operators are type-specific for `int` only
- No module operators for other types
- SRTP infrastructure exists but unused for arithmetic
- Result: 1014 type errors

## Path Forward

**Option A: Restore SRTP (Recommended)**
1. Revert arithmetic operators to polymorphic
2. Ensure SRTP witnesses are properly consulted during type checking
3. Witnesses provide type-specific resolutions
4. Alex emits type-specific MLIR based on resolved types

**Option B: Full ML Style**
1. Keep `int`-only standard operators
2. Add module operators for all numeric types
3. Update Alloy to use module operators
4. Remove SRTP for arithmetic (keep for formatting operators like `$`)

## Key Files

- `NativeGlobals.fs` - Built-in operator bindings
- `SRTPResolution.fs` - SRTP witness infrastructure
- `CheckExpressions.fs` - Where operator lookup happens
- `Unify.fs` - Constraint solving

## Related Memories
- `fncs_type_specific_operators_status`
- `fncs_platform_aware_type_resolution`
- `ml_integer_type_patterns`

# NTU Type System Implementation in CCS

## Overview

This document describes how CCS implements the NTU (Native Type Universe) type system for platform-generic types that resolve via quotation-based platform bindings.

## NTUKind Discriminated Union

The core type representation:

```fsharp
/// NTU (Native Type Universe) type kinds
type NTUKind =
    // Platform-dependent (resolved via quotations)
    | NTUint      // Platform word, signed
    | NTUuint     // Platform word, unsigned
    | NTUnint     // Native int (pointer-sized signed)
    | NTUunint    // Native uint (pointer-sized unsigned)
    | NTUptr of NativeType  // Pointer to type
    | NTUsize     // size_t equivalent
    | NTUdiff     // ptrdiff_t equivalent
    
    // Fixed width (platform-independent)
    | NTUint8
    | NTUint16
    | NTUint32
    | NTUint64
    | NTUuint8
    | NTUuint16
    | NTUuint32
    | NTUuint64
    | NTUfloat32
    | NTUfloat64
```

## F# Type to NTU Mapping

### Standard F# Types

| F# Type | NTU Internal | Notes |
|---------|--------------|-------|
| `int` | NTUint | Platform word (64-bit on x86_64) |
| `uint` | NTUuint | Platform word (unsigned) |
| `int8` / `sbyte` | NTUint8 | Fixed 8-bit |
| `int16` | NTUint16 | Fixed 16-bit |
| `int32` | NTUint32 | Fixed 32-bit |
| `int64` | NTUint64 | Fixed 64-bit |
| `uint8` / `byte` | NTUuint8 | Fixed 8-bit unsigned |
| `uint16` | NTUuint16 | Fixed 16-bit unsigned |
| `uint32` | NTUuint32 | Fixed 32-bit unsigned |
| `uint64` | NTUuint64 | Fixed 64-bit unsigned |
| `nativeint` | NTUnint | Pointer-sized signed |
| `unativeint` | NTUunint | Pointer-sized unsigned |
| `Ptr<'T, 'Region, 'Access>` | NTUptr | Pointer-shaped handle; `nativeptr<'T>` is not denotable (`TNativePtr` is compiler-internal) |
| `float32` / `single` | NTUfloat32 | 32-bit float |
| `float` / `double` | NTUfloat64 | 64-bit float |

### Semantic Aliases (from Alloy)

| Alloy Alias | NTU Internal | Purpose |
|-------------|--------------|---------|
| `platformint` | NTUint | Explicit platform word |
| `platformuint` | NTUuint | Explicit platform word unsigned |
| `platformsize` | NTUsize | size_t equivalent |

## Type Identity vs Type Width

### Key Principle

Type identity and type width are **separate concerns**:

```fsharp
// Type identity - enforced by CCS
NTUint ≠ NTUint64   // Different types!
NTUint ≠ NTUint32   // Different types!

// Type width - resolved by Alex
NTUint on x86_64 → i64
NTUint on ARM32 → i32
```

### What CCS Enforces

1. **Type Identity**: `int + int` ✓, `int + int64` ✗
2. **Unification**: NTU types unify with themselves only
3. **SRTP Resolution**: Operator witnesses based on type identity
4. **No Width Assumptions**: CCS never assumes byte sizes

### What Alex Resolves

1. **Concrete Widths**: NTUint → i64 on x86_64
2. **Memory Layouts**: Struct field offsets
3. **Calling Conventions**: Register allocation

## NTULayout: Erased Assumptions

Following F*'s pattern:

```fsharp
/// Platform-resolved type layout (erased at runtime)
type NTULayout = {
    Kind: NTUKind
    /// Erased - only for type checking, resolved by Alex
    AssumedSize: int option
    AssumedAlignment: int option
}
```

The `AssumedSize` and `AssumedAlignment` are **compile-time metadata only**. They are erased - not present at runtime.

## Type Constructor Updates

### Before (Hardcoded Widths)

```fsharp
// WRONG - hardcoded 8 bytes
let intTyCon = mkTypeConRef "int" 0 (TypeLayout.Inline(8, 8))
```

### After (NTU Types)

```fsharp
// CORRECT - platform-dependent
let intTyCon = mkTypeConRef "int" 0 (NTULayout.Create(NTUint))
let int64TyCon = mkTypeConRef "int64" 0 (NTULayout.Create(NTUint64))
```

## Implementation Files

| File | Changes |
|------|---------|
| `NativeTypes.fs` | Add NTUKind, NTULayout types |
| `NativeGlobals.fs` | Update type constructors to use NTU |
| `SemanticGraph.fs` | Add platform context field |
| `Unify.fs` | Handle NTU type unification |
| `CheckExpressions.fs` | Map F# syntax to NTU types |

## Unification Rules

### NTU Types Unify with Themselves Only

```fsharp
match ty1, ty2 with
| TApp(tc1, []), TApp(tc2, []) when tc1.NTUKind = tc2.NTUKind -> 
    Success()  // Same NTU type
| TApp(tc1, []), TApp(tc2, []) when tc1.NTUKind <> tc2.NTUKind ->
    Error(TypeMismatch(ty1, ty2))  // Different NTU types
```

### No Implicit Widening

```fsharp
// These are TYPE ERRORS, not implicit conversions
let x: int64 = 42       // Error: int ≠ int64
let y: int = 42L        // Error: int64 ≠ int

// Explicit conversions required
let x: int64 = int64 42
let y: int = int 42L
```

## SRTP Resolution with NTU

SRTP witnesses are resolved based on NTU type identity:

```fsharp
// Operator (+) has witnesses for each NTU type
type NTUintOps = 
    static member inline (+) (a: int, b: int) : int = ...
    
type NTUint64Ops =
    static member inline (+) (a: int64, b: int64) : int64 = ...
```

CCS selects the correct witness based on operand types (NTUint vs NTUint64).

## Platform Predicates Integration

Platform predicates affect type validity:

```fsharp
// Only valid on 64-bit platforms
let x: int64 = ...  // Requires fits_u64

// Always valid
let y: int32 = ...  // No platform requirements
```

CCS validates predicates; Alex eliminates dead code.

## Migration from PlatformWord

The previous `TypeLayout.PlatformWord` design is superseded:

| Before | After |
|--------|-------|
| `TypeLayout.PlatformWord` | `NTULayout.Create(NTUint)` |
| Single discriminant | Full NTUKind enum |
| No type identity distinction | Clear type identity |

## Related Documentation

- `Platform_Predicates.md` - F*-style platform predicates
- `ccs-specification.md` - CCS specification
- `native-type-universe.md` - Original NTU design

# NTU Type System in FNCS

## Overview

FNCS implements the NTU (Native Type Universe) type system for platform-generic types. This follows the F* pattern where type WIDTH is an erased assumption, not part of type identity.

## NTUKind Discriminated Union

The core type representation in FNCS:

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
    | NTUint8 | NTUint16 | NTUint32 | NTUint64
    | NTUuint8 | NTUuint16 | NTUuint32 | NTUuint64
    | NTUfloat32 | NTUfloat64
```

## Erased Layout Assumptions

Following F*'s pattern, width is compile-time metadata:

```fsharp
/// Platform-resolved type layout (erased at runtime)
type NTULayout = {
    Kind: NTUKind
    /// Erased - only for type checking, resolved by Alex
    AssumedSize: int option
    AssumedAlignment: int option
}
```

## Type Identity vs Type Width

**Key Principle**: Type identity and type width are SEPARATE concerns.

- **Type Identity**: `NTUint ≠ NTUint64` - these are different types
- **Type Width**: Erased assumption, resolved by platform quotations

FNCS enforces type identity. It does NOT assume width. Alex witnesses quotations to resolve width.

## Integration with F# Type Names

Standard F# types map to NTU types:

| F# Type | NTU Internal | Notes |
|---------|--------------|-------|
| `int` | NTUint | Platform word, signed |
| `uint` | NTUuint | Platform word, unsigned |
| `int32` | NTUint32 | Fixed 32-bit |
| `int64` | NTUint64 | Fixed 64-bit |
| `nativeint` | NTUnint | Pointer-sized |
| `nativeptr<'T>` | NTUptr | Pointer |

## Platform Predicates

F*-inspired abstract propositions for conditional compilation:

```fsharp
/// Platform predicate types (abstract, erased)
type PlatformPredicate =
    | FitsU32     // Platform supports 32-bit word ops
    | FitsU64     // Platform supports 64-bit word ops
    | HasAVX512   // Has AVX-512 vector support
    | HasNEON     // Has NEON vector support
    | HasAtomics64 // Has 64-bit atomic operations
```

These predicates:
- Flow through FNCS unchanged
- Enable conditional compilation without runtime checks
- Resolved by Alex using platform quotations

## Option B: Internal NTU with Semantic Aliases

The architectural choice for exposing NTU:

1. **FNCS internally**: Uses NTU prefix for all native types
2. **Fidelity.Platform publicly**: Exposes semantic aliases (`platformint`, `platformsize`)
3. **Application code**: Uses standard `int` or explicit `platformint`

```
Level 1 (Default)     Level 2/3 (Explicit)     FNCS Internal
─────────────────────────────────────────────────────────────
int                   platformint              NTUint
uint                  platformuint             NTUuint
```

## Implementation Status

### Completed

1. **NativeTypes.fs** - NTUKind implementation complete:
   - `NTUKind` discriminated union with all primitive types
   - `PlatformPredicate` for F*-style predicates
   - `NTUKind` module with helper functions (`isPlatformDependent`, `isInteger`, etc.)
   - `TypeConRef` extended with `NTUKind: NTUKind option` field
   - Helper functions: `mkNTUTypeConRef`, `mkNTUTypeConRefWithArity`

2. **NativeGlobals.fs** - NTU-based type constructors:
   - All primitive types use `mkNTUTypeConRef` with appropriate NTU kinds
   - Pointer types (nativeptr, voidptr, byref, inref, outref) use NTUptr
   - Type checking helpers updated to use NTUKind
   - New helpers: `isPlatformDependentType`, `getNTUKind`

### Completed (cont.)

3. **SemanticGraph.fs** - Platform context added:
   - `PlatformContext` type with size/alignment resolution helpers
   - `SemanticGraph.Platform` field (optional)
   - `PlatformContext.fromPlatformPath` helper to create from .fidproj path
   - `PlatformContext.resolveSize` and `resolveAlign` for NTU type resolution

4. **ProjectChecker.fs** - Platform context wiring:
   - Extracts PlatformPath from FidprojOptions
   - Creates PlatformContext and attaches to SemanticGraph

## Files Modified

Primary implementation locations in FNCS:

- `src/Compiler/Checking.Native/NativeTypes.fs` - NTUKind definition ✓
- `src/Compiler/Checking.Native/NativeGlobals.fs` - NTU-based primitives ✓
- `src/Compiler/TypedTree/TcGlobals.fs` - TypeConRef usage updated ✓
- `src/Compiler/Checking.Native/SemanticGraph.fs` - Add platform context field (pending)

## Related Memories

- `native_type_universe_foundations` - Prior NTU design work
- `fncs_platform_aware_type_resolution` - Platform context passing
- `platform_word_implementation_status` - Superseded by NTU

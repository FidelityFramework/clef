# NTU Type System in FNCS

## Overview

FNCS implements the NTU (Native Type Universe) type system for platform-generic types. This follows the F* pattern where type WIDTH is an erased assumption, not part of type identity.

## NTUKind Discriminated Union (Width-as-Dimension, Feb 2026)

The core type representation uses **parameterized width** — 3 numeric kinds replace 16 discrete variants:

```fsharp
/// Platform-resolved width dimensions — NTU-native vocabulary
[<RequireQualifiedAccess>]
type WidthDimension =
    | Pointer    // Address width (64-bit on x86_64, 32-bit on ARM32)
    | Register   // Machine register / natural word width

/// How the width of a numeric type is determined
[<RequireQualifiedAccess>]
type NTUWidth =
    | Fixed of bits: int              // Known at all times: 8, 16, 32, 64
    | Resolved of WidthDimension      // Platform-dependent, resolved by Alex

/// NTU type kinds — numeric types parameterized by width
[<RequireQualifiedAccess>]
type NTUKind =
    | NTUint of NTUWidth      // Signed integer of any width
    | NTUuint of NTUWidth     // Unsigned integer of any width
    | NTUfloat of NTUWidth    // IEEE float of any width
    | NTUptr | NTUfnptr       // Pointer types (width = Pointer, implicit)
    | NTUsize | NTUdiff       // Semantic pointer-width aliases
    | NTUstring | NTUbool | NTUchar | NTUunit | NTUdecimal
    | NTUlazy | NTUseq
    | NTUarray | NTUlist | NTUmap | NTUset
    | NTUuuid | NTUdatetime | NTUtimespan
```

**NTUother is ELIMINATED.** No escape hatch — every type is parameterized or user-defined composite.

Old → New mapping:
```
NTUint      → NTUint (Resolved Register)
NTUuint     → NTUuint (Resolved Register)
NTUnint     → NTUint (Resolved Pointer)
NTUunint    → NTUuint (Resolved Pointer)
NTUint32    → NTUint (Fixed 32)
NTUint64    → NTUint (Fixed 64)
NTUfloat32  → NTUfloat (Fixed 32)
NTUfloat64  → NTUfloat (Fixed 64)
**(Old DU listing removed — see NTUKind Discriminated Union section above for current parameterized form)**

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

**Key Principle**: Type identity and type width are SEPARATE concerns. Width is a first-class dimension.

- **Type Identity**: `NTUint(Resolved Register) ≠ NTUint(Fixed 64)` — different types
- **Type Width**: Erased assumption, resolved by Alex via `PlatformContext.Dimensions`

FNCS enforces type identity. It does NOT assume width. Alex witnesses quotations to resolve width.

## PlatformContext (Width Resolution)

```fsharp
type PlatformContext = {
    PlatformId: string
    Dimensions: Map<WidthDimension, int>  // Pointer → 64, Register → 64, etc.
    PointerAlign: int
    PlatformLibraryPath: string option
    Predicates: Map<PlatformPredicate, bool>
    FreestandingStartup: FreestandingStartup option
}

module PlatformContext =
    let resolveWidth (ctx: PlatformContext) (width: NTUWidth) : int =
        match width with
        | NTUWidth.Fixed bits -> bits
        | NTUWidth.Resolved dim -> ctx.Dimensions.[dim]
```

## Integration with F# Type Names

Standard F# types map to parameterized NTU types:

| F# Type | NTU Internal | Width |
|---------|--------------|-------|
| `int` | `NTUint (Resolved Register)` | Platform word |
| `uint` | `NTUuint (Resolved Register)` | Platform word |
| `int32` | `NTUint (Fixed 32)` | 32-bit |
| `int64` | `NTUint (Fixed 64)` | 64-bit |
| `nativeint` | `NTUint (Resolved Pointer)` | Pointer-sized |
| `float32` | `NTUfloat (Fixed 32)` | 32-bit |
| `float` | `NTUfloat (Fixed 64)` | 64-bit |
| `nativeptr<'T>` | `NTUptr` | Pointer-sized |
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

2. *(DELETED: NativeGlobals.fs - greenfield pending)*
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
- *(DELETED: NativeGlobals.fs)*
- `src/Compiler/TypedTree/TcGlobals.fs` - TypeConRef usage updated ✓
- `src/Compiler/Checking.Native/SemanticGraph.fs` - Add platform context field (pending)

## Multi-Dimensional Architecture (Feb 2026 Design Session)

Width is the **first implemented dimensional axis** of a broader multi-dimensional type substrate.
The full vision (documented in fsnative-spec `ntu-dimensional-architecture.md`) includes:

- **Width** (implemented): `NTUWidth = Fixed of int | Resolved of WidthDimension`
- **Memory Space** (design): global/shared/private/peripheral/stack — critical for GPU, MCU
- **Access Pattern** (design): read-only/write-only/read-write/volatile — formalizes BAREWire qualifiers
- **Alignment** (design): cache-line/natural/packed/page — platform-resolved like width
- **Tensor Shape** (future): batch/channel/height/width indices for ML/NPU targets

**Key insight**: Dimensions don't erase after type checking — they flow through the PSG and
inform code generation for any target. When a section of the program graph takes a platform
definition, it becomes concretely typed for that target, but the NTU machinery provides the
abstract dimensional underpinnings to accept and map from target to target.

**Multi-stack compilation**: Different sections of the program graph may target different
compute architectures (CPU, GPU, FPGA, NPU). Each section resolves dimensions against its
own PlatformContext. BAREWire contracts between sections ensure type-safe data handoff.

**Farscape's role**: Second-order consumer — it revealed that WidthDimension needed
extensibility for C ABI diversity, catalyzing this broader rethinking. Farscape resolves
C ABI widths at generation time using PlatformABI, emitting Fixed-width NTU types.
New dimensions come from Fidelity.Platform, not from binding generators.

## Related Memories

- `native_type_universe_foundations` - Prior NTU design work
- `fncs_platform_aware_type_resolution` - Platform context passing
- `platform_word_implementation_status` - Superseded by NTU
- `fidproj_platform_context_principle` - PlatformContext as dimension resolution source
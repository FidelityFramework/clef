# PlatformWord Implementation Status (January 2026)

> **STATUS: SUPERSEDED by NTU Architecture**
> The `PlatformWord` layout is being replaced by the NTU (Native Type Universe) architecture.
> See `ntu_type_system` memory for the new design.
>
> **Key Change**: Instead of a single `PlatformWord` layout discriminant, FNCS now uses
> a complete `NTUKind` discriminated union that distinguishes:
> - Platform-dependent types: `NTUint`, `NTUuint`, `NTUptr`, `NTUsize`, `NTUdiff`
> - Fixed-width types: `NTUint32`, `NTUint64`, etc.
>
> This provides proper type identity (NTUint ≠ NTUint64) while allowing platform
> quotations to resolve width at code generation time.

## Completed Work

### 1. TypeLayout.PlatformWord Added
File: `src/Compiler/Checking.Native/NativeTypes.fs`
```fsharp
type TypeLayout =
    | Inline of size: int * align: int
    | Reference of arena: ArenaAffinity
    | Opaque
    | PlatformWord  // NEW: Size depends on target architecture
```

### 2. Primitive Types Updated to Use PlatformWord
File: `src/Compiler/Checking.Native/NativeGlobals.fs`
- `intTyCon` → PlatformWord (was Inline(8,8))
- `uintTyCon` → PlatformWord (was Inline(8,8))
- `nintTyCon` (nativeint) → PlatformWord
- `unintTyCon` (unativeint) → PlatformWord
- `nativeptrTyCon` → PlatformWord
- `voidptrTyCon` → PlatformWord
- `byrefTyCon` → PlatformWord
- `inrefTyCon` → PlatformWord
- `outrefTyCon` → PlatformWord

### 3. Layout Functions Updated
- `layoutOf` in NativeTypes.fs: TNativePtr and TByref return PlatformWord
- `isValueType` in NativeGlobals.fs: PlatformWord treated as value type
- `computeRecordLayout` in NativeTypes.fs: PlatformWord propagates unknown layout
- Unify.fs: PlatformWord layout compatibility handled

### 4. F# 6 Dotless Indexer Syntax Fixed (Jan 4, 2026)
File: `src/Compiler/Checking.Native/CheckExpressions.fs`
- Added pattern for `SynExpr.App(_, _, objExpr, SynExpr.ArrayOrListComputed(false, indexExpr, _), _)`
- Now correctly recognized as `IndexGet` instead of list application
- Added corresponding `IndexSet` pattern for assignment

## Current Error State: 507 Type Errors

After dotless indexer fix, error count is 507 (down from inflated 1014 due to debug output).

### Error Distribution by File
| File | Errors |
|------|--------|
| Binary.fs | 150 |
| Text.fs | 58 |
| Bits.fs | 55 |
| Uuid.fs | 42 |
| Span.fs | 25 |
| Math.fs | 24 |
| Numerics.fs | 18 |
| Console.fs | 9 |
| String.fs | 8 |
| Memory.fs | 6 |
| Core.fs | 6 |
| NativeBuffer.fs | 2 |

Plus ~100 SRTP witness errors (`*.Invoke not defined`)

### Error Categories

**Category A: Type Identity Mismatches (~400 errors)**
- `expected 'int64', got 'int'`
- `expected 'int', got 'uint8'`
These are GENUINE type errors. FNCS correctly distinguishes `int ≠ int64 ≠ int32`.
Fix: Explicit type conversions in Alloy code.

**Category B: SRTP Witness Errors (~100 errors)**
- `Internal.IsEmpty.Invoke not defined`
- `Internal.Value.Invoke not defined`
- `Add.Invoke not defined`
These indicate SRTP resolution is not finding witness implementations.
Fix: SRTP witness resolution infrastructure.

## Architectural Principles (Confirmed)

1. **FNCS handles type IDENTITY** - `int`, `int64`, `int32` are DISTINCT types
2. **Alex handles type SIZE** - `PlatformWord` resolves to i64/i32 at codegen
3. **Errors are genuine** - Type mismatches in Alloy need downstream fixes

## Architecture Update: Quotation-Based Platform Bindings (Jan 2026)

The platform context approach has evolved. Instead of threading a `PlatformConfig` struct through FNCS, platform info comes from **quotation-based binding libraries**:

**Fidelity.Platform Monorepo**: `~/repos/Fidelity.Platform/`
```
Linux_x86_64/
├── Types.fs       # TypeLayout, SyscallConvention types
├── Platform.fs    # Expr<PlatformDescriptor> quotation
├── Syscalls.fs    # Syscall numbers
└── .fsproj
```

**Flow**:
1. **Firefly** parses fidproj via **Fidelity.Toml** (separate TOML 1.0 lib)
2. **Firefly** loads platform library, extracts quotations
3. **FNCS** receives quotations as parameters (NO file I/O)
4. **FNCS** attaches platform metadata to PSG nodes
5. **Alex** witnesses quotations → generates correct MLIR widths

**Key Insight**: Platform awareness flows FROM THE TOP via binding libraries (same pattern as Farscape → CMSIS for embedded).

## Next Steps (Updated)

1. **Thread platform quotations** - Firefly passes Expr<PlatformDescriptor> to FNCS
2. **FNCS attaches metadata** - Platform quotations flow through PSG unchanged
3. **Alex witnesses quotations** - Resolves PlatformWord to concrete i64/i32
4. **Fix SRTP witness resolution** - `*.Invoke` witness generation
5. **Fix Alloy type errors** - Explicit conversions where needed

## Related Memories
- `fncs_platform_aware_type_resolution` - Architecture design
- `fidproj_platform_context_principle` - Platform context flow
- `srtp_operator_architecture` - SRTP mechanism
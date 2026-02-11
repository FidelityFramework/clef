# FNCS Platform-Aware Type Resolution Architecture

> **Related**: This memory describes the platform-aware staging design. The implementation
> now uses the **NTU (Native Type Universe)** nomenclature. See `ntu_type_system` memory.
>
> Key NTU changes (Feb 2026):
> - Width is now a first-class dimension: `NTUWidth = Fixed of bits | Resolved of WidthDimension`
> - 3 parameterized kinds (`NTUint of NTUWidth`, `NTUuint of NTUWidth`, `NTUfloat of NTUWidth`) replace 16 discrete variants
> - `PlatformContext.Dimensions: Map<WidthDimension, int>` replaces `WordSize`/`PointerSize`
> - `NTUother` eliminated entirely

## Critical Insight: Nanopass Staging for Platform Types

The compilation pipeline has a deliberate staging for platform-dependent types:

```
FNCS: Type IDENTITY (int ≠ int64 ≠ int32, all distinct types)
      ↓
PSG:  Carries ABSTRACT types (int = "platform word", size TBD)
      ↓
Alex: Type RESOLUTION (platform word → i64 on x86_64, i32 on ARM32)
```

### What FNCS Needs to Know (Early Stage)
- Type **identity** - `int`, `int64`, `int32` are DISTINCT types
- Type **compatibility** - `int + int` ✓, `int + int64` ✗
- SRTP resolution - which operator witness for which type

### What FNCS Does NOT Need (Deferred to Alex)
- Exact byte sizes (is `int` 4 or 8 bytes?)
- Memory layout for codegen
- MLIR type widths (i32 vs i64)

### What Alex Needs (Late Stage)
- Concrete sizes based on target from fidproj
- `int` → `i64` on x86_64, `i32` on ARM32/thumbv8m
- `nativeptr<T>` → pointer size based on target

## TypeLayout.PlatformWord and Width-as-Dimension

TypeLayout.PlatformWord is now backed by parameterized NTUWidth:

```fsharp
// TypeConRef constructors use parameterized NTUKind
let intTyCon = mkNTUTypeConRef "int" (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)) TypeLayout.PlatformWord
let int32TyCon = mkNTUTypeConRef "int32" (NTUKind.NTUint (NTUWidth.Fixed 32)) (TypeLayout.Inline(4, 4))
let nintTyCon = mkNTUTypeConRef "nativeint" (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer)) TypeLayout.PlatformWord
let float64TyCon = mkNTUTypeConRef "float" (NTUKind.NTUfloat (NTUWidth.Fixed 64)) (TypeLayout.Inline(8, 8))
```

Alex resolves `Resolved` widths via `PlatformContext.Dimensions`:
- `Resolved Register` on x86_64 → 64 bits (8 bytes)
- `Resolved Register` on ARM32 → 32 bits (4 bytes)
- `Fixed 32` → always 32 bits (4 bytes), platform-independent

## Platform Context Flow: Quotation-Based Architecture (Updated Jan 2026)

**Correct Architecture (quotation-based):**
```
~/repos/Fidelity.Platform/Linux_x86_64/
├── Types.fs       # TypeLayout, SyscallConvention, etc.
├── Platform.fs    # Expr<PlatformDescriptor> quotation
├── Syscalls.fs    # Syscall numbers as quotations
    ↓
Firefly loads platform library (via Fidelity.Toml parsing of fidproj)
    ↓
Extracts quotations: typeLayouts, syscallConvention, platformDescriptor
    ↓
Passes to FNCS as PlatformContext parameter (NOT fidproj, NOT target triple)
    ↓
FNCS attaches platform metadata to PSG nodes
    ↓
Alex witnesses quotations → generates correct MLIR widths
```

**Critical I/O Boundary:**
- **Firefly** does ALL file I/O (fidproj parsing, platform library loading)
- **FNCS** is PURE - receives parameters only, no file system access
- Platform info comes as **pre-extracted quotations**, not raw config

**Platform Quotation Example:**
```fsharp
// From Fidelity.Platform/Linux_x86_64/Platform.fs
let typeLayouts: Expr<Map<string, TypeLayout>> = <@
    Map.ofList [
        "int8", { Size = 1; Alignment = 1 }
        "int32", { Size = 4; Alignment = 4 }
        "nativeint", { Size = 8; Alignment = 8 }  // 64-bit on x86-64
        ...
    ]
@>

let syscallConvention: Expr<SyscallConvention> = <@
    { CallingConvention = SysV_AMD64
      ArgRegisters = [| RDI; RSI; RDX; R10; R8; R9 |]
      ReturnRegister = RAX
      SyscallInstruction = Syscall }
@>
```

## Key Principle from User

> "Generics should still be a library or design-time consideration and SRTP is a compiler concern. So the point is to - as soon as platform and other constraints are known - and they should be known as soon as the fidproj file is read - that the SRTP resolution is affected."

This means:
1. **fidproj read time**: Platform context is KNOWN
2. **FNCS checking time**: SRTP resolution should USE platform context
3. **Operator resolution**: Based on type AND platform constraints

## Files to Modify

1. `NativeTypes.fs` - Add `TypeLayout.PlatformWord` case
2. (Type resolution via resolveSynType at boundary)
3. `NativeService.fs` - Thread platform config through checking
4. `ProjectLoader.fs` - Extract and pass platform config
5. Alex codegen - Resolve `PlatformWord` to concrete sizes

## Related Memories
- `fncs_type_specific_operators_status` - Current operator implementation
- `ml_integer_type_patterns` - ML/FStar reference patterns
- `fncs_architecture` - Overall FNCS design

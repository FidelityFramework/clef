# FNCS Platform-Aware Type Resolution Architecture

> **Related**: This memory describes the platform-aware staging design. The implementation
> now uses the **NTU (Native Type Universe)** nomenclature. See `ntu_type_system` memory.
>
> Key NTU changes:
> - `TypeLayout.PlatformWord` evolves into `NTUKind` discriminated union
> - Types like `NTUint`, `NTUuint`, `NTUptr` provide proper type identity
> - Platform predicates (`fits_u32`, `fits_u64`) enable conditional compilation

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

## TypeLayout.PlatformWord Concept

**Current (WRONG - hardcodes sizes in FNCS):**
```fsharp
let intTyCon = mkTypeConRef "int" 0 (TypeLayout.Inline(8, 8))  // HARDCODED 8 bytes
```

**Correct (abstract size, resolved by Alex):**
```fsharp
type TypeLayout =
    | Inline of size: int * align: int  // Fixed size types (int32, int64, etc.)
    | Reference of ArenaAffinity
    | Opaque                             // Unknown at this stage
    | PlatformWord                       // NEW: Size depends on target architecture

let intTyCon = mkTypeConRef "int" 0 TypeLayout.PlatformWord
let uintTyCon = mkTypeConRef "uint" 0 TypeLayout.PlatformWord
let nintTyCon = mkTypeConRef "nativeint" 0 TypeLayout.PlatformWord
let nativeptrTyCon = mkTypeConRef "nativeptr" 1 TypeLayout.PlatformWord
```

Alex then resolves based on target:
- `TypeLayout.PlatformWord` on x86_64 → 8 bytes (i64)
- `TypeLayout.PlatformWord` on ARM32 → 4 bytes (i32)
- `TypeLayout.PlatformWord` on WASM32 → 4 bytes (i32)

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
2. `NativeGlobals.fs` - Use `PlatformWord` for `int`, `uint`, `nativeint`, `nativeptr`
3. `NativeService.fs` - Thread platform config through checking
4. `ProjectLoader.fs` - Extract and pass platform config
5. Alex codegen - Resolve `PlatformWord` to concrete sizes

## Related Memories
- `fncs_type_specific_operators_status` - Current operator implementation
- `ml_integer_type_patterns` - ML/FStar reference patterns
- `fncs_architecture` - Overall FNCS design

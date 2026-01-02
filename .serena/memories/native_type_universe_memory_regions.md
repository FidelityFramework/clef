# Native Type Universe: Memory Regions (UMX Integration)

> **Canonical Source**: `fsnative-spec/spec/native-type-universe.md` Part 8
> **Status**: Intrinsic to FNCS - Core Fidelity Principle

## Core Principle

Memory region types are **intrinsic to FNCS** - as fundamental as `voption`. They:
- Carry semantic meaning through the entire compilation pipeline
- Guide every memory layout decision
- **Fidelity makes ALL memory layout decisions - MLIR/LLVM never determine layout**

### Erasure at Last Lowering

Types ARE erased - but at the **last possible lowering stage**, after Fidelity has made all decisions. By the time code reaches LLVM, "the type information that guided every transformation has done its job and compiled away to nothing."

This is the entire point of "Fidelity" - preserving type fidelity through compilation.

## Memory Regions

| Region | Use Case | Volatile | Cacheable | Code Generation Effect |
|--------|----------|----------|-----------|------------------------|
| `Stack` | Thread-local automatic | No | Yes | Stack allocation, auto cleanup |
| `Arena` | Bulk allocation, batch free | No | Yes | Arena allocator calls |
| `Peripheral` | Memory-mapped I/O | Yes | No | Volatile loads/stores |
| `Sram` | General RAM | No | Yes | Standard memory access |
| `Flash` | Read-only program memory | No | Yes | Read-only access |

```fsharp
type Stack      // Thread-local, automatic lifetime
type Arena      // Compiler-managed bulk allocation
type Peripheral // Memory-mapped I/O (volatile semantics)
type Sram       // General-purpose RAM
type Flash      // Read-only storage
```

## Access Kinds

| Kind | Read | Write | CMSIS | Code Generation Effect |
|------|------|-------|-------|------------------------|
| `ReadOnly` | Yes | No | `__I` | No store instructions |
| `WriteOnly` | No | Yes | `__O` | No load instructions |
| `ReadWrite` | Yes | Yes | `__IO` | Both permitted |

## Region-Typed Pointers

```fsharp
type Ptr<'T, 'Region, 'Access>

let gpioReg : Ptr<uint32, Peripheral, ReadWrite> = ...
let flashData : Ptr<byte, Flash, ReadOnly> = ...
```

### Compile-Time Safety

```fsharp
// ERROR: Cannot write to readOnly pointer
let writeFlash (p: Ptr<byte, Flash, ReadOnly>) =
    Ptr.write p 0uy  // Compile error!

// OK: Can read from readOnly
let readFlash (p: Ptr<byte, Flash, ReadOnly>) =
    Ptr.read p  // OK
```

## Hardware Peripheral Descriptors

```fsharp
[<PeripheralDescriptor("GPIO", 0x48000000UL)>]
type GPIO_TypeDef = {
    [<Register("MODER", 0x00u, "rw")>]
    MODER: Ptr<uint32, peripheral, readWrite>
    
    [<Register("IDR", 0x10u, "r")>]
    IDR: Ptr<uint32, peripheral, readOnly>
}
```

## Why This Matters

1. **Carry semantic meaning** through entire pipeline
2. **Guide Alex's code generation** - `Peripheral` → volatile LLVM
3. **Determine allocation strategy** - `Stack` vs `Arena`
4. **Enable compile-time safety** - region mismatches are type errors
5. **Erase at final lowering** - only after ALL Fidelity decisions

## Cross-References

- **fsnative-spec**: `spec/native-type-universe.md` Part 8
- **fsnative-spec**: `spec/memory-regions.md` for normative requirements
- **fsnative-spec**: `spec/access-kinds.md` for access kind rules
- **FNCS**: `quotation_semantic_carriers` for peripheral descriptors

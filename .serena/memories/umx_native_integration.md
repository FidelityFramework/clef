# UMX Native Integration in fsnative

## Milestone: Units of Measure on Any Type

**Date:** December 2025

In fsnative, units of measure work on **any type** - not just numerics like in .NET F#. This is not "UMX extended" - it's the native behavior of the type system.

## What Changed

### TypeParamKind Distinction

```fsharp
type TypeParamKind =
    | Type      // Regular type parameter: 'T
    | Measure   // Measure parameter: [<Measure>] 'u
```

### TypeConRef Tracks Parameter Kinds

```fsharp
type TypeConRef = {
    Name: string
    Module: ModulePath
    ParamKinds: TypeParamKind list  // Which params are types vs measures
    Layout: TypeLayout
}
```

### Pointer Types with Memory Semantics

```fsharp
// Ptr<'T, 'region, 'access> - native pointer with region and access measures
let ptrTyCon = mkTypeConRefWithMeasures "Ptr"
    [TypeParamKind.Type; TypeParamKind.Measure; TypeParamKind.Measure]
    (TypeLayout.Inline(8, 8))
```

## Memory Region Measures

Built-in measures for tracking where data lives:

| Measure | Purpose |
|---------|---------|
| `stack` | Automatically freed on scope exit |
| `arena` | Managed by allocator |
| `sram` | Fast on-chip RAM (embedded) |
| `flash` | Persistent storage (embedded) |
| `peripheral` | Memory-mapped I/O registers |
| `dma` | Accessible by DMA controller |

## Access Mode Measures

Built-in measures for tracking read/write permissions:

| Measure | Purpose |
|---------|---------|
| `ro` | Read-only access |
| `wo` | Write-only access |
| `rw` | Read-write access |

## Example: Type-Safe Hardware Access

```fsharp
// A GPIO register pointer: read-write access to peripheral memory
let gpioData: Ptr<uint32, peripheral, rw> = ...

// Read from an ADC: read-only access
let adcValue: Ptr<uint16, peripheral, ro> = ...

// DMA buffer: read-write access to DMA-accessible memory
let dmaBuffer: Span<byte, dma, rw> = ...
```

## Why This Matters

1. **Compile-time safety**: Memory access violations are type errors
2. **No runtime overhead**: Measures are erased - Ptr is just a pointer
3. **Hardware integration**: Peripheral access is type-checked
4. **Region tracking**: Lifetime and allocation context are explicit

## Files Changed

- `Checking.Native/NativeTypes.fs` - Added TypeParamKind, updated TypeConRef and TypeParam
- `Checking.Native/NativeGlobals.fs` - Added MemoryRegions, AccessModes, Ptr/Span/Ref types
- `Checking.Native/UnionFind.fs` - Updated freshTypeParam to track Kind

## Relationship to UMX Library

The FSharp.UMX library provides `[<MeasureAnnotatedAbbreviation>]` as a workaround for .NET F#'s numeric-only measure restriction. In fsnative, this workaround is unnecessary - measures work natively on any type.

## Next Steps

1. Unification must respect measure/type distinction
2. SRTP resolution for measure-parameterized types
3. Volatile access emission for peripheral regions
4. Error messages for access violations (FS8001, FS8002, FS8003)

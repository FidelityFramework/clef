# Platform Binding Recognition in FNCS

> **Status**: SUPERSEDED by unified binding architecture
> **See**: `binding_architecture_unified` in Firefly for canonical documentation
> **Last Updated**: January 2026

## Architecture Update

The original `Platform.Bindings` pattern in Alloy has been **superseded** by a cleaner three-layer architecture:

| Layer | Mechanism | Example |
|-------|-----------|---------|
| **FNCS Intrinsics** | Module pattern recognition | `Sys.write`, `NativePtr.set` |
| **Binding Libraries** | Quotation semantic carriers | GTK, CMSIS (Farscape-generated) |
| **User Code** | Pure F# using above | Alloy, applications |

## What Changed

### Old Pattern (DEPRECATED)
```fsharp
// Alloy declaring platform bindings with BCL stubs
module Platform.Bindings =
    let writeBytes fd buffer count : int = Unchecked.defaultof<int>  // BCL dependency!
```

FNCS recognized `.Bindings.` module pattern and marked as `SemanticKind.PlatformBinding`.

### New Pattern (CURRENT)
```fsharp
// User code uses FNCS intrinsics directly
let inline writeStr fd s =
    Sys.write fd (NativePtr.toNativeInt s.Pointer) s.Length
```

FNCS recognizes `Sys.*` module pattern and marks as `SemanticKind.Intrinsic`.

## FNCS Intrinsic Modules

FNCS should recognize these module patterns as intrinsics:

| Module | Operations | SemanticKind |
|--------|------------|--------------|
| `NativePtr` | get, set, add, toNativeInt, etc. | `Intrinsic "NativePtr.X"` |
| `Sys` | write, read, exit, sleep, time | `Intrinsic "Sys.X"` |
| `NativeDefault` | zeroed, unreachable | `Intrinsic "NativeDefault.X"` |

## External Library Bindings

For external libraries (GTK, CMSIS, etc.), the binding library carries semantic metadata via **quotations**:

```fsharp
// Farscape-generated binding library
let peripheralDescriptor: Expr<PeripheralDescriptor> = <@
    { Name = "GPIO"; BaseAddress = 0x48000000un; ... }
@>
```

FNCS inspects quotations at compile time and attaches metadata to PSG nodes.

## Cross-References

- **Firefly**: `binding_architecture_unified` - Canonical three-layer model
- **Firefly**: `native_binding_architecture` - Alex consumption
- **FNCS**: `quotation_semantic_carriers` - Quotation inspection
- **FNCS**: `fncs_architecture` - Core FNCS design

## Legacy Documentation

The content below describes the OLD pattern for reference during migration
# Quotation Semantic Carriers in FNCS

> **Status**: Forward-looking architectural direction for FNCS compiler intrinsics
> **Scope**: New compiler infrastructure not found in FCS

## Core Concept

F# quotations (`Expr<'T>`) encode program fragments as **first-class compile-time data**. In the Fidelity framework, quotations serve as **semantic carriers** - typed structures that carry memory constraints, peripheral descriptors, and other semantic metadata through the PSG construction pipeline.

**Critical Distinction**: Quotations are NOT evaluated at runtime. FNCS inspects quotation structure during PSG construction, extracts semantic information, and encodes it into the PSG. The generated native binary contains no quotation runtime support.

## FNCS Quotation Intrinsics

FNCS must provide deep intrinsics for quotation inspection:

```
┌──────────────────────────────────────────────────────────────────────────────┐
│  F# Source with Quotation                                                    │
│  <@ { MemoryRegion = Peripheral; BaseAddress = 0x48000000un } @>            │
└──────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌──────────────────────────────────────────────────────────────────────────────┐
│  FNCS Quotation Inspector                                                    │
│  • Pattern-match on Expr<'T> structure                                       │
│  • Extract: field names, types, literal values                               │
│  • Validate: region constraints, access patterns                             │
│  • Output: Semantic metadata for PSG node                                    │
└──────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌──────────────────────────────────────────────────────────────────────────────┐
│  PSG Node with Semantic Attachment                                           │
│  { Node: ..., Semantics: MemoryRegion(Peripheral, Volatile, 0x48000000) }   │
└──────────────────────────────────────────────────────────────────────────────┘
```

## Applications

### BAREWire Memory Mapping

BAREWire uses quotations to express memory layout constraints:

```fsharp
let memoryLayout: Expr<LayoutDescriptor> = <@
    { Alignment = 4un
      Size = 16un
      Region = Sram
      Access = ReadWrite }
@>
```

FNCS extracts alignment, size, and access constraints during PSG construction. Firefly uses this information to emit appropriately-aligned memory operations.

### Farscape Peripheral Bindings

Farscape generates hardware binding quotations from C/C++ header parsing:

```fsharp
let gpioDescriptor: Expr<PeripheralDescriptor> = <@
    { Name = "GPIO"
      Instances = Map.ofList [("GPIOA", 0x48000000un); ("GPIOB", 0x48000400un)]
      Layout = gpioLayout
      MemoryRegion = Peripheral }
@>
```

FNCS extracts:
- Peripheral name for symbol correlation
- Instance addresses for memory-mapped access
- Memory region (Peripheral → volatile semantics)
- Layout for proper field offsets

### Type Descriptors (Future)

Fidelity.Platform may carry type-level semantic information:

```fsharp
[<TypeDescriptor>]
let stringDescriptor: Expr<TypeSemantics> = <@
    { Representation = FatPointer(Ptr = uint8, Len = unativeint)
      Encoding = UTF8
      Ownership = Owned
      Drop = ZeroCost }
@>
```

## Implementation Requirements

### FNCS Must Implement

1. **Quotation Structure Inspection**
   - Pattern-match on `Expr.PropertyGet`, `Expr.Value`, `Expr.NewRecord`
   - Extract typed literal values (addresses, sizes, enums)
   - Validate semantic constraints at compile time

2. **PSG Semantic Attachment**
   - Carry extracted semantics as first-class PSG node metadata
   - Preserve semantic information through nanopass transformations
   - Make semantics available to Firefly's Alex traversal

3. **Compile-Time Only**
   - No quotation runtime library required
   - All inspection happens during PSG construction
   - Generated code contains resolved values, not quotation structures

### Firefly Consumption

Firefly's Alex traversal reads PSG semantic attachments:
- `MemoryRegion.Peripheral` → emit volatile loads/stores
- `Access.ReadOnly` → emit read-only memory access
- `Alignment(n)` → ensure aligned memory operations

## Normative Requirements

From fsnative-spec `native-type-mappings.md`:

> NORMATIVE: Quotations, active patterns, and computation expressions SHALL be fully supported. These features operate at compile time and impose no runtime overhead.

> NORMATIVE: Quotation-based metaprogramming SHALL NOT require runtime evaluation. All quotation inspection and transformation occurs during compilation.

## Relationship to FCS

This is **NEW to FNCS** - not found in FCS:
- FCS evaluates quotations at runtime via `FSharp.Core.Quotations`
- FNCS inspects quotations at compile time for semantic extraction
- No runtime quotation library is needed or permitted

## Cross-References

- **Firefly**: `binding_architecture_unified` memory - **CANONICAL** three-layer binding architecture
- **Firefly**: `fsharp_metaprogramming_patterns` memory - quotation usage in PSG
- **Firefly**: `delimited_continuations_architecture` memory - related CE desugaring
- **Firefly**: `native_binding_architecture` memory - platform binding resolution
- **fsnative-spec**: `spec/native-type-mappings.md` § "Compile-Time Metaprogramming"

## Relationship to Unified Binding Architecture

Quotation semantic carriers are the **Layer 2** mechanism in the unified binding architecture:

| Layer | What | Examples |
|-------|------|----------|
| Layer 1 | FNCS Intrinsics | `Sys.write`, `NativePtr.set`, `NativeDefault.zeroed` |
| **Layer 2** | **Quotation Semantic Carriers** | Farscape-generated GTK bindings, BAREWire memory layouts |
| Layer 3 | User Code | Application code |

**Key Insight**: Layer 1 intrinsics are operations native to the type universe (no semantic carrier needed). Layer 2 bindings carry rich metadata (memory layout, alignment, ownership) that cannot be expressed through simple type signatures alone.
# Native Type Universe: OCaml Provenance and Fidelity Extensions

> **Canonical Source**: `fsnative-spec/spec/native-type-universe.md` Appendix E
> **Status**: Design heritage documentation

## Design Philosophy

fsnative draws provenance from OCaml's direct memory layout idioms - concepts that F#/.NET lacks entirely because the CLR abstracts memory away.

## What OCaml Provides (KEEP)

| OCaml Concept | Value for fsnative |
|---------------|-------------------|
| **Products/Sums/Functions as primitives** | Type universe axioms |
| **Value-oriented structural assembly** | Records/tuples laid out contiguously |
| **Deterministic tag layout for DUs** | Tag = 0,1,2... in declaration order |
| **Fat pointer concept** | `{ptr, len}` for strings/arrays |
| **No null philosophy** | Everything representable without sentinels |
| **Unboxed by default** | No implicit heap allocation |

## What OCaml Lacks (SET ASIDE)

| OCaml Limitation | Fidelity Requirement |
|------------------|---------------------|
| **63-bit tagged integers** | Full-width integers (no GC tag) |
| **No cache line awareness** | 64-byte alignment matters |
| **No memory region types** | Stack/Arena/Peripheral/Sram/Flash |
| **No access kinds** | ReadOnly/WriteOnly/ReadWrite |
| **Desktop assumption** | Embedded/constrained targets |
| **Runtime type discrimination** | Compile-time only |

## Rust RAII Guideposts (ADAPT)

| Rust Concept | Fidelity Adaptation |
|--------------|---------------------|
| **Ownership** | Memory region types + coeffects |
| **Borrow checker** | Type-guided analysis (less invasive) |
| **Drop semantics** | Continuation-bounded resources |
| **Deterministic cleanup** | Arena/scope-bounded lifetimes |
| **Move semantics** | Linear types (Phase B) |

## Fidelity Extensions Beyond Both

### Cache Hierarchy Awareness

| Concern | OCaml | Rust | Fidelity |
|---------|-------|------|----------|
| **Cache line alignment** | No | Manual | First-class |
| **False sharing prevention** | No | Manual | Automatic |
| **Working set calculation** | No | No | Compile-time |
| **L1/L2/L3 tier placement** | No | No | Arena strategies |

### Hardware Memory Regions

| Region | OCaml | Rust | fsnative |
|--------|-------|------|----------|
| `Stack` | Implicit | Implicit | Explicit type |
| `Arena` | No | Manual | First-class |
| `Peripheral` | No | Manual unsafe | Type-safe |
| `Sram` | N/A | N/A | Explicit |
| `Flash` | N/A | N/A | Explicit |

## The Synthesis

1. **From OCaml**: Products, sums, functions; value-oriented assembly; fat pointers; no null
2. **Set Aside from OCaml**: GC tagging; desktop assumptions; runtime discrimination
3. **From Rust**: Deterministic cleanup; ownership tracking; RAII semantics
4. **Fidelity Original**: Memory regions; access kinds; cache awareness

## Comparison Table

| Aspect | OCaml | F# (.NET) | fsnative | Rust |
|--------|-------|-----------|----------|------|
| String encoding | Byte sequence | UTF-16 | **UTF-8** | UTF-8 |
| Option | heap (sometimes) | heap | **stack voption** | stack |
| Default int | 63-bit tagged | 32-bit | **Platform word** | Platform word |
| Null | No null | Nullable refs | **No null** | No null |
| Memory safety | Runtime GC | Runtime GC | **Compile-time** | Compile-time |
| Type representation | Runtime tagged | Runtime boxed | **Compile-time** | Compile-time |

## Cross-References

- **fsnative-spec**: `spec/native-type-universe.md` Appendix E
- **fsnative-spec**: `spec/features-for-ml-compatibility.md`

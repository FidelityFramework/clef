# Native Type Universe: Foundations

> **Canonical Source**: `fsnative-spec/spec/native-type-universe.md` Parts 1-2
> **Status**: Intrinsic to FNCS

## Core Principles

Native types are **intrinsic to FNCS** - they ARE the type universe, not wrappers or mappings.

### Type Universe Axioms

The native type universe is built on three primitive concepts from ML/OCaml:

1. **Products** (tuples, records) - Combine multiple values into one
2. **Sums** (discriminated unions) - Choose between alternatives
3. **Functions** - Transform values

Everything else is derived from these primitives.

### Memory Guarantees

- **No implicit boxing**: Value types remain on stack unless explicitly requested
- **Deterministic layout**: Memory representation is predictable and specified
- **No null**: All types are non-nullable by construction

### Type Equivalences

| User Writes | Underlying Implementation | Notes |
|-------------|--------------------------|-------|
| `option<'T>` | `voption<'T>` | Stack-allocated, non-null |
| `string` | UTF-8 fat pointer | `{ptr: *u8, len: usize}` |
| `int` | Platform word | `nativeint` semantics |

## Primitive Types Summary

| Type | Size | MLIR | Notes |
|------|------|------|-------|
| `unit` | ZST | (elided) | No runtime representation |
| `bool` | 1 byte | `i8` | `false`=0, `true`=1 |
| `int` | Platform word | `index` | Full precision (no GC tag) |
| `float` | 8 bytes | `f64` | IEEE 754 double |
| `float32` | 4 bytes | `f32` | IEEE 754 single |
| `char` | 4 bytes | `i32` | UTF-32 codepoint |

### Key Decisions

1. **`int` = platform word**: Not 32-bit like F#, not 63-bit like OCaml
   - **Critical**: Size is TARGET-DEPENDENT (64-bit on x86_64, 32-bit on ARM32)
   - FNCS uses `TypeLayout.PlatformWord`, Alex resolves to concrete size
   - See memory: `fncs_platform_aware_type_resolution`
2. **`char` = UTF-32**: Not UTF-16 like .NET, not Latin-1 like OCaml
3. **No GC tagging**: Full integer precision (unlike OCaml's 63-bit)

## Cross-References

- **fsnative-spec**: `spec/native-type-universe.md` Parts 1-2
- **fsnative-spec**: `spec/native-type-mappings.md` for normative requirements
- **Memory**: `fncs_platform_aware_type_resolution` - Platform-dependent type sizing
- **Memory**: `fidproj_platform_context_principle` - When platform context is known
- **Memory**: `srtp_operator_architecture` - SRTP and operator resolution
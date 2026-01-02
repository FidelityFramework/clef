# Native Type Universe: Reference Types

> **Canonical Source**: `fsnative-spec/spec/native-type-universe.md` Part 4
> **Status**: Intrinsic to FNCS

## String

**Memory Layout** (UTF-8 fat pointer):
```
┌─────────────────┬─────────────────┐
│ ptr: *u8        │ len: usize      │
└─────────────────┴─────────────────┘
     8 bytes           8 bytes       = 16 bytes
```

| Property | Value |
|----------|-------|
| **Encoding** | UTF-8 (NOT UTF-16) |
| **Length** | Byte count (not character count) |
| **Empty string** | `{ptr: valid, len: 0}` - NOT null |
| **MLIR** | `!fidelity.str` |

### Why UTF-8?

1. **Native interop** - Rust, C, systems APIs use UTF-8
2. **Compact** - 1 byte per ASCII
3. **Web/JSON native** - No transcoding
4. **Embedded-friendly** - No UTF-16 surrogates

### Character Iteration

```fsharp
for c in String.chars s do  // c : char (UTF-32, 4 bytes)
    printfn "%c" c
```

### API Changes (Null-Freedom)

| BCL Pattern | fsnative Pattern |
|-------------|------------------|
| `s.IndexOf(c)` → `-1` | `String.indexOf c s` → `voption<int>` |
| `s.Substring(i, len)` throws | `String.slice i len s` → `voption<string>` |
| `String.IsNullOrEmpty(s)` | `String.isEmpty s` |

## Array

**Memory Layout** (fat pointer):
```
┌─────────────────┬─────────────────┐
│ ptr: *T         │ len: usize      │
└─────────────────┴─────────────────┘
     8 bytes           8 bytes       = 16 bytes (header)
```

| Property | Value |
|----------|-------|
| **Element layout** | Contiguous, naturally aligned |
| **Bounds checking** | Always (no unsafe by default) |
| **Empty array** | `{ptr: valid, len: 0}` - NOT null |
| **Monomorphized** | `array<int>` stores unboxed ints |
| **MLIR** | `!fidelity.array<T>` |

### API Changes (Null-Freedom)

| BCL Pattern | fsnative Pattern |
|-------------|------------------|
| `arr.[i]` throws | `Array.tryItem i arr` → `voption<'T>` |
| `Array.find pred arr` throws | `Array.tryFind pred arr` → `voption<'T>` |

## Span / ReadOnlySpan

**Memory Layout** (borrowed view):
```
┌─────────────────┬─────────────────┐
│ ptr: *T         │ len: usize      │
└─────────────────┴─────────────────┘
```

| Property | Value |
|----------|-------|
| **Ownership** | Borrowed (does not own) |
| **Lifetime** | Must not outlive source |
| **Stack only** | Cannot escape to heap |
| **MLIR** | Same as array header |

## Cross-References

- **fsnative-spec**: `spec/native-type-universe.md` Part 4
- **fsnative-spec**: `spec/native-type-mappings.md` for MLIR mappings

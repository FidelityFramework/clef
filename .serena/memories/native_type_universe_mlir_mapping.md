# Native Type Universe: MLIR Type Mappings

> **Canonical Source**: `fsnative-spec/spec/native-type-universe.md` Appendix A
> **Status**: Reference for Firefly code generation

## Complete Type Mapping

| F# Type | MLIR Type | Notes |
|---------|-----------|-------|
| `unit` | (none - ZST) | Not materialized |
| `bool` | `i8` | 0=false, 1=true |
| `int` | `index` | Platform word |
| `int8` | `i8` | Signed 8-bit |
| `uint8` | `i8` | Unsigned 8-bit |
| `int16` | `i16` | Signed 16-bit |
| `uint16` | `i16` | Unsigned 16-bit |
| `int32` | `i32` | Signed 32-bit |
| `uint32` | `i32` | Unsigned 32-bit |
| `int64` | `i64` | Signed 64-bit |
| `uint64` | `i64` | Unsigned 64-bit |
| `nativeint` | `index` | = `int` |
| `unativeint` | `index` | Unsigned platform word |
| `float` | `f64` | IEEE 754 double |
| `float32` | `f32` | IEEE 754 single |
| `char` | `i32` | UTF-32 codepoint |
| `string` | `!fidelity.str` | UTF-8 fat pointer |
| `option<'T>` | `!fidelity.option<T>` | voption semantics |
| `Result<'T,'E>` | `!fidelity.result<T,E>` | Tagged union |
| `'a * 'b` | `tuple<A, B>` | Contiguous layout |
| Record | `!fidelity.record<...>` | Named fields |
| DU | `!fidelity.union<...>` | Tagged payload |
| `'a -> 'b` | `!fidelity.fn<A, B>` | Or direct `(A) -> B` |
| `array<'T>` | `!fidelity.array<T>` | Fat pointer |
| `list<'T>` | `!fidelity.list<T>` | Cons cells |
| `ref<'T>` | `!fidelity.ref<T>` | Or `ptr<T>` |
| `Ptr<'T,'R,'A>` | `ptr<T>` | Region in metadata |

## Fat Pointer Types

These types use the `{ptr, len}` representation:

```mlir
// String: UTF-8 fat pointer
!fidelity.str = tuple<ptr<i8>, index>  // 16 bytes

// Array: element fat pointer
!fidelity.array<T> = tuple<ptr<T>, index>  // 16 bytes

// Span: borrowed view (same layout)
!fidelity.span<T> = tuple<ptr<T>, index>  // 16 bytes
```

## Tagged Union Layout

```mlir
// Option<int>
!fidelity.option<index> = {
    tag: i8,      // 0=None, 1=Some
    payload: index
}

// Result<int, string>
!fidelity.result<index, !fidelity.str> = {
    tag: i8,      // 0=Ok, 1=Error
    payload: union<index, !fidelity.str>  // Size of larger variant
}
```

## Closure Layout

```mlir
// Closure capturing environment
!fidelity.closure<(A) -> B, Env> = {
    fn_ptr: ptr<fn(Env, A) -> B>,
    env: Env
}
```

## Cross-References

- **fsnative-spec**: `spec/native-type-universe.md` Appendix A
- **fsnative-spec**: `spec/native-type-mappings.md` for normative requirements
- **Firefly**: See Alex code generation for MLIR emission

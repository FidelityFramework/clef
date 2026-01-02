# Native Type Universe: Parameterized Types

> **Canonical Source**: `fsnative-spec/spec/native-type-universe.md` Part 5
> **Status**: Intrinsic to FNCS

## Option

```fsharp
let maybeValue : int option = Some 42
let nothing : string option = None
```

**Memory Layout** (stack-allocated tagged union):
```
┌──────────┬────────────────────┐
│ Tag (i8) │ Payload: 'T        │
└──────────┴────────────────────┘
   1 byte     sizeof<'T> + padding
```

| Property | Value |
|----------|-------|
| **Tag values** | `None` = 0, `Some` = 1 |
| **Stack allocated** | Always (never heap) |
| **Null-freedom** | `None` is tag 0, NOT null pointer |
| **MLIR** | `!fidelity.option<T>` |

### Key Distinction

| System | `option` Representation |
|--------|------------------------|
| OCaml | Heap-allocated block (sometimes) |
| F# (.NET) | Heap-allocated reference type |
| **fsnative** | **Stack-allocated voption** |

**FNCS Resolution**: User writes `int option`, FNCS compiles with `voption<int>` semantics.

## Result

```fsharp
let success : Result<int, string> = Ok 42
let failure : Result<int, string> = Error "not found"
```

**Memory Layout** (tagged union):
```
┌──────────┬────────────────────────────────────┐
│ Tag (i8) │ Payload: max(sizeof<'T>, sizeof<'E>)│
└──────────┴────────────────────────────────────┘
```

| Property | Value |
|----------|-------|
| **Tag values** | `Ok` = 0, `Error` = 1 |
| **Stack allocated** | Always |
| **MLIR** | `!fidelity.result<T, E>` |

### Why Result Over Exceptions

- Explicit in type signatures
- Compile-time exhaustiveness checking
- Zero runtime overhead
- Can cross FFI boundaries via BAREWire
- **Exceptions not supported for control flow**

## List

```fsharp
let numbers : int list = [1; 2; 3]
```

**Memory Layout** (cons cells):
```
┌────────────────────┬─────────────────────┐
│ head: 'T           │ tail: ptr<list<'T>> │
└────────────────────┴─────────────────────┘
```

| Property | Value |
|----------|-------|
| **Empty list** | Special tag, no allocation |
| **Immutable** | Always (structural sharing) |
| **Allocation** | Arena or stack (not GC) |
| **MLIR** | `!fidelity.list<T>` |

### When to Use

- Pattern matching on head/tail
- Recursive algorithms
- Functional transformations

### When NOT to Use (prefer array)

- Random access by index
- Performance-critical loops
- Large collections with mutations

## Cross-References

- **fsnative-spec**: `spec/native-type-universe.md` Part 5
- **fsnative-spec**: `spec/native-type-mappings.md` § Option, Result

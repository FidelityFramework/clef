# Native Type Universe: Functions and Mutable State

> **Canonical Source**: `fsnative-spec/spec/native-type-universe.md` Parts 6-7
> **Status**: Intrinsic to FNCS

## Function Types

### Representation Strategies

| Case | Representation |
|------|----------------|
| **Known call site** | Direct call (no indirection) |
| **Inline function** | Inlined at call site (fsil default) |
| **First-class value** | Function pointer or closure |
| **Captures environment** | Closure struct |

### Closure Representation

When a function captures variables:

```fsharp
let makeAdder n = fun x -> x + n  // Captures 'n'
```

**Memory Layout**:
```
┌─────────────────────┬─────────────────────┐
│ fn_ptr: ptr<fn>     │ env: captured values│
└─────────────────────┴─────────────────────┘
```

| Property | Value |
|----------|-------|
| **Environment** | Struct containing captured values |
| **Invocation** | `fn_ptr(env, args...)` |
| **Allocation** | Stack or arena (not GC) |
| **MLIR** | `!fidelity.closure<...>` |

### Inline Semantics (fsil)

| Function Type | Default Behavior |
|---------------|------------------|
| Simple arithmetic | Always inlined |
| Pipe operators | Always inlined |
| SRTP-constrained | Always inlined |
| Recursive | Not inlined |
| Large body | Compiler decides |

### Currying Optimization

- Fully-applied calls → direct multi-argument calls
- Partial application → flat closure capturing applied args
- `List.map f` → typically inlined at call site

## Mutable State

### Ref Cells

```fsharp
let counter : int ref = ref 0
counter := !counter + 1
```

| Property | Value |
|----------|-------|
| **Representation** | Single-field mutable record |
| **Allocation** | Stack or arena (not GC) |
| **MLIR** | `!fidelity.ref<T>` or `ptr<T>` |

### Mutable Bindings

```fsharp
let mutable x = 0
x <- x + 1
```

| Property | Value |
|----------|-------|
| **Scope** | Local to function |
| **Representation** | Stack slot |
| **Cannot escape** | Cannot be captured by closures |

### Mutable Record Fields

```fsharp
type Counter = { mutable Value: int }
c.Value <- c.Value + 1
```

| Property | Value |
|----------|-------|
| **Layout** | Same as immutable field |
| **Mutability** | Compile-time property only |

## Cross-References

- **fsnative-spec**: `spec/native-type-universe.md` Parts 6-7
- **FNCS**: `coeffect_compilation_strategy` for CE compilation

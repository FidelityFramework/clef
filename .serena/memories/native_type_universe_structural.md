# Native Type Universe: Structural Types

> **Canonical Source**: `fsnative-spec/spec/native-type-universe.md` Part 3
> **Status**: Intrinsic to FNCS

## Tuples (Anonymous Products)

```fsharp
let pair : int * string = (42, "hello")
```

**Memory Layout** (64-bit):
```
┌─────────────┬─────────────────────────────┐
│ int (word)  │ string (ptr + len = 2 words)│
└─────────────┴─────────────────────────────┘
     8 bytes           16 bytes              = 24 bytes
```

| Property | Value |
|----------|-------|
| **Structural typing** | `int * string` ≡ `int * string` |
| **Allocation** | Stack by default, arena when escaping |
| **No header** | Unlike OCaml (8-byte GC header) |
| **MLIR** | `tuple<index, !fidelity.str>` |

## Records (Named Products)

```fsharp
type Person = { Name: string; Age: int }
```

| Property | Value |
|----------|-------|
| **Nominal typing** | `Person` ≠ `{ Name: string; Age: int }` |
| **Field order** | Declaration order = memory layout |
| **No header** | Unlike OCaml |
| **MLIR** | `!fidelity.record<"Person", ...>` |

## Discriminated Unions (Named Sums)

```fsharp
type Shape = Circle of float | Rectangle of float * float | Point
```

**Memory Layout**:
```
┌──────────┬─────────┬────────────────────────────────────┐
│ Tag (i8) │ padding │ Payload (size of largest variant)  │
└──────────┴─────────┴────────────────────────────────────┘
```

| Property | Value |
|----------|-------|
| **Tag size** | `i8` for ≤256 variants |
| **Tag assignment** | 0, 1, 2... in declaration order |
| **Payload** | Size of largest variant |
| **MLIR** | `!fidelity.union<"Shape", ...>` |

### Single-Case Unions (Newtypes)

```fsharp
type UserId = UserId of int
```

**Optimization**: Tag elided - same representation as wrapped type.

## OCaml Comparison

| Aspect | OCaml | fsnative |
|--------|-------|----------|
| **Block header** | 8-byte GC header | **None** |
| **Field access** | Offset from header | Direct offset |
| **No-arg constructors** | Unboxed integer | Tag byte only |
| **Tag range** | 0-245 | 0-255 (full i8) |

## Cross-References

- **fsnative-spec**: `spec/native-type-universe.md` Part 3
- **fsnative-spec**: `spec/type-definitions.md` for type definition syntax

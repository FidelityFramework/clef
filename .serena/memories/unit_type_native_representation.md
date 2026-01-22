# Unit Type Native Representation

> **Status**: Documented (January 2026)
> **Principle**: Clear, consistent story for F# developers inspecting generated code

## The Unit Story

F# `unit` is a **real value** (the single inhabitant `()`), not C's `void`.

### Native Representation
- `unit` maps to `i32` at the MLIR/LLVM level
- The unit value `()` is represented as `i32 0`
- Every function returning `unit` returns `i32 0`

### Why i32, Not Void?

1. **Type consistency**: Unit is a value, so it has a representation
2. **ABI simplicity**: Functions always return something (no void special case)
3. **Debuggability**: You can see the return value in the generated code
4. **F# semantics**: `let x = printfn "hello"` binds `x` to `()`

### Code Generation

```mlir
// F# function returning unit
func.func @printGreeting() -> i32 {
    // ... print operations ...
    %c0 = arith.constant 0 : i32
    func.return %c0 : i32
}
```

### The Exit Exception (That Isn't)

`Sys.exit : int -> unit` has type `int -> unit` even though it never returns.

**At MLIR level:**
```mlir
// After syscall, emit unreachable unit return (type-correct)
%v_syscall = llvm.inline_asm "syscall" ...
%v_unit = arith.constant 0 : i32    // Unreachable but honors type
func.return %v_unit : i32
```

**Why do this?**
- Type contract is honored: exit "returns" unit
- No special-case void handling
- LLVM recognizes unreachable code and optimizes
- F# developers see consistent semantics

## Contrast with Null

`null` for reference types is represented as `!llvm.ptr` with value 0 (null pointer).

| Concept | F# Type | Native Type | Native Value |
|---------|---------|-------------|--------------|
| Unit value | `unit` | `i32` | `0` |
| Null reference | `'a option` | `!llvm.ptr` | `0` (null) |
| None | `Option<'a>` | Tagged struct | Tag = 0 |

**Key distinction**: Unit is a value; null is absence of reference.

## Type Mapping (TypeMapping.fs)

```fsharp
// In Serialize.fs
| TUnit -> sb.Append("i32") |> ignore  // Unit maps to i32 for ABI
```

## Related

- `entry_point_elaboration_architecture` - Uses unit return for `_start`
- `ntu_type_system` - NTUKind.NTUunit definition

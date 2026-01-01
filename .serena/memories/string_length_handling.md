# String Length Handling in FNCSEmitter

> **Last Updated**: December 31, 2025

## The Problem

When emitting write syscalls for strings, we need to know the string length. This is straightforward for string literals (compile-time known), but challenging for strings from runtime operations like `Console.ReadLine`.

## The Insight: Dual Length Tracking

FNCSEmitter tracks **two kinds of string lengths** in `EmissionContext`:

### 1. Static String Lengths (`StringLengths: Map<int, int>`)
- Compile-time known lengths
- Used for string literals (e.g., `"Hello, World!"` → length 13)
- Stored as an integer value

### 2. Dynamic String Lengths (`DynamicStringLengths: Map<int, string>`)
- Runtime-computed lengths stored as SSA values
- Used for strings from syscalls like `read()` where the actual length is only known at runtime
- Stored as the SSA name (e.g., `%v14`) that holds the length

## Implementation Pattern

### For ReadLine (read syscall):
```fsharp
// 1. Call read syscall, get bytes_read in %v12
let readResultSSA, zipper7 = MLIRZipper.witnessSyscall ...

// 2. Subtract 1 to exclude newline: %v14 = %v12 - 1
let adjustedLenSSA, zipper9 = MLIRZipper.witnessArith "arith.subi" readResultSSA oneSSA (Integer I64) zipper8

// 3. Store the SSA name as the dynamic length
ctx |> EmissionContext.bindDynamicStringLength nid adjustedLenSSA
```

### For Interpolated Strings:
```fsharp
// Check dynamic length first, then fall back to static
match EmissionContext.recallDynamicStringLength exprNodeId ctx with
| Some dynLenSSA ->
    // Use the dynamic length SSA directly in the write syscall
    Args = [(fdSSA, Integer I32); (ptrSSA, Pointer); (dynLenSSA, Integer I64)]
| None ->
    // Fall back to static length
    match EmissionContext.recallStringLength exprNodeId ctx with
    | Some len -> ... emit constant for len ...
```

## Propagation Through Bindings

Both static and dynamic lengths propagate through:
- **Bindings**: `let name = Console.ReadLine()` → binding gets the dynamic length
- **VarRefs**: References to `name` copy the dynamic length from the definition

This ensures that when an interpolated string like `$"Hello, {name}!"` is emitted, the `{name}` part uses the actual bytes read, not a hardcoded buffer size.

## Key Files

- `src/Alex/Generation/FNCSEmitter.fs` - EmissionContext with dual length tracking
- `src/Alex/Traversal/MLIRZipper.fs` - StaticBuffer global type for read buffers

## Why This Matters

Without dynamic length tracking, we'd have to either:
1. Use the full buffer size (254 bytes) - prints garbage after the actual content
2. Scan for null terminator at runtime - extra complexity and overhead

The dual tracking approach keeps compile-time optimization for literals while correctly handling runtime-computed lengths.

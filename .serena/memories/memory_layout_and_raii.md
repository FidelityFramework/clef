# Memory Layout and RAII Patterns for Native F#

## Purpose

This memory captures how types should correlate to memory layout in FNCS, and how deterministic memory management (RAII-style) should work. This is the key architectural turning point where getting primitives right has positive ripple effects across the platform.

## Core Principle: Types Determine Layout

In Fidelity, **types are not just for checking - they ARE the layout specification**.

```
Traditional:
  Type checking → Type erasure → Runtime determines layout

Fidelity:
  Type checking → Types preserved → Layout computed from types → MLIR/LLVM emit
```

## Memory Layout Primitives

### Record Layout (like Rust repr(C))

```fsharp
type NativeStr = {
    Pointer: nativeptr<byte>   // 8 bytes, offset 0
    Length: int64              // 8 bytes, offset 8
}
// Total: 16 bytes, alignment 8
```

**Algorithm:**
1. Compute max field alignment
2. For each field in declaration order:
   - Align offset to field alignment
   - Place field
   - Advance offset by field size
3. Pad total size to struct alignment

### Union Layout (Tagged Unions)

```fsharp
type Result<'T, 'E> =
    | Ok of 'T      // tag = 0
    | Error of 'E   // tag = 1
```

**Layout:**
- Tag field (discriminant) first
- Union of payload variants
- Size = tag + max(payload sizes) + padding

**Optimization opportunities:**
- Single-case unions: no tag needed (transparent)
- Null-pointer optimization: `option<ref<'T>>` can use null for None
- Bit-stealing for small discriminants

### Transparent Wrappers (like repr(transparent))

```fsharp
[<Struct>]
type UserId = UserId of int64
// Layout identical to int64, zero overhead
```

**Rules:**
- At most one non-zero-sized field
- Layout matches that field exactly
- Enables zero-cost newtypes for type safety

### Primitive Layout

| F# Type | Native Layout | Size | Alignment |
|---------|---------------|------|-----------|
| int32 | i32 | 4 | 4 |
| int64 | i64 | 8 | 8 |
| float32 | f32 | 4 | 4 |
| float | f64 | 8 | 8 |
| bool | i8 | 1 | 1 |
| char | i32 (Unicode codepoint) | 4 | 4 |
| nativeint | ptr | 8 (on 64-bit) | 8 |

## RAII: Deterministic Resource Management

### The Pattern

**Resource Acquisition Is Initialization:**
- Acquire resource = create object
- Release resource = object goes out of scope
- No explicit close/free calls needed
- No GC, no runtime overhead

### Scope-Based Cleanup

```fsharp
let processFile path =
    let handle = File.open path      // Resource acquired
    let data = handle.readAll()      // Use resource
    process data
    // handle goes out of scope → cleanup emitted here
```

**Compiler responsibility:**
1. Track which values need cleanup (have Drop semantics)
2. Emit cleanup code at scope exits (including early returns, exceptions)
3. Emit in reverse order of acquisition

### Drop Order Guarantees

```fsharp
let example () =
    let a = acquireA()    // Acquired first
    let b = acquireB()    // Acquired second
    use c = acquireC()    // 'use' binding
    // ... work ...
    // Drop order: c, b, a (reverse of acquisition)
```

**Struct fields:** Drop in declaration order (like Rust).

### The 'use' Binding

F# already has `use` for IDisposable. For native, this becomes:

```fsharp
use handle = File.open path
// Compiler emits: cleanup(handle) at scope exit
```

**Implementation:** `use` bindings are syntactic sugar for try-finally with cleanup call.

## Memory Regions (UMX Integration)

FNCS should absorb UMX patterns for memory region tracking:

```fsharp
type Ptr<'T, 'region, 'access> = nativeint
// 'region: stack, heap, peripheral, arena
// 'access: readOnly, writeOnly, readWrite

let read<'T, 'r, 'a when 'a :> ReadAccess> (ptr: Ptr<'T, 'r, 'a>) : 'T = ...
let write<'T, 'r, 'a when 'a :> WriteAccess> (ptr: Ptr<'T, 'r, 'a>) (value: 'T) : unit = ...
```

**Region types:**
- `stack` - Function-local, automatic cleanup
- `arena` - Compiler-managed temporary allocation
- `peripheral` - Memory-mapped I/O, requires volatile access
- `heap` - Long-lived, explicit management (or arena)

## Allocation Strategies

### Stack Allocation (Default)

Most values are stack-allocated:
- Records, tuples, small unions
- No allocation/deallocation overhead
- Lifetime tied to scope

### Arena Allocation

For values that outlive their scope but have bounded lifetime:

```fsharp
withArena (fun arena ->
    let data = arena.alloc<Data>()
    // ... use data ...
) // Entire arena freed here
```

**Benefits:**
- Bulk deallocation (fast)
- No individual free calls
- Good for request/response patterns

### Escape Analysis

Compiler determines if a value escapes its scope:
- **Doesn't escape** → stack allocation
- **Escapes upward** → arena or caller-provided storage
- **Escapes to heap** → explicit heap allocation (rare)

## Type-to-MLIR Mapping

### Records → LLVM Struct

```fsharp
type Point = { X: float; Y: float }
```

```mlir
!point = !llvm.struct<(f64, f64)>
```

### Unions → Tagged Union

```fsharp
type Option<'T> = Some of 'T | None
```

```mlir
// For Option<int64>:
!option_i64 = !llvm.struct<(i8, i64)>  // tag + payload
```

### Functions → LLVM Function Pointers

```fsharp
type Transform = int -> int
```

```mlir
!transform = !llvm.ptr<func<i64 (i64)>>
```

## Key Design Decisions for FNCS

### 1. Monomorphize All Generics

No type erasure. Generate specialized code for each instantiation.

```fsharp
let add<'T when 'T: (static member (+): 'T * 'T -> 'T)> x y = x + y
add 1 2       // Generates add_int
add 1.0 2.0   // Generates add_float
```

### 2. Layout Computed at Type Check Time

Don't defer to LLVM. FNCS should compute exact layouts.

```fsharp
type Layout = {
    Size: int
    Alignment: int
    FieldOffsets: Map<string, int>
}

let computeLayout (ty: NativeType) : Layout = ...
```

### 3. Drop Semantics in Type System

Types should indicate whether they need cleanup:

```fsharp
type TypeInfo = {
    Layout: Layout
    NeedsDrop: bool
    DropFn: FunctionRef option
}
```

### 4. Volatile Access for Peripherals

Memory region types should trigger volatile loads/stores:

```fsharp
// Reading from peripheral memory
let value = Ptr.read<uint32, Peripheral, ReadOnly> gpioAddr
// Emits: llvm.load volatile
```

## Success Criteria

1. **Layout determinism**: Same type → same layout, always
2. **No boxing**: Primitive types stay unboxed
3. **Scope-based cleanup**: Deterministic drop at scope exit
4. **Region safety**: Memory region misuse is a type error
5. **FFI compatibility**: Can produce C-compatible layouts

## References

- Rust Reference: Type Layout
- Rust repr(transparent) RFC
- MLton: Unboxed representation
- Real World OCaml: Memory Representation
- Fidelity Memory Model memory in Firefly

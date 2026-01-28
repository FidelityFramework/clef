# Flat Closures: The Universal Architectural Pattern

**Date:** January 28, 2026  
**Critical:** This is THE foundational pattern for ALL constructs in Fidelity

---

## The Principle

**Everything is a flat closure.** There are no exceptions, no alternatives, no special cases.

- Lambdas = flat closures
- Lazy values = flat closures
- Seq generators = flat closures
- Empty collections = flat closures (with zero captures)
- Non-empty collections = flat closures (with captures)

**Why ONE pattern?** Architectural consistency, predictable performance, no null pointers, stack allocation, deterministic lifetimes.

---

## Flat Closure Structure

A flat closure is a struct with:
1. **code_ptr** (always present): Function pointer for operations
2. **captures** (zero or more): Captured values embedded directly in struct

```mlir
// Empty collection (zero captures)
{ code_ptr: ptr }

// Lambda with 2 captures
{ code_ptr: ptr, cap0: T0, cap1: T1 }

// Lazy with value and captures
{ computed: i1, value: T, code_ptr: ptr, cap0: T0, cap1: T1 }
```

### Key Properties

- ✅ **Stack-allocated** via `memref.alloca`
- ✅ **Direct embedding** (captures are struct fields, not pointers)
- ✅ **No null checks** (struct is always concrete)
- ✅ **No garbage collector** (deterministic lifetimes via RAII)
- ❌ **NO null pointers** (architectural incompatibility)

---

## Empty Collections as Flat Closures

Empty collections are NOT null pointers. They are flat closures with zero captures.

### List.empty

```fsharp
// WRONG (old, contaminated)
List.empty → null pointer

// RIGHT (flat closure)
List.empty → { code_ptr }
```

**MLIR emission:**
```mlir
%empty_list = llvm.mlir.undef : !llvm.struct<(ptr)>
```

### Map.empty

```fsharp
// WRONG (old, contaminated)
Map.empty → null pointer

// RIGHT (flat closure)
Map.empty → { code_ptr }
```

### Set.empty

```fsharp
// WRONG (old, contaminated)
Set.empty → null pointer

// RIGHT (flat closure)
Set.empty → { code_ptr }
```

---

## Non-Empty Collections as Flat Closures

Non-empty collections are flat closures WITH captures.

### List.cons

```fsharp
// List cons cell
{ code_ptr: ptr, head: T, tail: List<T> }
```

**NOT** a separate heap-allocated struct pointed to by a pointer. The head and tail ARE the captures.

### Map/Set nodes

AVL tree nodes follow the same pattern - they're flat closures with the node data as captures.

---

## isEmpty Operations

**WRONG approach:**
```mlir
// ❌ Comparing to null
%null = llvm.mlir.null : !llvm.ptr
%is_empty = llvm.icmp eq %collection, %null
```

**RIGHT approach:**

Baker decomposes `isEmpty` operations into structural checks. This may be:
- Checking capture count
- Calling through code_ptr
- Pattern matching on structure

**Witnesses observe what Baker produces.** They don't implement isEmpty logic directly.

---

## Lambdas as Flat Closures

From "Arity on the Side of Caution" blog post:

```fsharp
let greet prefix name = 
    Console.writeln $"{prefix}, {name}!"

let hello = greet "Hello"  // Partial application
```

**The closure for `hello`:**
```mlir
// Flat closure: { code_ptr, captured_prefix }
%closure = memref.alloca() : memref<2xi64>
memref.store %greet_ptr, %closure[0] : memref<2xi64>
memref.store %hello_str, %closure[1] : memref<2xi64>
```

Stack-allocated, no heap, no GC.

---

## Lazy Values as Flat Closures

Lazy values = flat closure + memoization state:

```mlir
// Lazy<T> = { computed: i1, value: T, code_ptr: ptr, cap0, cap1, ... }
%lazy_struct = llvm.alloca 1 x !lazy_type
```

**NOT** `{ code_ptr, env_ptr }` where env_ptr could be null.

---

## Seq Generators as Flat Closures

Seq = flat closure + state machine:

```mlir
// Seq<T> = { state_tag: i32, state_data: T, code_ptr: ptr, cap0, cap1, ... }
```

The state machine is embedded in the closure structure.

---

## Academic Basis

### ML Tradition

OCaml's arity tracking and closure representation:
- Functions carry explicit arity in Lambda IR
- Most calls are saturated → direct call with register passing
- Partial applications → closure struct (NOT heap allocation)
- Stack allocation is standard for non-escaping closures

### F# Integration

F#'s type system provides:
- Curried function types with explicit arity
- Partial application visibility at compile time
- Capture analysis from scope/lifetime tracking

Fidelity extends this:
- All closures use the SAME flat structure
- No special cases for "empty" vs "non-empty"
- ONE pattern for consistency and performance

---

## Why No Null Pointers?

### Architectural Incompatibility

Null pointers require:
- Runtime null checks (branch misprediction penalty)
- Special "empty" vs "non-empty" code paths
- Heap allocation for non-null values (GC pressure)
- Pointer indirection (cache miss overhead)

Flat closures provide:
- No branches for empty checks (structure is known)
- ONE code path (all closures have the same shape)
- Stack allocation (deterministic, fast)
- Direct access (no indirection)

### Memory Fidelity

The framework is named "Fidelity" because it **preserves memory and type safety**:
- F# types map to precise native representations
- Compiler-verified lifetimes
- Deterministic allocation (stack/arena)
- No runtime (no GC, no managed heap)

Null pointers violate fidelity:
- They introduce runtime failure modes (NullReferenceException equivalent)
- They break the type-level guarantees
- They require a runtime to manage

---

## Sources

**Blog Post:** "Arity on the Side of Caution" - `/home/hhh/repos/SpeakEZ/hugo/content/blog/Arity On The Side Of Caution.md`
- Lines 164-167: Flat closure MLIR example
- Lines 186-195: Stack-allocated closures
- Line 32: "Fidelity doesn't need or want a managed runtime or garbage collector"

**Sample Code:** `/home/hhh/repos/Firefly/samples/console/FidelityHelloWorld/13a_SimpleCollections/SimpleCollections.fs`
- Shows collection operations that compile to flat closures

**Canonical Witness:** `src/MiddleEnd/Alex/Witnesses/LazyWitness.fs`
- Example of witnessing flat closure patterns via XParsec

---

## User Quote (January 28, 2026)

"We don't use null. Never have, never will. I don't know where you 'guessed' at that and managed to bring that corruption into my code but GET RID OF IT NOW."

"Everything is a flat closure. Empty collection is just a flat closure with zero captures - still has the `code_ptr` field, just no capture fields after it."

**The standing art composes up. Use it.**

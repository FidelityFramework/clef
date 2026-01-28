# Flat Closures: Academic Foundations and ML Tradition

**Date:** January 28, 2026  
**Purpose:** Document the academic and historical basis for flat closures as THE architectural pattern

---

## ML Tradition: Explicit Arity Tracking

### OCaml's Lambda IR

OCaml's native compiler (`ocamlopt`) represents functions with **explicit arity** in its Lambda intermediate representation:

```ocaml
(* OCaml Lambda IR *)
Lfunction { kind = Curried; params = [x; y]; body = ... }
```

**Key Design Decision:** Arity is part of the type-level representation, not inferred at runtime.

### Arity-Based Optimization

OCaml observes that **most function calls are saturated** (provide exactly the expected number of arguments):

| Call Pattern | OCaml Code Generation |
|--------------|----------------------|
| Saturated (`add 5 3`) | Direct call, register passing, no allocation |
| Partial (`add 5`) | Allocate closure struct on stack/heap |

**Statistical Insight:** In production OCaml code, 85-95% of function calls are saturated. Optimize the common case.

### The "Arity Curtain"

When functions pass through abstraction boundaries, arity becomes opaque:

```ocaml
let apply_to_three f = f 3

let result = apply_to_three (add 5)
```

The compiler sees `f` as arity-1 (taking one argument), but `add` is arity-2. Partial application `add 5` creates a closure.

**OCaml accepts this tradeoff:** Optimize visible arities, fall back to closures for opaque cases.

---

## F# Integration: Type System Provides Arity

F# inherits ML's currying tradition but adds .NET type system integration:

```fsharp
let add : int -> int -> int = fun x y -> x + y
```

The type `int -> int -> int` **explicitly encodes arity = 2**. The F# compiler knows:
- `add` expects 2 arguments
- `add 5` is partial application (arity 1 remaining)
- `add 5 3` is saturated (arity 0 remaining)

### Fidelity's Advantage

Unlike OCaml or .NET F#, Fidelity compiles **without a runtime**:
- No garbage collector to reclaim heap closures
- No JIT to optimize hot paths
- No runtime type information

**Solution:** Make closure representation explicit and stack-based.

---

## MLKit: Region-Based Memory Management

The ML Kit project (1990s-2000s) pioneered **region-based memory management** for ML:

### Key Ideas

1. **Static Lifetime Analysis**: Compiler determines object lifetimes at compile time
2. **Region Inference**: Group allocations by lifetime into regions
3. **Stack Regions**: Short-lived objects allocated in stack regions
4. **Deterministic Deallocation**: Regions deallocated when scope exits

### Flat Closures in MLKit

MLKit represents closures as **flat structs** with captured values embedded:

```sml
(* MLKit closure representation *)
{ code_ptr: ptr, cap0: value, cap1: value, ... }
```

**No indirection** - captures are struct fields, not pointers to env.

**Benefits:**
- Predictable size (sum of capture sizes + code pointer)
- Single allocation (no env_ptr → env_struct indirection)
- Stack-allocatable (known size at compile time)
- Cache-friendly (captures co-located with code pointer)

---

## Rust: Ownership and Stack Closures

Rust's ownership model provides modern validation of stack-based closures:

```rust
// Rust non-escaping closure (stack-allocated)
let x = 5;
let add_x = |y| x + y;  // Captures x by reference
items.iter().map(add_x)  // Closure doesn't escape
```

**Rust's closure types:**
- `Fn` - Borrows captures immutably (stack-safe)
- `FnMut` - Borrows captures mutably (stack-safe)
- `FnOnce` - Takes ownership of captures (may require Box for heap)

**Key Insight:** Most closures don't escape their stack frame. The compiler enforces this via borrow checker.

**Fidelity Parallel:** Our RAII analysis determines closure lifetimes. Non-escaping closures → stack allocation.

---

## Why No Null Pointers?

### Academic Consensus

ML, Haskell, Rust, and modern type theory converge on:
**Null is not a value - it's the absence of a value. Use Option/Maybe instead.**

### Tony Hoare's "Billion Dollar Mistake"

> "I call it my billion-dollar mistake... the invention of the null reference in 1965."  
> — Tony Hoare, 2009

Null pointers introduce:
- Runtime failure modes (NullPointerException, segfault)
- Defensive null checks everywhere (branch misprediction)
- Type system holes (T vs T | null semantic inconsistency)

### ML Tradition: Algebraic Data Types

```ocaml
(* OCaml - no nulls, explicit absence *)
type 'a option = None | Some of 'a

(* Empty list is a constructor, not null *)
type 'a list = [] | (::) of 'a * 'a list
```

**Key Principle:** Absence is **explicit** (None, []), not **implicit** (null).

### Flat Closures Eliminate Need for Null

```fsharp
// WRONG (null-based model)
type Closure = { code_ptr: ptr; env_ptr: ptr }  // env_ptr = null if no captures?

// RIGHT (flat closure model)
type Closure = { code_ptr: ptr; captures: T list }  // captures = [] if no captures
// Represented as: { code_ptr: ptr, cap0: T0, cap1: T1, ... }
```

**Zero captures = { code_ptr }** - still a concrete struct, no special "empty" case, no null.

---

## Fidelity's Architectural Commitments

### 1. Everything Is a Flat Closure

Lambdas, lazy thunks, seq generators, empty collections - **all use the same pattern**:

```mlir
// Empty collection
%empty = llvm.mlir.undef : !llvm.struct<(ptr)>  // { code_ptr }

// Lambda with 2 captures
%closure = llvm.mlir.undef : !llvm.struct<(ptr, i64, ptr)>  // { code_ptr, cap0, cap1 }

// Lazy thunk with memoization
%lazy = llvm.mlir.undef : !llvm.struct<(i1, T, ptr, ...)>  // { computed, value, code_ptr, caps }
```

### 2. Stack Allocation by Default

```mlir
%closure_mem = memref.alloca() : memref<closure_type>
```

**Heap allocation only when:**
- Closure escapes stack frame (RAII analysis detects this)
- Closure size exceeds stack limit (compile-time known)

### 3. No Null, Ever

**Architectural Incompatibility:** Null pointers require:
- Runtime null checks (branching)
- Special "empty" vs "non-empty" code paths
- Heap allocation distinction
- Garbage collection for cleanup

**Flat closures provide:**
- No branches (structure is always known)
- ONE code path (all closures have same shape)
- Stack allocation (deterministic lifetime)
- Direct access (no indirection penalty)

---

## Performance Characteristics

### Memory Layout

```
Traditional Closure (env_ptr model):
Closure: [code_ptr: 8 bytes, env_ptr: 8 bytes]  // 16 bytes
         ↓
Env:     [cap0: 8 bytes, cap1: 8 bytes]         // 16 bytes
Total: 32 bytes (2 allocations, 1 indirection)

Flat Closure:
Closure: [code_ptr: 8 bytes, cap0: 8 bytes, cap1: 8 bytes]  // 24 bytes
Total: 24 bytes (1 allocation, 0 indirections)
```

**Savings:**
- 25% less memory (24 vs 32 bytes)
- 50% fewer allocations (1 vs 2)
- 100% fewer pointer dereferences (0 vs 1)

### Cache Behavior

Flat closures exhibit better cache locality:
- Code pointer and captures in same cache line
- No chase of env_ptr → env data
- Fewer TLB misses (single contiguous allocation)

---

## Sources

**Academic Papers:**
- Appel, "Compiling with Continuations" (1992) - Closure conversion
- Birkedal et al., "The ML Kit" (1998-2006) - Region-based memory management
- Tarditi et al., "TIL: A Type-Directed Optimizing Compiler for ML" (1996) - Closure optimization

**Language Implementations:**
- OCaml: `ocaml/ocaml` on GitHub - See `lambda/lambda.ml` for explicit arity
- MLton: `MLton/mlton` - Whole-program ML compiler with closure optimization
- Rust: Rust Book Chapter 13 (Closures) - Stack-based closure model

**Blog Posts:**
- "Arity on the Side of Caution" (SpeakEZ blog, January 2026) - Fidelity's arity tracking
- Xavier Leroy's OCaml optimization talks - Saturated call optimization

**Key Quote from Xavier Leroy (OCaml lead):**
> "In practice, most function applications are fully saturated. We optimize for the common case: direct calls with register-passed arguments. Partial application remains correct but slower."

---

## Conclusion

Flat closures are not an invention - they're the **natural evolution** of 50 years of ML compiler research:

1. **1970s-1980s:** ML establishes currying and explicit arity
2. **1990s:** MLKit demonstrates region-based flat closures
3. **2000s:** OCaml proves saturated-call optimization in production
4. **2010s:** Rust validates stack-based closure safety via ownership
5. **2020s:** Fidelity extends flat closures to **all** constructs (lambdas, lazy, seq, collections)

**The standing art composes up. We use it.**

# Type Checker Anti-Patterns: What NOT To Do

## Purpose

This memory captures critical mistakes to avoid when building the FNCS native type checker. Often knowing what NOT to do is as valuable as knowing what to do.

## Soundness and Correctness

### Anti-Pattern 1: Skip the Occurs Check

**The Problem:** Before binding a type variable to a type, you MUST verify the type doesn't contain that variable.

```
Without occurs check:
  'a ~ 'a -> int
  Creates infinite type: (...(int -> int) -> int) -> int

With occurs check:
  Fails immediately with clear error
```

**The Fix:** Always implement occurs check in unification. It prevents infinite types and non-termination.

### Anti-Pattern 2: Intentional Unsoundness

**The Problem:** TypeScript intentionally broke soundness for "developer ergonomics." Result: you cannot prove any interesting properties about TypeScript code.

**The Fix:** Maintain soundness. For Fidelity, types carry memory guarantees - unsoundness means memory corruption.

### Anti-Pattern 3: Silent Failures During Type Checking

**The Problem:** Swallowing errors or returning placeholder types when resolution fails.

**The Fix:** Every failure is a signal. Emit clear errors, don't continue with broken state.

## Memory and Ownership

### Anti-Pattern 4: Self-Referential Structures

**The Problem (from Rust):** Data structures that contain pointers to their own fields.

```rust
struct SelfRef {
    data: String,
    ref_to_data: &str,  // Points into data - INVALID after move
}
```

**Why it's bad:** When the struct moves (stack to heap, reallocation), interior pointers become invalid.

**The Fix:** Use arena allocation, indices instead of pointers, or explicit Pin semantics. For FNCS, consider whether native types should support interior references at all.

### Anti-Pattern 5: Clone to Bypass Ownership

**The Problem (from Rust):** Using `.clone()` to make borrow checker errors disappear.

**Why it's bad:** Hides the real ownership issue, adds runtime overhead, masks bugs.

**The Fix:** Understand and fix the ownership issue. If the code needs multiple ownership, use explicit shared ownership.

### Anti-Pattern 6: Re-borrowing Mutable as Shared

**The Problem:** Converting `&mut T` to `&T` and then using both.

**Why it's bad:** Has all cons of mutable refs AND all cons of shared refs, pros of neither.

**The Fix:** Choose one borrowing mode. Don't mix.

## Type System Design

### Anti-Pattern 7: Overly Abstract Lifetimes

**The Problem (from Rust):** Lifetimes that are too abstract for developers to understand.

**Why it's bad:** Compiles but is overly restrictive. Developers can't reason about it.

**The Fix:** Consider the Polonius approach - represent borrows concretely as "origins" (sets of loans to places) rather than abstract lifetime names.

### Anti-Pattern 8: Separating Constraint Collection from Solving

**The Problem (from older implementations):** Collecting all constraints first, then solving in a separate pass.

**Why it's bad:** Errors reported far from their source. Can't incrementally refine types during checking.

**The Fix:** F# approach - interleave solving with checking. Solve constraints immediately when possible, defer only when necessary.

### Anti-Pattern 9: Mutable Substitutions via HashMap

**The Problem:** Using HashMap for type variable substitutions.

**Why it's bad:** Chains of substitutions don't collapse. Same variable looked up repeatedly. Inefficient.

**The Fix:** Use Union-Find. Variables are unified directly, chains collapse automatically. O(α(n)) amortized with path compression.

### Anti-Pattern 10: Row Polymorphism via Subtyping

**The Problem:** Implementing record types with subtyping rules.

**Why it's bad:** Subtyping and type inference don't mix. Need complex subsumption rules.

**The Fix:** Use row polymorphism with type equality only. No subtyping needed.

## Implementation Pitfalls

### Anti-Pattern 11: Phase Ordering Problems

**The Problem:** Each optimization pass makes pessimistic assumptions about others.

**Why it's bad:** Global result is suboptimal. Fixing one pass breaks another.

**The Fix:** Design passes with explicit dependencies. Use nanopass architecture where each pass has clear pre/post conditions.

### Anti-Pattern 12: Keeping IL Machinery "Just in Case"

**The Problem:** Preserving ImportMap, ILTypeRef, etc. behind feature flags.

**Why it's bad:** Cognitive overhead. Dead code. BCL assumptions leak through.

**The Fix:** DELETE, don't guard. Use the F# compiler as reference if you need to understand something, but don't preserve the machinery.

### Anti-Pattern 13: Central Dispatch in Type Checking

**The Problem:** Handler registry that routes based on expression kind with special cases.

**Why it's bad:** Attracts more special cases. Library knowledge leaks into type checker.

**The Fix:** Type checking should be uniform. Special behavior comes from types, not name matching.

## Memory Layout

### Anti-Pattern 14: Type Erasure for Native Compilation

**The Problem:** Erasing types early, using uniform representation.

**Why it's bad:** Requires boxing for multi-word values. Runtime overhead. GC integration needed.

**The Fix:** Monomorphization. Generate specialized code for each type instantiation. Types determine exact layout.

### Anti-Pattern 15: Implicit Layout Decisions

**The Problem:** Letting the backend decide field ordering and padding.

**Why it's bad:** Non-deterministic layouts. FFI compatibility issues. Can't reason about memory at source level.

**The Fix:** Explicit layout control. Types should determine layout. Use repr-like attributes when needed.

## F# Compiler (FCS) Specific Anti-Patterns

These are patterns observed in the fsharp compiler that should be avoided:

### Anti-Pattern 16: IL Import Assumption
**The Problem:** 3.2MB/59 files (the entire type-checking layer) assume IL machinery exists for importing types from assemblies.

**Why it's bad:** Creates massive dependency on .NET runtime concepts that don't exist in native compilation.

**The Fix:** Native types from the ground up. Type information comes from source, not assemblies.

### Anti-Pattern 17: Separate AST and Typed Tree
**The Problem:** FCS maintains `SynExpr` (syntax) and `FSharpExpr` (typed) as separate structures requiring correlation.

**Why it's bad:** Requires complex "Baker" logic to correlate trees. Creates unnecessary intermediate representations.

**The Fix:** Unified representation where types are attached during construction. The output IS the semantic graph.

### Anti-Pattern 18: BCL Type Dependencies
**The Problem:** Type system assumes BCL types exist (`System.String`, `System.Int32`, etc.).

**Why it's bad:** Couples type checking to .NET runtime. Native strings are UTF-8 `NativeStr`, not BCL `System.String`.

**The Fix:** Native type primitives from the start. `string` means `NativeStr`, not `System.String`.

### Anti-Pattern 19: Soft-Delete Reachability (when not needed)
**The Problem:** Marking nodes as unreachable but preserving structure (needed for dual-tree zipper navigation).

**Why it's bad:** Keeps dead code in the graph. Only necessary when correlating separate trees.

**The Fix:** Hard prune before handoff. With unified representation, unreachable nodes serve no purpose.

### Anti-Pattern 20: SRTP as Post-Hoc Overlay
**The Problem:** Resolving statically resolved type parameters after the typed tree is constructed.

**Why it's bad:** Creates additional pass over the tree. Resolution information not intrinsic to nodes.

**The Fix:** SRTP resolution during type checking. Resolved member attached to node during construction.

### Anti-Pattern 21: Global Mutable State in Solver
**The Problem:** Global mutable state in constraint solving (e.g., shared substitution tables).

**Why it's bad:** Makes reasoning about solver behavior difficult. Parallel solving becomes complex.

**The Fix:** Immutable substitution threading. Use persistent data structures for constraint environments.

## Downstream Type Flow Anti-Patterns

These anti-patterns occur when FNCS provides correct type information but downstream consumers (like Firefly/Alex) ignore or discard it.

### Anti-Pattern 22: Ignoring FNCS TypeLayout in Downstream Mapping

**The Problem (January 2026):** FNCS correctly defines string type layout:
```fsharp
// FNCS NativeGlobals.fs - CORRECT
let stringTyCon = mkTypeConRef "string" 0 (TypeLayout.Inline(16, 8))  // Fat pointer
```

But downstream `mapType` ignores this and returns wrong type:
```fsharp
// Firefly FNCSTransfer.fs - WRONG
| "string" -> Pointer  // Ignores that FNCS knows strings are fat pointers!
```

**Why it's critical:** The type information IS the contract. When downstream code ignores it, type mismatches manifest as mysterious MLIR errors far from the source.

**The Fix:** Downstream code must respect FNCS type semantics. `mapType` must return `NativeStrType` (fat pointer struct) for strings, matching the `TypeLayout.Inline(16, 8)` that FNCS defines.

### Anti-Pattern 23: Hardcoding Function Signatures Instead of Using Node.Type

**The Problem:** PSG nodes carry `Type: NativeType` from FNCS. But downstream code ignores it:
```fsharp
// WRONG - Hardcoded signature ignores valueNode.Type
| SemanticKind.Lambda _ ->
    let signature = "(!llvm.ptr) -> !llvm.ptr"  // HARDCODED!
    ...
```

**Why it's bad:** FNCS resolved the types. The node has `TFun(stringType, intType)`. Using hardcoded signatures breaks the principled type flow.

**The Fix:** Derive signatures from the actual types:
```fsharp
// RIGHT - Use the type FNCS provided
match valueNode.Type with
| NativeType.TFun(paramTy, retTy) ->
    sprintf "(%s) -> %s"
        (Serialize.mlirType (mapType paramTy))
        (Serialize.mlirType (mapType retTy))
```

### Anti-Pattern 24: "Fallback" Logic That Discards Type Information

**The Problem:** Creating fallback paths for "wasn't traversed yet" scenarios that use hardcoded types instead of querying the graph.

**Why it's bad:** The graph contains everything. FNCS put the types there. The zipper provides "attention" to any node. There's no legitimate "wasn't traversed yet" if you use the architecture correctly.

**The Principle:** Type information flows: FNCS → PSG nodes → `mapType` → `Serialize.mlirType` → MLIR string. Every step must preserve the semantics. Fallbacks that hardcode types break this chain.

---

## Summary: The Big Ones

| Priority | Anti-Pattern | Why Critical |
|----------|--------------|--------------|
| 1 | Skip occurs check | Non-termination, infinite types |
| 2 | Self-referential structs | Memory corruption after move |
| 3 | **Separate AST/typed tree** | Requires Baker-style correlation |
| 4 | Type erasure for native | Requires boxing, GC |
| 5 | **IL machinery preservation** | Cognitive overhead, BCL leakage |
| 6 | HashMap for substitutions | Inefficiency, chain explosion |
| 7 | Unsoundness for ergonomics | Memory guarantees broken |
| 8 | **BCL type dependencies** | Native types can't compile |
| 9 | **Soft-delete when unified** | Keeps dead code unnecessarily |
| 10 | **SRTP as post-hoc overlay** | Extra pass, non-intrinsic |

## Sources

- Rust Design Patterns: Clone anti-pattern
- Common Rust Lifetime Misconceptions (pretzelhammer)
- Effective Rust: Borrows and self-referential structs
- Thunderseethe: Union-Find for unification
- F# Compiler: Constraint solver architecture
- MLton: Monomorphization benefits
- SIGPLAN Blog: Type soundness proofs
- **F# Compiler (FCS)**: IL dependency cone analysis
- **Firefly/Baker**: Dual-tree zipper correlation patterns

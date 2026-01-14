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

## Historical Anti-Patterns (Resolved)

These anti-patterns from the original FCS-based approach have been resolved by FNCS's clean-sheet implementation:

- **IL Import Assumption**: FNCS has no IL machinery - types come from source only
- **Separate AST/Typed Tree**: FNCS attaches types during construction, no correlation needed
- **BCL Type Dependencies**: FNCS uses NTU types exclusively
- **SRTP as Post-Hoc Overlay**: FNCS resolves SRTP during type checking

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

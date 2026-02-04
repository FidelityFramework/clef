# Inline Architecture: Real Functions, MLIR Norms, F# Idiom Preservation

**Date:** 2026-02-04  
**Context:** Resolving spurious VarRef wrapper nodes during inline expansion  
**Decision:** Option 2 - Real functions by default, MLIR-level optimization

---

## Architectural Principle

**F# Native uses REAL FUNCTIONS with proper calling conventions. The `inline` keyword is NOT for compile-time substitution - it's a hint for MLIR optimization.**

### The Three Options

| Approach | Default Behavior | `inline` Keyword | Optimization |
|----------|------------------|------------------|--------------|
| **Option 1** | Inline substitution | Redundant | PSG-level (early, inflexible) |
| **Option 2** ✅ | Real func.func | MLIR hint | MLIR-level (late, flexible) |
| **Option 3** | Real func.func | Ignored | Pure MLIR passes |

**We chose Option 2** because it preserves F# idioms, maintains MLIR norms, and enables multi-target flexibility.

---

## Why Real Functions Matter

### 1. **Multi-Target Compilation** (CPU/GPU/TPU/NPU/Microcontroller)
Different targets make different inlining decisions:
- **CPU**: Inline small functions, preserve stack for debugging
- **GPU**: Aggressive inlining, minimize divergence
- **TPU**: Preserve functions for operator fusion
- **NPU**: Target-specific operator libraries
- **Microcontroller**: Balance code size vs performance

MLIR norms allow backends to choose. PSG-level inlining forces ONE decision for ALL targets.

### 2. **Width Separation from Types**
Intrinsic dimensional types enable control flow vs data flow pivots:
```fsharp
// Same F# code
let process (data: array<float32>) = ...

// Different MLIR per target
// CPU: scf.for + arith.addf
// GPU: gpu.launch + vector operations  
// TPU: tpu.einsum (fused operator)
```

Width (platform word size, vector width) is SEPARATE from type identity. Real functions preserve this separation.

### 3. **F# BCL Idiom Preservation**
Design-time experience must match F# expectations:
```fsharp
// Developer writes F# idioms
Console.write "Hello"
Array.map f xs
List.filter pred lst

// NOT syscall syntax
Sys.write STDOUT buffer length
```

Platform library (Fidelity.Platform) provides **adaptation layer** from F# idioms → target-specific MLIR.

---

## The Spurious VarRef Problem (Resolved)

### Root Cause
When FNCS inline-substituted functions during PSG construction:
```fsharp
let inline write (s: string) = Sys.write STDOUT s
```

Calling `Console.write "Hello"` created:
1. Literal "Hello" (node 478)  
2. **Binding for parameter `s` pointing to node 478** (during inline substitution)
3. **VarRef("s", Some 478)** when body references `s` (spurious wrapper!)
4. Application uses VarRef instead of Literal directly

VarRef should point to **Binding nodes**, not Literal nodes. This violated PSG structure.

### Solution
**Remove `inline` keyword from platform library functions:**
```fsharp
// BEFORE (inline substitution, creates VarRef wrapper)
let inline write (s: string) : unit =
    let _ = Sys.write STDOUT s
    ()

// AFTER (real function, proper calling convention)
let write (s: string) : unit =
    let _ = Sys.write STDOUT s
    ()
```

PSG structure after fix:
```
Application(Console.write, [Literal("Hello")])
  ↓ function call
func.func @Console.write(%s: memref<?xi8>)
  Application(Sys.write, [STDOUT, %s])
```

Clean, no VarRef indirection. Arguments flow through call chain naturally.

---

## When to Use `inline` in F# Native

### ✅ USE `inline` for:
1. **Generic constraints (SRTP)** - F# language requirement
   ```fsharp
   let inline add x y = x + y  // Requires (+) operator
   ```

2. **MLIR optimization hints** - Hot paths, small functions
   ```fsharp
   let inline fastPath x = x * 2 + 1  // Suggest inlining
   ```

### ❌ DO NOT use `inline` for:
1. **Platform library adapters** - Console, Array wrappers
2. **Functions with complex bodies** - Let MLIR decide
3. **Multi-target abstraction** - Need flexibility per backend

### 🤔 Default Assumption
**When in doubt, OMIT `inline`.** Let MLIR optimization passes make the decision based on:
- Call frequency (profiling)
- Function size (code bloat vs speed)
- Target constraints (GPU divergence, TPU fusion opportunities)

---

## FNCS Implementation

### PSG Construction
Functions WITHOUT `inline`:
```fsharp
let write s = Sys.write STDOUT s
```

FNCS emits:
```
SemanticKind.Binding("write", ...)
  └─ SemanticKind.Lambda([("s", stringType)], bodyNode)
      └─ SemanticKind.Application(Sys.write, [STDOUT, VarRef("s")])
```

When called: `Console.write "Hello"`
```
SemanticKind.Application(VarRef("Console.write"), [Literal("Hello")])
```

VarRef points to **Binding node** for Console.write. Argument is **Literal** (direct child). ✅ Correct structure.

### Inline Expansion (SRTP only)
Functions WITH `inline` ONLY when SRTP requires it:
```fsharp
let inline add x y = x + y
```

FNCS substitutes body during type checking to resolve generic constraints. This is **F# language semantics**, not optimization.

---

## Firefly/Alex Responsibilities

Alex does NOT decide whether to inline. Alex witnesses PSG structure:
- **Application → VarRef("funcName")**: Emit `func.call @funcName`
- **Lambda**: Emit `func.func` with parameters
- MLIR backend optimization passes decide inlining

No `isMain` special cases, no "inline this intrinsic" logic. Trust the PSG.

---

## Fidelity.Platform Guidelines

Platform libraries provide **F# idiom adaptation**, not zero-cost abstractions via inline:

```fsharp
// ✅ CORRECT: Real function, MLIR decides optimization
let write (s: string) : unit =
    let _ = Sys.write STDOUT s
    ()

// ❌ WRONG: Inline forces PSG substitution, creates VarRef wrappers  
let inline write (s: string) : unit =
    let _ = Sys.write STDOUT s
    ()
```

Users get F# idioms at design time. Compiler generates portable MLIR. Backend optimizes per target.

---

## Golden Rules

1. **Default: Real functions** - Omit `inline` unless SRTP requires it
2. **MLIR norms preserve optionality** - Don't force early decisions
3. **F# idioms at design time** - Platform library is adaptation layer
4. **Width ≠ Type** - Dimensional types enable target flexibility
5. **Trust the PSG** - Alex witnesses structure, doesn't decide inlining

---

## Related Memories

- `fncs_architecture` - Overall FNCS design
- `mlir_memref_strings_no_llvm_cruft` - Memref semantics, no fat pointers
- `alex_compositional_architecture_elements_patterns_witnesses` - Firefly witness architecture

**When resuming this work:** Read this memory FIRST. Inline is a hint, not a command. Real functions preserve architectural flexibility.

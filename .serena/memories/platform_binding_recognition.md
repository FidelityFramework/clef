# Platform Binding Recognition in FNCS

> **Status**: Critical architectural pattern for BCL-free platform integration
> **Last Updated**: January 2, 2026

## Core Concept

Platform bindings are functions defined in Alloy's `Platform.Bindings` module that serve as **recognition markers** for Firefly's Alex traversal. FNCS's role is to:

1. **Recognize** platform bindings by module structure (NOT string matching on names)
2. **Preserve types** from Alloy's binding definitions
3. **Mark with SemanticKind.PlatformBinding** for downstream recognition
4. **Pass complete type information** to Firefly for MLIR generation

## The BCL-Free Module Convention

Alloy uses a module convention instead of `DllImportAttribute` (which requires BCL):

```fsharp
// Alloy/Primitives.fs - BCL-free platform bindings
module Primitives =
    module Bindings =
        /// Alex intercepts calls to this module and provides MLIR emission
        let writeBytes (fd: int) (buffer: nativeint) (count: int) : int =
            0  // Placeholder - Alex replaces with syscall

        let readBytes (fd: int) (buffer: nativeint) (maxCount: int) : int =
            0  // Placeholder - Alex replaces with syscall
```

**Recognition Pattern**: Any qualified name containing `.Bindings.` or starting with `Bindings.`

## FNCS Recognition Logic (CheckExpressions.fs)

The `checkLongIdent` function must:

1. **Look up the binding FIRST** to get its type from Alloy
2. **Check if it's a platform binding** by module structure
3. **Preserve the type** while marking as platform binding

```fsharp
// CORRECT PATTERN
let isPlatformBinding =
    name.StartsWith("Bindings.") || name.Contains(".Bindings.")

match tryLookupBinding name env with
| Some binding when isPlatformBinding ->
    // PRESERVE the type from Alloy, mark as platform binding
    let entryPoint = parts.[parts.Length - 1]
    builder.Create(
        SemanticKind.PlatformBinding entryPoint,
        binding.Type,  // USE THE REAL TYPE from Alloy
        range,
        arena = env.CurrentArena)
| Some binding ->
    // Normal binding reference
    builder.Create(
        SemanticKind.VarRef(name, binding.NodeId),
        binding.Type,
        range,
        arena = env.CurrentArena)
| None when isPlatformBinding ->
    // Platform binding not in scope - fallback with fresh type var
    let entryPoint = parts.[parts.Length - 1]
    let resultTy = freshTypeVar range
    builder.Create(
        SemanticKind.PlatformBinding entryPoint,
        resultTy,
        range,
        arena = env.CurrentArena)
```

## CRITICAL: Type Preservation

**The type MUST come from Alloy's definition**. For `writeBytes`:

```fsharp
// Alloy defines this type:
let writeBytes (fd: int) (buffer: nativeint) (count: int) : int = 0
// Type: int -> nativeint -> int -> int
```

FNCS must resolve this type and attach it to the PSG node. If FNCS uses `freshTypeVar` when the binding exists in scope, the type information is LOST.

### Anti-Pattern (WRONG)

```fsharp
// WRONG - Checks isPlatformBinding BEFORE looking up binding
if isPlatformBinding then
    let resultTy = freshTypeVar range  // LOSES TYPE INFO!
    builder.Create(SemanticKind.PlatformBinding entryPoint, resultTy, ...)
else
    match tryLookupBinding name env with ...
```

This loses the type `int -> nativeint -> int -> int` and replaces it with an unresolved type variable.

## Information Flow to Firefly

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  Alloy/Primitives.fs                                                        │
│  let writeBytes (fd: int) (buffer: nativeint) (count: int) : int = 0       │
│  Type: int -> nativeint -> int -> int                                       │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│  FNCS (CheckExpressions.fs)                                                 │
│  1. Look up "Primitives.Bindings.writeBytes" in environment                 │
│  2. Found: binding with Type = int -> nativeint -> int -> int               │
│  3. Recognize: ".Bindings." → platform binding                              │
│  4. Create PSG node:                                                        │
│     - Kind: PlatformBinding "writeBytes"                                    │
│     - Type: int -> nativeint -> int -> int (PRESERVED!)                     │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│  Firefly/Alex (FNCSTransfer.fs)                                             │
│  • Receives PSG with SemanticKind.PlatformBinding                           │
│  • Has COMPLETE type information for curried application handling           │
│  • Generates platform-specific MLIR (syscall for writeBytes)                │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Why Type Preservation Matters

Curried function applications need type information to:

1. **Count expected arguments** - How many args before dispatching?
2. **Generate correct LLVM types** - Syscall signature must match
3. **Accumulate arguments** - Track partial application state

Without the type, Alex cannot determine when a curried platform binding has all its arguments.

## Relationship to Static/Dynamic Binding

From the blog "Library Binding in Fidelity Framework":

- **Static binding**: Library code linked into executable (determined at build time)
- **Dynamic binding**: Library loaded at runtime (P/Invoke style)

This is a **configuration decision**, not a code decision. The same `Platform.Bindings` pattern works for both. Alex consults project configuration to determine emission strategy.

FNCS doesn't care about static vs dynamic - it just:
1. Recognizes the platform binding pattern
2. Preserves the type
3. Marks appropriately for downstream processing

## Cross-References

- **Firefly**: `native_binding_architecture` - Alex's consumption of platform bindings
- **fsnative-spec**: `spec/native-type-mappings.md` - Type mapping requirements
- **Blog**: "Library Binding in Fidelity Framework" - Static/dynamic binding concepts
- **Blog**: "Standing Art: F# Metaprogramming" - Quotations as semantic carriers

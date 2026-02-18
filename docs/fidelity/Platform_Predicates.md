# Platform Predicates (F*-Inspired)

## Overview

Platform predicates are abstract propositions that enable conditional compilation without runtime checks. This design follows the F* pattern where platform capabilities are expressed as erased assumptions.

## F* Background

In F*, platform-dependent code uses predicates like `fits_u32` and `fits_u64`:

```fstar
(* F* platform predicate example *)
assume val fits_u32 : bool
assume val fits_u64 : bool

(* Conditional definition based on predicate *)
let platform_word_size =
  if fits_u64 then 64
  else if fits_u32 then 32
  else 16  (* fallback *)
```

Key insight: These predicates are **abstract** during type checking and **resolved** during code generation.

## Fidelity Platform Predicates

### Core Predicates

```fsharp
// Fidelity.Platform/Linux_x86_64/Capabilities.fs
module Capabilities =
    /// Platform supports 32-bit word operations
    let fits_u32: Expr<bool> = <@ true @>
    
    /// Platform supports 64-bit word operations
    let fits_u64: Expr<bool> = <@ true @>
    
    /// 64-bit support implies 32-bit support
    let fits_u64_implies_u32: Expr<unit> = <@ () @>
```

### Vector Extension Predicates

```fsharp
    /// Platform has AVX-512 vector support
    let has_avx512: Expr<bool> = <@ false @>  // CPU-dependent
    
    /// Platform has AVX2 vector support
    let has_avx2: Expr<bool> = <@ true @>
    
    /// Platform has NEON vector support (ARM)
    let has_neon: Expr<bool> = <@ false @>  // x86_64 doesn't have NEON
    
    /// Maximum supported vector width in bits
    let vector_width_max: Expr<int> = <@ 256 @>  // AVX2
```

### Atomics Predicates

```fsharp
    /// Platform has 64-bit atomic operations
    let has_atomics_64: Expr<bool> = <@ true @>
    
    /// Platform has 128-bit CAS (compare-and-swap)
    let has_atomics_128: Expr<bool> = <@ true @>  // cmpxchg16b on x86_64
```

### Memory Model Predicates

```fsharp
    /// Platform has cache coherency
    let has_cache_coherent: Expr<bool> = <@ true @>
    
    /// Platform supports memory-mapped I/O
    let has_mmio: Expr<bool> = <@ true @>
```

## How Predicates Flow Through the Pipeline

### 1. Fidelity.Platform Definition

```fsharp
// Platform binding library defines predicates as quotations
let fits_u64: Expr<bool> = <@ true @>
```

### 2. Firefly Extraction

```fsharp
// Firefly loads platform library and extracts quotations
let capabilities = loadPlatformCapabilities platformPath
// capabilities.fits_u64 = <@ true @>
```

### 3. FNCS Attachment

```fsharp
// FNCS receives predicates as part of PlatformContext
type PlatformContext = {
    Predicates: Map<string, Expr<bool>>
    // fits_u64 -> <@ true @>
}
```

### 4. Alex Witnessing

```fsharp
// Alex evaluates predicates and eliminates dead branches
match evaluatePredicate "fits_u64" ctx with
| true -> 
    // Generate 64-bit code path
    emitI64Operations()
| false ->
    // Skip this branch entirely
    ()
```

## Usage in Application Code

### Conditional Compilation

```fsharp
// Application code uses predicates for conditional logic
let vectorAdd (a: array<float>) (b: array<float>) =
    if Platform.has_avx512 then
        vectorAdd_avx512 a b
    elif Platform.has_avx2 then
        vectorAdd_avx2 a b
    elif Platform.has_neon then
        vectorAdd_neon a b
    else
        vectorAdd_scalar a b
```

After Alex witnesses the predicates, dead branches are eliminated:

```mlir
// On x86_64 with AVX2 (has_avx512 = false, has_avx2 = true)
// Only vectorAdd_avx2 implementation remains
func @vectorAdd(%a: !llvm.ptr, %b: !llvm.ptr) {
    // AVX2 implementation
}
```

### Platform-Specific Types

```fsharp
// Type selection based on platform
type WordType =
    if Platform.fits_u64 then int64
    elif Platform.fits_u32 then int32
    else int16
```

## Predicate Implications

Some predicates imply others:

```fsharp
// 64-bit implies 32-bit
fits_u64 ==> fits_u32

// AVX-512 implies AVX2
has_avx512 ==> has_avx2

// AVX2 implies SSE4.2
has_avx2 ==> has_sse42
```

FNCS can use these implications for type checking:

```fsharp
// If fits_u64 is true, we know fits_u32 is also true
// No need to check both
```

## Platform Predicate Matrix

| Predicate | Linux_x86_64 | Linux_ARM64 | Linux_ARM32 | BareMetal_ARM32 |
|-----------|--------------|-------------|-------------|-----------------|
| fits_u32 | true | true | true | true |
| fits_u64 | true | true | false | false |
| has_avx512 | CPU-dep | false | false | false |
| has_avx2 | true | false | false | false |
| has_neon | false | true | true | true |
| has_atomics_64 | true | true | false | false |
| has_atomics_128 | true | true | false | false |

## Implementation in FNCS

### Predicate Type

```fsharp
/// Platform predicate (abstract proposition)
type PlatformPredicate =
    | FitsU32
    | FitsU64
    | HasAVX512
    | HasAVX2
    | HasNEON
    | HasAtomics64
    | HasAtomics128
    | Custom of string
```

### Predicate Context

```fsharp
/// Context carrying predicate values
type PredicateContext = {
    /// Known predicate values
    Values: Map<PlatformPredicate, Expr<bool>>
    
    /// Implication rules
    Implications: (PlatformPredicate * PlatformPredicate) list
}
```

### Predicate Checking

```fsharp
/// Check if predicate is satisfied
let checkPredicate (pred: PlatformPredicate) (ctx: PredicateContext) : bool option =
    match ctx.Values.TryFind pred with
    | Some expr -> evaluateConstBool expr
    | None -> 
        // Check implications
        ctx.Implications
        |> List.tryPick (fun (antecedent, consequent) ->
            if consequent = pred then
                checkPredicate antecedent ctx
            else None)
```

## Dead Code Elimination

Alex uses predicates to eliminate unreachable code:

```fsharp
// Before predicate resolution
if Platform.has_avx512 then
    avx512_path()
else
    fallback_path()

// After resolution on x86_64 without AVX-512
// The avx512_path branch is completely removed
fallback_path()
```

This happens at compile time, resulting in smaller binaries with no runtime overhead.

## Related Documentation

- `NTU_Type_System.md` - NTU type implementation
- `Fidelity.Platform/Capabilities.fs` - Predicate definitions
- `fncs-specification.md` - FNCS specification

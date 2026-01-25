# NTU Collection Architecture

## Design Philosophy

Collections in Fidelity are **FNCS-level primitives** using the NTU (Native Type Universe) machinery. This follows ML/F* patterns where collection types are language-level constructs with platform-resolved metadata.

### Key Principle: Erased Width Generics

NTUKind provides "erased generics" for platform-dependent values:

```
Source Level        FNCS Level (Abstract)     Alex Level (Resolved)
─────────────────────────────────────────────────────────────────────
int                 NTUint                    i64 (x86_64) / i32 (ARM32)
array.Length        NTUsize                   i64 (x86_64) / i32 (ARM32)
array[i]            Index by NTUint           Same as above
```

Type identity (`NTUint ≠ NTUint64`) is preserved during type checking. Width metadata is erased when Alex witnesses platform quotations.

## F*/ML Inspiration

### F* LowStar.Buffer Pattern

```fstar
val len : mbuffer a rrel rel -> GTot U32.t  // Ghost - not computable at runtime
val length : mbuffer a rrel rel -> GTot nat // Mathematical natural number

// Indexing with precondition
let get (h:HS.mem) (p:mbuffer a rrel rel) (i:nat)
  : Ghost a (requires (i < length p)) (ensures (fun _ -> True))
```

F* separates:
- **Proof level**: `nat`, `U32.t` ghost values, SMT verification
- **Runtime level**: Extracted to C `uint32_t` or `size_t`

### Fidelity Adaptation

Fidelity doesn't have SMT proofs, but NTUKind serves the analogous role:
- **Type checking**: Abstract types with NTUKind identity
- **Codegen**: Platform quotations resolve concrete widths

## FNCS Collection Types

### NativeArray<'T>

The fundamental contiguous collection:

```fsharp
// FNCS intrinsic type (not library type)
type NativeArray<'T> =
    // Pointer to first element
    Pointer: NTUptr<'T>
    // Number of elements (platform-sized)
    Length: NTUsize
    // Memory region affinity (stack, arena, heap)
    Region: MemoryRegion  // Erased metadata

// Operations as FNCS intrinsics:
Array.length : NativeArray<'T> -> NTUint  // Returns platform word for F# compat
Array.get    : NativeArray<'T> -> NTUint -> 'T
Array.set    : NativeArray<'T> -> NTUint -> 'T -> unit
Array.create : NTUint -> 'T -> NativeArray<'T>
```

**Design choice**: `Array.length` returns `NTUint` (not `NTUsize`) for F# source compatibility. F# uses `int` for array lengths.

### NativeSpan<'T>

A view into contiguous memory (does not own):

```fsharp
type NativeSpan<'T> =
    Pointer: NTUptr<'T>
    Length: NTUsize

// Non-owning - lifetime tied to source
Span.ofArray  : NativeArray<'T> -> NativeSpan<'T>
Span.slice    : NativeSpan<'T> -> NTUint -> NTUint -> NativeSpan<'T>
```

### NativeSlice<'T>

Immutable view (like ReadOnlySpan):

```fsharp
type NativeSlice<'T> =
    Pointer: NTUptr<'T>
    Length: NTUsize
    // Immutable marker (enforced by type system)
```

## Type Resolution Flow

```
F# Source: let arr = Array.create 10 0
                              ↓
FCS Parse: App(Array.create, [Int 10; Int 0])
                              ↓
FNCS Check: 
  - 10 : NTUint (platform word)
  - 0 : NTUint (element type inferred)
  - Result: NativeArray<NTUint>
  - Array.Length type: NTUint
                              ↓
PSG: Intrinsic(Array.create) with NTU-typed arguments
                              ↓
Alex: Witness platform quotations
  - NTUint on x86_64 → i64
  - NTUsize on x86_64 → i64
                              ↓
MLIR: memref<10 x i64> or llvm.array<10 x i64>
```

## Integration with Memory Levels

Collections integrate with Fidelity's "memory management by choice":

### Level 1 (Default)
- Compiler chooses stack vs arena based on escape analysis
- Developer writes standard F# array syntax
- NTU types resolved automatically

### Level 2 (Hints)
- Developer can hint memory preference: `[<StackAlloc>]`
- Region affinity guides allocation strategy
- Still NTU-typed, quotation-resolved

### Level 3 (Explicit)
- Developer specifies exact allocation: `Arena.allocArray<'T> region count`
- Full control over memory layout
- NTU types with explicit region parameters

## Why Not Library Collections?

The user guidance is clear: avoid "over-paralleling BCL" by having a separate collections library. Instead:

1. **FNCS provides primitives** - Array, Span, Slice are intrinsic types
2. **F# syntax works** - `arr.[i]`, `arr.Length`, `Array.create` all work
3. **NTU handles platform** - Width resolved by quotations, not library code
4. **Libraries focus on domain** - Higher-level abstractions if needed, built on FNCS primitives

## Relationship to Current 507 Errors

The type mismatch errors (`expected 'int64', got 'int'`) stem from:
1. Code using explicit `int64` where `int` (NTUint) should be used
2. Missing recognition of NTU type identity in some paths

With proper NTU collections:
- Array indexing uses `NTUint`
- Array length returns `NTUint`
- No explicit `int64` needed for platform operations
- Type identity preserved, width resolved by Alex

## Implementation Files

### FNCS (fsnative)
- `NativeTypes.fs` - NTUKind enum (already has NTUsize, NTUptr)
- *(DELETED: NativeGlobals.fs - greenfield pending)*
- `CheckExpressions.fs` - Array operation type checking
- `SemanticGraph.fs` - Platform context for quotation resolution

### Firefly
- `Alex/TypeMapping.fs` - Witness NTU to MLIR types
- `Alex/CodeGeneration/` - Array operation codegen

## Open Questions

1. **Multi-dimensional arrays** - Should `NativeArray<'T>` support multi-dim, or separate type?
2. **Bounds checking** - Insert runtime checks? Configurable by memory level?
3. **Literal arrays** - `[| 1; 2; 3 |]` syntax - stack or arena allocated?

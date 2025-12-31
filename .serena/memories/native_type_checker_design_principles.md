# Native Type Checker Design Principles

## Purpose

This memory captures architectural principles for building a native-first type checker for FNCS, based on research into ML type systems, Rust RAII patterns, and the F# compiler architecture.

## The Core Insight: Types Guide Memory Layout

In Fidelity, **types are not erased early** - they carry semantic meaning through the entire compilation pipeline, guiding every memory layout decision. This is fundamentally different from:

- **OCaml/Standard ML**: Type erasure after checking, uniform value representation (everything is a word, lowest bit distinguishes int/pointer)
- **Java/.NET**: Types exist but layout determined by runtime/GC
- **Rust**: Types directly determine layout, but with focus on ownership/borrowing

For FNCS, we want **Rust-like type-to-layout correlation** with **ML-like type inference**.

## Architectural Principles

### 1. Unified Representation (No Separate AST/Typed Tree)

**From F# compiler analysis:** Baker exists because FCS separates syntax tree from typed tree. If we build them together, correlation is intrinsic.

**Principle:** Construct a single semantic graph where:
- Types are attached during construction
- SRTP is resolved during type checking
- No post-hoc overlay needed

### 2. Monomorphization for Native Compilation

**From MLton and Rust research:** 

| Approach | Pros | Cons |
|----------|------|------|
| Monomorphization | Preserves layout, enables optimization | Binary bloat, no separate compilation |
| Type Erasure | Single implementation, smaller binary | Boxing overhead, less optimization |

**Principle:** FNCS should monomorphize generics. For native compilation without GC, this preserves exact memory layouts and enables type-specific optimizations.

### 3. Deterministic Memory with Scope-Based Cleanup

**From Rust RAII:**
- Resources acquired = object created
- Resources released = object goes out of scope
- Drop order: reverse of creation order
- No GC, no runtime overhead

**Principle:** FNCS types should carry enough information for Alex to emit deterministic cleanup at scope exits. This is "RAII semantics without the Rust complexity."

### 4. Constraint-Based Type Inference

**From Hindley-Milner and F# constraint solver:**

Three-phase approach:
1. **Constraint generation**: Walk AST, create type equations
2. **Unification**: Solve equations using Union-Find
3. **Generalization**: At let-bindings, generalize unconstrained variables

**Principle:** Use Union-Find for substitutions (not hashmap). This dramatically simplifies the solver and improves efficiency.

### 5. SRTP Resolution During Type Checking

**From F# architecture:** SRTP constraints are solved *during* type checking, not as a separate pass. Solutions are stored in mutable cells and consumed by codegen.

**Principle:** Keep SRTP resolution. It's essential for Alloy's operator overloading (like `$`). The resolution should be captured in the semantic graph for Alex to emit.

### 6. Hard Prune Before Handoff

**Principle:** After type checking and reachability analysis, hard-prune unreachable nodes before handing to Firefly. Unlike soft-delete (needed for Baker's dual-tree zipper), we don't need to preserve unreachable structure.

## What We Keep from F#

- Type representation (TType with forall, app, tuple, fun, var, measure)
- Constraint solver core (equations, traits - not IL constraints)
- SRTP mechanism (TraitCall, witness resolution)
- Let-binding generalization
- Delayed expression checking pattern (elegant for method resolution)

## What We Remove

- ImportMap (no IL import)
- ILTypeRef, ILMethodRef (no IL types)
- Type providers
- Assembly metadata reading
- BCL type mapping
- IL generation

## Key Data Structures

```fsharp
// Type representation (simplified from F#)
type NativeType =
    | TForall of typars: TypeParam list * body: NativeType
    | TApp of tycon: TypeConRef * args: NativeType list
    | TTuple of elements: NativeType list
    | TFun of domain: NativeType * range: NativeType
    | TVar of typar: TypeParam
    | TMeasure of measure: Measure
    | TRecord of fields: (string * NativeType) list
    | TUnion of cases: UnionCase list

// Constraint types (no IL constraints)
type Constraint =
    | TypeEquals of NativeType * NativeType
    | HasMember of NativeType * memberName: string * signature: NativeType
    | HasMeasure of NativeType * Measure

// Semantic graph node with type attached
type SemanticNode = {
    Id: NodeId
    Kind: NodeKind
    Type: NativeType option  // Attached during construction
    SRTPResolution: TraitResolution option  // Resolved during checking
    Children: NodeId list
    // No IsReachable - unreachable nodes are removed
}
```

## Success Criteria

1. Types attached during construction (no correlation pass)
2. SRTP resolved during type checking (no separate nanopass)
3. Graph hard-pruned before handoff to Firefly
4. Memory layout determinable from types alone
5. No IL/BCL machinery anywhere

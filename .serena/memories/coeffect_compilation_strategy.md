# Coeffect-Guided Compilation Strategy in FNCS

> **Status**: Forward-looking architectural direction for FNCS compiler intrinsics
> **Scope**: New compiler infrastructure not found in FCS

## Core Concept

**Coeffects** track what code NEEDS from its environment - the dual of effects (what code DOES to its environment). In the Fidelity framework, coeffect analysis guides the compilation strategy for computation expressions, determining whether to compile to:

- **DCont dialect** (delimited continuations) for sequential effects
- **Inet dialect** (interaction nets) for parallel pure computations

This is the **DCont/Inet duality** - a principled decomposition based on referential transparency.

## The Duality Model

```
┌──────────────────────────────────────────────────────────────────────────────┐
│  Computation Expression Source                                               │
│  validated { let! x = v1; and! y = v2; return x + y }                       │
└──────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌──────────────────────────────────────────────────────────────────────────────┐
│  FNCS Coeffect Analysis                                                      │
│  • Track: what each binding NEEDS (environment, state, context)              │
│  • Classify: sequential dependency vs parallel independence                  │
│  • Output: Coeffect annotations on PSG nodes                                 │
└──────────────────────────────────────────────────────────────────────────────┘
                                      │
              ┌───────────────────────┴───────────────────────┐
              ▼                                               ▼
┌────────────────────────────────┐       ┌────────────────────────────────────┐
│  Sequential (DCont)            │       │  Parallel (Inet)                   │
│  • let! chains                 │       │  • and! combinators                │
│  • State dependence            │       │  • Independent branches            │
│  • Continuation preservation   │       │  • Data flow graph                 │
└────────────────────────────────┘       └────────────────────────────────────┘
```

## Compilation Strategy Table

| CE Pattern | Coeffect Signature | Compilation Target | MLIR Dialect |
|------------|-------------------|-------------------|--------------|
| `async { let! x = a; let! y = b; return f x y }` | Sequential dependence | Continuation chain | DCont |
| `validated { let! x = a; and! y = b; return x + y }` | Parallel independence | Interaction net | Inet |
| `state { let! s = get; do! put (s+1); return s }` | Environment access | State monad | DCont |
| `reader { let! r = ask; return r.Config }` | Context requirement | Reader applicative | Inet |
| Mixed patterns | Analyze subexpressions | Split by pattern | Both |

## Coeffect Categories

### Resource Coeffects
Track what resources code NEEDS from its environment:

| Coeffect | Meaning | Example |
|----------|---------|---------|
| `Reads<'R>` | Needs read access to R | `let! cfg = getConfig` |
| `Uses<'S>` | Needs resource S | `let! conn = useConnection` |
| `Requires<'C>` | Needs capability C | `let! _ = requireAdmin` |

### Ordering Coeffects
Track sequencing requirements:

| Coeffect | Meaning | Compilation |
|----------|---------|-------------|
| `Sequential` | Must execute in order | DCont with `dcont.shift` |
| `Parallel` | Can execute independently | Inet with parallel reduction |
| `Barrier` | Synchronization point | Join/merge operation |

## FNCS Implementation Requirements

### Coeffect Tracking Infrastructure

1. **PSG Node Coeffect Annotation**
   ```fsharp
   type PSGNode = {
       // ... existing fields
       Coeffects: CoeffectSet  // NEW: environmental requirements
   }
   ```

2. **CE Desugaring with Coeffect Inference**
   ```fsharp
   // Each let! infers coeffects from the bound expression
   let! x = getState   // Coeffect: Reads<State>
   let! y = pureValue  // Coeffect: Pure (no requirements)
   ```

3. **Compilation Strategy Selection**
   ```fsharp
   match node.Coeffects with
   | Pure | ReaderOnly -> compileToInet node
   | HasSequentialDependence -> compileToDCont node
   | Mixed parts -> splitAndCompile parts
   ```

### Desugaring Recognition

FNCS must recognize CE desugaring patterns:

```fsharp
// Source
maybe { let! x = opt1; let! y = opt2; return x + y }

// Desugared (what FNCS sees)
builder.Bind(opt1, fun x ->
    builder.Bind(opt2, fun y ->
        builder.Return(x + y)))

// FNCS recognizes: nested Bind calls = continuation chain
// Coeffect analysis determines: sequential or parallel?
```

## DCont Dialect Compilation

For sequential patterns, emit DCont operations:

```mlir
// Sequential async
%k0 = dcont.reset {
    %x = dcont.shift @asyncOp1
    %y = dcont.shift @asyncOp2  // Depends on %x completion
    dcont.pure (%x, %y)
}
```

## Inet Dialect Compilation

For parallel patterns, emit Inet operations:

```mlir
// Parallel validated
%net = inet.create {
    %v1 = inet.principal @validate1
    %v2 = inet.principal @validate2  // Independent of %v1
    %result = inet.auxiliary @combine %v1, %v2
}
```

## Relationship to Delimited Continuations

The coeffect system determines WHEN to use delimited continuations:

- **All CEs** desugar to nested lambdas (implicit continuations)
- **DCont dialect** preserves these continuations in generated code
- **Inet dialect** eliminates continuations via parallel data flow
- **Coeffect analysis** chooses which approach

See Firefly's `delimited_continuations_architecture` memory for dialect details.

## Normative Requirements

From fsnative-spec `native-type-mappings.md`:

> NORMATIVE: Computation expressions SHALL be fully supported. These features operate at compile time and impose no runtime overhead.

The coeffect analysis occurs entirely at compile time. Generated code contains no coeffect metadata - only the compilation strategy result.

## Cross-References

- **Firefly**: `delimited_continuations_architecture` - DCont/Inet dialect details
- **Firefly**: `fsharp_metaprogramming_patterns` - CE as continuation capture
- **FNCS**: `quotation_semantic_carriers` - related compile-time semantics
- **fsnative-spec**: `spec/native-type-mappings.md` § "Compile-Time Metaprogramming"

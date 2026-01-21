# PSG Enrichment Infrastructure

> **Full documentation:** `/home/hhh/repos/Firefly/docs/PSG_Enrichment_Architecture.md`

## Key Concepts

**Enrichment** is the parent concept for compiler-synthesized PSG structure:
- **Elaboration** (PLT term): Fleshing out intrinsic semantics
- **Saturation** (Fidelity term): Filling PSG "to the brim" before lowering

## Two Enrichment Kinds

| Kind | Meaning | Examples |
|------|---------|----------|
| `"Intrinsic"` | Synthesized for intrinsic implementation | Hidden syscall in `Console.write` |
| `"Baker"` | Decomposition of language features to primitives | HOF recursion, seq state machines, lazy thunks |

**Baker covers all language feature decomposition:**
- HOF decomposition: `List.map` → recursion
- Seq expressions: `seq { }` → state machine nodes
- Lazy expressions: `lazy x` → thunk structure

## Metadata Schema

```fsharp
module ElaborationMetadata =
    let Kind = "Elaboration.Kind"   // "Intrinsic" or "Baker"
    let For = "Elaboration.For"     // e.g., "List.map", "Console.write"
    let Id = "Elaboration.Id"       // Links related nodes (int)
```

## Implementation

- `src/Compiler/PSGSaturation/SemanticGraph/Elaboration.fs` - Marking API
- `markBaker` / `markIntrinsic` convenience functions
- `freshId()` for generating unique expansion IDs

## Note on Coeffect Analysis

Coeffect analysis is SEPARATE from enrichment. It computes metadata about existing structure (SSA, mutability, yield states) - it does NOT create nodes. See `coeffect_analysis` memory.

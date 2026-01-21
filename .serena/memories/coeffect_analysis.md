# Coeffect Analysis

> **Full documentation:** `/home/hhh/repos/Firefly/docs/Coeffect_Analysis_Architecture.md`

## Key Distinction

**Coeffect Analysis is NOT Enrichment.**

- **Enrichment** (elaboration + saturation): Synthesizes PSG nodes
- **Coeffect Analysis**: Computes metadata ABOUT existing PSG structure

PSG structure is unchanged by coeffect analysis - it produces mappings, indices, and tables.

## What Coeffect Analysis Computes

| Analysis | Output | Purpose |
|----------|--------|---------|
| SSA Assignment | `Map<NodeId, SSA>` | Variable versioning |
| Mutability Analysis | `Set<NodeId>` | Which bindings are mutable |
| Yield State Indices | State machine layout | Seq lowering |
| Pattern Binding Analysis | Binding scopes | Match lowering |
| String Table | Literal collection | Data section |

## The Control-Flow ↔ Dataflow Pivot

This is why coeffects exist in Fidelity:
- F# source: Declarative (dataflow)
- Native code: Imperative (control-flow)

Coeffect analysis enables informed pivoting between representations.

## Pipeline Position

```
PSG Saturation (Enrichment)
         ↓
Coeffect Analysis  ← Analyzes complete structure
         ↓
Alex/Zipper → MLIR
```

Runs AFTER enrichment because it needs to see ALL nodes including synthesized ones.

## "Only Pay for What You Use"

Analyses are demand-driven - no seq expressions means no yield state analysis.

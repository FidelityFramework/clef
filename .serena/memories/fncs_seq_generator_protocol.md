# FNCS Seq Semantic Contract

## Context

This memory captures the **semantic contract** for `Seq<'T>` in FNCS - what sequences mean, not how they're compiled.

## Decision

`Seq<'T>` is an iteration type with these semantic guarantees:

1. **Lazy**: Elements computed on demand, not eagerly
2. **Pull-based**: Consumer controls iteration pace
3. **Composable**: Operations chain without intermediate allocation
4. **Restartable**: Can iterate multiple times (re-runs computation)

## Abstract Iteration Protocol

```
Advance → bool     // Move to next, returns false if exhausted
Current → 'T      // Get current element (valid after successful Advance)
Reset → unit      // Restart from beginning
```

This is an ABSTRACT protocol - concrete representation is strategy-dependent.

## Type and Operations

```fsharp
type Seq<'T>   // Abstract - implementation varies by strategy

module Seq =
    val empty : Seq<'T>
    val singleton : 'T -> Seq<'T>
    val map : ('T -> 'U) -> Seq<'T> -> Seq<'U>
    val filter : ('T -> bool) -> Seq<'T> -> Seq<'T>
    val collect : ('T -> Seq<'U>) -> Seq<'T> -> Seq<'U>
    val fold : ('S -> 'T -> 'S) -> 'S -> Seq<'T> -> 'S
    val iter : ('T -> unit) -> Seq<'T> -> unit
    // ... etc
```

## What This Does NOT Specify

Implementation details belong in Alex strategies, NOT here:
- Per-expression struct types
- State field encoding
- MoveNext function generation
- MLIR state machine emission

## Rationale

Separating semantics from implementation allows:
- StateMachine strategy (current): struct + state + MoveNext
- DCont strategy (future): yield as shift, for-in as reset
- Other strategies as needed

## Related

- `/home/hhh/repos/fsnative/docs/fidelity/FNCS_Lazy_Seq_Coroutine_Intrinsics.md`
- `/home/hhh/repos/Firefly/.serena/memories/computation_strategy_architecture.md`

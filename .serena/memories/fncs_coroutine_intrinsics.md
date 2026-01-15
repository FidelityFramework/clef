# FNCS Async Semantic Contract

## Context

This memory captures the **semantic contract** for `Async<'T>` in FNCS - what async computation means, not how it's implemented.

## Decision

`Async<'T>` is a suspendable computation type with these semantic guarantees:

1. **Monadic**: Satisfies monad laws (left/right identity, associativity)
2. **Suspendable**: Can pause execution at bind points
3. **Resumable**: Paused computation can continue later
4. **Composable**: Asyncs compose without blocking

## Type and Operations

```fsharp
type Async<'T>   // Abstract - implementation varies by strategy

module Async =
    // Core monad operations
    val Return : 'T -> Async<'T>
    val Bind : Async<'T> -> ('T -> Async<'U>) -> Async<'U>
    val Zero : Async<unit>
    val Combine : Async<unit> -> Async<'T> -> Async<'T>
    val Delay : (unit -> Async<'T>) -> Async<'T>

    // Execution
    val Start : Async<unit> -> unit
    val RunSynchronously : Async<'T> -> 'T

    // Composition
    val Parallel : Async<'T>[] -> Async<'T[]>
    val StartChild : Async<'T> -> Async<Async<'T>>

    // Utilities
    val Sleep : int -> Async<unit>
```

## What This Does NOT Specify

Implementation details belong in Alex strategies, NOT here:
- LLVM coroutine intrinsics (`llvm.coro.*`)
- Frame struct layout
- State machine encoding
- Suspension point mechanics

## Rationale

Separating semantics from implementation allows:
- StateMachine strategy (current): LLVM coroutines, no runtime
- DCont strategy (future): Delimited continuations, effect handlers
- Runtime-based (theoretical): Thread pool, tasks

## Strategy Selection Criteria

| Target | Recommended Strategy |
|--------|---------------------|
| Freestanding/embedded | StateMachine (no runtime) |
| Desktop with DCont | DCont (more expressive) |
| Interop with runtime | Runtime-based |

## Related

- `/home/hhh/repos/fsnative/docs/fidelity/FNCS_Lazy_Seq_Coroutine_Intrinsics.md`
- `/home/hhh/repos/Firefly/.serena/memories/computation_strategy_architecture.md`
- `/home/hhh/repos/Firefly/.serena/memories/async_llvm_coroutines.md` (StateMachine impl)

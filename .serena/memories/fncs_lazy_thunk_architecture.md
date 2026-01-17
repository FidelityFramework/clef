# FNCS Lazy Semantic Contract

## Context

This memory captures the **semantic contract** for `Lazy<'T>` in FNCS - what lazy computation means, not how it's implemented.

## Decision

`Lazy<'T>` is a computation type with these semantic guarantees:

1. **Deferred**: The wrapped computation doesn't run until forced
2. **At-most-once**: The computation runs at most one time
3. **Memoized**: After first force, result is cached
4. **Idempotent**: `force` returns the same result every time

## Type and Operations

```fsharp
type Lazy<'T>   // Abstract - implementation varies by strategy

module Lazy =
    val create : (unit -> 'T) -> Lazy<'T>
    val force : Lazy<'T> -> 'T
    val isValueCreated : Lazy<'T> -> bool
```

## NTUKind

`NTUlazy` - Marks this as a lazy computation type in the Native Type Universe.

## What This Does NOT Specify

Implementation details belong in Alex strategies, NOT here:
- Struct layout (`{ flag, value, thunk }`)
- Check-and-call pattern
- Thread safety mechanisms
- MLIR emission

## Rationale

Separating semantics from implementation allows:
- StateMachine strategy (current): simple struct + flag check
- DCont strategy (future): delimited continuation capture
- Other strategies as targets require

## Implementation Notes (January 2026)

The initial implementation attempted a `{code_ptr, env_ptr}` model with null env_ptr.
This was WRONG - it ignored the flat closure architecture just established in PRD-11.

**Correct approach:** Lazy is an EXTENDED flat closure:
```
Lazy<T> = {computed: i1, value: T, code_ptr: ptr, cap₀, cap₁, ...}
```

See `compose_from_standing_art_principle` memory for the general lesson.

## Related

- `/home/hhh/repos/fsnative/docs/fidelity/FNCS_Lazy_Seq_Coroutine_Intrinsics.md`
- `/home/hhh/repos/Firefly/.serena/memories/computation_strategy_architecture.md`
- `compose_from_standing_art_principle` - Critical architectural principle
- `lazy_thunk_calling_convention` - Option B decision details

# fsil Integration into FNCS

## Goal

fsil's inline + SRTP pattern becomes **the default semantic model** in FNCS - functions are transparent by default, generic operations resolve through witness hierarchy automatically.

## What fsil Provides (as library)

```fsharp
// Explicit inline + SRTP ceremony
let inline iter ([<InlineIfLambda>] f) (x: _) : unit =
    Internal.Iterate.Invoke(x, f)

// Static member convention for extensibility
type Tree<'T> =
    static member Iterate(self, fn) = ...  // Enables iter, fold, exists, etc.
```

## What FNCS Provides (intrinsic)

```fsharp
// Functions transparent by default (no inline annotation needed)
let process x = transform x  // Compiler sees through this

// SRTP resolves implicitly through witness hierarchy
let add x y = x + y  // Finds (+) via Alloy.BasicOps

// Collection protocol auto-detected and derived
type Tree<'T> =
    static member Iterate(self, fn) = ...
// FNCS automatically provides: iter, iteri, fold, exists, forall, find
```

## The Semantic Shift

| Aspect | FCS | FNCS |
|--------|-----|------|
| Default | Non-inline (opaque) | Inline (transparent) |
| Opt-out | N/A | `[<Opaque>]` attribute |
| SRTP | Explicit constraints | Implicit via witnesses |
| Generic ops | Require ceremony | Just work |

## Implementation Points in FNCS

| File | Change |
|------|--------|
| `CheckExpressions.fs` | Default to inline, add `[<Opaque>]` |
| `ConstraintSolver.fs` | Implicit SRTP, witness hierarchy search |
| `TcGlobals.fs` | Register Alloy witness types |
| `CollectionProtocol.fs` (new) | Detect Iterate/Map, synthesize derived ops |

## Why This Matters

When compiler sees through all function boundaries:
- **Escape analysis** spans entire call graph
- **Arena allocation** can be inferred
- **Lifetime analysis** works across abstractions
- **Fusion** of map/filter/fold chains becomes possible

## Documentation

- `~/repos/fsil/docs/fidelity/fsil_Integration_Plan.md` - Detailed plan
- `~/repos/fsnative/docs/fidelity/FNCS_Pruning_Plan.md` - Overall FNCS roadmap

## Status

fsil patterns to be absorbed during FNCS Phase 4-5 (after native types established).

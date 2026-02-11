# Generalized Escape Analysis — Implemented (Feb 2026, commit 02519cc)

## Architecture

```
PSGElaboration Phase (before Alex):
  EscapeAnalysis.analyzeGraph → Map<NodeId, EscapeKind>
    ↓ (bundled into TransferCoeffects.EscapeAnalysis)

Alex Witnessing Phase:
  pAllocValue queries ctx.Coeffects.EscapeAnalysis
    → StackScoped: memref.alloca (stack)
    → EscapesViaReturn: memref.alloc (heap, via AllocStatic)

Backend:
  memref.alloc → --finalize-memref-to-llvm → malloc call
  Console mode: libc malloc (just works)
  Freestanding: needs bump allocator (future work)
```

## EscapeKind DU (from "Managed Mutability" blog)

```fsharp
type EscapeKind =
    | StackScoped            // safe for stack
    | EscapesViaClosure of targetNode: NodeId
    | EscapesViaReturn       // must heap-allocate
    | EscapesViaByRef        // must pin or heap-allocate
```

## Key Components

### findAllocatingSites
Detects both `DUConstruct` and string-returning `Application` nodes.

### isTransitivelyReturned
Traces through IfThenElse/Sequential parent chain to function return.
Handles DUConstruct inside match arms that are the final expression.

### pAllocValue (PULL model)
Pattern combinator that queries EscapeAnalysis coeffect:
- `StackScoped` → delegates to `pUndef` (memref.alloca)
- `EscapesViaReturn` → delegates to `pAllocStatic` (memref.alloc)

### MemRefOp.AllocStatic
New MLIR op variant: heap allocation with compile-time static shape.
Serializes as `memref.alloc() : memref<Nxi8>` (no dynamic size SSA).

## Files Modified

| File | Change |
|------|--------|
| EscapeAnalysis.fs | EscapeKind DU, findAllocatingSites, isTransitivelyReturned |
| Types.fs | MemRefOp.AllocStatic variant |
| Serialize.fs | AllocStatic serialization |
| MemRefElements.fs | pAllocStatic element |
| MemoryPatterns.fs | pAllocValue combinator, pDUCase updated |

## Design Authority

Three blog posts:
- "Inferring Memory Lifetimes" (Jan 14) — three-level lifetime design
- "Doubling Down" (Jan 23) — allocation strategy as coeffect
- "Managed Mutability" (Feb 5) — EscapeKind DU, PULL model, phased roadmap

## Future Work (builds on this infrastructure)

- Arena injection (Phase 2): function signature transforms for arena parameters
- Closure escape integration: flat closure detection + allocation decisions
- Lifetime inference (Phase 3): minimum lifetime bounds, auto-scope arenas
- Freestanding bump allocator: needed when freestanding samples use DUs

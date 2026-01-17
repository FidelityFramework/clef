# PRD-14 Lazy Implementation Status (January 2026)

## Current State: Captures Not Working

**No-capture case WORKS:**
```
lazy 42 → Lazy.force → 42 ✓
```

**Capture case FAILS (garbage values):**
```
let x = 10; let y = 20
let sum = lazy (x + y)
Lazy.force sum → 4200198 (should be 30) ✗
```

## Root Cause Under Investigation

The issue is in **capture witnessing** in `FNCSTransfer.fs`. When processing `SemanticKind.LazyExpr`:

```fsharp
| SemanticKind.LazyExpr (bodyId, captures) ->
    let captureVals =
        captures
        |> List.choose (fun cap ->
            match cap.SourceNodeId with
            | Some srcId ->
                match resolveNodeToVal srcId z with  // ← PROBLEM HERE
                | Some v -> Some v
                | None -> None
            | None -> None)
```

`resolveNodeToVal` looks up NodeId in zipper's recalled results. But captured bindings (x, y) may not be accessible in current traversal scope. The SourceNodeId points to where variable was DEFINED, but we need the VALUE.

## What's Working

1. **FNCS correctly computes captures** - JSON shows:
   - `LazyExpr (NodeId 561, [{ Name = "x" ... }, { Name = "y" ... }])`
   - Captures have correct names and types

2. **Lazy struct types are correct** in MLIR:
   - No captures: `!llvm.struct<(i1, i64, !llvm.ptr)>`
   - With captures: `!llvm.struct<(i1, i64, !llvm.ptr, i32, i32)>`

3. **Option B calling convention implemented**:
   - Force allocs struct on stack, passes pointer to thunk
   - Thunk receives pointer, should extract its own captures

## Files Modified This Session

**FNCS:**
- `Applications.fs` - Added `Lazy.force` → `SemanticKind.LazyForce` conversion
- `Applications.fs` - Made `collectVarRefs` public, added `computeCaptures`
- `Coordinator.fs` - `checkLazy` uses `computeCaptures`

**Alex:**
- `LazyWitness.fs` - Option B: thunk receives ptr, SSA cost = 4
- `SSAAssignment.fs` - LazyExpr: 5+N, LazyForce: 4
- `FNCSTransfer.fs` - Simplified LazyForce (uniform)
- `Witness.fs` - Removed cruft `LazyOp` case

## Next Steps

1. **Debug capture witnessing** - Why aren't captured bindings resolved?
   - Check what `SourceNodeId` actually points to
   - May need to look up bindings differently than `resolveNodeToVal`

2. **Review how Lambda handles captures** - Closures work, lazy should follow same pattern

3. **Check binding scope** - Are x, y bindings being recalled before LazyExpr processes?

## Key Resources to Review

- **PRD-14**: `/home/hhh/repos/Firefly/docs/WREN_Stack_PRDs/PRD-14-Lazy.md`
- **Serena memories**: 
  - `lazy_thunk_calling_convention` - Option B details
  - `compose_from_standing_art_principle` - Must extend Lambda pattern
  - `fncs_lazy_thunk_architecture` - Semantic contract
  - `memory_layout_and_raii` - Struct layout principles

## Sample Location

`/home/hhh/repos/Firefly/samples/console/FidelityHelloWorld/14_Lazy/`
- Single canonical file: `Lazy.fs`
- Tests: no captures, with captures (x+y), captured multiplication

## Architectural Reminder

> "The standing art composes up. Use it."

Lazy captures MUST work the same way as Lambda captures (PRD-11). If Lambda's capture witnessing works, Lazy should follow identical pattern.

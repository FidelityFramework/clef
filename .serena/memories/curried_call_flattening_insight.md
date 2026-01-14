# Curried Call Flattening Insight (January 2026)

## STATUS: RESOLVED ✅ (January 2026)

The fix was applied to FNCS Applications.fs (not CheckExpressions.fs). Added `flattenApplication` recursive helper that runs AFTER the initial `(targetFuncId, allArgs)` computation to recursively flatten when `targetFuncId` points to an Application node.

**Location**: `/src/Compiler/Checking.Native/Expressions/Applications.fs` lines ~285-305

**Implementation**:
```fsharp
let rec flattenApplication (funcId: NodeId) (args: NodeId list) : NodeId * NodeId list =
    match builder.Nodes.TryFind funcId with
    | Some node ->
        match node.Kind with
        | SemanticKind.Application(innerFuncId, innerArgs) ->
            flattenApplication innerFuncId (innerArgs @ args)
        | _ -> (funcId, args)
    | None -> (funcId, args)

let (targetFuncId, allArgs) = flattenApplication targetFuncId allArgs
```

**Verified**: All samples 01-04 compile and run correctly.

---

# Original Issue

## The Problem

Sample 04 uses pipe operators with curried functions:
```fsharp
Console.readln()
|> greet prefix
```

The fncs_expr.txt shows NESTED structure:
```
App(App(Var(greet), [prefix]), [readln()])
```

But per spec: "Fully-applied curried calls compile to direct multi-argument calls"

It SHOULD be:
```
App(Var(greet), [prefix, readln()])
```

## Root Cause Found

FNCS **already has** curried application flattening at CheckExpressions.fs:1610-1622. But there's a gap in the PIPE REDUCTION logic.

### How Pipes Are Handled (Lines 1588-1607)

```fsharp
| SemanticKind.VarRef(name, _) when isPipeRight name ->
    match existingArgs with
    | [valueId] ->
        // argNode is the function, valueId is the value
        // Transform: f(x) instead of (|>)(x)(f)
        (argNode.Id, [valueId])  // ← THE BUG!
```

The pipe `(|>)(readln())(greet prefix)` is transformed to:
- `targetFuncId = argNode.Id` (the `greet prefix` Application node)
- `allArgs = [valueId]` (the readln() result)

This creates `App((greet prefix), [readln()])` - correct pipe elimination but **no curried flattening**!

### The Bug

After pipe transformation, `targetFuncId` points to an Application node (`greet prefix`).
The code then creates `SemanticKind.Application(targetFuncId, allArgs)`.
But it doesn't check: "Is targetFuncId itself an Application that should be flattened?"

### The Fix Location

In CheckExpressions.fs, after the `let (targetFuncId, allArgs) = ...` block, before creating the Application node:

Check if `targetFuncId` is an Application, and if so, recursively flatten:
- Look up the node for targetFuncId
- If it's Application(innerFuncId, innerArgs), flatten to (innerFuncId, innerArgs @ allArgs)
- Repeat until targetFuncId is not an Application

## Key Insight

The flattening logic exists but only applies when `funcNode.Kind` (the immediate function expression) is Application. The pipe reduction transforms the structure in a way that bypasses this check:

1. `(|>)(x)(f)` where `f = (greet prefix)` (an Application)
2. Pipe reduction returns `(f.Id, [x])` 
3. Code creates `Application(f.Id, [x])`
4. But f.Id points to Application(greet, [prefix])
5. No further flattening occurs!

## Architectural Note

This fix belongs in FNCS (CheckExpressions.fs), NOT in Firefly/Alex.
- FNCS builds the PSG
- Firefly consumes it as "correct by construction"
- Alex witnesses should NOT need to flatten - PSG should already be flat

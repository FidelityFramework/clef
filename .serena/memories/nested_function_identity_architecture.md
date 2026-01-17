# Nested Function Identity Architecture

> **Created**: January 2026
> **PRD**: PRD-13 (Recursion)
> **Status**: Implementation in progress

## The Problem

Nested functions with the same name collide when emitted as MLIR:

```fsharp
let factorialTail n =
    let rec loop acc n = ...    // Emits as @loop
    loop 1 n

let fibonacciTail n =
    let rec loop a b n = ...    // Also emits as @loop - COLLISION!
    loop 0 1 n
```

## The Principle

> **Structural identity is computed at construction time, not reconstructed during emission.**

Following F*/OCaml precedent:
- The enclosing scope is known during PSG construction
- Store it ON the Lambda node
- Downstream phases use it directly - no traversal

## The Solution

### FNCS Side (3 changes)

1. **TypeEnv field**: Add `EnclosingFunction: string option`
2. **Lambda field**: Add `enclosingFunction: string option` to SemanticKind.Lambda
3. **Bindings.fs**: Before checking function body, set `bodyEnv.EnclosingFunction = Some name`

The Lambda records its OWN enclosing function (from incoming `env`).

### Firefly Side (1 change)

SSAAssignment's `collectLambdas` uses enclosingFunction for qualified names:
```fsharp
let qualifiedName =
    match enclosingFunction with
    | Some parent -> sprintf "%s_%s" parent baseName
    | None -> baseName
```

## Anti-Patterns to Avoid

### DON'T traverse to find enclosing function
```fsharp
// WRONG
let rec findEnclosing nodeId =
    match graph.Nodes.[nodeId].Parent with
    | Some pid -> ... traverse up ...
```

### DON'T use Zipper position for identity
```fsharp
// WRONG
let qualifiedName = Focus.parentBinding zipper ...
```

### DON'T add special logic in witnesses
```fsharp
// WRONG
if isRecursiveSelfRef varRef z then ...
```

## Key Files

| File | Change |
|------|--------|
| `fsnative/.../Types.fs` | TypeEnv.EnclosingFunction |
| `fsnative/.../SemanticGraph.fs` | Lambda case gets enclosingFunction |
| `fsnative/.../Bindings.fs` | Set bodyEnv.EnclosingFunction |
| `Firefly/.../SSAAssignment.fs` | Use enclosingFunction in collectLambdas |

## Testing

1. Verify intermediate JSON shows `enclosingFunction: {"Some": "factorialTail"}` on nested Lambdas
2. Verify MLIR shows `@factorialTail_loop` (not `@loop`)
3. Verify execution produces correct results

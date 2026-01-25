# TypeApp Preserves Kind Principle

## The Architectural Decision

**When type application (TypeApp) is applied to a semantically-transparent node, the result preserves that node's Kind with the instantiated type. Application nodes are reserved for value-level function calls, not type-level instantiation.**

## The Problem That Revealed This Principle

When processing `NativePtr.stackalloc<byte> 256`, FNCS was creating:

```
Application(                           // Value application: stackalloc<byte> 256
  Application(                         // TypeApp: stackalloc<byte>
    Intrinsic("NativePtr.stackalloc"), // Base intrinsic
    []                                 // No value args (type args only)
  ),
  [256]                                // Value argument
)
```

This structure was problematic because:
1. The zipper couldn't directly recognize the intrinsic
2. Code generation had to "look through" the intermediate Application
3. The structure implied a value-level call when only type instantiation occurred

## The Correct Structure

After the fix:

```
Application(                           // Value application: stackalloc<byte> 256
  Intrinsic("NativePtr.stackalloc"),   // Intrinsic with instantiated type
  [256]                                // Value argument
)
```

The Intrinsic node has type `int -> nativeptr<byte>` (the instantiated type), not `TForall(['T], int -> nativeptr<'T>)`.

## The Principle

### Type-Level vs Value-Level Operations

| Operation | Level | PSG Representation |
|-----------|-------|-------------------|
| `f<T>` (type instantiation) | Type | Preserves inner Kind with instantiated type |
| `f x` (function call) | Value | Creates Application node |
| `f<T> x` (both) | Both | Instantiated inner Kind, then Application |

### Why This Belongs in Construction, Not a Nanopass

A nanopass would clean up a structural mistake. But the principle of FNCS is **"types attached during construction, not post-hoc."** The right structure should be created from the start.

**Arguments against a cleanup nanopass:**
- Nanopasses transform well-formed input; this would be fixing malformed input
- The type information is available during construction
- Creating wrong structure then fixing it wastes work
- It violates the "correct by construction" principle

**Arguments for inline construction logic:**
- Single point of truth: each SynExpr case produces the right structure once
- Type information (`funcNode.Kind`, `resultType`) is immediately available
- No downstream cleanup needed
- The zipper receives a clean graph

## The Implementation

In `CheckExpressions.fs`, the TypeApp handler:

```fsharp
| SynExpr.TypeApp(funcExpr, _, typeArgs, _, _, _, _) ->
    let funcNode = checkExpr env builder funcExpr
    let typeArgTypes = typeArgs |> List.map (... greenfield type resolution ...)
    let resultType = ... // Instantiate TForall with type args
    
    // ARCHITECTURAL PRINCIPLE: Preserve Kind for transparent nodes
    match funcNode.Kind with
    | SemanticKind.Intrinsic name ->
        // TypeApp of Intrinsic → Intrinsic with instantiated type
        builder.Create(SemanticKind.Intrinsic name, resultType, range)
    | _ ->
        // Other expressions → Application node
        builder.Create(SemanticKind.Application(funcNode.Id, []), resultType, range, ...)
```

## Generalization: The Dispatch Table

The pattern is: "What structure does TypeApp produce for various inner expression Kinds?"

| Inner Kind | TypeApp Result | Rationale |
|------------|----------------|-----------|
| `Intrinsic name` | `Intrinsic name` with instantiated type | Intrinsics are compiler-recognized; preserve recognition |
| `VarRef` | Could preserve with instantiated type | Variable still references same definition |
| `Lambda` | Could preserve with instantiated type params | Lambda body unchanged |
| Other | `Application(inner, [])` | Default: explicit type instantiation node |

This table should be extended as cases arise, but the principle is consistent: **transparent nodes preserve their Kind**.

## Related Principles

1. **FNCS constructs types during graph construction** - No post-hoc type overlay
2. **Soft-delete for reachability** - Preserve structure for debugging
3. **Zipper receives clean graph** - No special-case traversal logic needed
4. **Application = value-level** - Don't use Application for type-level operations

## Case Study Value

This decision illustrates the difference between:
- **Cleanup nanopass**: Fix mistakes after they're made (wrong)
- **Correct construction**: Build the right structure from the start (right)

When facing a similar choice, ask: "Am I cleaning up a mess, or deciding what to build?" If the former, the fix belongs earlier in the pipeline.

## References

- `CheckExpressions.fs`: TypeApp handler (~line 1183)
- Memory: `fncs_architecture` - FNCS design principles
- Memory: `architecture_principles` - Layer separation, construction vs transformation

# Baker Ingredients Discipline

> **Created**: January 2026
> **Context**: Architectural corruption discovered during Match saturation implementation

## The Cardinal Rule

**Recipes ONLY call Ingredients. NEVER Primitives directly.**

Even a single primitive must be wrapped as an Ingredient. This seems "silly" but is the **firewall** that maintains architectural integrity.

## Three-Layer Model (Strict)

```
Layer 3: RECIPES      → 5-15 lines, ONLY call Ingredients
Layer 2: INGREDIENTS  → Exposed API, wrap primitives (even single ones)
Layer 1: PRIMITIVES   → Internal/private, atomic node builders
```

### Access Control

```fsharp
// Primitives.fs - INTERNAL to Baker.Ingredients
module internal Primitives =
    let extractPayloadField ... = ...  // Raw builder
    let letBind ... = ...              // Raw builder

// Ingredients.fs - PUBLIC API for Recipes
module Ingredients =
    let extractPayload scrutinee ty = 
        Primitives.extractPayloadField scrutinee 0 ty
    
    let bindValue name value ty =
        Primitives.letBind name value ty
    
    // Composite: common combination
    let extractAndBind scrutinee name ty =
        recipe {
            let! payload = extractPayload scrutinee ty
            return! bindValue name payload ty
        }
```

## Why Single-Primitive Wrappers Matter

1. **Habit enforcement** - The moment you allow "just this one primitive," you're on the path to 100-line imperative code
2. **Semantic naming** - `extractPayload` captures INTENT; primitive call is implementation detail
3. **Future-proof** - Wrapper can later add shadow AST, validation, logging without touching Recipes
4. **Composability** - Ingredients compose; primitives don't (they're too low-level)

## The Anti-Pattern (What NOT To Do)

```fsharp
// WRONG: Recipe calling primitives directly
let matchRecipe scrutinee cases =
    recipe {
        // 100 lines of primitive calls...
        let! tagMatches = compareTagEq scrutineeId tagIndex
        let! payloadId = extractPayloadField scrutineeId 0 ty
        let! bindingId = letBind name payloadId ty
        // ... more primitive soup ...
    }
```

This is **imperative functional code** - it has functional syntax but imperative structure. It's the exact corruption we must prevent.

## The Correct Pattern

```fsharp
// Ingredients (composite)
let guardedUnionCase scrutinee tagIndex payload guard body =
    recipe {
        let! tagCheck = checkTag scrutinee tagIndex
        let! binding = extractAndBind scrutinee payload.Name payload.Type
        let! guardedBody = applyGuard guard (wrapBody binding body)
        return (tagCheck, guardedBody)
    }

let caseChain cases elseCase =
    recipe {
        return! List.foldBack chainCase cases elseCase
    }

// Recipe - TRIVIAL composition
let matchRecipe scrutinee cases =
    caseChain 
        (cases |> List.map (fun c -> guardedUnionCase scrutinee c.Tag c.Payload c.Guard c.Body))
        unitValue
```

~5 lines. The Recipe is a one-liner calling Ingredients.

## Composite Ingredients

When you see a pattern of primitives appearing together, create a composite Ingredient:

| Pattern | Composite Ingredient |
|---------|---------------------|
| `extractPayloadField` + `letBind` | `extractAndBind` |
| `compareTagEq` + `ifThenElse` | `guardedCase` |
| `boolLit true` + guard application | `applyOptionalGuard` |
| Multiple `ifThenElse` chain | `caseChain` |

## XParsec Integration

Ingredients should leverage XParsec combinator nature:

```fsharp
// Ingredient as parser combinator
let pUnionCase = 
    pTag .>>. pPayload .>>. pGuard .>>. pBody
    |>> fun (tag, payload, guard, body) -> guardedUnionCase tag payload guard body
```

This makes it **impossible not to use** the proper structure - the types enforce it.

## Recipe Checkpoint (Enforced)

Before ANY Recipe commit:

| Check | Requirement |
|-------|-------------|
| Line count | < 15 lines |
| Calls only | Ingredients (never Primitives) |
| Structure | Trivial composition, no complex control flow |
| Naming | Recipe name = operation, Ingredient calls = steps |

## Litmus Test

> "If I'm writing a `match` statement or `if/else` chain in a Recipe, I'm doing it wrong."

Recipes should be linear compositions of Ingredients. All branching logic belongs in Ingredients.

## Identified Ingredient Patterns (January 2026 Audit)

Based on analysis of existing Recipes, these are the **meaningful repeating patterns**:

### Control Flow Ingredients

| Ingredient | Purpose | Wraps |
|------------|---------|-------|
| `withOptionalGuard test guard` | Combine test with optional guard | `andAlso` or identity |
| `selectByComparison cmp a b ty` | if cmp then a else b | `ifThenElse` |
| `wrapInSequence elements ty` | Create Sequential node | `createWithChildren` |

### List Ingredients

| Ingredient | Purpose | Wraps |
|------------|---------|-------|
| `decomposeList xs elemTy` | Get (head, tail, isEmpty) | `head`, `tail`, `isEmpty` |
| `mapAndPrepend f head acc elemTy` | Apply f, prepend result | `app1`, `cons` |
| `testPredicate pred elem` | Apply predicate to bool | `app1` with boolType |

### Pattern Match Ingredients

| Ingredient | Purpose | Wraps |
|------------|---------|-------|
| `checkTag scrutinee tagIndex` | Compare union tag | `compareTagEq` |
| `extractAndBindPayload scrutinee name ty` | Extract payload + let bind | `extractPayloadField`, `letBind` |
| `matchesLiteral scrutinee literal` | Create literal + compare | `createAndEmit`, `compareEq` |
| `alwaysMatch` | Return true guard | `boolLit true` |

### Application Ingredients

| Ingredient | Purpose | Wraps |
|------------|---------|-------|
| `applyMapper f x outTy` | Apply mapping function | `app1` |
| `applyFolder f acc x outTy` | Apply folder function | `app2` |
| `applyPredicate p x` | Apply predicate | `app1` with boolType |

## Migration Strategy

1. **Create Ingredients.fs** with all patterns above
2. **Make Primitives internal** - only Ingredients exposed
3. **Rewrite Recipes** - each should be ~5-15 lines calling Ingredients
4. **Delete hand-jammed code** - no primitive calls in Recipes

## Parent Edge Establishment (CRITICAL)

**Baker-created nodes MUST have Parent edges established for Zipper traversal.**

### Design Decision: DEFER to Fold-In

**Recipes create STRUCTURE. Fold-in handles INTEGRATION.**

Parent edge linkage is DEFERRED to fold-in, NOT front-loaded in recipes. This is intentional:

1. **Separation of concerns**: Recipes are pure "structure templates" - they define WHAT to build
2. **Centralized integration**: Fold-in handles HOW to integrate into the graph
3. **Bottom-up construction**: Recipes often create children before parents (can't thread parent ID)
4. **Alignment**: Fold-in already handles ID reconciliation and reference updates

### The Current Gap

- `mkNode` creates nodes with `Parent = None`
- Recipes build structure with correct Children but no Parent edges
- Fold-in updates references but doesn't establish Parent edges
- **Result: New nodes are orphaned, Zipper cannot traverse them**

### The Fix (in Fold-In)

`foldInDecompositions` should:

```fsharp
let foldInDecompositions graph decompositions =
    // 1. Add all new nodes to graph (existing)
    let graphWithNewNodes = addAllNodes graph decompositions
    
    // 2. NEW: Establish internal Parent edges from Children relationships
    let graphWithParents = establishParentEdges graphWithNewNodes
    
    // 3. NEW: Set replacement root's Parent = original node's Parent
    let graphWithRootLinked = linkReplacementRoots graph decompositions
    
    // 4. Update external references (existing)
    let finalGraph = updateReferences graphWithRootLinked decompositions
    
    finalGraph
```

**Internal linkage** (step 2): For each node, update its children to have `Parent = Some nodeId`

**External linkage** (step 3): Replacement root gets `Parent = original.Parent`

### Implementation Location

All linkage logic belongs in `HOFDecomposition.fs` in `foldInDecompositions`.

Recipes and Ingredients should NOT concern themselves with Parent edges.

## XParsec Template Pattern (Pseudo-AST)

**Ingredients return `Expanded<'a>`, not raw `NodeId`.**

The key insight: Ingredients are **templates** that produce BOTH the PSG structure AND the semantic shadow in one operation.

```fsharp
type Expanded<'a> = {
    Value: 'a              // The PSG node(s)
    Shadow: ShadowExpr     // Semantic description
    Provenance: Provenance // Link to inspiring source
}

// Ingredient as template - produces PSG AND shadow
let extractAndBindPayload scrutinee name ty : Recipe<Expanded<NodeId>> =
    recipe {
        let! payloadId = extractPayloadField scrutinee 0 ty
        let! bindingId = letBind name payloadId ty
        let shadow = ShadowLet(name, ShadowFieldGet(scrutinee, "payload"))
        return expanded bindingId shadow
    }
```

**Combinator composition preserves shadows:**
```fsharp
let guardedUnionCase scrutinee tag payload guard body =
    recipe {
        let! tagCheck = checkTag scrutinee tag           // Expanded<NodeId>
        let! binding = extractAndBindPayload scrutinee payload.Name payload.Type
        let! result = withOptionalGuard tagCheck.Value guard
        // Shadows compose automatically
        return composeShadows [tagCheck; binding; result]
    }
```

This is the **key integration point** with XParsec:
- The Ingredient IS the template
- The template produces both structure AND documentation
- Recipes compose templates without knowing about shadows
- The shadow accumulates automatically through composition
- **You literally cannot NOT use it** - the types enforce the pattern

## See Also

- `baker_saturation_architecture` - Overall Baker architecture
- `baker_shadow_ast_architecture` - Shadow AST integration (Expanded<'a> type)
- `compose_from_standing_art_principle` - Why composition matters

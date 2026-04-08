# Baker Saturation Architecture

## Document Purpose

This document provides a comprehensive architectural specification for Baker, the HOF (Higher-Order Function) decomposition component of CCS. It captures the design rationale, the three-layer combinator model, the parallel saturation vision, and implementation guidance.

**Companion Memory:** `baker_saturation_architecture` (terse reference)

---

## 1. The Problem: Why Baker Exists

### 1.1 The Gap Between F# and Native

F# developers write elegant functional code using higher-order collection operations:

```fsharp
let result = 
    myList 
    |> List.filter isValid
    |> List.map transform
    |> List.fold combine initial
```

In .NET, the CLR provides these implementations. In Fidelity's native compilation path, **there is no runtime**. The compiler must "bake in" the algorithms directly.

### 1.2 The Two-Tier Model

Collection operations fall into two categories:

**Primitives** (Alex witnesses directly to MLIR):
- `List.empty` → null pointer
- `List.isEmpty` → null check
- `List.head` → GEP + load
- `List.tail` → GEP + load  
- `List.cons` → arena alloc + stores

**HOFs** (Baker decomposes to PSG):
- `List.map` → recursive pattern using primitives
- `List.filter` → recursive pattern with conditional cons
- `List.fold` → recursive pattern with accumulator
- etc.

**The Principle:** Alex knows how to witness primitives. Baker's job is to decompose HOFs into structures that only use primitives.

### 1.3 The Original Problem: Verbose Boilerplate

The naive approach to decomposition produces ~100 lines of manual PSG node construction per operation:

```fsharp
// ANTI-PATTERN: Manual node-by-node construction
let decomposeListMap ctx mapper list elemType =
    let xsParamNode = mkExpandedNode ctx (SemanticKind.PatternBinding "xs") listType
    let emptyNode = mkEmptyCollectionNode ctx IntrinsicModule.List outputListType
    let isEmptyFuncType = NativeType.TFun (inputListType, Types.boolType)
    let isEmptyIntrinsicNode = mkIntrinsicNode ctx IntrinsicModule.List "isEmpty" isEmptyFuncType
    // ... 90 more lines of nearly identical boilerplate
```

Every operation repeats the same patterns:
- isEmpty guard
- head/tail extraction  
- let rec binding
- recursive call structure

This is unmaintainable, error-prone, and obscures the actual algorithm.

---

## 2. The Three-Layer Combinator Model

### 2.1 Architecture Overview

The Baker metaphor extends throughout:
- **Ingredients/** - The raw components (primitives, patterns)
- **Recipes/** - How to combine ingredients for each dish (operation)
- **Baker (orchestration)** - The chef who executes recipes

```
┌─────────────────────────────────────────────────────────────────┐
│  Layer 3: RECIPES (Baker/Recipes/*.fs)                          │
│  "The finished dishes"                                          │
│                                                                 │
│  let listMapRecipe = foldRight (empty out) (λh r → cons (f h) r)│
│  let listFilterRecipe = foldRight (empty) (λh r → guardCons p h)│
│  let listFoldRecipe = foldLeft state (λacc h → app2 f acc h)    │
│  let listRevRecipe = foldLeft (empty) (λacc h → cons h acc)     │
└─────────────────────────────────────────────────────────────────┘
                              ↓ uses
┌─────────────────────────────────────────────────────────────────┐
│  Layer 2: PATTERNS (Baker/Ingredients/Patterns.fs)              │
│  "Cooking techniques"                                           │
│                                                                 │
│  foldRight : baseCase → combine → list → Recipe                 │
│  foldLeft  : baseCase → combine → list → Recipe                 │
│  foldLeft2 : baseCase → combine → list1 → list2 → Recipe        │
│                                                                 │
│  (Generates: isEmpty guard, head/tail, let rec, initial call)   │
└─────────────────────────────────────────────────────────────────┘
                              ↓ uses
┌─────────────────────────────────────────────────────────────────┐
│  Layer 1: PRIMITIVES (Baker/Ingredients/Primitives.fs)          │
│  "Raw ingredients"                                              │
│                                                                 │
│  empty, isEmpty, head, tail, cons        (List)                 │
│  isSome, isNone, get, some, none         (Option)               │
│  app, app2, ifThenElse, letRec, lambda   (Structure)            │
│  guardCons = λcond h t → if cond then cons h t else t           │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 Layer 1: Primitives

Primitives are singleton PSG node builders. Each returns the nodes created and the root node ID:

```fsharp
/// Create an empty list node
let emptyList (elemType: NativeType) : RecipeBuilder<NodeId>

/// Create an isEmpty check
let isEmpty (listNode: NodeId) : RecipeBuilder<NodeId>

/// Create a head extraction
let head (listNode: NodeId) (elemType: NativeType) : RecipeBuilder<NodeId>

/// Create a tail extraction  
let tail (listNode: NodeId) (elemType: NativeType) : RecipeBuilder<NodeId>

/// Create a cons cell
let cons (headNode: NodeId) (tailNode: NodeId) : RecipeBuilder<NodeId>

/// Create a function application
let app (funcNode: NodeId) (argNode: NodeId) : RecipeBuilder<NodeId>

/// Create an if-then-else
let ifThenElse (guard: NodeId) (thenBr: NodeId) (elseBr: NodeId) : RecipeBuilder<NodeId>
```

### 2.3 Layer 2: Patterns

Patterns generate the full recursive structure. They encode the boilerplate that was being repeated:

```fsharp
/// Generate a right-fold recursive structure
/// 
/// Produces:
///   let rec loop xs =
///     if isEmpty xs then baseCase
///     else combine (head xs) (loop (tail xs))
///   in loop inputList
let foldRight 
    (baseCase: RecipeBuilder<NodeId>)
    (combine: NodeId -> NodeId -> RecipeBuilder<NodeId>)
    (listArg: NodeId)
    (elemType: NativeType)
    : RecipeBuilder<NodeId>

/// Generate a left-fold recursive structure (with accumulator)
///
/// Produces:
///   let rec loop acc xs =
///     if isEmpty xs then acc
///     else loop (combine acc (head xs)) (tail xs)
///   in loop initialAcc inputList
let foldLeft
    (initialAcc: RecipeBuilder<NodeId>)
    (combine: NodeId -> NodeId -> RecipeBuilder<NodeId>)
    (listArg: NodeId)
    (elemType: NativeType)
    (accType: NativeType)
    : RecipeBuilder<NodeId>
```

### 2.4 Layer 3: Recipes

Recipes become trivial compositions—the WHAT without the HOW:

```fsharp
/// List.map: apply f to each element
let listMapRecipe ctx mapper list inType outType =
    foldRight
        (emptyList outType)
        (fun head recurse -> cons (app mapper head) recurse)
        list inType

/// List.filter: keep elements where predicate is true
let listFilterRecipe ctx predicate list elemType =
    foldRight
        (emptyList elemType)
        (fun head recurse -> guardCons (app predicate head) head recurse)
        list elemType

/// List.fold: left fold with accumulator
let listFoldRecipe ctx folder state list elemType stateType =
    foldLeft
        (pure state)  // Initial accumulator is the state argument
        (fun acc head -> app2 folder acc head)
        list elemType stateType

/// List.rev: reverse via left fold
let listRevRecipe ctx list elemType =
    foldLeft
        (emptyList elemType)
        (fun acc head -> cons head acc)
        list elemType elemType

/// List.exists: short-circuit or
let listExistsRecipe ctx predicate list elemType =
    foldRight
        (boolLiteral false)
        (fun head recurse -> orShortCircuit (app predicate head) recurse)
        list elemType

/// List.forall: short-circuit and
let listForallRecipe ctx predicate list elemType =
    foldRight
        (boolLiteral true)
        (fun head recurse -> andShortCircuit (app predicate head) recurse)
        list elemType
```

**Each recipe is 5-10 lines instead of 100+.**

---

## 3. The Two-Level Fold Duality

A key architectural insight is that "fold" appears at two levels:

### 3.1 Combinator Level: Building Sub-Trees

`foldRight` and `foldLeft` are the patterns that BUILD PSG sub-trees. They capture the recursive structure of list processing.

### 3.2 Orchestration Level: Merging Results

The saturation pass itself is a fold over decomposition sites:

```fsharp
let saturate (graph: SemanticGraph) : SemanticGraph =
    let sites = discover graph
    sites |> List.fold (fun g site -> applyRecipe site g) graph
```

This duality—fold to build, fold to merge—is not coincidental. It reflects the compositional nature of the problem.

---

## 4. Parallel Saturation Model

### 4.1 The Vision

For large codebases, saturation can be parallelized by category:

```
                    Discovery Nanopass
                           │
                           │ Categorize by collection type
                           │
         ┌─────────────────┼─────────────────┐
         │                 │                 │
         ↓                 ↓                 ↓
   ┌──────────┐     ┌──────────┐     ┌──────────┐
   │   List   │     │   Map    │     │  Option  │
   │ Saturator│     │ Saturator│     │ Saturator│
   │  Worker  │     │  Worker  │     │  Worker  │
   └────┬─────┘     └────┬─────┘     └────┬─────┘
        │                │                │
        │  SubTrees      │  SubTrees      │  SubTrees
        │                │                │
        └────────────────┼────────────────┘
                         │
                         ↓
              MailboxProcessor / Fold
                         │
                         ↓
                  Saturated PSG
```

### 4.2 Why Parallelization Works

1. **Disjoint Sites**: Each HOF application is a unique node. Workers don't compete for the same sites.

2. **Additive Results**: Workers produce NEW nodes. No mutation of existing structure.

3. **Commutative Merge**: The order of applying results doesn't matter (up to node ID assignment).

### 4.3 Implementation Sketch

```fsharp
/// Parallel saturation with fold-in
let saturateParallel (graph: SemanticGraph) : SemanticGraph =
    // Discovery phase (sequential)
    let sites = discover graph
    
    // Categorize by collection type
    let categorized = 
        sites 
        |> List.groupBy (fun site -> site.Intrinsic.Module)
        |> Map.ofList
    
    // Fan out: parallel workers per category
    let results =
        categorized
        |> Map.toArray
        |> Array.Parallel.map (fun (category, sites) ->
            let worker = getWorker category
            sites |> List.map (worker.Saturate graph))
        |> Array.collect id
    
    // Fold in: merge all results
    results |> Array.fold mergeResult graph
```

### 4.4 MailboxProcessor for Streaming

For even larger graphs, a MailboxProcessor can stream results:

```fsharp
let saturateStreaming (graph: SemanticGraph) : Async<SemanticGraph> =
    async {
        let agent = MailboxProcessor.Start(fun inbox ->
            let rec loop currentGraph = async {
                let! msg = inbox.Receive()
                match msg with
                | SaturationResult result ->
                    let newGraph = mergeResult result currentGraph
                    return! loop newGraph
                | Complete reply ->
                    reply.Reply(currentGraph)
                    return ()
            }
            loop graph)
        
        // Spawn workers that post results to agent
        let! _ = 
            categories
            |> List.map (fun cat -> async {
                let results = saturateCategory cat graph
                for r in results do
                    agent.Post(SaturationResult r)
            })
            |> Async.Parallel
        
        // Signal completion and get final graph
        return! agent.PostAndAsyncReply(Complete)
    }
```

---

## 5. Zipper-Based Discovery

### 5.1 Why Zipper for Discovery?

The PSGZipper (already used in Alex) provides:

1. **Positional Context**: Parent, siblings, depth in tree
2. **Bidirectional Navigation**: Up, down, left, right
3. **Future Fusion Detection**: See adjacent operations

### 5.2 Discovery with Context

```fsharp
type DecompositionSite = {
    NodeId: NodeId
    Intrinsic: IntrinsicInfo
    Args: NodeId list
    ResultType: NativeType
    /// Parent context for fusion opportunities
    ParentContext: PathStep option
    /// Sibling HOFs (for detecting map |> filter chains)
    AdjacentHOFs: NodeId list
}

/// Discover all HOF sites using zipper traversal
let discover (graph: SemanticGraph) : DecompositionSite list =
    let rec visit (z: PSGZipper) (acc: DecompositionSite list) =
        let site = tryClassifyAsSite z
        let acc' = match site with Some s -> s :: acc | None -> acc
        
        // Visit children
        let acc'' = visitChildren z acc'
        
        acc''
    
    match PSGZipper.fromEntryPoint graph with
    | Some z -> visit z []
    | None -> []
```

### 5.3 Future: Fusion Detection

With parent/sibling context, we can detect fusion opportunities:

```fsharp
// Detect: list |> List.map f |> List.filter p
// Fuse to: list |> List.filterMap (fun x -> let y = f x in if p y then Some y else None)

let detectMapFilterFusion (site: DecompositionSite) (graph: SemanticGraph) =
    match site.ParentContext with
    | Some parent when isFilterApplication parent.Parent ->
        Some (FusionOpportunity.MapFilter (site, parent.Parent.Id))
    | _ -> None
```

---

## 6. Lessons from Firefly's Alex Architecture

Baker is NOT a copy of Alex, but several architectural patterns transfer beautifully.

### 6.1 The Three Concerns (Alex)

Alex separates three concerns cleanly:

```
┌─────────────────────────────────────────────────────────────────┐
│  PSGZipper        │ Pure navigation (Focus, Path, Graph)        │
│                   │ NO state, NO coeffects, NO accumulation     │
├───────────────────┼─────────────────────────────────────────────┤
│  TransferCoeffs   │ Pre-computed, IMMUTABLE                     │
│                   │ SSA assignment, platform info, mutability   │
│                   │ Computed ONCE before traversal              │
├───────────────────┼─────────────────────────────────────────────┤
│  MLIRAccumulator  │ Mutable fold state                          │
│                   │ Collects emitted ops, tracks visited nodes  │
│                   │ The "acc" in the fold                       │
└───────────────────┴─────────────────────────────────────────────┘
```

**Lesson:** Separate navigation, pre-computed data, and accumulation. Don't mix them.

### 6.2 The Codata Pattern (Alex)

Alex witnesses RETURN codata; the fold ACCUMULATES:

```fsharp
// Alex pattern: witnesses return, fold accumulates
let rec visitNode ctx z nodeId =
    let output = classifyAndWitness ctx z node  // Witness RETURNS WitnessOutput
    MLIRAccumulator.addTopLevelOps output.TopLevelOps acc  // Fold ACCUMULATES
    { output with TopLevelOps = [] }  // Clear after accumulating
```

**Lesson:** Don't push into accumulator from deep in the call stack. Return codata up, accumulate at one point.

### 6.3 The Coeffect Pattern (Alex)

Coeffects are computed ONCE, then read-only:

```fsharp
let computeCoeffects graph isFreestanding =
    {
        SSA = SSAAssign.assignSSA arch graph        // Pre-assign all SSA names
        Platform = PlatformRes.analyze graph ...    // Resolve all platform bindings
        Mutability = MutAnalysis.analyze graph      // Analyze all mutability
        // ... computed ONCE, never modified
    }
```

**Lesson:** Front-load analysis. Don't compute coeffects during traversal.

### 6.4 What Transfers to Baker

| Alex Pattern | Baker Equivalent | Notes |
|--------------|------------------|-------|
| PSGZipper | Same PSGZipper | Reuse directly for discovery |
| TransferCoeffects | DiscoveryCoeffects | Lighter - just reachability, types |
| MLIRAccumulator | RecipeAccumulator | Collects new nodes, tracks expansions |
| Witnesses return codata | Recipes return sub-trees | Same pattern, different codata |
| Fold accumulates | Fold merges sub-trees | Same pattern |

### 6.5 What Does NOT Transfer

| Alex Aspect | Baker Difference | Reason |
|-------------|------------------|--------|
| MLIR emission | PSG construction | Different output domain |
| SSA assignment | Not needed | PSG uses NodeIds, not SSA |
| Complex coeffects | Simpler coeffects | Less pre-computation needed |
| Single traversal | Discover then apply | Two-phase is cleaner for Baker |

### 6.6 The Fold Everywhere Insight

Alex's architecture revealed: **folds are the universal pattern**.

```fsharp
// Alex: fold over PSG nodes → MLIR ops
let transfer graph = 
    graph.Nodes |> fold visitNode emptyMLIR

// Baker: fold over decomposition sites → enriched PSG  
let saturate graph =
    sites |> fold applyRecipe graph

// Recipes: fold over list elements → sub-tree
let foldRight base combine list =
    // Generates: fold (fun acc h -> combine h acc) base list
```

**Lesson:** When in doubt, express it as a fold. The algebra composes.

### 6.7 Code Reference: Alex's Canonical Pattern

From `Alex/Traversal/MLIRTransfer.fs`:

```fsharp
/// ARCHITECTURAL PRINCIPLE: This is the FOLD. It:
/// 1. Navigates via zipper (Huet-style, purely positional)
/// 2. Classifies via SemanticKind match (semantic lens)
/// 3. Calls witnesses which RETURN WitnessOutput (codata)
/// 4. ACCUMULATES the returned codata (single point of accumulation)
///
/// The fold is the only place that adds to TopLevelOps.
/// Witnesses return; the fold accumulates.
let rec private visitNode ctx z nodeId : WitnessOutput =
    // ...
```

This comment IS the architecture. Baker should have an equivalent canonical comment.

---

## 7. Directory Structure

```
Baker/
├── Ingredients/
│   ├── Primitives.fs      # Layer 1: Singleton PSG builders
│   │   - emptyList, emptyMap, emptySet
│   │   - isEmpty, head, tail, cons
│   │   - isSome, isNone, some, none
│   │   - app, app2, ifThenElse, letRec, lambda
│   │
│   ├── Patterns.fs        # Layer 2: Recursive structure generators
│   │   - foldRight, foldLeft, foldLeft2
│   │   - guardCons, orShortCircuit, andShortCircuit
│   │
│   └── RecipeBuilder.fs   # Monadic builder for clean composition
│       - RecipeBuilder<'a> type
│       - bind, return, map operations
│
├── Traversal/
│   └── Discovery.fs       # Zipper-based site discovery
│       - DecompositionSite type
│       - discover function
│       - fusion detection (future)
│
├── Recipes/
│   ├── ListRecipes.fs     # Layer 3: List operation recipes
│   ├── MapRecipes.fs      # Layer 3: Map operation recipes
│   ├── SetRecipes.fs      # Layer 3: Set operation recipes
│   └── OptionRecipes.fs   # Layer 3: Option operation recipes
│
├── HOFDecomposition.fs    # Orchestration: discover → apply → merge
│
└── ShadowAST.fs           # Shadow tree for tooling transparency
```

---

## 8. Implementation Roadmap

### Phase 1: Combinator Foundation
1. Create `Baker/Ingredients/RecipeBuilder.fs` - monadic builder type
2. Create `Baker/Ingredients/Primitives.fs` - singleton builders
3. Create `Baker/Ingredients/Patterns.fs` - foldRight, foldLeft

### Phase 2: Recipe Migration
1. Rewrite `ListRecipes.fs` using combinators (5-10 lines per op)
2. Verify builds and test with existing samples
3. Migrate Map, Set, Option recipes

### Phase 3: Discovery Enhancement
1. Create `Baker/Traversal/Discovery.fs` with zipper
2. Add parent context capture
3. Document fusion opportunities for future

### Phase 4: Parallel Infrastructure (Future)
1. Add category-based worker spawning
2. Implement fold-in merge
3. Optional: MailboxProcessor streaming

---

## 9. Design Decisions

### 8.1 Why Not Just Use F# Computation Expressions?

We could express recipes as computation expressions, but:
- The domain is small and well-defined
- Explicit combinators are more transparent
- Debugging is easier with simple functions

### 8.2 Why Zipper for Discovery (Not Just Filter)?

The current implementation uses `Map.values |> filter`. Zipper adds:
- Parent context (needed for fusion)
- Consistent pattern with Alex
- Future bidirectional queries

The one-time cost of zipper is minimal; the runway is substantial.

### 8.3 Enforcement: Type-Level Protection

The strongest defense against "pollution" from verbose patterns is making them **impossible to express**.

#### The Opaque Recipe Type

```fsharp
// Baker/Ingredients/RecipeBuilder.fs
module Baker.Ingredients.RecipeBuilder

// Recipe is OPAQUE - code outside Ingredients/ can't see inside
type Recipe = private Recipe of (Context -> SemanticNode list * NodeId)

// Only these combinators are exposed
val emptyList : NativeType -> Recipe
val cons : Recipe -> Recipe -> Recipe
val app : NodeId -> Recipe -> Recipe
val foldRight : Recipe -> (Recipe -> Recipe -> Recipe) -> NodeId -> NativeType -> Recipe
```

#### Access Control

| Function | Visibility | Why |
|----------|------------|-----|
| `mkExpandedNode` | `internal` to Ingredients/ | Recipes can't call directly |
| `mkApplicationNode` | `internal` to Ingredients/ | Recipes can't call directly |
| `emptyList`, `cons`, etc. | `public` | Recipes use these |
| `foldRight`, `foldLeft` | `public` | Recipes use these |

**Result:** Recipe files literally cannot write verbose boilerplate. The type system prevents it.

#### Migration Discipline

1. **Create Ingredients/ with opaque types FIRST** - Establish the barrier
2. **DELETE old verbose code** - Not comment out, DELETE. No "reference" to copy from.
3. **One recipe at a time** - Migrate, verify, commit
4. **No exceptions** - If a recipe needs > 15 lines, the combinator layer is missing something

#### Recipe Checkpoint (before any commit)

```
□ Line count < 15?
□ Only calls combinators from Ingredients/?
□ No direct PSG node construction?
□ No imports from Decomposition.fs node helpers?
```

#### If Tempted to Bypass

If you find yourself wanting to:
- Import `mkExpandedNode` into a Recipe file
- Write a "quick" manual node construction
- Copy code from the old verbose implementations

**STOP.** You're missing a primitive or pattern. The correct action is:
1. Identify what's missing
2. Add it to `Ingredients/Primitives.fs` or `Ingredients/Patterns.fs`
3. Use the new combinator in your Recipe

The barrier exists for a reason. Respect it.

### 8.4 Zipper Purity: Non-Negotiable

The PSGZipper MUST remain a **pure Huet zipper**. This is non-negotiable.

#### What Goes IN the Zipper

```fsharp
type PSGZipper = {
    Focus: SemanticNode      // Current position
    Path: ZipperPath         // Breadcrumbs back to root
    Graph: SemanticGraph     // The graph being navigated
}
```

**That's it. Nothing else.**

#### What Stays OUT of the Zipper

- ❌ Coeffects (pre-computed analysis results)
- ❌ Accumulator state (collected nodes, results)
- ❌ Mutable fields of any kind
- ❌ "Convenience" context that "would be nice to have"

#### The Pattern: Witness Context Out

```fsharp
// CORRECT: Context is separate, passed alongside zipper
type DiscoveryContext = {
    Zipper: PSGZipper           // Pure navigation
    Coeffects: DiscoveryCoeffs  // Pre-computed, immutable
    Accumulator: SiteAccum      // Mutable fold state
}

let discover ctx = 
    let z = ctx.Zipper
    let coeffs = ctx.Coeffects  // Witnessed OUT of zipper
    // ... use z for navigation, coeffs for data
```

#### Why This Matters

1. **Composability**: Pure zipper can be reused (Alex uses same zipper)
2. **Testability**: Navigation logic testable without coeffect setup
3. **Clarity**: Each concern has one home
4. **No Creep**: Prevents "just add one more field" degradation

#### The Litmus Test

If you're tempted to add a field to PSGZipper, ask:
- Is it about POSITION in the tree? → Maybe OK
- Is it about DATA at that position? → NO, witness it out
- Is it about ACCUMULATED results? → NO, separate accumulator

**When in doubt, keep it out.**

### 8.5 Shadow AST Integration

Shadow construction can be:
1. **Parallel**: Each combinator builds both PSG and shadow nodes
2. **Derived**: Generate shadow from PSG structure post-hoc

We choose **derived** for simplicity—the PSG IS the truth.

---

## 10. Examples: Before and After

### Before (Verbose Boilerplate)

```fsharp
let decomposeListMap ctx mapperNodeId listNodeId inputElemType outputElemType =
    let inputListType = NativeType.TList inputElemType
    let outputListType = NativeType.TList outputElemType
    let xsParamNode = mkExpandedNode ctx (SemanticKind.PatternBinding "xs") inputListType
    let emptyNode = mkEmptyCollectionNode ctx IntrinsicModule.List outputListType
    let isEmptyFuncType = NativeType.TFun (inputListType, Types.boolType)
    let isEmptyIntrinsicNode = mkIntrinsicNode ctx IntrinsicModule.List "isEmpty" isEmptyFuncType
    let xsRefForIsEmpty = mkVarRefNode ctx "xs" (Some xsParamNode.Id) inputListType
    let isEmptyAppNode = mkApplicationNode ctx isEmptyIntrinsicNode.Id [xsRefForIsEmpty.Id] Types.boolType
    let headFuncType = NativeType.TFun (inputListType, inputElemType)
    let headIntrinsicNode = mkIntrinsicNode ctx IntrinsicModule.List "head" headFuncType
    let xsRefForHead = mkVarRefNode ctx "xs" (Some xsParamNode.Id) inputListType
    let headAppNode = mkApplicationNode ctx headIntrinsicNode.Id [xsRefForHead.Id] inputElemType
    let fAppliedNode = mkApplicationNode ctx mapperNodeId [headAppNode.Id] outputElemType
    // ... 80 more lines ...
```

### After (Combinator Composition)

```fsharp
let listMapRecipe ctx mapper list inType outType =
    foldRight ctx
        (emptyList outType)
        (fun head recurse -> cons (app mapper head) recurse)
        list inType outType
```

**100+ lines → 5 lines. Same semantics. Clearer intent.**

---

## 11. Conclusion

Baker's combinator architecture achieves:

1. **Clarity**: Recipes express WHAT, not HOW
2. **Maintainability**: One change to a pattern fixes all recipes
3. **Extensibility**: New operations are trivial to add
4. **Parallelism**: Fan-out/fold-in model scales
5. **Future-Proofing**: Zipper discovery enables fusion optimization

The two-level fold duality (build sub-trees, merge results) is the conceptual foundation. The three-layer model (primitives → patterns → recipes) is the implementation structure.

**Baker bakes in the algorithms. Combinators make it elegant.**

# Baker Saturation Architecture

## Core Principle
Baker decomposes HOFs (List.map, fold, filter) into PSG sub-trees of primitives (isEmpty, head, tail, cons). Alex witnesses primitives; Baker creates structure.

## Three-Layer Combinator Model (The Baking Metaphor)

```
Layer 3: RECIPES     → "Finished dishes" - listMapRecipe, listFilterRecipe
Layer 2: PATTERNS    → "Cooking techniques" - foldRight, foldLeft (in Ingredients/)
Layer 1: PRIMITIVES  → "Raw ingredients" - empty, isEmpty, head, tail, cons
```

- **Ingredients/** folder contains primitives + patterns
- **Recipes/** folder contains trivial compositions (5-10 lines each)
- **Baker (HOFDecomposition)** is the chef who executes recipes

**Recipes are 5-10 lines, NOT 100+ lines of boilerplate.**

## Two-Level Fold Duality

1. **Combinator Level** (foldRight/foldLeft) - BUILD sub-trees from primitives
2. **Orchestration Level** (fan-out/fold-in) - MERGE sub-trees into PSG

## Parallel Saturation Model

```
Discovery → Categorize → Fan Out (parallel workers) → Fold In → Saturated PSG
```

- Discovery nanopass finds all HOF sites
- Categorize by collection type (List, Map, Set, Option)
- Workers are independent (disjoint sites, additive nodes)
- Fold merges results: `results |> fold applyResult graph`

## Zipper for Discovery

Use PSGZipper (same as Alex) for discovery traversal. Captures parent context for future fusion detection (e.g., map followed by filter → mapFilter fusion).

### Zipper Purity: NON-NEGOTIABLE

The zipper MUST remain a **pure Huet zipper**:
```fsharp
type PSGZipper = { Focus; Path; Graph }  // NOTHING ELSE
```

**What stays OUT:**
- ❌ Coeffects → separate DiscoveryCoeffects
- ❌ Accumulator → separate SiteAccumulator  
- ❌ Mutable fields
- ❌ "Convenience" context

**Pattern:** Witness context OUT of the zipper, pass alongside:
```fsharp
type DiscoveryContext = { Zipper; Coeffects; Accumulator }
```

**Litmus test:** Is it about POSITION? Maybe OK. Is it about DATA or RESULTS? Keep it out.

## Key Files

- `Baker/Ingredients/Primitives.fs` - Singleton PSG builders
- `Baker/Ingredients/Patterns.fs` - foldRight, foldLeft generators
- `Baker/Ingredients/RecipeBuilder.fs` - Monadic composition
- `Baker/Traversal/Discovery.fs` - Zipper-based site discovery
- `Baker/Recipes/*.fs` - Trivial recipe compositions
- `Baker/HOFDecomposition.fs` - Orchestration

## Anti-Pattern: Verbose Boilerplate

WRONG: 100+ lines manually constructing every node for each operation
RIGHT: 5-line recipe composing combinator patterns

## Enforcement Strategy: Type-Level Protection

### The Opaque Recipe Type
```fsharp
// Recipe is OPAQUE - Recipes can't see inside
type Recipe = private Recipe of (Context -> SemanticNode list * NodeId)
```

### Access Control
- `mkExpandedNode`, `mkApplicationNode`, etc. → `internal` to Ingredients/
- Recipes can ONLY call combinators (emptyList, cons, foldRight, etc.)
- **Type system prevents verbose boilerplate** - literally can't express it

### Migration Discipline
1. Create Ingredients/ with opaque types FIRST
2. DELETE old verbose code - don't comment, DELETE
3. No "reference implementations" lying around to pollute

### Recipe Checkpoint (before any commit)
```
Line count < 15?              ✓
Only calls combinators?       ✓  
No direct PSG node creation?  ✓
```

### If Tempted to Bypass
If you find yourself wanting to call `mkExpandedNode` from a Recipe file:
**STOP.** You're missing a primitive or pattern. Add it to Ingredients/ first.

## Four Pillars Integration (from Firefly)

Baker follows the Four Pillars from Firefly's Transfer architecture:

### Pillar A: Coeffects (Mise-en-place)
Baker computes ONCE; Alex witnesses. No "What if?" during transfer - only "What is?"
- All recursive structure computed in Baker (PSG nodes)
- Alex sees pre-computed structure, not computation

### Pillar B: Active Patterns (Semantic Lenses)
Match on MEANING, not strings:
```fsharp
// WRONG: match operation with "map" -> ...
// RIGHT: Use typed Recipe composition
let recipe = foldRight baseCase combine list elemType resultType
```

### Pillar C: Zipper (Universal Cursor)
Discovery phase uses PSGZipper for site identification.
Pure Huet zipper - position only, no accumulated data.

### Pillar D: Templates (Parameterized Output)
Recipes are templates filled with types and combinators.
```fsharp
// Recipe = pattern composition, not string building
foldRight (emptyList outputElem) (fun h r -> cons (f h) r) xs
```

## See Also

- `docs/fidelity/Baker_Saturation_Architecture.md` - Full detailed exposition
- `collection_machinery_architecture` memory - Primitives vs HOFs distinction
- Firefly `four_pillars_of_transfer` - Transfer architecture principles
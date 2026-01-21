# Collection Machinery Architecture

## Core Principle: PSGSaturation Decomposes, Alex Witnesses

The architecture for dynamic collection machinery follows the FNCS decomposition principle:

```
FNCS Primitives (correct types)
         ↓
PSGSaturation (DECOMPOSITION into algorithmic structure)
         ↓
Nanopass Pipeline (optimization, enrichment, purity analysis)
         ↓
PSG Graph (CONTAINS the full machinery)
         ↓
Alex (WITNESSES the graph → MLIR)
```

**Alex doesn't implement Map.add**. Alex sees a graph that already contains:
- Tree traversal logic
- Key comparison
- Node allocation (from arena)
- Rebalancing (AVL/Red-Black)
- Path copying for structural sharing

## Structural Sharing Preserves Referential Transparency

Immutable collections use structural sharing:
```
Map.add "b" 2 m1  →  Creates new path, shares unchanged subtrees
```

This is NOT just a memory optimization - it **preserves referential transparency**:
- Original collection unchanged → pure operation
- Pure operations → future parallelization (INet dialect)
- Pure operations → future vectorization (vector dialect)

## PSGSaturation Decomposition Examples

### Map.add key value map
```fsharp
match map with
| Empty → Node(key, value, Empty, Empty, 1)
| Node(k, v, left, right, h) →
    if key < k then
        let newLeft = Map.add key value left  // recurse
        balance k v newLeft right
    else if key > k then
        let newRight = Map.add key value right
        balance k v left newRight
    else
        Node(key, value, left, right, h)  // replace value
```

### List.map f xs
```fsharp
match xs with
| [] → []
| x :: rest → (f x) :: (List.map f rest)
```

### Range [|1..n|]
```fsharp
let arr = Array.zeroCreate (n - 1 + 1)
let mutable i = 0
let mutable v = 1
while v <= n do
    arr.[i] <- v
    v <- v + 1
    i <- i + 1
arr
```

## Graph Coloring for Parallelization (Future)

From blog "Speed & Safety with Graph Coloring":
- Nodes with same color can execute in parallel
- Pure operations are "flexible" color
- Collection ops are mostly pure → parallelizable

## Connection to DCont/INet Dialects (Future)

When these dialects arrive:
- Pure collection regions → INet dialect (parallel)
- Effectful boundaries → DCont dialect (sequential)
- Hybrid code switches between dialects

## First-Round Implementation (Current)

Use standard MLIR dialects:
- `scf.for`, `scf.while` for loops
- `arith.*` for arithmetic
- `memref.*` for array access
- `llvm.*` for struct manipulation

Structure code so future optimizations are POSSIBLE:
- Don't emit patterns that prevent vectorization
- Keep pure operations identifiable
- Preserve loop structures that can become vector loops

## Key Files

- PSGSaturation: Where decomposition happens
- SemanticGraph/Types.fs: SemanticKind for collections
- Alex/Witnesses/: Collection operation MLIR generation
- Alex/FNCSTransfer.fs: PSG traversal → MLIR emission

## Anti-Patterns

1. **Alex implementing algorithms** - Wrong layer. Decomposition belongs in PSGSaturation.
2. **Relying on LLVM -O3** - Unpredictable. Structure IR for explicit control.
3. **Mutable collection implementations** - Breaks referential transparency, prevents parallelization.
4. **Central dispatch on symbol names** - Use PSG structure, not string matching.

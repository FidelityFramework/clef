# Collection Vectorization Opportunity

## Key Insight

Collection operations are natural SIMD/vector candidates. Rather than relying on LLVM's `-O3` auto-vectorization (unpredictable, "best effort"), we should explicitly emit MLIR `vector` dialect for deterministic platform-specific SIMD.

## Why This Matters

1. **Deterministic vectorization** - We KNOW the code will use SIMD instructions
2. **Platform-specific targeting** - AVX-512 on x86_64, NEON on ARM64, etc.
3. **No optimization lottery** - Structure is in the IR, not discovered by optimizer
4. **Composable with future dialects** - When DCont/INet arrive, vector ops compose

## Collection Operations → Vector Patterns

| F# Operation | Vector Pattern | MLIR Vector Dialect |
|--------------|----------------|---------------------|
| `Array.map (fun x -> x * 2)` | Element-wise multiply | `vector.broadcast` + `arith.muli` |
| `Array.fold (+) 0` | Horizontal reduction | `vector.reduction <add>` |
| `List.sumBy f` | Map + reduce | `vector.contract` or FMA + reduction |
| `[|1..1024|]` | Iota (0,1,2,...) | `vector.step` or loop with vector store |
| `Array.map2 (+)` | Pairwise add | `arith.addi` on vector types |
| `Seq.filter` | Masked operations | `vector.compressstore` |

## Connection to Referential Transparency

Pure collection operations (most of them) are referentially transparent:
- This enables parallelization (future INet dialect)
- This enables vectorization (vector dialect NOW or soon)
- Structural sharing in Map/Set/List preserves purity

The decomposition in PSGSaturation should preserve vectorization opportunities:
- Loop structures that can become vector loops
- Reductions that can become horizontal vector ops
- Element-wise transforms that can become vector arithmetic

## Implementation Approach

### Phase 1 (Current): Standard MLIR Dialects
- Use `scf.for`, `arith.*`, `memref.*`
- Structure code so vectorization is POSSIBLE later
- Don't emit patterns that PREVENT vectorization

### Phase 2 (Future): Vector Dialect
- Add vector dialect emission for hot collection ops
- Platform-specific vector width selection (256-bit AVX2, 512-bit AVX-512, 128-bit NEON)
- Explicit `vector.load`, `vector.store`, `vector.reduction`

### Phase 3 (Future): Integration with DCont/INet
- Vector operations within interaction net nodes
- Vectorized tree traversals for Map/Set
- SIMD-accelerated sequence pipelines

## PRD Integration

All collection-related PRDs should note this opportunity in "Future Directions":
- PRD-13a (Core Collections) - Map/Set/List operations
- PRD-15 (SimpleSeq) - Sequence iteration
- PRD-16 (SeqOperations) - Seq.map, filter, fold

## Anti-Pattern: Relying on LLVM Auto-Vectorization

```
WRONG: Emit scalar loops, hope LLVM -O3 vectorizes them
RIGHT: Structure IR so WE control vectorization, emit vector dialect when ready
```

## References

- Blog: "Speed & Safety with Graph Coloring" - parallelization via graph coloring
- Blog: "Seeking Referential Transparency" - purity enables both parallelism AND vectorization
- MLIR Vector Dialect: https://mlir.llvm.org/docs/Dialects/Vector/

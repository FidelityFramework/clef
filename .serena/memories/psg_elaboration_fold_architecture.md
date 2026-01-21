# Elaboration Fold Architecture (Punch List)

> **Full doc**: `/home/hhh/repos/Firefly/docs/PSG_Elaboration_Fold_Architecture.md`

## Five Artifacts
1. PSG₀ - Original from type checking
2. Intrinsic Recipes - Isolated intrinsic elaboration structures  
3. PSG₁ - Post-intrinsic fold-in
4. Saturation Recipes - Isolated Baker decomposition structures
5. PSG₂ - Final saturated PSG → Alex

## Four Passes
- **Pass 1**: Intrinsic Fan-Out (parallel) → Intrinsic Recipes
- **Pass 2**: Intrinsic Fold-In → PSG₁  
- **Pass 3**: Saturation Fan-Out (parallel) → Saturation Recipes
- **Pass 4**: Saturation Fold-In → PSG₂

## Key Principles
- **Single Live PSG**: Only one version in memory; old GC'd after fold-in
- **Referential Transparency**: Recipes have NO dependencies on each other
- **Fresh Graph**: Fold-in builds new graph; elaborated nodes not included (not marked/patched)
- **Inspectable Intermediates**: Each artifact emitted via `-k` flag

## Infrastructure Location
`fsnative/src/Compiler/Nanopass/` - Recipe.fs, FanOut.fs, FoldIn.fs, Serialization.fs

## Integration Point  
`NativeService.fs` wires the four passes between reachability and Alex delivery
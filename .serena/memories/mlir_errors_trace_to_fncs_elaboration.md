# MLIR Errors: Trace to FNCS Elaboration Root Causes

## Critical Debugging Pattern (January 2026)

**When you see an MLIR error, the root cause is almost always upstream in FNCS elaboration/saturation, NOT in Alex witnesses.**

### The Pattern

1. **Symptom appears in MLIR**: SSA type mismatch, undefined SSA values, wrong types
2. **Instinct (WRONG)**: Fix the witness that generates this MLIR
3. **Reality (CORRECT)**: The PSG is malformed - Baker/Recipe didn't create proper structure

### Case Study: Sample 05 PatternBinding

**MLIR Error:**
```
definition of SSA value '%v64#0' has type '!llvm.struct<(ptr, i64)>'
previously used here with type 'f64'
```

**Wrong diagnosis**: PatternBinding witness isn't generating extractvalue operations

**Correct diagnosis**: 
- PatternBinding nodes in PSG have `children: []` - NO VALUE SOURCE
- MatchRecipes.fs `Pattern.Union` case IGNORES `_payload` parameter
- Recipe never creates FieldGet to extract DU payload
- Recipe never wires extraction to PatternBinding

**The PSG shows the truth:**
```json
{
  "id": 529,
  "kind": "PatternBinding \"x\"",
  "children": [],  // <-- EMPTY! No value source!
  "type": "int"
}
```

A correct Recipe would create:
```
FieldGet(scrutinee, "IntVal_payload") → NodeId 999
PatternBinding("x") with children: [999] → binds extracted value
```

### Diagnostic Questions

When you see an MLIR error:

1. **Is the SSA defined?** If not, check if the PSG node has children
2. **Are PSG children populated?** Empty children = Recipe didn't wire the structure
3. **Is the type wrong?** Check the PSG node's type field vs what Recipe should create
4. **Does the PSG have the expected structure?** Baker creates structure; witnesses just traverse it

### The Rule

> **Alex witnesses TRAVERSE structure. FNCS Baker CREATES structure.**
> 
> If structure is missing, the witness can't traverse it.
> If types are wrong, the Recipe assigned wrong types.
> 
> MLIR errors are usually PSG malformation, not witness bugs.

### Verification Steps

1. Check `05_psg2.json` (saturated PSG) for the problematic nodes
2. Verify `children` arrays are populated
3. Verify `type` fields are correct
4. If structure is wrong → fix in Baker/Recipes (FNCS)
5. If structure is correct but MLIR is wrong → then check witness

### Files to Check

- `/home/hhh/repos/fsnative/src/Compiler/Baker/Recipes/*.fs` - Recipe implementations
- `/home/hhh/repos/fsnative/src/Compiler/Baker/Ingredients/Primitives.fs` - Building blocks
- `target/intermediates/05_psg2.json` - Saturated PSG structure
- `target/intermediates/06_coeffects.json` - SSA assignments

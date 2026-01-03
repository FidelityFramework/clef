# FNCS Phase Debugging Protocol

## Overview

FNCS emits intermediate files at each phase when the `-k` (keep intermediates) flag is used.
These files are essential for tracing issues like missing function inlining or undefined references.

## Phase Files Generated

When compiling with `-k`:

```
target/intermediates/
├── fncs_phase_1_structural.json    # After type checking, before reachability
├── fncs_phase_4_reachability.json  # With IsReachable marks (soft-delete)
├── fncs_phase_5_final.json         # Final result before MLIR generation
├── fncs_expr.json                  # FSharpNativeExpr - expression-centric view (JSON)
├── fncs_expr.txt                   # FSharpNativeExpr - pretty-printed text
├── ProjectName.mlir                # Generated MLIR
├── ProjectName.ll                  # LLVM IR
└── ProjectName.o                   # Object file
```
target/intermediates/
├── fncs_phase_1_structural.json    # After type checking, before reachability
├── fncs_phase_4_reachability.json  # With IsReachable marks (soft-delete)
├── fncs_phase_5_final.json         # Final result before MLIR generation
├── ProjectName.mlir                # Generated MLIR
├── ProjectName.ll                  # LLVM IR
└── ProjectName.o                   # Object file
```

## Phase File Structure

Each phase JSON file contains:

```json
{
  "summary": {
    "phase": 4,
    "phaseName": "Reachability Analysis",
    "nodeCount": 12608,
    "reachableCount": 120,
    "entryPointCount": 1
  },
  "nodes": [
    {
      "id": 11999,
      "kind": "Binding (\"writeStrOut\", ...)",
      "type": "TFun (string -> int)",
      "isReachable": true,
      "children": [11998],
      "parent": null,
      "range": "/path/to/file.fs:45:4",
      "srtpResolution": null
    }
  ],
  "entryPoints": [12604],
  "diagnostics": []
}
```

## Debugging Workflow

### 1. For Linker Errors (undefined reference to 'foo')

```bash
# Compile with intermediates
Firefly compile Project.fidproj -k

# Search for the symbol in phase 4
grep -i "foo" target/intermediates/fncs_phase_4_reachability.json
```

Look for:
- **Binding node** with the function name → confirms definition exists
- **VarRef nodes** pointing to it → shows call sites
- **isReachable: true/false** → is it being pruned?

### 2. Tracing a Function Definition

1. Find the Binding node for the function
2. Check its `children` field - this is the body (usually a Lambda)
3. Trace the Lambda's body through Application nodes

Example trace for `writeStrOut`:
```
Binding (11999) → Lambda (11998) → TypeAnnotation (11997)
                                 → Application (11996)
                                   → Application (11994)
                                     → VarRef to Primitives.writeStr
                                     → VarRef to STDOUT
                                   → VarRef to str
```

### 3. SRTP Resolution Issues

Search for nodes with `srtpResolution != null`:
```bash
grep "srtpResolution.*:.*[^n]" target/intermediates/fncs_phase_4_reachability.json
```

If a TraitCall node has `srtpResolution: null`, the SRTP wasn't resolved.

### 4. Checking Reachability

```bash
# Count unreachable nodes
grep '"isReachable": false' target/intermediates/fncs_phase_4_reachability.json | wc -l

# Find unreachable nodes that should be reachable
grep -B10 '"isReachable": false' target/intermediates/fncs_phase_4_reachability.json | grep "kind.*Binding"
```

## Key Node Kinds

| Kind | Description |
|------|-------------|
| `Binding (name, isMut, isRec, isEntry)` | Let binding / function definition |
| `Lambda (params, bodyId)` | Function body |
| `Application (funcId, argIds)` | Function call |
| `VarRef (name, defId)` | Variable reference - `defId` links to definition |
| `TypeAnnotation (exprId, type)` | Type annotation wrapper |
| `Sequential [ids]` | Sequence of expressions |
| `ModuleDef (name, memberIds)` | Module containing bindings |

## Common Issues

### Issue: Function appears as extern in MLIR

**Symptom**: MLIR has `llvm.func @foo()` without body, linker error "undefined reference"

**Diagnosis**:
1. Find the Binding node in phase 4 - is it there?
2. Check if `isReachable: true` - is it pruned?
3. Check if children contain the body
4. If all OK, the issue is in FNCSTransfer (not following inline body)

### Issue: SRTP not resolved

**Symptom**: Operator like `$` not dispatching correctly

**Diagnosis**:
1. Find the TraitCall or Application node
2. Check `srtpResolution` field - should have witness info
3. If null, check if constraint was solved (phase 2/3)

## Enabling Phase Emission Programmatically

```fsharp
// Before type checking
FNCSPhaseConfig.enableAllPhases "/path/to/intermediates"

// Or selectively
FNCSPhaseConfig.enablePhases "/path/to/intermediates" [1; 4; 5]

// Check config
printfn "%s" (FNCSPhaseConfig.getConfigSummary())
```

## Related Memories

- `fncs_architecture` - FNCS overall architecture
- `compilation_pipeline` - Full Firefly compilation flow
- `native_binding_architecture` - How platform bindings work

# FNCS Architecture (F# Native Compiler Services)

## Overview

FNCS is the native type checker for Firefly. It performs complete type checking from `SynExpr` (parsed syntax) and builds the **SemanticGraph** with types attached during construction (not post-hoc).

**Key Design Principles:**
- BCL-free: No .NET runtime dependencies
- Types attached during construction
- SRTP resolved via native WitnessResolution
- Soft-delete reachability preserves full graph for debugging

## Core Data Structure: SemanticGraph

```fsharp
type SemanticGraph = {
    Nodes: Map<NodeId, SemanticNode>
    EntryPoints: NodeId list
    Modules: Map<ModulePath, NodeId list>
    Types: Map<string, NodeId>
}

type SemanticNode = {
    Id: NodeId
    Kind: SemanticKind
    Type: NativeType
    IsReachable: bool    // Soft-delete marker
    Children: NodeId list
    Parent: NodeId option
    SRTPResolution: WitnessResolution option
    ...
}
```

## Phase Pipeline

FNCS operates as a nanopass compiler with inspectable intermediates:

```
Phase 0: PARSING
  Input:  Source text
  Output: ParsedInput (SynExpr tree)
         ↓
Phase 1: STRUCTURAL CONSTRUCTION
  Input:  SynExpr + TypeEnv
  Output: SemanticGraph with nodes, edges, TYPES ATTACHED
  Emit:   fncs_phase_1_structural.json
         ↓
Phase 2: CONSTRAINT SOLVING
  Input:  SemanticGraph + Constraint list
  Output: SemanticGraph with resolved types
         ↓
Phase 3: SRTP RESOLUTION
  Input:  SemanticGraph with TraitCall nodes
  Output: SemanticGraph with WitnessResolution attached
         ↓
Phase 4: REACHABILITY ANALYSIS
  Input:  SemanticGraph + EntryPoints
  Output: SemanticGraph with IsReachable marks
  Emit:   fncs_phase_4_reachability.json
         ↓
Phase 5: FINAL RESULT
  Input:  SemanticGraph + Diagnostics
  Output: CheckResult
  Emit:   fncs_phase_5_final.json
```

## Key Modules

| Module | Location | Purpose |
|--------|----------|---------|
| NativeService.fs | Checking.Native/ | Public API, orchestrates checking |
| SemanticGraph.fs | Checking.Native/ | Graph types, reachability |
| CheckExpressions.fs | Checking.Native/ | Expression type checking |
| NativeTypes.fs | Checking.Native/ | Native type representation |
| Unify.fs | Checking.Native/ | Type unification |
| SRTPResolution.fs | Checking.Native/ | SRTP constraint solving |
| Infrastructure/ | Checking.Native/ | Phase config and emission |

## Enabling Phase Emission

```fsharp
// In Firefly CLI with -k flag
FNCSPhaseConfig.enableAllPhases intermediatesDir
```

This enables:
- Soft-delete reachability (preserves full graph)
- JSON emission at phases 1, 4, 5
- Node tracing for debugging

## Integration Points

### Firefly Compilation Flow
```
.fidproj → ProjectChecker → NativeService.checkParsedInputs
                         → SemanticGraph with CheckResult
                         → FNCSTransfer → MLIR
                         → Toolchain → Native Binary
```

### MLIR Generation (FNCSTransfer)
- Traverses SemanticGraph from entry points
- Follows VarRef definitions to inline bodies
- Platform bindings via Alloy.Primitives.Bindings convention
- Generates LLVM dialect MLIR

## Related Memories
- `fncs_phase_debugging_protocol` - How to debug using phase files
- `native_binding_architecture` - Platform binding resolution
- `compilation_pipeline` - Full Firefly compilation flow

# FSharpNative Compiler Services (FNCS) Project Overview

## Purpose

FNCS (FSharpNative Compiler Services) provides native-first type checking for the Fidelity framework ecosystem. It is a **ground-up rebuild** of the type-checking layer, not a pruned fork of FCS.

## ARCHITECTURAL DECISION (December 2025)

**REBUILD, NOT PRUNE**: Cascade deletion analysis revealed that 3.2MB across 59 files (the entire FCS type-checking layer) depends on IL import assumptions. The type checker must be **rebuilt from scratch** for the native type universe.

See: `native_type_checker_architecture` memory for full design.

## Naming Convention

| Original | Native Version |
|----------|---------------|
| FSharp.Compiler.Service | FSharpNative.Compiler.Service |
| FCS | FNCS |

## Architecture

### The Rebuild Approach

The native type checker produces a **unified semantic representation**:
- Types attached during construction (no separate typed tree)
- SRTP resolved during type checking (not post-hoc)
- Hard prune reachability before handoff
- Baker absorbed (no dual-tree zipper needed)

### Core Modules (New)

| Module | Purpose |
|--------|---------|
| `NativeGlobals.fs` | Built-in types (string=UTF8, option=value-type, no obj) |
| `NativeTypes.fs` | Type representation with memory layout |
| `UnionFind.fs` | Efficient substitution with path compression |
| `Constraints.fs` | Constraint types: Equals, HasMember, LayoutCompatible |
| `Unify.fs` | Unification algorithm with occurs check |
| `CheckExpr.fs` | Unified construction (AST + types together) |
| `SRTPResolution.fs` | SRTP during type checking (Alloy witness hierarchy) |
| `Reachability.fs` | Hard prune before handoff |
| `SemanticGraph.fs` | Output structure for Firefly |

### Output API

```fsharp
let checkProject (sources: SourceFile list) (options: CheckOptions) : CheckResult =
    // Returns SemanticGraph with types attached, SRTP resolved, hard-pruned
```

## Development Phases

### Phase 1: Native Type Checker (CURRENT FOCUS)

Build the new type checker from principled foundations. Output:
- `checkProject(sources) → SemanticGraph` API
- Types attached during construction
- SRTP resolved intrinsically
- Hard-pruned reachable nodes only

### Phase 2: Firefly Integration

- Replace FCS integration with FNCS API call
- Remove absorbed components from Firefly (~10K LOC):
  - Baker, PSG Builder, Symbol Correlation, ResolveSRTP
- Firefly becomes a focused lowering orchestrator

### Phase 3: Tooling (FSNAC)

- FsNativeAutoComplete wraps FNCS for IDE support
- Native type hover info, SRTP resolution display
- `.fidproj` project recognition

### POST-QC_DEMO: XParsec Parser

Replace FsLex/FsYacc with XParsec for self-hosting enablement.
See: `xparsec_parser_unification` memory.

## Related Projects

- **Firefly**: AOT F# compiler consuming FNCS (lowering orchestrator)
- **FSNAC**: FsNativeAutoComplete - LSP server using FNCS
- **Alloy**: Native F# library (BCL replacement, witness hierarchy)
- **fsnative-spec**: F# Native Language Specification fork

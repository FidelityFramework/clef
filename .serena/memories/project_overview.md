# FSharpNative Compiler Services (FNCS) Project Overview

## Purpose

FNCS (FSharpNative Compiler Services) provides native-first type checking for the Fidelity framework ecosystem. It is a **ground-up rebuild** of the type-checking layer, not a pruned fork of FCS.

## ARCHITECTURAL DECISION (December 2025)

**REBUILD WITH PRESERVATION**: The type checker uses native types instead of BCL, but **FCS design-time infrastructure must be preserved**:
- Symbol tracking (FSharpSymbol, locations, references)
- Editor service APIs (GetToolTip, GetDeclaration, GetSymbolUses)
- Typed tree structure for correlation
- Source locations for navigation

**PSG CONSTRUCTION IN FNCS**: FNCS now builds the PSG (Program Semantic Graph). Firefly consumes the PSG as "correct by construction" and focuses on code generation.

See: `native_type_checker_architecture` and `fncs_fcs_preservation` memories for details.

## Naming Convention

| Original | Native Version |
|----------|---------------|
| FSharp.Compiler.Service | FSharpNative.Compiler.Service |
| FCS | FNCS |

## Architecture

### The Architecture Approach

FNCS produces a **PSG with native types and design-time capabilities**:
- Native type universe (UTF-8 strings, voption, no obj)
- SRTP resolved during type checking
- Full symbol information preserved for editor navigation
- PSG construction (moved from Firefly)

Firefly consumes the PSG and focuses on code generation (Alex/Zipper → MLIR → LLVM).

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

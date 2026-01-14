# FSharpNative Compiler Services (FNCS) Project Overview

## Purpose

FNCS (FSharpNative Compiler Services) provides native-first type checking for the Fidelity framework ecosystem. It is a **complete, standalone** type checker operating in the Native Type Universe (NTU) - no BCL types, no IL imports, no runtime dependencies.

## Architecture

FNCS produces a **PSG (Program Semantic Graph) with native types**:
- Native Type Universe (UTF-8 strings, value-type options, no `obj`)
- SRTP resolved during type checking
- Types attached during construction (not post-hoc)
- Union-Find based constraint solving

Firefly consumes the PSG and handles code generation (Alex/Zipper → MLIR → LLVM).

### Core Modules

| Module | Purpose |
|--------|---------|
| `NativeGlobals.fs` | Built-in types, NTUKind definitions |
| `NativeTypes.fs` | NativeType, TypeParam, TypeConRef |
| `UnionFind.fs` | Type variable binding, path compression |
| `Unify.fs` | Unification algorithm with occurs check |
| `SemanticGraph.fs` | PSG structure, reachability |
| `NativeService.fs` | Public API, orchestration |
| `Expressions/` | Modular expression checking |

### Expression Checking Modules

```
Expressions/
├── Coordinator.fs    # SynExpr dispatch
├── Types.fs          # TypeEnv, helpers
├── Bindings.fs       # Let/LetRec
├── Applications.fs   # App, TypeApp, Lambda
├── Intrinsics.fs     # FNCS intrinsic modules
├── ControlFlow.fs    # If/Match/While/For
├── Collections.fs    # Tuple/Array/Record
├── Patterns.fs       # Pattern matching
├── Identity.fs       # Identifier resolution
├── Literals.fs       # Constant handling
├── SynTypes.fs       # SynType checking
└── TypeOperations.fs # Cast/TypeTest/AddressOf
```

### Output API

```fsharp
let checkProject (sources: SourceFile list) (options: CheckOptions) : CheckResult
// Returns: SemanticGraph with types attached, diagnostics
```

## FNCS Intrinsics

Operations native to the type universe (no external binding needed):

| Module | Operations |
|--------|------------|
| `Sys` | write, read, exit |
| `NativePtr` | set, get, add, stackalloc |
| `NativeDefault` | zeroed, unreachable |
| `Array` | zeroCreate, length, get, set |
| `Console` | write, writeln, readln |
| `String` | length, concat |

## Related Projects

- **Firefly**: AOT F# compiler consuming FNCS PSG
- **Fidelity.Platform**: Platform-specific bindings via quotations
- **fsnative-spec**: F# Native Language Specification

## Historical Note

FNCS was originally conceived as a fork of FCS (F# Compiler Services). As of January 2026, FNCS is a clean-sheet implementation. The only FCS dependency is the parser (`SynExpr` types) which represents standard F# syntax.

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

### Directory Structure (January 2026)

```
src/Compiler/
├── NativeTypedTree/           # Core native type system
│   ├── NativeTypes.fs         # NTUKind, NativeType, TypeLayout
│   ├── (Type resolution via resolveSynType in Types.fs)
│   ├── Unify.fs               # Unification with occurs check
│   ├── UnionFind.fs           # Type variable binding
│   ├── NativeService.fs       # Public API, orchestration
│   ├── SRTPResolution.fs      # SRTP constraint solving
│   ├── NameResolution.fs      # Name/symbol resolution
│   ├── FSharpNativeExpr.fs    # Expression-centric view
│   ├── Expressions/           # Modular expression checking
│   │   ├── Coordinator.fs     # SynExpr dispatch
│   │   ├── Types.fs           # TypeEnv, helpers
│   │   ├── Intrinsics.fs      # FNCS intrinsic modules
│   │   ├── Bindings.fs        # Let/LetRec
│   │   ├── Applications.fs    # App, TypeApp, Lambda
│   │   └── ...
│   └── Infrastructure/        # Phase config, emission
├── PSGSaturation/             # SemanticGraph, saturation
│   └── SemanticGraph/
├── Baker/                     # Type resolution layer
└── Project/                   # .fidproj handling
```

### Core Modules

| Module | Location | Purpose |
|--------|----------|---------|
| `Types.fs` | NativeTypedTree/Expressions/ | TypeEnv, resolveSynType |
|  | COMPLETE (resolveSynType in Types.fs) |
| `NativeTypes.fs` | NativeTypedTree/ | NativeType, TypeParam, TypeConRef, TypeLayout |
| `Intrinsics.fs` | NativeTypedTree/Expressions/ | FNCS intrinsic resolution |
| `UnionFind.fs` | NativeTypedTree/ | Type variable binding, path compression |
| `Unify.fs` | NativeTypedTree/ | Unification algorithm with occurs check |
| `SemanticGraph.fs` | PSGSaturation/SemanticGraph/ | PSG structure, reachability |
| `NativeService.fs` | NativeTypedTree/ | Public API, orchestration |

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
├── (SynType resolved at boundary via Types.fs)

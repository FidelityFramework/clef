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
│   ├── *(DELETED: NativeGlobals.fs - greenfield pending)*
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
| *(DELETED)* | | *greenfield pending* |
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
├── *(DELETED: SynTypes.fs - greenfield pending)*
└── TypeOperations.fs # Cast/TypeTest/AddressOf
```

### Output API

```fsharp
let checkProject (sources: SourceFile list) (options: CheckOptions) : CheckResult
// Returns: SemanticGraph with types attached, diagnostics
```

## Memory Region Types *(NativeGlobals.fs DELETED - greenfield pending)*

FNCS provides type-safe memory regions via measure types:

### Memory Regions
```fsharp
module MemoryRegions =
    let stack      // Stack memory - automatically freed on scope exit
    let arena      // Arena/heap memory - managed by allocator
    let sram       // Fast on-chip RAM (embedded)
    let flash      // Persistent storage (embedded)
    let peripheral // Memory-mapped I/O registers
    let dma        // DMA-accessible memory
    let external'  // Off-chip SDRAM
```

### Access Modes
```fsharp
module AccessModes =
    let readOnly   // ro - read-only access
    let writeOnly  // wo - write-only access
    let readWrite  // rw - read-write access
```

### Memory Types
| Type | Description |
|------|-------------|
| `Ptr<'T, 'region, 'access>` | Native pointer with region and access tracking |
| `Span<'T, 'region, 'access>` | Fat pointer (ptr + length) with memory safety |
| `ReadOnlySpan<'T, 'region>` | Immutable view (ptr + length) |
| `Arena<'lifetime>` | Bump allocator with lifetime tracking |

## FNCS Intrinsics

Operations native to the type universe (no external binding needed):

| Module | Operations |
|--------|------------|
| `Sys` | write, read, exit |
| `NativePtr` | set, get, add, stackalloc, copy, fill |
| `NativeDefault` | zeroed, unreachable |
| `Array` | zeroCreate, create, init, copy, length, get, set, tryItem, isEmpty |
| `Arena` | fromPointer, alloc, allocAligned, remaining, reset |
| `String` | length, concat2, isEmpty, contains, startsWith, endsWith, etc. |
| `DateTime` | now, fromTicks, addDays, etc. |
| `TimeSpan` | fromMilliseconds, fromSeconds, totalSeconds, etc. |

## Related Projects

- **Firefly**: AOT F# compiler consuming FNCS PSG
- **Fidelity.Platform**: Platform-specific bindings via quotations
- **fsnative-spec**: F# Native Language Specification

## Historical Note

FNCS was originally conceived as a fork of FCS (F# Compiler Services). As of January 2026, FNCS is a clean-sheet implementation. The only FCS dependency is the parser (`SynExpr` types) which represents standard F# syntax.

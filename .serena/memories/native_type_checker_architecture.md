# Native Type Checker Architecture

## Overview

FNCS (F# Native Compiler Services) is a complete, standalone type checker for native F# compilation. It operates entirely within the Native Type Universe (NTU) - there are no BCL types, no IL imports, no runtime dependencies.

## Core Principle: NTU-Only

FNCS uses native types exclusively:

| Type | Representation |
|------|----------------|
| `string` | UTF-8 fat pointer (ptr + length, 16 bytes) |
| `int` | Platform word (NTUint) |
| `int32` | Fixed 32-bit (NTUint32) |
| `option<'T>` | Value type (tag + payload), no null |
| `obj` | **Does not exist** |

## Architecture Layers

```
┌─────────────────────────────────────────────────────────────────────┐
│                         Source Files (.fs)                          │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                           PARSER                                    │
│  F# parser producing SynExpr, SynModule, etc.                       │
│  (Standard F# syntax - produces AST)                                │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      TYPE ENVIRONMENT                               │
│  Type resolution via resolveSynType at parser boundary                             │
│  NTUKind: Type classification (NTUint, NTUptr, NTUstring, etc.)    │
│  Platform Context: Quotation-based type width resolution           │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                     EXPRESSION CHECKING                             │
│  Checking.Native/Expressions/ modules:                              │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐          │
│  │ Coordinator  │───▶│ Bindings     │───▶│ Applications │          │
│  └──────────────┘    └──────────────┘    └──────────────┘          │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐          │
│  │ Intrinsics   │    │ ControlFlow  │    │ Collections  │          │
│  └──────────────┘    └──────────────┘    └──────────────┘          │
│                                                                     │
│  Types attached DURING construction (not post-hoc)                  │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    CONSTRAINT SOLVING                               │
│  Union-Find unification with path compression                       │
│  Constraint.Equals → tryUnify → bind type variables                 │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    REACHABILITY ANALYSIS                            │
│  Entry point → transitive closure → soft-delete unreachable         │
│  (Preserves structure for debugging with -k flag)                   │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    SEMANTIC GRAPH (PSG)                             │
│  Output to Firefly:                                                 │
│  - SemanticNode with types attached                                 │
│  - SRTP resolved via WitnessResolution                              │
│  - Only reachable nodes marked                                      │
└─────────────────────────────────────────────────────────────────────┘
```

## Module Structure

```
src/Compiler/Checking.Native/
├── (Types defined in NativeTypes.fs, resolution via resolveSynType)
├── NativeTypes.fs           # NativeType, TypeParam, TypeConRef
├── UnionFind.fs             # Type variable binding, path compression
├── Unify.fs                 # Unification algorithm
├── SemanticGraph.fs         # PSG structure, reachability
├── NativeService.fs         # Public API, orchestration
├── Expressions/             # Expression checking (modular)
│   ├── Types.fs             # TypeEnv, helpers
│   ├── Coordinator.fs       # SynExpr dispatch
│   ├── Bindings.fs          # Let/LetRec
│   ├── Applications.fs      # App, TypeApp, Lambda
│   ├── Intrinsics.fs        # FNCS intrinsic modules
│   ├── ControlFlow.fs       # If/Match/While/For
│   ├── Collections.fs       # Tuple/Array/Record
│   ├── Patterns.fs          # Pattern matching
│   └── ...
└── Infrastructure/          # Phase config, emission
```

## Type System

### NativeType

```fsharp
type NativeType =
    | TForall of TypeParam list * NativeType
    | TApp of TypeConRef * NativeType list
    | TTuple of NativeType list * isStruct: bool
    | TFun of NativeType * NativeType
    | TVar of TypeParam
    | TMeasure of Measure
    | TAnon of fields * isStruct
    | TByref of NativeType * ByrefKind
    | TNativePtr of NativeType
    | TRecord of TypeConRef * (string * NativeType) list
    | TUnion of TypeConRef * UnionCaseInfo list
    | TError of string
```

### TypeParam with Union-Find

```fsharp
type TypeParam = {
    Id: int
    Name: string
    Kind: TypeParamKind
    Constraints: Constraint list
    mutable Parent: TypeParamState
    Range: SourceRange
}

type TypeParamState =
    | Unbound
    | Bound of NativeType
```

### Constraint System

```fsharp
type Constraint =
    | Equals of NativeType * NativeType * SourceRange
    | HasMember of ty * name * signature * range    // SRTP
    | HasMeasure of NativeType * Measure * range
    | Subtype of sub * super * range
    | LayoutCompatible of NativeType * TypeLayout * range
    | HasTypeArgs of NativeType * args * result * range
```

## Union-Find Operations

```fsharp
/// Find representative with path compression
let rec find (typar: TypeParam) : TypeParam * NativeType option

/// Bind type parameter to concrete type
let bind (typar: TypeParam) (ty: NativeType) : unit

/// Apply substitutions, following Union-Find pointers
let rec applySubst (ty: NativeType) : NativeType
```

**Critical**: Downstream consumers (like Alex/TypeMapping) must use `find` to resolve type variables, not check `tvar.Parent` directly.

## FNCS Intrinsics

Operations native to the type universe - no external binding needed:

| Module | Operations |
|--------|------------|
| `Sys` | write, read, exit (syscall primitives) |
| `NativePtr` | set, get, add, stackalloc, copy, fill |
| `NativeDefault` | zeroed, unreachable |
| `Array` | zeroCreate, create, length, get, set |
| `Console` | write, writeln, readln |
| `String` | length, concat, substring |

## Entry Point Handling

Entry points (`[<EntryPoint>]` functions) have constrained signatures:

```fsharp
// In Bindings.fs checkBinding:
if isEntryPoint then
    // Constrain parameter to string[] (argv)
    let stringArrayType = mkArrayType env.Globals.StringType
    addConstraint (Constraint.Equals(paramTy, stringArrayType, range)) env
    // Constrain return type to int
    addConstraint (Constraint.Equals(bodyNode.Type, env.Globals.IntType, range)) env
```

## Integration with Firefly

FNCS is a **pure** compiler service - no file I/O:

```
Firefly (orchestration):
  - Parse .fidproj
  - Resolve dependencies
  - Load platform quotations
  - Pass to FNCS
       ↓
FNCS (pure compilation):
  - Type check
  - Build PSG
  - Return SemanticGraph + diagnostics
       ↓
Firefly/Alex:
  - Traverse PSG
  - Generate MLIR
  - Compile to native
```

## Historical Note

FNCS was originally designed as a modification of FCS (F# Compiler Services). As of January 2026, FNCS is a complete standalone implementation. The only remaining FCS dependency is the parser (`SynExpr` types), which is standard F# syntax representation.

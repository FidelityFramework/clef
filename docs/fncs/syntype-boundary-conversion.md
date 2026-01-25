# SynType: Transient Boundary Representation

## Overview

In F# Native Compiler Services (FNCS), `SynType` plays a strictly limited role. It exists **only** at the parser boundary and is **immediately** converted to `NativeType`. SynType does not propagate into the type checking system.

## Architecture Principle

```
Parser → SynType → resolveSynType → NativeType → Type Checking
              ↑                          ↓
              │                          └── NativeType propagates everywhere
              └── SynType dies here
```

**Key insight**: SynType is transient. It exists because the parser cannot produce fully resolved types without type environment context. However, once that context is available, SynType is converted immediately and discarded.

## Why SynType Exists

The parser runs without type environment knowledge:

```fsharp
// Parser sees these as equivalent syntax
type Foo = int32      // What is int32? Parser doesn't know
type Bar = MyModule.T // What is MyModule.T? Parser doesn't know
```

The parser produces `SynType` nodes that capture the **syntactic** representation:
- `SynType.LongIdent` for named types (`int`, `string`, `MyModule.Type`)
- `SynType.App` for generic types (`List<int>`, `Option<string>`)
- `SynType.Tuple` for tuples (`int * string`)
- `SynType.Fun` for functions (`int -> string`)
- etc.

## The Boundary Conversion

`resolveSynType` in `Types.fs` is the single conversion point:

```fsharp
let rec resolveSynType (env: TypeEnv) (synType: SynType) : NativeType =
    match synType with
    | SynType.LongIdent(SynLongIdent(idents, _, _)) ->
        let name = idents |> List.map (fun id -> id.idText) |> String.concat "."
        match resolveTypeName name env with
        | Some ty -> ty
        | None -> NativeType.TError $"Unknown type: {name}"
    // ... other cases
```

This function:
1. Takes the type environment (which knows about type definitions, abbreviations, etc.)
2. Converts the syntactic representation to a semantic `NativeType`
3. Returns an error type if resolution fails (preserving diagnostics)

## What SynType Does NOT Do

SynType does **not**:
- Propagate through the type checking system
- Get stored in the PSG (Program Semantic Graph)
- Get passed as callbacks to type-checking functions
- Exist outside the immediate boundary conversion

## NativeType is the Type System

The Native Type Universe (NTU) defines all types:

```fsharp
type NativeType =
    | TInt8 | TInt16 | TInt32 | TInt64
    | TUInt8 | TUInt16 | TUInt32 | TUInt64
    | TFloat32 | TFloat64
    | TString
    | TFun of NativeType * NativeType
    | TTuple of NativeType list * isStruct: bool
    | TApp of TypeConRef * NativeType list
    | TVar of TypeParam
    // ... etc.
```

Type checking operates exclusively on `NativeType`. The PSG stores `NativeType`. Code generation consumes `NativeType`.

## Historical Context

Previous iterations of FNCS incorrectly threaded `checkSynType` callbacks through the type checking system. This pattern was:

1. **Unnecessary** - SynType can be resolved at the point of encounter
2. **Polluting** - It spread parser concerns into semantic analysis
3. **Complex** - It required callback threading through many modules

The cleanup removed ~70 occurrences of this anti-pattern, replacing them with direct `resolveSynType` calls at conversion sites.

## Type Width vs Type Identity

Note that `NativeType` captures **type identity**, not width. A 32-bit integer on one platform might be 64 bits on another. Type identity (`TInt32`) is resolved in FNCS; type **width** is resolved downstream by Alex based on the target platform.

```
FNCS: int32 → NativeType.TInt32    (identity: "32-bit signed integer")
Alex: NativeType.TInt32 → i32      (width: 4 bytes on this platform)
```

## Summary

| Concern | Where Resolved | Representation |
|---------|----------------|----------------|
| Syntax | Parser | `SynType` |
| Type identity | FNCS boundary | `NativeType` |
| Type width | Alex/Backend | MLIR/LLVM types |

SynType is a means to an end: capturing syntactic type information until the type environment provides enough context to resolve it. Once resolved, SynType is discarded forever.

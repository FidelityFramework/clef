# TypedTree IL Architecture Analysis

## Overview

This memory documents where IL types appear in the FCS TypedTree and what must change for FNCS native-first compilation.

## Key Discovery: IL Types Are Localized

IL types are NOT pervasive in TypedTree. They appear in specific, well-defined locations:

### 1. Type Import Mechanism (TILObjectReprData)

```fsharp
type TyconRepresentation =
    | TFSharpTyconRepr of FSharpTyconData   // F# types - NO IL
    | TILObjectRepr of TILObjectReprData    // Imported .NET types - IL HERE
    | TAsmRepr of ILType                     // Inline IL assembly
    | TMeasureableRepr of TType             // Measures - NO IL
    | TNoRepr                               // Unknown - NO IL
```

`TILObjectReprData = ILScopeRef * ILTypeDef list * ILTypeDef`

This is ONLY for types imported from .NET assemblies. F# types use `TFSharpTyconRepr`.

### 2. Operations (TOp)

```fsharp
type TOp =
    // IL-specific operations
    | ILAsm of ILInstr list * TTypes        // Inline IL
    | ILCall of ... ILMethodRef ...         // .NET method calls
    | Goto of ILCodeLabel                    // State machine (int)
    | Label of ILCodeLabel                   // State machine (int)
    
    // F# operations (NO IL)
    | TraitCall of TraitConstraintInfo       // SRTP - PRESERVE!
    | UnionCase of UnionCaseRef
    | ValFieldGet of RecdFieldRef
    // ... many more
```

### 3. Core Types Are IL-Free

`TType`, `Typar`, `TyparConstraint`, and the core `Expr` structure do NOT use IL types directly.

## FNCS Transformations Required

| FCS Type | Purpose | FNCS Equivalent |
|----------|---------|-----------------|
| `TILObjectReprData` | Imported .NET types | `TNativeReprData` |
| `ILScopeRef` | Assembly provenance | `NativeScopeRef` |
| `ILTypeDef` | .NET type metadata | `NativeTypeDef` |
| `ILMethodRef` | .NET method ref | `NativeFunctionRef` |
| `TOp.ILCall` | .NET method call | `TOp.NativeCall` |
| `TOp.ILAsm` | Inline IL | **Remove** |
| `ILInstr` | IL instructions | Empty scaffolding |
| `ILCodeLabel` | Labels | Keep (`int` alias) |

## What FNCS Preserves

- **TType** - Core type representation
- **Typar** - Type parameters
- **TyparConstraint** - Type constraints
- **TraitConstraintInfo** - SRTP resolution (critical!)
- **Expr** - Expression structure with ranges

## Native Type Layer Design

```fsharp
type NativeScopeRef =
    | Local                        // Current compilation unit
    | NativeModule of ModulePath   // External native module (Alloy)

type NativeTypeRef = {
    Scope: NativeScopeRef
    Path: string list
    Name: string
}

type NativeTypeDef = {
    Name: string
    Fields: NativeFieldDef list
    Size: int                      // Memory layout
    Alignment: int
    Region: MemoryRegion option    // UMX region
}
```

## Baker Integration Opportunity

Baker correlates FSharpExpr with PSG by walking both in parallel. All information Baker extracts (types, SRTP, ranges) already exists in the typed tree.

FNCS could expose this correlation directly, eliminating need for external Baker.

## Implementation Files

- `src/Compiler/TypedTree/TypedTree.fsi` - Where IL types are used
- `src/Compiler/AbstractIL/il.fsi` - IL type definitions
- `src/Compiler/AbstractIL/NativeIL.fs` - To be created

## References

- Firefly `/docs/FNCS_TypedTree_Architecture.md` - Full architectural narrative
- `fncs_architecture` memory in Firefly - FNCS design principles
- `baker_component` memory in Firefly - Baker architecture

# FNCS Integration Status (December 2025)

## Completed Work

### Namespace Rename: DONE ✅
- Project file: `FSharp.Native.Compiler.Service.fsproj`
- Assembly: `FSharp.Native.Compiler.Service`
- Namespace: `FSharp.Native.Compiler.*` (was `FSharp.Compiler.*`)
- ~159 source files updated
- FsLex/FsYacc module flags updated
- Solution files updated
- Build succeeds: `/home/hhh/repos/fsnative/artifacts/bin/FSharp.Native.Compiler.Service/Debug/net9.0/FSharp.Native.Compiler.Service.dll`

### Native Type Checker: ~85-90% DONE
Located in `/home/hhh/repos/fsnative/src/Compiler/Checking.Native/`:
- `NativeTypes.fs` - Type representation
- `NativeGlobals.fs` - Built-in types, Ptr, memory regions
- `UnionFind.fs` - Path compression, occurs check
- `Unify.fs` - Unification with detailed errors
- `SemanticGraph.fs` - All F# constructs, types attached at construction
- `CheckExpr.fs` - Expression checking (~80-85%)
- `SRTPResolution.fs` - SRTP during type checking (~95%)

## Next Steps: Build FNCS Public API

FNCS currently has the native type checker module but NO public API. Need to build:

### 1. Create Public API Module
```fsharp
// src/Compiler/Service/NativeService.fs (new file)
module FSharp.Native.Compiler.Service

type CheckOptions = {
    SourceFiles: string list
    References: string list
    // ... 
}

type CheckResult = {
    Graph: SemanticGraph    // Hard-pruned, types attached
    Errors: Diagnostic list
    Warnings: Diagnostic list
}

let checkProject (options: CheckOptions) : CheckResult =
    // 1. Parse source files using existing FCS parser → SynExpr
    // 2. Run native type checker on SynExpr → SemanticNode
    // 3. Hard prune unreachables
    // 4. Return SemanticGraph
```

### 2. Wire Up Parser to Native Type Checker
The FCS parser still exists in FNCS and produces `SynExpr`. Need to:
- Parse source files
- Feed `SynExpr` to `CheckExpr.checkExpr`
- Collect results into `SemanticGraph`

### 3. Build SemanticGraph Output
The `SemanticGraph` module already exists with `SemanticNode`. Need to:
- Create graph from accumulated nodes
- Apply reachability analysis
- Hard prune

## What Firefly Will Receive

Instead of:
- `FSharpCheckProjectResults`
- `FSharpSymbol`, `FSharpEntity`, `FSharpType`
- `FSharpExpr` (typed tree)

Firefly will receive:
- `SemanticGraph` with `SemanticNode` list
- Each node has: Id, Kind, Range, Type (attached), SRTPResolution, ArenaAffinity
- Only reachable nodes (hard pruned)

## What Firefly Will Remove (~10K LOC)

Once FNCS API is ready:
- `src/Core/FCS/` - All FCS integration
- `src/Baker/` - Typed tree overlay
- `src/Core/PSG/Builder/` - Graph construction (FNCS does this)
- `src/Core/PSG/Correlation.fs` - No separate trees
- `src/Core/PSG/Nanopass/ResolveSRTP.fs` - FNCS does this
- `src/Core/PSG/Nanopass/ValidateNativeTypes.fs` - FNCS does this
- `src/Core/PSG/TypeIntegration.fs` - Types are intrinsic

## Firefly Will Keep

- `src/Alex/` - MLIR generation (Zipper + XParsec + Bindings)
- `src/Core/PSG/Nanopass/` (lowering passes only):
  - FlattenApplications
  - LowerInterpolatedStrings
  - DetectPlatformBindings
  - etc.
- CLI infrastructure

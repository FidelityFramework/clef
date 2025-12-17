# FNCS Pruning Plan: From FCS to F# Native Compiler Services

## Overview

This document outlines the plan to transform the `fsnative` repository from a full F# compiler fork into a lean **F# Native Compiler Services (FNCS)** library optimized for the Fidelity framework's native compilation pipeline.

**Goal**: Create `FSharp.Native.Compiler.Service.dll` - a minimal, fast-compiling library that provides:
- Lexing and parsing (preserved from FCS)
- Syntax tree construction (preserved, with native extensions)
- Type checking with native type universe (modified)
- SRTP resolution against Alloy witnesses (modified)
- Symbol resolution and IDE services (streamlined)

**Non-Goal**: This is NOT a general-purpose F# compiler. We deliberately remove:
- MSBuild integration
- NuGet dependency management
- .NET assembly/IL generation
- FSI (F# Interactive)
- Project "cracking" infrastructure
- Multi-targeting support

## Strategic Context

### The Fidelity Compilation Pipeline

```
F# Source → FNCS → PSG → Alex → MLIR → LLVM → Native Binary
              ↑
         This repository
```

FNCS replaces FCS in the Fidelity pipeline. It provides:
1. **Parsing**: Lexer, parser, syntax tree (largely unchanged from FCS)
2. **Type Checking**: Modified to use native types, not BCL types
3. **Typed Tree**: FSharpExpr with native type resolution
4. **Symbol Services**: For IDE integration via FidelityAC

### What FNCS Does NOT Provide

FNCS stops at the typed tree. It does NOT:
- Generate IL or any executable code
- Resolve NuGet packages
- Read MSBuild project files
- Support scripting or REPL
- Handle multi-targeting or SDK resolution

All code generation happens in Firefly's Alex pipeline via MLIR.

## Pruning Categories

### Category 1: REMOVE ENTIRELY

These components have no role in native compilation:

#### Build Infrastructure
```
src/FSharp.Build/                    # MSBuild tasks - REMOVE
src/FSharp.DependencyManager.Nuget/  # NuGet integration - REMOVE
src/Microsoft.FSharp.Compiler/       # Legacy compiler host - REMOVE
```

#### Compiler Executables
```
src/fsc/                             # fsc.exe driver - REMOVE
src/fsi/                             # FSI interactive - REMOVE
```

#### IL/Assembly Generation
```
src/Compiler/AbstractIL/             # IL reading/writing - REMOVE
src/Compiler/CodeGen/                # IL code generation - REMOVE
src/Compiler/Optimize/               # IL optimization passes - REMOVE
```

#### Driver Infrastructure
```
src/Compiler/Driver/CreateILModule.fs      # IL module creation - REMOVE
src/Compiler/Driver/StaticLinking.fs       # Assembly linking - REMOVE
src/Compiler/Driver/OptimizeInputs.fs      # IL optimization - REMOVE
src/Compiler/Driver/FxResolver.fs          # .NET SDK resolution - REMOVE
src/Compiler/Driver/ScriptClosure.fs       # Script dependencies - REMOVE
src/Compiler/Driver/BinaryResourceFormats.fs # Win32 resources - REMOVE
```

### Category 2: KEEP AND MODIFY

These are the core components that define FNCS:

#### Type System (CRITICAL MODIFICATIONS)
```
src/Compiler/Checking/TcGlobals.fs         # ADD: Native type definitions
src/Compiler/Checking/CheckExpressions.fs  # MODIFY: Native literal typing
src/Compiler/Checking/ConstraintSolver.fs  # MODIFY: Native SRTP resolution
```

#### Typed Tree
```
src/Compiler/TypedTree/TypedTree.fs        # MODIFY: Native type representations
src/Compiler/TypedTree/TypedTreeBasics.fs  # ADD: Native constructors
src/Compiler/TypedTree/TypedTreeOps.fs     # Keep, minor adaptations
```

### Category 3: KEEP AS-IS

These components are BCL-agnostic and work unchanged:

#### Lexer
```
src/Compiler/lex.fsl                       # Token definitions
src/Compiler/SyntaxTree/LexHelpers.fs      # Lexer utilities
src/Compiler/SyntaxTree/LexFilter.fs       # Offside rule
```

#### Parser
```
src/Compiler/pars.fsy                      # Grammar definition
src/Compiler/SyntaxTree/ParseHelpers.fs    # Parse utilities
```

#### Syntax Tree
```
src/Compiler/SyntaxTree/SyntaxTree.fs      # Untyped AST
src/Compiler/SyntaxTree/SyntaxTreeOps.fs   # AST operations
src/Compiler/SyntaxTree/SyntaxTrivia.fs    # Whitespace/comments
src/Compiler/SyntaxTree/PrettyNaming.fs    # Name handling
src/Compiler/SyntaxTree/XmlDoc.fs          # Documentation comments
```

#### Core Utilities
```
src/Compiler/Utilities/range.fs            # Source locations
src/Compiler/Utilities/lib.fs              # General utilities
src/Compiler/Utilities/ResizeArray.fs      # Collections
src/Compiler/Utilities/HashMultiMap.fs     # Hash collections
```

#### Symbols (Streamlined)
```
src/Compiler/Symbols/Symbols.fs            # Keep core symbol types
src/Compiler/Symbols/SymbolHelpers.fs      # Keep helpers
src/Compiler/Symbols/Exprs.fs              # Keep FSharpExpr
```

### Category 4: KEEP BUT STREAMLINE

These components need simplification:

#### Service Layer
```
src/Compiler/Service/service.fs            # STREAMLINE: Remove IDE-heavy features
src/Compiler/Service/FSharpCheckerResults.fs # STREAMLINE: Focus on typed tree
src/Compiler/Service/FSharpParseFileResults.fs # KEEP
src/Compiler/Service/QuickParse.fs         # KEEP for IDE
src/Compiler/Service/SemanticClassification.fs # KEEP for IDE
```

**Remove from Service:**
- BackgroundCompiler.fs (IDE incremental - too heavy)
- IncrementalBuild.fs (MSBuild-centric)
- FSharpProjectSnapshot.fs (project system)
- FSharpWorkspace*.fs (workspace management)
- ServiceAssemblyContent.fs (assembly reading)

#### Driver (Minimal)
```
src/Compiler/Driver/CompilerConfig.fs      # STREAMLINE: Remove IL options
src/Compiler/Driver/CompilerDiagnostics.fs # KEEP
src/Compiler/Driver/CompilerOptions.fs     # STREAMLINE: Native options only
src/Compiler/Driver/ParseAndCheckInputs.fs # KEEP: Core pipeline
```

**Remove from Driver:**
- CompilerImports.fs (assembly imports)
- GraphChecking/ (parallel IL gen)

## New Components to Add

### Native Type Definitions

Create `src/Compiler/Checking/NativeTypes.fs`:

```fsharp
/// Native type definitions for FNCS
module internal FSharp.Compiler.NativeTypes

/// Native string type (replaces System.String for literals)
let nativeStrTycon = ...

/// Native option (voption, not nullable)
let nativeOptionTycon = ...

/// Native array (fat pointer, not System.Array)
let nativeArrayTycon = ...

/// Native span with lifetime
let nativeSpanTycon = ...
```

### Native SRTP Resolution

Create `src/Compiler/Checking/NativeSRTP.fs`:

```fsharp
/// SRTP resolution against Alloy witness hierarchy
module internal FSharp.Compiler.NativeSRTP

/// Resolve trait constraint against Alloy witnesses
let resolveNativeWitness (traitInfo: TraitConstraintInfo) = ...

/// Alloy witness hierarchy search
let expandWitnessHierarchy (ty: TType) = ...
```

### Configuration

Create `src/Compiler/FNCSConfig.fs`:

```fsharp
/// FNCS configuration
[<RequireQualifiedAccess>]
type FNCSMode =
    | Native      // Full native type universe (default)
    | Compatible  // BCL types for comparison/testing

type FNCSConfig = {
    Mode: FNCSMode
    AlloyPath: string option  // Path to Alloy for witness resolution
}
```

## Project File Changes

### Before (FSharp.Compiler.Service.fsproj)
- ~200 source files
- Complex MSBuild logic
- Multi-targeting
- NuGet packaging

### After (FSharp.Native.Compiler.Service.fsproj)
- ~80 source files
- Simple project structure
- Single target (net9.0)
- Local reference only

### Estimated Build Time Impact

| Metric | FCS | FNCS (Target) |
|--------|-----|---------------|
| Source files | ~200 | ~80 |
| Lines of code | ~400K | ~150K |
| Clean build | ~3 min | <1 min |
| Incremental | ~30 sec | <10 sec |

## Phased Implementation

### Phase 1: Structural Pruning (Week 1-2)

1. Fork project file as `FSharp.Native.Compiler.Service.fsproj`
2. Remove Category 1 files entirely
3. Remove unused source files from project
4. Verify it still builds (with stubs if needed)

### Phase 2: Service Streamlining (Week 2-3)

1. Remove heavy Service components
2. Create minimal `FNCSChecker` API
3. Expose only: Parse, TypeCheck, GetTypedTree
4. Remove workspace/project management

### Phase 3: Native Type Integration (Week 3-5)

1. Add `NativeTypes.fs` with type definitions
2. Modify `TcGlobals.fs` to register native types
3. Modify `CheckExpressions.fs` for native literal typing
4. Add configuration for Native vs Compatible mode

### Phase 4: SRTP Modification (Week 5-7)

1. Add `NativeSRTP.fs` with witness resolution
2. Modify `ConstraintSolver.fs` to use native witnesses
3. Test against Alloy patterns

### Phase 5: Integration Testing (Week 7-8)

1. Create test harness in Firefly
2. Verify HelloWorld compiles with FNCS
3. Verify SRTP resolves correctly
4. Benchmark build times

## API Surface

### Public API (FSharp.Native.Compiler.Service)

```fsharp
namespace FSharp.Native.Compiler

/// Configuration for FNCS
type FNCSConfig

/// Main entry point for type checking
type FNCSChecker =
    /// Parse a source file
    member ParseFile: source: string * path: string -> FNCSParseResults

    /// Type check parsed files
    member CheckFiles: parsed: FNCSParseResults list * config: FNCSConfig -> FNCSCheckResults

/// Parse results (syntax tree)
type FNCSParseResults =
    member SyntaxTree: SynModuleOrNamespace list
    member Diagnostics: FNCSDiagnostic list

/// Type check results (typed tree)
type FNCSCheckResults =
    /// Get the typed expression tree
    member TypedTree: FSharpExpr

    /// Get resolved symbols
    member GetSymbols: unit -> FSharpSymbol list

    /// Get type at position (for IDE)
    member GetTypeAtPosition: line: int * col: int -> FSharpType option

    /// Get SRTP resolutions
    member GetSRTPResolutions: unit -> SRTPResolution list

/// SRTP resolution result
type SRTPResolution = {
    TraitCall: Range
    WitnessType: FSharpType
    ResolvedMember: string
    IsNativeWitness: bool
}
```

### Internal Dependencies

FNCS depends only on:
- `FSharp.Core` (F# runtime)
- `System.Collections.Immutable` (data structures)
- `System.Memory` (spans)

NO dependency on:
- MSBuild
- NuGet.* packages
- System.Reflection.Metadata (IL reading)

## Namespace Changes

```
FSharp.Compiler.*           → FSharp.Native.Compiler.*
FSharp.Compiler.Service.*   → FSharp.Native.Compiler.Service.*
FSharp.Compiler.Symbols.*   → FSharp.Native.Compiler.Symbols.*
```

## Success Criteria

1. **Build Time**: Clean build < 1 minute
2. **Binary Size**: `FSharp.Native.Compiler.Service.dll` < 5 MB
3. **API Simplicity**: < 10 public types
4. **Native Types**: String literals type as `NativeStr`
5. **SRTP**: Resolves against Alloy witnesses
6. **Firefly Integration**: HelloWorld samples compile correctly

## Related Documents

- `/docs/FNCS_Architecture.md` - Firefly's FNCS documentation
- `fsnative-spec/docs/FNCS_Specification.md` - Language specification for native types
- `From Bridged To Self Hosted.md` - Long-term extraction strategy

## Appendix: Files to Remove

### Complete Directory Removals
```
src/FSharp.Build/
src/FSharp.DependencyManager.Nuget/
src/Microsoft.FSharp.Compiler/
src/fsc/
src/fsi/
src/Compiler/AbstractIL/
src/Compiler/CodeGen/
src/Compiler/Optimize/
src/Compiler/Interactive/
src/Compiler/Legacy/
src/Compiler/Driver/GraphChecking/
```

### Individual File Removals from Kept Directories

**From src/Compiler/Driver/:**
- CreateILModule.fs, CreateILModule.fsi
- StaticLinking.fs, StaticLinking.fsi
- OptimizeInputs.fs, OptimizeInputs.fsi
- FxResolver.fs, FxResolver.fsi
- ScriptClosure.fs, ScriptClosure.fsi
- BinaryResourceFormats.fs, BinaryResourceFormats.fsi

**From src/Compiler/Service/:**
- BackgroundCompiler.fs, BackgroundCompiler.fsi
- IncrementalBuild.fs, IncrementalBuild.fsi
- FSharpProjectSnapshot.fs
- FSharpWorkspace.fs
- FSharpWorkspaceQuery.fs
- FSharpWorkspaceState.fs
- ServiceAssemblyContent.fs, ServiceAssemblyContent.fsi

**From src/Compiler/Facilities/:**
- Files related to IL/assembly handling

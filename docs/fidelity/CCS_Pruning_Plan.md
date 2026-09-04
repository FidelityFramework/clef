# CCS Pruning Plan: From FCS to Clef Compiler Service

## Overview

This document outlines the plan to transform the `clef` repository from a full F# compiler fork into a lean **Clef Compiler Service (CCS)** library optimized for the Fidelity framework's native compilation pipeline.

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
F# Source → CCS → PSG → Alex → MLIR → LLVM → Native Binary
              ↑
         This repository
```

CCS replaces FCS in the Fidelity pipeline. It provides:
1. **Parsing**: Lexer, parser, syntax tree (largely unchanged from FCS)
2. **Type Checking**: Modified to use native types, not BCL types
3. **Typed Tree**: FSharpExpr with native type resolution
4. **Symbol Services**: For IDE integration via FidelityAC

### What CCS Does NOT Provide

CCS stops at the typed tree. It does NOT:
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

These are the core components that define CCS:

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
/// Native type definitions for CCS
module internal FSharp.Compiler.NativeTypes

/// Native string type (replaces System.String for literals)
let nativeStrTycon = ...

/// Native option (voption, not nullable)
let nativeOptionTycon = ...

/// Native array (a `memref<?xT>` view, not System.Array)
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

Create `src/Compiler/CCSConfig.fs`:

```fsharp
/// CCS configuration
[<RequireQualifiedAccess>]
type CCSMode =
    | Native      // Full native type universe (default)
    | Compatible  // BCL types for comparison/testing

type CCSConfig = {
    Mode: CCSMode
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

| Metric | FCS | CCS (Target) |
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
2. Create minimal `CCSChecker` API
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
2. Verify HelloWorld compiles with CCS
3. Verify SRTP resolves correctly
4. Benchmark build times

## API Surface

### Public API (FSharp.Native.Compiler.Service)

```fsharp
namespace FSharp.Native.Compiler

/// Configuration for CCS
type CCSConfig

/// Main entry point for type checking
type CCSChecker =
    /// Parse a source file
    member ParseFile: source: string * path: string -> CCSParseResults

    /// Type check parsed files
    member CheckFiles: parsed: CCSParseResults list * config: CCSConfig -> CCSCheckResults

/// Parse results (syntax tree)
type CCSParseResults =
    member SyntaxTree: SynModuleOrNamespace list
    member Diagnostics: CCSDiagnostic list

/// Type check results (typed tree)
type CCSCheckResults =
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

CCS depends only on:
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
4. **Native Types**: String literals have native semantics (UTF-8 `memref<?xi8>` view)
5. **SRTP**: Resolves against Alloy witnesses
6. **Firefly Integration**: HelloWorld samples compile correctly

## API Exposure Strategy

A key motivation for CCS is exposing internal FCS APIs that Firefly needs for AST/typed tree correlation. These APIs are currently private in FCS.

### APIs to Expose

| API | Source Location | Purpose |
|-----|-----------------|---------|
| Range Correlation | `Exprs.fs` + new service | Map SynExpr ranges to FSharpExpr for Baker |
| Symbol Context | `CheckDeclarations.fs` | Binding scopes for def-use analysis |
| SRTP State | `ConstraintSolver.fs` | Witness resolution details for native SRTP |

### Implementation Approach

Create `src/Compiler/Service/CCSPublicAPI.fs` as a stability layer:

```fsharp
namespace FSharp.Native.Compiler.Service

/// Correlates source ranges between syntax and typed trees
type RangeCorrelationService =
    /// Get the FSharpExpr at a given source range
    member GetTypedExprAtRange: range -> FSharpExpr option

    /// Build correlation map for entire file
    member BuildCorrelationMap: FSharpImplementationFileContents -> Map<range, FSharpExpr>

/// Symbol resolution context for def-use analysis
type SymbolContextService =
    member GetContextAtPosition: int * int -> SymbolContext
    member GetDefinitions: unit -> (FSharpSymbol * range) list
    member GetUses: FSharpSymbol -> range list

/// SRTP resolution details for native witness generation
type SRTPService =
    member GetResolutions: FSharpImplementationFileContents -> SRTPResolutionInfo list

type SRTPResolutionInfo = {
    TraitConstraint: TraitConstraintInfo
    CallSite: range
    TypeArguments: FSharpType list
    ResolvedWitness: FSharpMemberOrFunctionOrValue option
    IsNativeWitness: bool
}
```

### Files to Modify for API Exposure

- `src/Compiler/Symbols/Exprs.fs` - Already has `FSharpExpr.Range`; expose correlation building
- `src/Compiler/Checking/ConstraintSolver.fsi` - Expose `TraitConstraintInfo` resolution trace
- `src/Compiler/Service/FSharpCheckerResults.fs` - Add accessors for new services

---

## Native Type System Integration

### TcGlobals.fs Modifications

The type universe is defined in `TcGlobals.fs`. Add native types alongside BCL types:

```
TcGlobals.fs modifications:
├── Modify string_ty to have native semantics (UTF-8 `memref<?xi8>` view)
├── Modify option_tcr to have native semantics (voption: value type, never null)
├── Modify array_tcr to have native semantics (a `memref<?xT>` view)
├── Add memory region phantom types (Peripheral, SRAM, Flash, Arena, Stack)
└── Add access kind phantom types (ReadOnly, WriteOnly, ReadWrite)
```

### New Files to Create

| File | Purpose |
|------|---------|
| `src/Compiler/Checking/NativeTypes.fs` | Native type constructors and definitions |
| `src/Compiler/Checking/NativeSRTP.fs` | Alloy witness registry and resolution |
| `src/Compiler/TypedTree/PeripheralTypes.fs` | Farscape peripheral descriptor types |
| `src/Compiler/Checking/PeripheralAttributes.fs` | Farscape attribute recognition |

### CheckExpressions.fs String Literal Modification

The critical change is at ~line 7342 in `CheckExpressions.fs`:

```fsharp
// CURRENT (produces System.String)
| false, LiteralArgumentType.Inline ->
    TcPropagatingExprLeafThenConvert cenv overallTy g.string_ty env m (fun () ->
        mkString g m s, tpenv)

// CCS (string with native UTF-8 `memref<?xi8>` view semantics)
| false, LiteralArgumentType.Inline ->
    TcPropagatingExprLeafThenConvert cenv overallTy g.string_ty env m (fun () ->
        mkString g m s, tpenv)  // Same API, string_ty now has native semantics
```

---

## BAREWire/Farscape Integration Architecture

### Memory Region Types

CCS must understand BAREWire's memory region types as first-class:

```fsharp
type MemoryRegionKind =
    | Peripheral    // Memory-mapped I/O (volatile, no cache)
    | SRAM          // General RAM
    | Flash         // Read-only at runtime
    | SystemControl // ARM system registers
    | Arena         // Compiler-managed temporary
    | Stack         // Thread-local
```

These are represented as phantom type parameters using FSharp.UMX measures:

```fsharp
type Ptr<'T, [<Measure>] 'region, [<Measure>] 'access>
type Memory<'T, [<Measure>] 'region>
```

### Access Kind Enforcement

Access kinds constrain operations on memory pointers:

| Kind | Read | Write | CMSIS Equivalent |
|------|------|-------|------------------|
| `ReadOnly` | YES | NO | `__I` |
| `WriteOnly` | NO | YES | `__O` |
| `ReadWrite` | YES | YES | `__IO` |

**Constraint Solver Integration:**
- Add `AccessConstraintInfo` alongside `TraitConstraintInfo`
- `SolveAccessConstraint` checks operation compatibility
- Error FS8001: Cannot read write-only pointer
- Error FS8002: Cannot write read-only pointer

### Farscape Peripheral Descriptors

CCS recognizes Farscape-generated peripheral types:

```fsharp
type PeripheralTypeInfo = {
    Family: string                      // e.g., "GPIO"
    Instances: Map<string, uint64>      // GPIOA -> 0x48000000
    Registers: Map<string, RegisterInfo>
    RegionKind: MemoryRegionKind
}

type RegisterInfo = {
    Name: string        // "ODR", "IDR", "BSRR"
    Offset: int         // Byte offset from base
    Access: AccessKind  // ReadOnly, WriteOnly, ReadWrite
    Width: int          // Bits (8, 16, 32)
    IsVolatile: bool
}
```

**Attribute Recognition:**
- `[<PeripheralDescriptor(family, baseAddr)>]` on types
- `[<Register(name, offset, access)>]` on fields
- `[<Peripheral(instance, address)>]` on instance values

### Native SRTP Witness Resolution

CCS resolves SRTP against native witnesses before BCL method tables:

```fsharp
module NativeSRTP =
    type NativeWitness =
        | WritableString    // $ operator on strings
        | Comparable        // Comparison operators
        | Arithmetic        // Arithmetic operators
        | MemoryRegion      // Region-aware operations
        | PeripheralAccess  // Peripheral register access

    let resolveNativeWitness (g: TcGlobals) (traitInfo: TraitConstraintInfo) =
        match traitInfo.MemberName, traitInfo.SupportTypes with
        | "op_Dollar", [ty] when isStringTy g ty ->  // string has native semantics
            Some (WritableString, "Alloy.Text.WritableString.op_Dollar")
        | "LoadVolatile", [ty] when isPeripheralPtrTy g ty ->
            Some (PeripheralAccess, "Platform.Peripheral.loadVolatile")
        | _ -> None
```

---

## Expanded Phased Implementation Timeline

```
Phase 0 (Weeks 1-2): Foundation
├── Fork project file, rename namespaces
├── Remove Category 1 directories (MSBuild, IL gen, FSI)
└── Create IL stubs for remaining references
    Target: Build succeeds with stubs

Phase 1 (Weeks 2-4): Core Pruning
├── Remove heavy Service components
├── Streamline Driver
└── Target: Build < 1.5 min

Phase 2 (Weeks 4-7): Native Types
├── NativeTypes.fs with type constructors
├── TcGlobals native type integration
├── CheckExpressions literal typing (line ~7342)
└── Target: "Hello" types as string with native semantics

Phase 3 (Weeks 4-8): API Exposure [Parallel with Phase 2]
├── RangeCorrelationService
├── SymbolContextService
├── SRTPService
└── CCSPublicAPI.fs stability layer

Phase 4 (Weeks 7-10): Native SRTP
├── NativeSRTP.fs witness registry
├── ConstraintSolver integration
└── Target: $ resolves to Alloy witnesses

Phase 5 (Weeks 9-14): Memory Semantics
├── Memory region types in type system
├── Access kind constraint solving
├── Coeffect tracking preparation
├── Farscape attribute recognition
└── Target: BAREWire types type-check correctly

Phase 6 (Weeks 13-16): Integration Testing
├── Firefly integration
├── HelloWorld sample validation
└── Target: Build < 1 min, all samples pass
```

### Parallel Work Streams

```
Week:  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16

Phase 0 (Foundation)     ████
Phase 1 (Core Pruning)      ██████
Phase 2 (Native Types)         ████████████
Phase 3 (API Exposure)         ████████████████  [Parallel]
Phase 4 (Native SRTP)                ████████████
Phase 5 (Memory Sem.)                      ████████████████
Phase 6 (Integration)                                  ████████
```

---

## Related Documents

- `Firefly/docs/CCS_Architecture.md` - Firefly's CCS documentation
- `Firefly/docs/CCS_Ecosystem.md` - Cross-repository relationships
- `clef-lang-spec/docs/fidelity/CCS_Specification.md` - Language specification for native types
- `SpeakEZ/hugo/content/proposals/From Bridged To Self Hosted.md` - Long-term extraction strategy

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

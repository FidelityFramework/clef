# FNCS Phase 1 Transformation Plan

## From F# Compiler Services to F# Native Compiler Services

**Version**: 1.0
**Status**: Planning
**Last Updated**: 2025-12-18
**Author**: SpeakEZ Technologies

---

## Executive Summary

This document provides the complete, detailed transformation plan for **Phase 1** of the fsnative repository transition. Phase 1 establishes the foundation for "bridged" compilation by:

1. **Removing BCL-centric subsystems** (~92,000 lines) that have no role in native compilation
2. **Restructuring the project** for publication as `FSharp.Native.Compiler.Services`
3. **Replacing TcGlobals type registry** contents with intrinsic native types
4. **Establishing housekeeping standards** (copyright, namespaces, build configuration)

Phase 1 does NOT include the deeper semantic changes (fsil/UMX pattern absorption, FidType implementation) - those belong to Phase 2+. Phase 1 creates a clean, buildable foundation that can still function in "bridged" mode with Firefly while the native type machinery is developed.

---

## Table of Contents

1. [Strategic Context](#strategic-context)
2. [The Absorption Model](#the-absorption-model)
3. [Inventory of Changes](#inventory-of-changes)
   - [Subsystem Removal](#subsystem-removal)
   - [Files to Modify](#files-to-modify)
   - [Files to Create](#files-to-create)
4. [Housekeeping Requirements](#housekeeping-requirements)
   - [Namespace Transformation](#namespace-transformation)
   - [Copyright and Licensing](#copyright-and-licensing)
   - [Build Configuration](#build-configuration)
   - [NuGet Publication](#nuget-publication)
5. [TcGlobals Transformation](#tcglobals-transformation)
6. [Cross-References to Alloy](#cross-references-to-alloy)
7. [Execution Checklist](#execution-checklist)
8. [Validation Criteria](#validation-criteria)

---

## Strategic Context

### The Problem: Semantic Impedance

The current F# Compiler Services (FCS) makes hardcoded assumptions about the BCL (Base Class Library) type universe. When FCS encounters a string literal `"Hello"`, it types it as `System.String`. When it resolves `a + b`, it searches .NET method tables for `op_Addition`. These assumptions are baked into the type system at a fundamental level.

For Fidelity/Firefly, this creates **semantic impedance**:

- FCS produces a typed tree where `"Hello"` is `System.String`
- Firefly needs it to be `NativeStr` (UTF-8, deterministic lifetime)
- The "Baker" layer currently bridges this gap by ignoring FCS semantics
- This is wasteful - we type-check twice (once in FCS, once in Firefly)

### The Solution: Absorption

The strategic document ["Firefly: From Bridged to Self Hosted"](~/repos/SpeakEZ/hugo/content/proposals/Firefly%20Compiler%20From%20Bridged%20To%20Self%20Hosted.md) defines the **absorption strategy**:

> "fsil and UMX patterns don't just inform FNCS; they *become* FNCS. The inline ceremony disappears. The measure annotation workarounds disappear. What remains is a type system where these capabilities are reflexive."

**Key insight**: The type machinery currently defined in Alloy (NativeStr, voption, NativeArray, memory regions, access kinds) **moves INTO fsnative** as compiler intrinsics. This is NOT:

- Adding parallel native types alongside BCL types
- Pointing fslibCcu at Alloy as an external library
- Creating dual codepaths or mode switches

It IS:

- Making `string_ty` BE the native string (UTF-8, deterministic lifetime)
- Making `voption` BE the default option type
- Having the compiler KNOW these types intrinsically

### Phase 1 Scope

Phase 1 prepares the foundation by:

1. **Removing dead weight** - Subsystems with no role in native compilation
2. **Restructuring for publication** - New namespace, build configuration
3. **Preparing TcGlobals** - Understanding and documenting the type registry
4. **Establishing patterns** - Housekeeping standards for ongoing work

Phase 1 is deliberately **non-breaking for bridged mode**. After Phase 1, Firefly can still use fsnative through Baker, with the same semantics as before. The deep type absorption happens in Phase 2+.

---

## The Absorption Model

### What "Absorption" Means

The strategic document defines absorption as library patterns becoming language intrinsics. To understand this concretely, consider the current vs. target state:

#### Current State (FCS/Bridged)

```
TcGlobals.fs:
  fslibCcu → Points to FSharp.Core CCU
  string_ty → mk_MFCore_tcref fslibCcu "string" → System.String

When FCS sees "Hello":
  → CheckExpressions.fs line ~7383
  → TcPropagatingExprLeafThenConvert ... g.string_ty ...
  → Types as System.String

When Firefly receives this:
  → Baker ignores the type
  → Firefly re-resolves to NativeStr
```

#### Target State (FNCS/Absorbed)

```
TcGlobals.fs:
  v_nativestr_ty → FidType.NativeStr  (intrinsic, no CCU lookup)
  string_ty → v_nativestr_ty  (alias for compatibility)

When FNCS sees "Hello":
  → CheckExpressions.fs
  → TcPropagatingExprLeafThenConvert ... g.nativestr_ty ...
  → Types as NativeStr directly

When Firefly receives this:
  → PSG receives NativeStr
  → No re-resolution needed
```

### What Moves INTO fsnative

From the strategic document section "What Moves Into FNCS":

| Component | Current Location | After Absorption |
|-----------|-----------------|------------------|
| `NativeStr` | Alloy.Text | FNCS intrinsic (string literals type as this) |
| `voption<'T>` | Alloy.Core | FNCS intrinsic |
| `NativeArray<'T>` | Alloy.Memory | FNCS intrinsic |
| `NativePtr<'T, 'region, 'access>` | Alloy.Memory | FNCS intrinsic (with measures) |
| Inline semantics | fsil library | FNCS default behavior |
| Measure types for non-numerics | UMX library | FNCS intrinsic |
| Memory region measures | Not expressible | FNCS intrinsic |
| Access kind measures | Not expressible | FNCS intrinsic |

### What Remains in Alloy

After absorption, Alloy becomes lighter:

| Component | Purpose |
|-----------|---------|
| BCL-sympathetic API | `Console.WriteLine`, `File.ReadAllText` naming conventions |
| Collection modules | `List`, `Map`, `Set` with native implementations |
| I/O abstractions | Console, File, Network |
| Platform.Bindings | Module convention for syscall surface (Alex provides implementations) |
| BAREWire integration | Zero-copy serialization |

The key difference: after absorption, Alloy's functions USE types that the compiler knows intrinsically. Alloy no longer DEFINES what `NativeStr` is - the compiler knows.

---

## Inventory of Changes

### Subsystem Removal

The following subsystems are removed entirely in Phase 1. Each has a clear rationale based on the architectural separation.

#### AbstractIL (28,324 lines) - REMOVE

**Location**: `src/Compiler/AbstractIL/`

**Files**:
| File | Lines | Purpose |
|------|-------|---------|
| `il.fs` + `il.fsi` | ~8,000 | IL type definitions |
| `ilbinary.fs` + `ilbinary.fsi` | ~4,000 | Binary format handling |
| `ilread.fs` + `ilread.fsi` | ~6,000 | Assembly reading |
| `ilwrite.fs` + `ilwrite.fsi` | ~5,000 | Assembly writing |
| `ilreflect.fs` + `ilreflect.fsi` | ~2,500 | Reflection emit |
| `ilprint.fs`, `ilmorph.fs`, etc. | ~2,800 | Supporting utilities |

**Rationale**: FNCS outputs to PSG/MLIR, not IL. All assembly I/O is irrelevant. The IL type definitions (`ILType`, `ILMethodDef`, etc.) are pervasive throughout FCS but are not needed for native compilation.

**Impact**: Removing AbstractIL requires stubbing or removing references in:
- `TypedTree.fs` (uses `ILType` for some representations)
- `TcGlobals.fs` (uses `ILTypeRef` for attribute info)
- Driver files (assembly resolution)

---

#### CodeGen (15,522 lines) - REMOVE

**Location**: `src/Compiler/CodeGen/`

**Files**:
| File | Lines | Purpose |
|------|-------|---------|
| `IlxGen.fs` + `IlxGen.fsi` | ~10,000 | Core IL generation |
| `EraseClosures.fs` + `EraseClosures.fsi` | ~2,000 | Closure lowering |
| `EraseUnions.fs` + `EraseUnions.fsi` | ~2,000 | Union lowering |
| `IlxGenSupport.fs` + `IlxGenSupport.fsi` | ~1,500 | Generation utilities |

**Rationale**: IL generation is the entire purpose of this directory. FNCS stops at the typed tree; Alex generates MLIR.

**Impact**: Clean removal - nothing in the type-checking pipeline depends on CodeGen.

---

#### Optimize (9,739 lines) - REMOVE

**Location**: `src/Compiler/Optimize/`

**Files**:
| File | Lines | Purpose |
|------|-------|---------|
| `Optimizer.fs` + `Optimizer.fsi` | ~5,000 | Core optimization |
| `DetupleArgs.fs` | ~800 | Argument detupling |
| `InnerLambdasToTopLevelFuncs.fs` | ~1,200 | Lambda lifting |
| `LowerCalls.fs`, `LowerSequences.fs`, etc. | ~2,700 | IL-specific lowering |

**Rationale**: These are IL-level optimizations. MLIR/LLVM handles optimization for native code.

**Impact**: Clean removal - optimization runs after type checking.

---

#### Interactive (6,213 lines) - REMOVE

**Location**: `src/Compiler/Interactive/`

**Files**:
| File | Lines | Purpose |
|------|-------|---------|
| `fsi.fs` + `fsi.fsi` | ~4,500 | F# Interactive REPL |
| `FSharpInteractiveServer.fs` + `.fsi` | ~800 | Server mode |
| `fsihelp.fs`, `ControlledExecution.fs` | ~900 | Supporting utilities |

**Rationale**: FSI is a runtime REPL. FNCS is an AOT frontend. These are fundamentally incompatible.

**Impact**: Clean removal - FSI is self-contained.

---

#### vsintegration (29,183 lines) - REMOVE

**Location**: `vsintegration/src/`

**Subdirectories**:
- `FSharp.Editor/` - VS editor integration
- `FSharp.LanguageService/` - VS language service
- `FSharp.ProjectSystem.FSharp/` - VS project system
- `FSharp.VS.FSI/` - VS FSI integration

**Rationale**: Visual Studio integration is not relevant for native compilation. FidelityAC provides IDE services for native development.

**Impact**: Entire directory tree removal. No impact on compiler core.

---

#### FSharp.Build (2,866 lines) - REMOVE

**Location**: `src/FSharp.Build/`

**Files**:
| File | Lines | Purpose |
|------|-------|---------|
| `Fsc.fs` | ~800 | MSBuild Fsc task |
| `Fsi.fs` | ~300 | MSBuild Fsi task |
| `FSharpCommandLineBuilder.fs` | ~400 | Command line construction |
| `*.targets`, `*.props` | N/A | MSBuild integration files |

**Rationale**: MSBuild integration has no role. FNCS is consumed as a library by Firefly.

**Impact**: Clean removal - this is a separate project.

---

#### LegacyMSBuildResolver (489 lines) - REMOVE

**Location**: `src/LegacyMSBuildResolver/`

**Rationale**: Legacy .NET Framework assembly resolution. Irrelevant for native compilation.

---

#### SimulatedMSBuildResolver (345 lines) - REMOVE

**Location**: `src/Compiler/Facilities/SimulatedMSBuildReferenceResolver.fs`

**Rationale**: Fallback MSBuild resolver. Same as above.

---

#### Compiler Executables (499 lines) - REMOVE

**Location**: `src/fsc/` and `src/fsi/`

**Rationale**: These are entry points for standalone compiler execution. FNCS is a library consumed by Firefly.

---

#### Legacy Directory (minimal) - REMOVE

**Location**: `src/Compiler/Legacy/`

**Files**: `LegacyHostedCompilerForTesting.fs`

**Rationale**: Testing infrastructure for legacy compiler hosting.

---

### Summary: Removal by Line Count

| Subsystem | Lines | Percentage of Total |
|-----------|-------|---------------------|
| AbstractIL | 28,324 | 30.6% |
| vsintegration | 29,183 | 31.5% |
| CodeGen | 15,522 | 16.8% |
| Optimize | 9,739 | 10.5% |
| Interactive | 6,213 | 6.7% |
| FSharp.Build | 2,866 | 3.1% |
| MSBuild Resolvers | 834 | 0.9% |
| Compiler Executables | 499 | 0.5% |
| **TOTAL REMOVAL** | **~92,680** | **100%** |

---

### Files to Modify

#### TcGlobals.fs (2,010 lines) - REPLACE CONTENTS

**Location**: `src/Compiler/TypedTree/TcGlobals.fs`

**Current Structure**:
```
Lines 51-82:   FSharpLib module - namespace paths ("Microsoft.FSharp.Core")
Lines 188+:    fslibCcu parameter - CCU pointing to FSharp.Core
Lines 217:     mk_MFCore_tcref - helper to build type refs via CCU lookup
Lines 240-284: v_*_tcr - type constructor refs (string, int, bool, etc.)
Lines 424-453: v_*_ty - actual type instances
Lines 500+:    Intrinsic operators and functions
```

**Transformation Strategy**: Keep file structure, replace CCU-based lookups with intrinsic FidType definitions. See [TcGlobals Transformation](#tcglobals-transformation) section.

---

#### Driver Files - STREAMLINE

**Location**: `src/Compiler/Driver/`

**Files to Modify**:
| File | Lines | Modification |
|------|-------|--------------|
| `CompilerImports.fs` | ~2,500 | Remove MSBuild resolution paths |
| `CompilerConfig.fs` | ~1,500 | Remove IL-centric options |
| `CompilerDiagnostics.fs` | ~2,000 | Remove MSBuild error types |
| `CompilerOptions.fs` | ~1,800 | Remove IL generation options |

**Files to Remove from Driver**:
| File | Lines | Reason |
|------|-------|--------|
| `CreateILModule.fs` | ~1,500 | IL module creation |
| `StaticLinking.fs` | ~800 | Assembly linking |
| `OptimizeInputs.fs` | ~600 | IL optimization orchestration |
| `FxResolver.fs` | ~400 | .NET SDK resolution |
| `ScriptClosure.fs` | ~300 | Script dependencies |
| `BinaryResourceFormats.fs` | ~200 | Win32 resources |

---

#### Service Files - STREAMLINE

**Location**: `src/Compiler/Service/`

**Files to Remove**:
| File | Lines | Reason |
|------|-------|--------|
| `BackgroundCompiler.fs` | ~1,200 | IDE incremental - too heavy |
| `IncrementalBuild.fs` | ~800 | MSBuild-centric |
| `FSharpProjectSnapshot.fs` | ~400 | Project system |
| `FSharpWorkspace*.fs` | ~1,000 | Workspace management |
| `TransparentCompiler.fs` | ~2,000 | Advanced IDE feature |

**Files to Keep and Simplify**:
| File | Lines | Notes |
|------|-------|-------|
| `service.fs` | ~500 | Main FSharpChecker - simplify API |
| `FSharpCheckerResults.fs` | ~800 | Keep core, remove IL-related |
| `FSharpParseFileResults.fs` | ~300 | Keep as-is |
| `QuickParse.fs` | ~200 | Keep for tooling |
| `SemanticClassification.fs` | ~400 | Keep for tooling |

---

### Files to Create

#### Phase 1 Creates (Stubs/Infrastructure)

| File | Purpose | Priority |
|------|---------|----------|
| `src/Compiler/TypedTree/FidType.fs` | Native type representation (stub initially) | High |
| `src/Compiler/Checking/NativeTypes.fs` | Native type constructors (stub initially) | High |
| `src/Compiler/Service/FNCSPublicAPI.fs` | Public API stability layer | High |
| `Directory.Build.props` | Updated build configuration | High |

#### Phase 2+ Creates (Not in Phase 1)

These are documented here for context but implemented later:

| File | Purpose | Phase |
|------|---------|-------|
| `src/Compiler/Checking/NativeSRTP.fs` | Alloy witness resolution | Phase 2 |
| `src/Compiler/TypedTree/MemoryMeasures.fs` | Region/access measures | Phase 3 |
| `src/Compiler/Checking/CollectionProtocol.fs` | fsil pattern absorption | Phase 3 |

---

## Housekeeping Requirements

### Namespace Transformation

All public namespaces must be updated to reflect the new identity.

#### Namespace Mapping

| Current | New |
|---------|-----|
| `FSharp.Compiler` | `FSharp.Native.Compiler` |
| `FSharp.Compiler.Service` | `FSharp.Native.Compiler.Service` |
| `FSharp.Compiler.Symbols` | `FSharp.Native.Compiler.Symbols` |
| `FSharp.Compiler.Text` | `FSharp.Native.Compiler.Text` |
| `FSharp.Compiler.CodeAnalysis` | `FSharp.Native.Compiler.CodeAnalysis` |
| `FSharp.Compiler.Diagnostics` | `FSharp.Native.Compiler.Diagnostics` |
| `FSharp.Compiler.Syntax` | `FSharp.Native.Compiler.Syntax` |
| `FSharp.Compiler.TypedTree` | `FSharp.Native.Compiler.TypedTree` |

#### Files Requiring Namespace Updates

Every `.fs` and `.fsi` file in retained directories requires namespace updates:

```bash
# Approximate count of files requiring namespace changes
find src/Compiler -name "*.fs" -o -name "*.fsi" | wc -l
# Expected: ~150-180 files after removal
```

#### Implementation Approach

1. **Automated Find/Replace**: Use regex patterns for bulk updates
2. **Module Aliases**: Create backward-compatibility aliases where needed
3. **Verification**: Compile and fix any missed references

```bash
# Example find/replace pattern
sed -i 's/namespace FSharp\.Compiler$/namespace FSharp.Native.Compiler/g' src/Compiler/**/*.fs
sed -i 's/open FSharp\.Compiler\./open FSharp.Native.Compiler./g' src/Compiler/**/*.fs
```

---

### Copyright and Licensing

#### Current Headers

FCS files contain Microsoft copyright headers:

```fsharp
// Copyright (c) Microsoft Corporation.  All Rights Reserved.
// See License.txt in the project root for license information.
```

#### Required Changes

1. **Preserve Original Copyright**: The fork retains Microsoft's copyright for derived work
2. **Add SpeakEZ Notice**: Additions are copyright SpeakEZ Technologies
3. **Update License Reference**: Point to fsnative LICENSE file

#### New Header Format

For **modified** files:

```fsharp
// Original work Copyright (c) Microsoft Corporation.  All Rights Reserved.
// Modifications Copyright (c) 2025 SpeakEZ Technologies.
// Licensed under the MIT license. See LICENSE.txt in the project root.
```

For **new** files:

```fsharp
// Copyright (c) 2025 SpeakEZ Technologies.
// Licensed under the MIT license. See LICENSE.txt in the project root.
```

#### LICENSE.txt

Create or update `/LICENSE.txt`:

```
MIT License

Original work Copyright (c) Microsoft Corporation.
Modifications Copyright (c) 2025 SpeakEZ Technologies.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

[Standard MIT license text...]
```

---

### Build Configuration

#### Directory.Build.props Updates

**Location**: `src/Directory.Build.props` or root level

**Current State**: References Microsoft infrastructure, multi-targeting, complex SDK logic

**Required Changes**:

```xml
<Project>
  <PropertyGroup>
    <!-- Identity -->
    <Product>F# Native Compiler Services</Product>
    <Company>SpeakEZ Technologies</Company>
    <Copyright>Original work (c) Microsoft Corporation. Modifications (c) 2025 SpeakEZ Technologies.</Copyright>

    <!-- Versioning -->
    <VersionPrefix>1.0.0</VersionPrefix>
    <VersionSuffix>alpha1</VersionSuffix>

    <!-- Build Configuration -->
    <TargetFramework>net9.0</TargetFramework>
    <LangVersion>preview</LangVersion>
    <TreatWarningsAsErrors>false</TreatWarningsAsErrors>

    <!-- Output -->
    <AssemblyName>FSharp.Native.Compiler.Service</AssemblyName>
    <RootNamespace>FSharp.Native.Compiler</RootNamespace>

    <!-- Disable FCS-specific MSBuild integration -->
    <DisableFSharpCorePackageReference>true</DisableFSharpCorePackageReference>
  </PropertyGroup>

  <PropertyGroup Condition="'$(Configuration)' == 'Release'">
    <Optimize>true</Optimize>
    <DebugType>portable</DebugType>
  </PropertyGroup>
</Project>
```

#### Project File Transformation

**From**: `src/Compiler/FSharp.Compiler.Service.fsproj`
**To**: `src/Compiler/FSharp.Native.Compiler.Service.fsproj`

**Key Changes**:

1. Remove multi-targeting
2. Remove FSharp.Build project reference
3. Remove IL generation source files
4. Remove MSBuild task references
5. Add new FNCS source files
6. Simplify dependencies

```xml
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Library</OutputType>
    <TargetFramework>net9.0</TargetFramework>
    <GenerateDocumentationFile>true</GenerateDocumentationFile>
  </PropertyGroup>

  <!-- Core Dependencies -->
  <ItemGroup>
    <PackageReference Include="FSharp.Core" Version="9.0.100" />
    <PackageReference Include="System.Collections.Immutable" Version="8.0.0" />
  </ItemGroup>

  <!-- Source Files (reduced set) -->
  <ItemGroup>
    <!-- Utilities -->
    <Compile Include="Utilities\*.fs" />

    <!-- Syntax Tree -->
    <Compile Include="SyntaxTree\*.fs" />

    <!-- Lexer/Parser -->
    <Compile Include="lex.fs" />
    <Compile Include="pars.fs" />

    <!-- Type System -->
    <Compile Include="TypedTree\*.fs" />

    <!-- Checking -->
    <Compile Include="Checking\*.fs" />

    <!-- Symbols -->
    <Compile Include="Symbols\*.fs" />

    <!-- Driver (streamlined) -->
    <Compile Include="Driver\CompilerConfig.fs" />
    <Compile Include="Driver\CompilerDiagnostics.fs" />
    <Compile Include="Driver\CompilerOptions.fs" />
    <Compile Include="Driver\ParseAndCheckInputs.fs" />

    <!-- Service (streamlined) -->
    <Compile Include="Service\FNCSPublicAPI.fs" />
    <Compile Include="Service\service.fs" />
    <Compile Include="Service\FSharpCheckerResults.fs" />
    <Compile Include="Service\FSharpParseFileResults.fs" />
  </ItemGroup>
</Project>
```

---

### NuGet Publication

#### Package Identity

| Property | Value |
|----------|-------|
| Package ID | `FSharp.Native.Compiler.Service` |
| Authors | SpeakEZ Technologies |
| Description | F# Native Compiler Services - Frontend for native F# compilation |
| Tags | fsharp, compiler, native, aot |
| Repository URL | https://github.com/speakez-tech/fsnative |
| License | MIT |

#### nuspec Configuration

Create `FSharp.Native.Compiler.Service.nuspec`:

```xml
<?xml version="1.0" encoding="utf-8"?>
<package xmlns="http://schemas.microsoft.com/packaging/2012/06/nuspec.xsd">
  <metadata>
    <id>FSharp.Native.Compiler.Service</id>
    <version>$version$</version>
    <title>F# Native Compiler Services</title>
    <authors>SpeakEZ Technologies</authors>
    <owners>SpeakEZ Technologies</owners>
    <requireLicenseAcceptance>false</requireLicenseAcceptance>
    <license type="expression">MIT</license>
    <projectUrl>https://github.com/speakez-tech/fsnative</projectUrl>
    <description>
      F# Native Compiler Services provides parsing, type checking, and
      symbol resolution for native F# compilation. It is the frontend
      for the Fidelity framework's native compilation pipeline.
    </description>
    <copyright>Original work (c) Microsoft Corporation. Modifications (c) 2025 SpeakEZ Technologies.</copyright>
    <tags>fsharp compiler native aot fidelity</tags>
    <dependencies>
      <group targetFramework="net9.0">
        <dependency id="FSharp.Core" version="9.0.100" />
        <dependency id="System.Collections.Immutable" version="8.0.0" />
      </group>
    </dependencies>
  </metadata>
</package>
```

---

## TcGlobals Transformation

### Understanding TcGlobals Structure

TcGlobals.fs is the **type universe registry** - the central location where the compiler's known types are defined. Understanding its structure is essential for Phase 2 type absorption.

#### Current Architecture (Lines 1-500)

```fsharp
// Line 51-82: FSharpLib module defines namespace paths
module FSharpLib =
    let Root = "Microsoft.FSharp"
    let Core = Root + ".Core"
    // ...

// Line 188: TcGlobals class takes fslibCcu as constructor parameter
type TcGlobals(..., fslibCcu: CcuThunk, ...) =

    // Line 217: Helper to build type refs via CCU lookup
    let mk_MFCore_tcref ccu n = mkNonLocalTyconRef2 ccu CorePathArray n

    // Lines 240-284: Type constructor references (TCRs)
    let v_string_tcr = mk_MFCore_tcref fslibCcu "string"
    let v_int32_tcr  = mk_MFCore_tcref fslibCcu "int32"
    let v_bool_tcr   = mk_MFCore_tcref fslibCcu "bool"
    // ... 40+ more type references

    // Lines 424-453: Actual type instances
    let v_string_ty = mkNonGenericTy v_string_tcr
    let v_int32_ty  = mkNonGenericTy v_int32_tcr
    let v_bool_ty   = mkNonGenericTy v_bool_tcr
    // ... corresponding types
```

#### The Pattern

The current pattern is:
1. **fslibCcu** points to an external CCU (FSharp.Core)
2. **mk_MFCore_tcref** looks up types by name in that CCU
3. Types are **resolved at runtime** by name matching

This is fundamentally a **late-binding** approach - the compiler discovers types by querying external metadata.

#### Target Architecture

The target pattern is:
1. **FidType** is a discriminated union defined IN fsnative
2. Types are **known at compile time** as cases of FidType
3. No CCU lookup needed - the compiler IS the type definition

```fsharp
// NEW: FidType discriminated union (defined in src/Compiler/TypedTree/FidType.fs)
[<RequireQualifiedAccess>]
type FidType =
    | Unit
    | Bool
    | Int8 | Int16 | Int32 | Int64 | Int128
    | UInt8 | UInt16 | UInt32 | UInt64 | UInt128
    | Float32 | Float64
    | NativeInt | NativeUInt
    | Char
    | NativeStr    // THE string type
    | VOption of element: FidType
    | NativeArray of element: FidType * region: MemoryRegion
    | FatPtr of pointee: FidType * alignment: Alignment * region: MemoryRegion * access: AccessKind
    | Span of element: FidType * lifetime: Lifetime * region: MemoryRegion
    | Tuple of elements: FidType list * layout: TupleLayout
    | Record of entity: FidEntity * fields: FidField list * layout: RecordLayout
    | Union of entity: FidEntity * cases: FidUnionCase list * layout: UnionLayout
    | Function of arg: FidType * ret: FidType * coeffect: Coeffect * transparency: Transparency
    | TypeVar of typar: FidTypar
    | App of tycon: FidTycon * args: FidType list
    | Owned of inner: FidType
    | Borrowed of inner: FidType * lifetime: Lifetime * mutability: Mutability
    | Shared of inner: FidType * refCounting: RefCountStrategy option
    | Measure of baseType: FidType * measure: FidMeasure

// MODIFIED: TcGlobals uses intrinsic types
type TcGlobals(...) =  // No fslibCcu parameter

    // Types are intrinsic, not looked up
    let v_nativestr_ty = FidType.NativeStr
    let v_int32_ty = FidType.Int32
    let v_bool_ty = FidType.Bool

    // Backward compatibility alias
    let v_string_ty = v_nativestr_ty
```

### Phase 1 TcGlobals Work

In Phase 1, we:

1. **Document** the complete structure of TcGlobals (done above)
2. **Create stub** `FidType.fs` with the discriminated union skeleton
3. **Do NOT yet replace** the CCU-based mechanism (that's Phase 2)
4. **Prepare** for the transformation by understanding all call sites

#### TcGlobals Call Site Analysis

Files that reference `g.string_ty`, `g.int_ty`, etc.:

```bash
grep -rn "g\.string_ty\|g\.int_ty\|g\.bool_ty" src/Compiler/Checking/
# Expected: ~50-100 references across multiple files
```

These will need updates in Phase 2 when the type system changes.

---

## Cross-References to Alloy

### Type Correspondence

This section documents the correspondence between Alloy types and their FNCS intrinsic equivalents. This is essential for understanding what "absorption" means concretely.

#### Alloy/src/Core/Text.fs → FidType.NativeStr

**Alloy Definition** (current):

```fsharp
// ~/repos/Alloy/src/Core/Text.fs
[<Struct>]
type NativeStr =
    val mutable private buffer: nativeptr<byte>
    val mutable private length: int
    // UTF-8 encoded, null-terminated, deterministic lifetime
```

**FNCS Absorption** (target):

```fsharp
// fsnative/src/Compiler/TypedTree/FidType.fs
type FidType =
    // ...
    | NativeStr  // Compiler knows this IS the string type
    // ...
```

**Key Insight**: After absorption, the compiler doesn't look up "what is NativeStr" from Alloy metadata. The compiler KNOWS NativeStr intrinsically - its layout, semantics, and operations are built-in.

---

#### Alloy/src/Core/Core.fs → FidType.VOption

**Alloy Definition** (current):

```fsharp
// ~/repos/Alloy/src/Core/Core.fs
[<Struct>]
type voption<'T> =
    | ValueNone
    | ValueSome of 'T
    // Value type, stack-allocated
```

**FNCS Absorption** (target):

```fsharp
// fsnative/src/Compiler/TypedTree/FidType.fs
type FidType =
    // ...
    | VOption of element: FidType
    // ...
```

**Semantic Difference from FCS**:
- FCS `option<'T>` is a reference type (heap-allocated)
- FNCS `voption<'T>` is a value type (stack-allocated)
- After absorption, `Some 42` types as `VOption Int32`, not `Option Int32`

---

#### Alloy/src/Core/Memory.fs → FidType.NativeArray, FidType.FatPtr

**Alloy Definition** (current):

```fsharp
// ~/repos/Alloy/src/Core/Memory.fs
[<Struct>]
type NativeArray<'T> =
    val mutable private buffer: nativeptr<'T>
    val mutable private length: int
    val mutable private capacity: int

[<Struct>]
type FatPtr<'T, 'Align, 'Owner> =
    val Pointer: nativeptr<'T>
    val Length: int
    val Capacity: int
```

**FNCS Absorption** (target):

```fsharp
type FidType =
    // ...
    | NativeArray of element: FidType * bounds: ArrayBounds * region: MemoryRegion
    | FatPtr of pointee: FidType * alignment: Alignment * region: MemoryRegion * access: AccessKind
    // ...
```

---

#### fsil Patterns → Default Transparency

**fsil Pattern** (current):

```fsharp
// ~/repos/fsil - library requires explicit [<InlineIfLambda>]
let inline iter ([<InlineIfLambda>] f) (x: _) : unit =
    Internal.Iterate.Invoke(x, f)
```

**FNCS Absorption** (target):

```fsharp
// Functions are transparent by default
let iter f x = Internal.Iterate.Invoke(x, f)  // No 'inline' needed

// Opt-out via [<Opaque>] attribute when opacity is desired
[<Opaque>]
let opaqueFunction x = ...
```

---

#### UMX Patterns → First-Class Measures

**UMX Pattern** (current):

```fsharp
// ~/repos/FSharp.UMX - workaround for non-numeric measures
[<MeasureAnnotatedAbbreviation>] type string<[<Measure>] 'm> = string
let customerId: string<customerId> = %"cust-123"
```

**FNCS Absorption** (target):

```fsharp
// Native types defined WITH measure parameters
type NativePtr<'T, [<Measure>] 'region, [<Measure>] 'access>

// Memory regions as first-class measures
[<Measure>] type peripheral
[<Measure>] type sram
[<Measure>] type flash

// Access kinds as first-class measures
[<Measure>] type readOnly
[<Measure>] type writeOnly
[<Measure>] type readWrite
```

---

### Reference Documents

| Document | Location | Purpose |
|----------|----------|---------|
| Strategic Proposal | `~/repos/SpeakEZ/hugo/content/proposals/Firefly Compiler From Bridged To Self Hosted.md` | High-level absorption strategy |
| Alloy Source | `~/repos/Alloy/src/` | Native type implementations |
| fsil Source | `~/repos/fsil/` | Inline-by-default patterns |
| UMX Source | `~/repos/FSharp.UMX/` | Phantom type patterns |
| Firefly CLAUDE.md | `~/repos/Firefly/CLAUDE.md` | Architecture principles |

---

## Execution Checklist

### Pre-Removal Preparation

- [ ] Create branch `phase1-transformation`
- [ ] Backup current build state
- [ ] Document current build time (baseline)
- [ ] Document current binary size (baseline)
- [ ] Run full test suite (baseline)

### Subsystem Removal

- [ ] Remove `src/Compiler/AbstractIL/` (28,324 lines)
- [ ] Remove `src/Compiler/CodeGen/` (15,522 lines)
- [ ] Remove `src/Compiler/Optimize/` (9,739 lines)
- [ ] Remove `src/Compiler/Interactive/` (6,213 lines)
- [ ] Remove `vsintegration/` (29,183 lines)
- [ ] Remove `src/FSharp.Build/` (2,866 lines)
- [ ] Remove `src/LegacyMSBuildResolver/` (489 lines)
- [ ] Remove `src/Compiler/Facilities/SimulatedMSBuildReferenceResolver.*` (345 lines)
- [ ] Remove `src/fsc/` and `src/fsi/` (499 lines)
- [ ] Remove `src/Compiler/Legacy/` (minimal)

### Driver/Service Streamlining

- [ ] Remove Driver files: CreateILModule, StaticLinking, OptimizeInputs, FxResolver, ScriptClosure, BinaryResourceFormats
- [ ] Remove Service files: BackgroundCompiler, IncrementalBuild, FSharpProjectSnapshot, FSharpWorkspace*, TransparentCompiler
- [ ] Modify `CompilerImports.fs` - remove MSBuild resolution
- [ ] Modify `CompilerConfig.fs` - remove IL options
- [ ] Create stubs for removed dependencies

### Housekeeping

- [ ] Update all namespaces (`FSharp.Compiler.*` → `FSharp.Native.Compiler.*`)
- [ ] Update all copyright headers
- [ ] Create/update `LICENSE.txt`
- [ ] Update `Directory.Build.props`
- [ ] Rename project file to `FSharp.Native.Compiler.Service.fsproj`
- [ ] Update project file contents (remove IL sources, add new sources)
- [ ] Create `FSharp.Native.Compiler.Service.nuspec`

### New Files

- [ ] Create `src/Compiler/TypedTree/FidType.fs` (stub)
- [ ] Create `src/Compiler/Checking/NativeTypes.fs` (stub)
- [ ] Create `src/Compiler/Service/FNCSPublicAPI.fs`

### Validation

- [ ] Build succeeds
- [ ] Build time < 90 seconds (target: < 60 seconds)
- [ ] Binary size < 10 MB (target: < 5 MB)
- [ ] Firefly can reference and use FNCS in bridged mode
- [ ] HelloWorld sample compiles through full pipeline

---

## Validation Criteria

### Build Metrics

| Metric | Baseline (FCS) | Phase 1 Target |
|--------|----------------|----------------|
| Source Files | ~200 | ~80 |
| Lines of Code | ~400,000 | ~150,000 |
| Clean Build Time | ~3 min | < 90 sec |
| Binary Size | ~15 MB | < 10 MB |

### Functional Requirements

1. **Parsing**: All F# syntax parses correctly
2. **Type Checking**: Type checking completes for valid code
3. **Diagnostics**: Errors and warnings are reported correctly
4. **Symbol Resolution**: Symbols resolve for IDE features
5. **Typed Tree**: FSharpExpr is available for Firefly consumption
6. **Bridged Mode**: Firefly pipeline works with FNCS in bridged mode

### Integration Test: HelloWorld

```fsharp
// Sample that must work through full pipeline
open Alloy.Console

[<EntryPoint>]
let main _ =
    WriteLine "Hello, World!"
    0
```

After Phase 1:
- FNCS parses and type-checks this
- Firefly receives typed tree
- Baker bridges types (still in bridged mode)
- Native binary executes correctly

---

## Appendix A: Complete File Removal List

### Directories to Delete Entirely

```
src/Compiler/AbstractIL/
src/Compiler/CodeGen/
src/Compiler/Optimize/
src/Compiler/Interactive/
src/Compiler/Legacy/
src/FSharp.Build/
src/LegacyMSBuildResolver/
src/fsc/
src/fsi/
vsintegration/
```

### Individual Files to Delete

**From src/Compiler/Driver/**:
- `CreateILModule.fs`, `CreateILModule.fsi`
- `StaticLinking.fs`, `StaticLinking.fsi`
- `OptimizeInputs.fs`, `OptimizeInputs.fsi`
- `FxResolver.fs`, `FxResolver.fsi`
- `ScriptClosure.fs`, `ScriptClosure.fsi`
- `BinaryResourceFormats.fs`, `BinaryResourceFormats.fsi`

**From src/Compiler/Service/**:
- `BackgroundCompiler.fs`, `BackgroundCompiler.fsi`
- `IncrementalBuild.fs`, `IncrementalBuild.fsi`
- `FSharpProjectSnapshot.fs`
- `FSharpWorkspace.fs`
- `FSharpWorkspaceQuery.fs`
- `FSharpWorkspaceState.fs`
- `TransparentCompiler.fs`, `TransparentCompiler.fsi`
- `ServiceAssemblyContent.fs`, `ServiceAssemblyContent.fsi`

**From src/Compiler/Facilities/**:
- `SimulatedMSBuildReferenceResolver.fs`, `SimulatedMSBuildReferenceResolver.fsi`

---

## Appendix B: Namespace Transformation Script

```bash
#!/bin/bash
# namespace-transform.sh
# Run from fsnative repository root

# Backup first
cp -r src src.backup

# Transform namespaces in all F# files
find src/Compiler -name "*.fs" -o -name "*.fsi" | while read file; do
    # Namespace declarations
    sed -i 's/namespace FSharp\.Compiler$/namespace FSharp.Native.Compiler/g' "$file"
    sed -i 's/namespace FSharp\.Compiler\./namespace FSharp.Native.Compiler./g' "$file"

    # Open statements
    sed -i 's/open FSharp\.Compiler$/open FSharp.Native.Compiler/g' "$file"
    sed -i 's/open FSharp\.Compiler\./open FSharp.Native.Compiler./g' "$file"

    # Module declarations
    sed -i 's/module FSharp\.Compiler\./module FSharp.Native.Compiler./g' "$file"

    # Type references in code
    sed -i 's/FSharp\.Compiler\./FSharp.Native.Compiler./g' "$file"
done

echo "Namespace transformation complete. Backup at src.backup/"
```

---

## Appendix C: Copyright Header Update Script

```bash
#!/bin/bash
# copyright-update.sh
# Run from fsnative repository root

NEW_HEADER='// Original work Copyright (c) Microsoft Corporation.  All Rights Reserved.
// Modifications Copyright (c) 2025 SpeakEZ Technologies.
// Licensed under the MIT license. See LICENSE.txt in the project root.'

find src/Compiler -name "*.fs" -o -name "*.fsi" | while read file; do
    # Check if file has Microsoft copyright
    if grep -q "Microsoft Corporation" "$file"; then
        # Replace first copyright block
        sed -i '1,/^$/c\'"$NEW_HEADER"'\n' "$file"
    fi
done

echo "Copyright headers updated."
```

---

## Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-12-18 | Claude/SpeakEZ | Initial Phase 1 transformation plan |

---

*This document is part of the F# Native Compiler Services (FNCS) project. For questions or clarifications, contact SpeakEZ Technologies.*

# CCS Phase 1 Transformation Plan

## From F# Compiler Services to Clef Compiler Service

**Version**: 1.0
**Status**: Planning
**Last Updated**: 2025-12-18
**Author**: SpeakEZ Technologies

---

## Executive Summary

This document provides the complete, detailed transformation plan for **Phase 1** of the clef repository transition. Phase 1 establishes the foundation for "bridged" compilation by:

1. **Removing BCL-centric subsystems** (~92,000 lines) that have no role in native compilation
2. **Restructuring the project** for publication as `FSharp.Native.Compiler.Services`
3. **Replacing TcGlobals type registry** contents with intrinsic native types
4. **Establishing housekeeping standards** (copyright, namespaces, build configuration)

Phase 1 creates a clean, buildable foundation that can function in "bridged" mode with Firefly while the native type machinery is developed.

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

For Fidelity/Firefly, this creates significant **semantic impedance mismatches**:

- FCS produces a typed tree where `"Hello"` is `System.String` (UTF-16, GC-managed)
- Firefly needs `string` to mean something different (UTF-8, deterministic lifetime)
- The "Baker" layer currently bridges this gap by ignoring FCS semantics
- This is wasteful - we type-check twice (once in FCS, once in Firefly)

### The Solution: Absorption

The strategic document ["Firefly: From Bridged to Self Hosted"](~/repos/SpeakEZ/hugo/content/proposals/Firefly%20Compiler%20From%20Bridged%20To%20Self%20Hosted.md) defines the **absorption strategy**:

> "fsil and UMX patterns don't just inform CCS; they *become* CCS. The inline ceremony disappears. The measure annotation workarounds disappear. What remains is a type system where these capabilities are reflexive."

**Key insight**: The type semantics currently defined in Alloy **move INTO Clef** as compiler intrinsics. Users continue to write `string`, `option`, `array` - the same F# types they always use. What changes is what those types *mean*. This is NOT:

- Adding new type names that users must learn
- Pointing fslibCcu at Alloy as an external library
- Creating dual codepaths or mode switches

It IS:

- Making `string` intrinsically mean UTF-8 encoded, deterministic lifetime
- Making `option` intrinsically mean value type, zero-cost None
- Having the compiler KNOW native semantics for all standard types

### Phase 1 Scope

Phase 1 prepares the foundation by:

1. **Removing dead weight** - Subsystems with no role in native compilation
2. **Restructuring for publication** - New namespace, build configuration
3. **Preparing TcGlobals** - Understanding and documenting the type registry
4. **Establishing patterns** - Housekeeping standards for ongoing work

Phase 1 is deliberately **non-breaking for bridged mode**. After Phase 1, Firefly can still use Clef through Baker, with the same semantics as before. If we see reason to keep those zipper mechanics for merging AST and typed trees we will likely move them in a later phase of transformation.

---

## The Absorption Model

### What "Absorption" Means

Currently we define absorption as Alloy/fsil/UMX library patterns becoming Clef language intrinsics. To understand this concretely, consider the current vs. target state:

#### Current State (FCS/Bridged)

```
TcGlobals.fs:
  fslibCcu → Points to FSharp.Core CCU
  string_ty → mk_MFCore_tcref fslibCcu "string" → System.String

When FCS sees "Hello":
  → CheckExpressions.fs line ~7383
  → TcPropagatingExprLeafThenConvert ... g.string_ty ...
  → Types as System.String (UTF-16, GC-managed)

When Firefly receives this:
  → Baker ignores the BCL type semantics
  → Firefly re-resolves to native semantics
```

#### Target State (CCS/Absorbed)

```
TcGlobals.fs:
  string_ty → Intrinsic definition (no CCU lookup)
             Native semantics: UTF-8, deterministic lifetime

When CCS sees "Hello":
  → CheckExpressions.fs
  → TcPropagatingExprLeafThenConvert ... g.string_ty ...
  → Types as string with native semantics

When Firefly receives this:
  → PSG receives string with native semantics already attached
  → No re-resolution needed
```

### What Moves INTO Clef

From the strategic document section "What Moves Into CCS":

| F# Type | Current Semantics | After Absorption |
|---------|------------------|------------------|
| `string` | System.String (UTF-16, GC) | UTF-8 encoded, deterministic lifetime |
| `option<'T>` | Reference type, heap allocated | Value type, zero-cost None |
| `array<'T>` | System.Array (GC, boxed elements) | Contiguous memory, compile-time or runtime size |
| `nativeptr<'T>` (F#; not denotable in Clef) | Bare pointer, no safety | Region-tracked, access-kind constrained |
| Inline semantics | Requires explicit attributes | Default behavior |
| Measure types for non-numerics | UMX workaround patterns | First-class support |
| Memory region measures | Not expressible | First-class support |
| Access kind measures | Not expressible | First-class support |

### What Remains in Alloy

After absorption, Alloy becomes a pure function library:

| Component | Purpose |
|-----------|---------|
| BCL-sympathetic API | `Console.WriteLine`, `File.ReadAllText` naming conventions |
| Collection modules | `List`, `Map`, `Set` with native implementations |
| I/O abstractions | Console, File, Network |
| Platform.Bindings | Module convention for syscall surface (Alex provides implementations) |
| BAREWire integration | Zero-copy serialization |

The key difference: after absorption, Alloy's functions operate on types that the compiler defines intrinsically. Alloy provides *functions*, not *types*. When you write `Console.WriteLine "Hello"`, Alloy provides `WriteLine`, but the compiler intrinsically knows what `string` means.

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

**Rationale**: CCS outputs to PSG/MLIR, not IL. All assembly I/O is irrelevant. The IL type definitions (`ILType`, `ILMethodDef`, etc.) are pervasive throughout FCS but are not needed for native compilation.

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

**Rationale**: IL generation is the entire purpose of this directory. CCS stops at the typed tree; Alex generates MLIR.

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

**Rationale**: FSI is a runtime REPL. CCS is an AOT frontend. These are fundamentally incompatible.

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

**Rationale**: MSBuild integration has no role. CCS is consumed as a library by Firefly.

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

**Rationale**: These are entry points for standalone compiler execution. CCS is a library consumed by Firefly.

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

**Transformation Strategy**: Keep file structure, replace CCU-based lookups with intrinsic type definitions. See [TcGlobals Transformation](#tcglobals-transformation) section.

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
| `src/Compiler/TypedTree/IntrinsicTypes.fs` | Intrinsic type definitions (stub initially) | High |
| `src/Compiler/Checking/NativeSemantics.fs` | Native semantic definitions (stub initially) | High |
| `src/Compiler/Service/CCSPublicAPI.fs` | Public API stability layer | High |
| `Directory.Build.props` | Updated build configuration | High |

#### Phase 2+ Creates (Not in Phase 1)

These are documented here for context but implemented later:

| File | Purpose | Phase |
|------|---------|-------|
| `src/Compiler/Checking/IntrinsicSRTP.fs` | SRTP resolution against intrinsic types | Phase 2 |
| `src/Compiler/TypedTree/MemoryMeasures.fs` | Region/access measures | Phase 3 |
| `src/Compiler/Checking/CollectionProtocol.fs` | Transparent iteration patterns | Phase 3 |

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
2. **Add SpeakEZ Notice**: Additions are copyright Braidpoint
3. **Update License Reference**: Point to clef LICENSE file

#### New Header Format

For **modified** files:

```fsharp
// Original work Copyright (c) Microsoft Corporation.  All Rights Reserved.
// Modifications Copyright (c) 2025 Braidpoint.
// Licensed under the MIT license. See LICENSE.txt in the project root.
```

For **new** files:

```fsharp
// Copyright (c) 2025 Braidpoint.
// Licensed under the MIT license. See LICENSE.txt in the project root.
```

#### LICENSE.txt

Create or update `/LICENSE.txt`:

```
MIT License

Original work Copyright (c) Microsoft Corporation.
Modifications Copyright (c) 2025 Braidpoint.

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
    <Product>Clef Compiler Service</Product>
    <Company>SpeakEZ Technologies</Company>
    <Copyright>Original work (c) Microsoft Corporation. Modifications (c) 2025 Braidpoint.</Copyright>

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
5. Add new CCS source files
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
    <Compile Include="Service\CCSPublicAPI.fs" />
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
| Description | Clef Compiler Service - Frontend for native F# compilation |
| Tags | fsharp, compiler, native, aot |
| Repository URL | https://github.com/speakez-tech/clef |
| License | MIT |

#### nuspec Configuration

Create `FSharp.Native.Compiler.Service.nuspec`:

```xml
<?xml version="1.0" encoding="utf-8"?>
<package xmlns="http://schemas.microsoft.com/packaging/2012/06/nuspec.xsd">
  <metadata>
    <id>FSharp.Native.Compiler.Service</id>
    <version>$version$</version>
    <title>Clef Compiler Service</title>
    <authors>SpeakEZ Technologies</authors>
    <owners>SpeakEZ Technologies</owners>
    <requireLicenseAcceptance>false</requireLicenseAcceptance>
    <license type="expression">MIT</license>
    <projectUrl>https://github.com/speakez-tech/clef</projectUrl>
    <description>
      Clef Compiler Service provides parsing, type checking, and
      symbol resolution for native F# compilation. It is the frontend
      for the Fidelity framework's native compilation pipeline.
    </description>
    <copyright>Original work (c) Microsoft Corporation. Modifications (c) 2025 Braidpoint.</copyright>
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
1. Types are **known at compile time** with intrinsic native semantics
2. No CCU lookup needed - the compiler defines type semantics directly
3. User-facing type names remain the same (`string`, `option`, `int`)

```fsharp
// MODIFIED: TcGlobals defines types intrinsically
type TcGlobals(...) =  // No fslibCcu parameter needed for core types

    // Types are intrinsic with native semantics, not looked up from external CCU
    // User writes "string" → compiler knows it means UTF-8, deterministic lifetime
    let v_string_ty = IntrinsicType.String  // Native string semantics

    // User writes "option" → compiler knows it means value type, zero-cost None
    let v_option_tcr = IntrinsicType.Option  // Native option semantics

    // User writes "int" → compiler knows native machine representation
    let v_int32_ty = IntrinsicType.Int32

    // User writes "bool" → compiler knows single-bit representation
    let v_bool_ty = IntrinsicType.Bool
```

The internal representation (whether it's called `IntrinsicType`, `FidType`, or something else) is an implementation detail. What matters is that when users write standard F# types, the compiler intrinsically knows their native semantics without consulting external assembly metadata.

### Phase 1 TcGlobals Work

In Phase 1, we:

1. **Document** the complete structure of TcGlobals (done above)
2. **Create stub** for intrinsic type infrastructure (implementation detail TBD)
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

### Semantic Correspondence

This section documents what absorption means for the standard F# types. The key principle: **users write the same types they always have** (`string`, `option`, `array`). What changes is the semantic definition the compiler uses internally.

#### `string` - Native String Semantics

**Current Semantics** (FCS/BCL):
- `System.String` - UTF-16 encoded, garbage collected, immutable reference type

**Target Semantics** (CCS):
- UTF-8 encoded, null-terminated, deterministic lifetime
- When binding goes out of scope, memory is freed
- String literals have static lifetime (live in `.rodata`)

**User Experience**: No change. You write `"Hello"` and get a `string`. The difference is what `string` *means*.

---

#### `option<'T>` - Value Option Semantics

**Current Semantics** (FCS/BCL):
- Reference type, heap-allocated
- `None` is typically null, `Some x` allocates a wrapper object

**Target Semantics** (CCS):
- Value type, stack-allocated by default
- `None` has zero runtime cost (just a tag)
- No heap allocation for simple option values

**User Experience**: No change. You write `Some 42` and `None`. The difference is that `option` is now a value type with zero-cost `None`.

---

#### `array<'T>` - Native Array Semantics

**Current Semantics** (FCS/BCL):
- `System.Array` - GC-managed, bounds-checked at runtime, boxed header

**Target Semantics** (CCS):
- Contiguous memory, no boxed header
- Compile-time size tracking when size is known
- Region-aware (stack, heap, arena)

**User Experience**: No change. You write `[| 1; 2; 3 |]` and get an `array`. The difference is the memory representation and lifetime management.

---

#### Inline Semantics - Default Transparency

**Current State** (fsil library workaround):

```fsharp
// Requires explicit [<InlineIfLambda>] ceremony
let inline iter ([<InlineIfLambda>] f) (x: _) : unit =
    Internal.Iterate.Invoke(x, f)
```

**Target Semantics** (CCS):

```fsharp
// Functions are transparent by default - no ceremony needed
let iter f x = Internal.Iterate.Invoke(x, f)

// Opt-out via [<Opaque>] when opacity is desired
[<Opaque>]
let opaqueFunction x = ...
```

**User Experience**: Less boilerplate. The `inline` keyword and `[<InlineIfLambda>]` ceremony become unnecessary for most code.

---

#### Measures on Non-Numeric Types

**Current State** (UMX library workaround):

```fsharp
// UMX provides workaround for measures on strings, etc.
[<MeasureAnnotatedAbbreviation>] type string<[<Measure>] 'm> = string
let customerId: string<customerId> = %"cust-123"
```

**Target Semantics** (CCS):

```fsharp
// Measures work naturally on any type
let customerId: string<customerId> = "cust-123"  // No % operator needed

// Memory regions and access kinds as measures
let ptr: Ptr<byte, Sram, ReadWrite> = ...
```

**User Experience**: Measures become first-class on all types, not just numeric. The UMX workarounds become unnecessary.

---

### Reference Documents

| Document | Location | Purpose |
|----------|----------|---------|
| Strategic Proposal | `~/repos/SpeakEZ/hugo/content/proposals/Firefly Compiler From Bridged To Self Hosted.md` | High-level absorption strategy |
| Alloy Source | `~/repos/Alloy/src/` | Function library (reference for API surface) |
| fsil Source | `~/repos/fsil/` | Inline-by-default patterns (to be absorbed) |
| UMX Source | `~/repos/FSharp.UMX/` | Phantom type patterns (to be absorbed) |
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

- [ ] Create `src/Compiler/TypedTree/IntrinsicTypes.fs` (stub)
- [ ] Create `src/Compiler/Checking/NativeSemantics.fs` (stub)
- [ ] Create `src/Compiler/Service/CCSPublicAPI.fs`

### Validation

- [ ] Build succeeds
- [ ] Build time < 90 seconds (target: < 60 seconds)
- [ ] Binary size < 10 MB (target: < 5 MB)
- [ ] Firefly can reference and use CCS in bridged mode
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
6. **Bridged Mode**: Firefly pipeline works with CCS in bridged mode

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
- CCS parses and type-checks this
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
# Run from clef repository root

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
# Run from clef repository root

NEW_HEADER='// Original work Copyright (c) Microsoft Corporation.  All Rights Reserved.
// Modifications Copyright (c) 2025 Braidpoint.
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

*This document is part of the Clef Compiler Service (CCS) project. For questions or clarifications, contact SpeakEZ Technologies.*

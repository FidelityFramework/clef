# F# Native Compiler Services (FNCS)

## Overview

FNCS (F# Native Compiler Services) is a pruned fork of the F# Compiler Services (FCS) optimized for native compilation. It provides the frontend for the Fidelity framework, producing typed abstract syntax trees and resolved SRTP constraints that flow to Firefly for native code generation.

**Key Differences from FCS:**

| Aspect | FCS | FNCS |
|--------|-----|------|
| Target | .NET runtime | Native binaries |
| Type universe | BCL types (System.String, etc.) | Standard F# types with native semantics |
| SRTP resolution | .NET method tables | Alloy witness hierarchy |
| Output | IL generation | Typed tree + SRTP metadata |
| Dependencies | Full MSBuild, project system | Minimal, no IL generation |

## Relationship to Fidelity Ecosystem

```
┌─────────────────────────────────────────────────────────────────┐
│                     Fidelity Ecosystem                          │
│                                                                 │
│  fsnative-spec          fsnative           Firefly              │
│  ┌─────────────┐       ┌─────────────┐    ┌─────────────┐      │
│  │ F# Native   │       │ FNCS        │    │ PSG/Alex    │      │
│  │ Language    │──────▶│ Compiler    │───▶│ Native      │      │
│  │ Spec        │ impl  │ Services    │uses│ Pipeline    │      │
│  └─────────────┘       └─────────────┘    └─────────────┘      │
│        │                     │                   │              │
│        ▼                     ▼                   ▼              │
│   Normative rules      Typed tree +        MLIR → LLVM         │
│   for native types     SRTP resolution     → Native            │
└─────────────────────────────────────────────────────────────────┘
```

- **fsnative-spec** defines the normative rules FNCS must implement
- **FNCS** (this repository) implements the F# Native type system
- **Firefly** consumes FNCS output for native code generation

## What FNCS Provides

### 1. Native Type Resolution

String literals, option types, and arrays resolve to native types:

```fsharp
// F# syntax
let greeting = "Hello"        // Standard F#: System.String
                              // FNCS: string with native semantics (UTF-8 fat pointer)

let maybeValue = Some 42      // Standard F#: int option (reference)
                              // FNCS: int voption (value type)
```

### 2. SRTP Resolution Against Alloy

Statically resolved type parameters resolve against the Alloy witness hierarchy:

```fsharp
let inline add a b = a + b

// Standard F#: Searches System.Int32.op_Addition
// FNCS: Searches Alloy.BasicOps, finds Add<int>
```

### 3. Exposed APIs for Firefly Integration

FNCS exposes internal APIs that FCS keeps private:

| API | Purpose |
|-----|---------|
| `RangeCorrelationService` | Map SynExpr ranges to FSharpExpr for PSG construction |
| `SymbolContextService` | Binding scopes for def-use analysis |
| `SRTPService` | Witness resolution details for native SRTP |

## Quick Start

### Building FNCS

```bash
cd ~/repos/fsnative
dotnet build src/FSharp.Compiler.Service/FSharp.Compiler.Service.fsproj
```

### Using with Firefly

FNCS is referenced as a project dependency in Firefly's `.fsproj`:

```xml
<ProjectReference Include="$(FsnativePath)/src/FSharp.Compiler.Service/FSharp.Compiler.Service.fsproj" />
```

Firefly calls FNCS for parsing and type checking:

```fsharp
// In Firefly's FCS integration
let checker = FSharpChecker.Create()
let parseResults, checkResults = checker.ParseAndCheckFileInProject(...)

// Extract typed tree and SRTP resolutions
let typedTree = checkResults.ImplementationFile
let srtpResolutions = FNCSPublicAPI.getSRTPResolutions checkResults
```

## Directory Structure

```
fsnative/
├── docs/
│   └── fidelity/
│       ├── README.md                 # This file
│       └── FNCS_Pruning_Plan.md      # Implementation roadmap
├── src/
│   └── Compiler/
│       ├── Checking/                 # Type checking, SRTP
│       │   ├── CheckExpressions.fs   # Literal type resolution
│       │   ├── ConstraintSolver.fs   # SRTP resolution
│       │   ├── NativeTypes.fs        # (NEW) Native type constructors
│       │   └── NativeSRTP.fs         # (NEW) Alloy witness resolution
│       ├── Service/
│       │   ├── FSharpCheckerResults.fs
│       │   └── FNCSPublicAPI.fs      # (NEW) Stability layer
│       ├── Symbols/
│       │   └── Exprs.fs              # FSharpExpr API
│       └── TypedTree/
│           ├── TcGlobals.fs          # Type universe
│           └── PeripheralTypes.fs    # (NEW) Farscape descriptors
└── tests/
```

## Documentation

| Document | Description |
|----------|-------------|
| [FNCS_Pruning_Plan.md](FNCS_Pruning_Plan.md) | Detailed implementation roadmap with phases |
| [fsnative-spec](https://github.com/user/fsnative-spec) | Normative language specification |
| [Firefly FNCS_Ecosystem.md](../../../Firefly/docs/FNCS_Ecosystem.md) | How all components integrate |

## Implementation Status

See [FNCS_Pruning_Plan.md](FNCS_Pruning_Plan.md) for the phased implementation timeline:

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 0 | Foundation (fork, rename, initial pruning) | Pending |
| Phase 1 | Core Pruning (remove MSBuild, IL gen) | Pending |
| Phase 2 | Native Type Semantics (string, option with native semantics) | Pending |
| Phase 3 | API Exposure (Range correlation, SRTP) | Pending |
| Phase 4 | Native SRTP (Alloy witnesses) | Pending |
| Phase 5 | Memory Semantics (BAREWire/Farscape) | Future |
| Phase 6 | Integration Testing | Future |

## Contributing

FNCS follows the architectural principles documented in:
- Serena memory: `architecture_principles`
- Serena memory: `fncs_architecture`

Key constraints:
1. No BCL type dependencies in the native type path
2. All changes must preserve typed tree structure for Firefly correlation
3. New APIs go through `FNCSPublicAPI.fs` stability layer

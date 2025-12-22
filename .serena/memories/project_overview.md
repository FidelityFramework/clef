# FSharpNative Compiler Services (FNCS) Project Overview

## Purpose

FNCS (FSharpNative Compiler Services) is a fork of F# Compiler Services (FCS) modified to support native-first compilation in the Fidelity framework ecosystem. It provides the core compiler infrastructure for:

1. **Firefly Compiler**: AOT F# compiler targeting native binaries
2. **Native type resolution**: Compile-time type checking without BCL dependencies
3. **Fidelity integration**: Support for `.fidproj` projects and Alloy library

## Naming Convention

The project uses consistent "Native" insertion for native-first components:

| Original | Native Version |
|----------|---------------|
| FSharp.Compiler.Service | FSharpNative.Compiler.Service |
| FCS | FNCS |
| fcs-samples | fncs-samples |
| FCSBenchmarks | FNCSBenchmarks |

## Architecture

### Core Components

- **src/Compiler/**: Core compiler implementation
  - `FSharpNative.Compiler.Service.fsproj` - Main compiler service library
  - Type checking, parsing, semantic analysis

- **src/FSharp.Core/**: F# Core library (runtime support)

- **src/fsc/**: F# compiler executable

- **src/fsi/**: F# Interactive

### Key Dependencies

- .NET SDK (see global.json for version)
- Uses MSBuild for project loading

## Development Goals

### Phase 1: Native Type Resolution
- Modify type resolution to work without BCL/mscorlib
- Support Alloy library as alternative standard library
- Enable freestanding compilation mode

### Phase 2: FIDPROJ Support
- Coordinate with FSNAC (FsNativeAutoComplete) for IDE support
- Parse TOML-based project files
- Generate FSharpProjectOptions for native projects

### Phase 3: Firefly Integration
- Provide semantic analysis for Firefly's PSG construction
- Support SRTP resolution for native types
- Enable incremental compilation support

## Building

```bash
./build.sh  # or Build.cmd on Windows
dotnet build FSharpNative.Compiler.Service.sln
```

## Related Projects

- **Firefly**: AOT F# compiler consuming FNCS
- **FSNAC**: FsNativeAutoComplete - LSP server using FNCS
- **Alloy**: Native F# library (BCL replacement)
- **fsnative-spec**: F# Native Language Specification fork

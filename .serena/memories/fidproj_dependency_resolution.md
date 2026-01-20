# Fidproj Dependency Resolution

## Overview

The `SourceResolver` module in `/src/Compiler/Project/SourceResolver.fs` handles loading source files from fidproj projects and their dependencies.

## Key Architecture (January 2026)

### Recursive Transitive Dependency Loading

Dependencies are loaded **recursively** with:
- **Deepest-first ordering**: Transitive dependencies are resolved before direct dependencies
- **Cycle detection**: Visited paths are tracked to detect circular dependencies
- **Deduplication**: Shared dependencies across multiple dependents are included only once

### Source File Ordering

The final source file order is:
1. All transitive dependency sources (deepest first)
2. Direct dependency sources (in declaration order)
3. Project's own sources (in declaration order)

### Error Types

```fsharp
type SourceResolutionError =
    | DependencyDirectoryNotFound of name: string * path: string
    | DependencyFidprojNotFound of name: string * path: string
    | DependencyFidprojLoadError of name: string * path: string * message: string
    | DependencySourceFileNotFound of name: string * path: string
    | ProjectSourceFileNotFound of path: string
    | CircularDependency of chain: string list
```

### Key Functions

- `getDependencySourcesRec`: Internal recursive function with cycle detection
- `getDependencySources`: Public wrapper for single dependency resolution
- `getAllSourcesInOrder`: Main entry point for project compilation

## Example Dependency Chain

```
HelloWorld.fidproj
  └─ dependencies: fidelity_platform = { path = ".../Fidelity.Platform/Linux_x86_64" }
      └─ Fidelity.Platform.fidproj
          └─ dependencies: barewire = { path = ".../BAREWire/src" }
              └─ BAREWire.fidproj
                  └─ sources: [Memory.fs, Types.fs, ...]
```

Result: BAREWire sources → Fidelity.Platform sources → HelloWorld sources

## Design Principles

1. **NO hardcoded library names** - The resolver is completely generic
2. **Fail loudly** - Missing files/directories return errors, never silent fallbacks
3. **Single source of truth** - Each dependency's fidproj defines its own source ordering
4. **Cycle protection** - Circular dependencies are detected and reported clearly

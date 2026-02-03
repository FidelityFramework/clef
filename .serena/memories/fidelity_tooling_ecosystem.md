# Fidelity Native F# Tooling Ecosystem

> **Created**: January 1, 2026  
> **Updated**: February 1, 2026 (Lattice rebrand complete)  
> **Organization**: FidelityFramework (GitHub)

## Complete Repository Map

### Core Compiler & Language Server

| Repository | Path | Purpose |
|------------|------|------------|
| **fsnative** | `~/repos/fsnative` | FNCS: parsing, type checking with native types, **PSG construction** |
| **fsnative-spec** | `~/repos/fsnative-spec` | F# Native language specification |
| **FsNativeAutoComplete** | `~/repos/FsNativeAutoComplete` | Unified LSP server for native + managed F# |

### Editor Extensions (Rebranded from Ionide → Lattice, Feb 2026)

| Repository | Path | Upstream |
|------------|------|----------|
| **lattice-vscode** | `~/repos/lattice-vscode` | ionide/ionide-vscode-fsharp |
| **lattice-vim** | `~/repos/lattice-vim` | ionide/Ionide-vim |
| **lattice-vscode-helpers** | `~/repos/lattice-vscode-helpers` | ionide/ionide-vscode-helpers |
| **lattice-analyzers** | `~/repos/lattice-analyzers` | ionide/ionide-analyzers |

**Rebrand History**: These repos were renamed Feb 1, 2026 from `ionide-*-fsnative` → `lattice-*` to reflect the "ion → lattice" chemical progression metaphor (individual ions bonding into organized crystal structures).

### Libraries

| Repository | Path | Purpose |
|------------|------|------------|
| **Fidelity.Platform** | `~/repos/Fidelity.Platform` | Platform-specific bindings and type layouts |
| **BAREWire** | `~/repos/BAREWire` | Binary serialization (future) |
| **Farscape** | `~/repos/Farscape` | Distributed compute (future) |

### Compiler Infrastructure

| Repository | Path | Purpose |
|------------|------|------------|
| **Firefly** | `~/repos/Firefly` | AOT compiler: **consumes PSG from FNCS** → MLIR → LLVM → Native |

## Dependency Graph

```
                    ┌─────────────────────────────────────┐
                    │         Editor Extensions           │
                    │  ┌─────────────┐ ┌───────────────┐  │
                    │  │ lattice-    │ │ lattice-vim   │  │
                    │  │ vscode      │ │               │  │
                    │  └──────┬──────┘ └───────┬───────┘  │
                    │         │                │          │
                    │         └───────┬────────┘          │
                    │                 │ LSP               │
                    └─────────────────┼───────────────────┘
                                      │
                    ┌─────────────────▼───────────────────┐
                    │      FsNativeAutoComplete (FSNAC)   │
                    │  ┌─────────────┐ ┌───────────────┐  │
                    │  │ Native Path │ │ Managed Path  │  │
                    │  │ (FNCS)      │ │ (FSAC embed)  │  │
                    │  │ .fidproj    │ │ .fsproj       │  │
                    │  │ .fsnx       │ │ .fsx          │  │
                    │  └──────┬──────┘ └───────┬───────┘  │
                    └─────────┼────────────────┼──────────┘
                              │                │
              ┌───────────────▼───┐    ┌───────▼───────┐
              │      FNCS         │    │     FCS       │
              │ fsnative compiler │    │ F# Compiler   │
              └───────────────────┘    │ Services      │
                                       └───────────────┘

lattice-analyzers ──────► FSharp.Analyzers.SDK (NuGet, no fork)
lattice-vscode-helpers ─► VSCode API bindings
```

## Use As-Is (NuGet Dependencies)

| Package | Purpose |
|---------|---------|
| `Ionide.LanguageServerProtocol` | LSP protocol types |
| `FSharp.Analyzers.SDK` | Analyzer infrastructure |

## Package/Extension IDs (After Rebrand)

| Old Name | New Name | Published |
|----------|----------|-----------|
| `Ionide.FsNative.Analyzers` | `Lattice.Analyzers` | NuGet (pending) |
| `ionide-fsnative` (extension) | `lattice-fsharp` | VSCode Marketplace (pending) |
| `Ionide.FsNative.VSCode.Helpers` | `Lattice.VSCode.Helpers` | NuGet (not published) |

## Key Changes Per Forked Repo

### lattice-vscode
- NuGet reference: `fsautocomplete` → `fsnativeautocomplete`
- Extension ID: `ionide-fsnative` → `lattice-fsharp`
- Config namespace: `ionide.fsnative.*` → `lattice.fsharp.*`
- File associations: `.fidproj`, `.fsnx`
- UI: Memory layout viewer, SRTP resolution display, `fsnative/*` LSP endpoints

### lattice-vim
- Command: `vim.g['fsharp#fsautocomplete_command']` → FSNAC path
- Lua module: `require('ionide')` → `require('lattice')`
- Filetype detection: `.fidproj`, `.fsnx`
- LSP handlers: `fsnative/*` custom endpoints

### lattice-analyzers
- Package: `Ionide.FsNative.Analyzers` → `Lattice.Analyzers`
- Namespace: `Ionide.FsNative.Analyzers` → `Lattice.Analyzers`
- Target: net10.0 (upgraded from net8.0)
- Inherited: `EqualsNullAnalyzer`, struct-related analyzers
- **Planned** (not yet implemented):
  - `BclTypeAnalyzer` - Warn on `System.*` BCL types
  - `ObjTypeAnalyzer` - Warn on `obj` usage (not in NTU)
  - `BoxingAnalyzer` - Detect value→reference conversions
  - `ExceptionPatternAnalyzer` - Warn on .NET exceptions
  - `PlatformBindingAnalyzer` - Validate Fidelity.Platform usage

### lattice-vscode-helpers
- Package: `Ionide.FsNative.VSCode.Helpers` → `Lattice.VSCode.Helpers`
- Namespace: `Ionide.FsNative.VSCode.Helpers` → `Lattice.VSCode.Helpers`
- Target: netstandard2.0 (Fable requirement, unchanged)
- Purpose: Generic VSCode API bindings for Fable

## File Extension Mapping

| Extension | Handler | Description |
|-----------|---------|-------------|
| `.fidproj` | FSNAC Native | Fidelity project (TOML) |
| `.fsnx` | FSNAC Native | F# Native script |
| `.fsproj` | FSNAC → FSAC | Standard F# project |
| `.fsx` | FSNAC → FSAC | Standard F# script |

## Analyzer Architecture (Important!)

**FNCS has NO analyzers built-in.** Analyzers are:
1. Written in `lattice-analyzers` using `FSharp.Analyzers.SDK`
2. Published to NuGet as `Lattice.Analyzers`
3. Loaded by FSNAC at runtime
4. Fed `FSharpCheckResults` from FNCS
5. Return diagnostics to editor via FSNAC's LSP

See related memory: `fncs_architecture` for FNCS purity (no file I/O, no analyzers).

# Fidelity Native F# Tooling Ecosystem

> **Created**: January 1, 2026
> **Organization**: FidelityFramework (GitHub)

## Complete Repository Map

### Core Compiler & Language Server

| Repository | Path | Purpose |
|------------|------|---------|
| **fsnative** | `~/repos/fsnative` | FNCS: parsing, type checking with native types, **PSG construction** |
| **fsnative-spec** | `~/repos/fsnative-spec` | F# Native language specification |
| **FsNativeAutoComplete** | `~/repos/FsNativeAutoComplete` | Unified LSP server for native + managed F# |

### Editor Extensions (Forked from Ionide)

| Repository | Path | Upstream |
|------------|------|----------|
| **ionide-vscode-fsnative** | `~/repos/ionide-vscode-fsnative` | ionide/ionide-vscode-fsharp |
| **Ionide-vim-fsnative** | `~/repos/Ionide-vim-fsnative` | ionide/Ionide-vim |
| **ionide-vscode-native-helpers** | `~/repos/ionide-vscode-native-helpers` | ionide/ionide-vscode-helpers |
| **ionide-native-analyzers** | `~/repos/ionide-native-analyzers` | ionide/ionide-analyzers |

### Libraries

| Repository | Path | Purpose |
|------------|------|---------|
| **Fidelity.Platform** | `~/repos/Fidelity.Platform` | Platform-specific bindings and type layouts |
| **BAREWire** | `~/repos/BAREWire` | Binary serialization (future) |
| **Farscape** | `~/repos/Farscape` | Distributed compute (future) |

### Compiler Infrastructure

| Repository | Path | Purpose |
|------------|------|---------|
| **Firefly** | `~/repos/Firefly` | AOT compiler: **consumes PSG from FNCS** → MLIR → LLVM → Native |

## Dependency Graph

```
                    ┌─────────────────────────────────────┐
                    │         Editor Extensions           │
                    │  ┌─────────────┐ ┌───────────────┐  │
                    │  │ VSCode      │ │ Vim/Neovim    │  │
                    │  │ fsnative    │ │ fsnative      │  │
                    │  └──────┬──────┘ └───────┬───────┘  │
                    │         │                │          │
                    │         └───────┬────────┘          │
                    │                 │ LSP               │
                    └─────────────────┼───────────────────┘
                                      │
                    ┌─────────────────▼───────────────────┐
                    │      FsNativeAutoComplete           │
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

ionide-native-analyzers ──────► FSharp.Analyzers.SDK (NuGet, no fork)
ionide-vscode-native-helpers ─► VSCode API bindings
```

## Use As-Is (NuGet Dependencies)

| Package | Purpose |
|---------|---------|
| `Ionide.LanguageServerProtocol` | LSP protocol types |
| `FSharp.Analyzers.SDK` | Analyzer infrastructure |

## Key Changes Per Forked Repo

### ionide-vscode-fsnative
- Change NuGet reference from `fsautocomplete` to `fsnativeautocomplete`
- Add `.fidproj` and `.fsnx` file associations
- Add UI for `fsnative/*` custom endpoints
- Add memory layout viewer, SRTP resolution display

### Ionide-vim-fsnative
- Change `vim.g['fsharp#fsautocomplete_command']` default
- Add `.fidproj` and `.fsnx` filetype detection
- Add handlers for `fsnative/*` endpoints

### ionide-native-analyzers
- Keep: `EqualsNullAnalyzer`, struct-related analyzers
- Add: `BclTypeAnalyzer`, `ObjTypeAnalyzer`, `ExceptionPatternAnalyzer`
- Add: `BoxingAnalyzer`, `PlatformBindingAnalyzer`

### ionide-vscode-native-helpers
- Likely minimal changes (generic VSCode bindings)
- Update imports if namespace changes needed

## File Extension Mapping

| Extension | Handler | Description |
|-----------|---------|-------------|
| `.fidproj` | FSNAC Native | Fidelity project (TOML) |
| `.fsnx` | FSNAC Native | F# Native script |
| `.fsproj` | FSNAC → FSAC | Standard F# project |
| `.fsx` | FSNAC → FSAC | Standard F# script |

# fsnative Directory Restructuring Plan

**Date**: January 2026

## Core Principle: NTU Coherence

The Native Type Universe (NTU) is the single source of truth for types. All tooling resolves types through NTU, not FSharpType/reflection.

**SynType is SYNTAX, not INDIRECTION**: Parser produces SynType, resolution goes directly to NTUKind.

## Directory Triage Summary

### DELETE
- `Microsoft.FSharp.Compiler/` - Empty placeholder
- `FSharp.VisualStudio.Extension/` - Not priority for native tooling

### ARCHIVE (to reference/)
- `FSharp.Core/` - Not used at runtime, keep as pattern reference

### RENAME
- `FSharp.Compiler.LanguageServer/` → `FSharp.Native.Compiler.LanguageServer/`
- `FSharp.Compiler.Interactive.Settings/` → `FSharp.Native.Compiler.Interactive/`
- `fsi/` → `fnsi/`

### KEEP
- `FSharp.DependencyManager.Nuget/` - Design-time package resolution
- `Compiler/` internals (NativeTypedTree, PSGSaturation, Nanopass, Baker, SyntaxTree)

### EVALUATE
- `Compiler/TypedTree/` - May be needed for inference, mark for review
- `Compiler/Service/` - Determine minimal FCS surface
- `Compiler/Symbols/` - PSG may replace FSharpSymbol need
- `Microsoft.CommonLanguageServerProtocol.Framework.Proxy/` - Check if referenced

## Target Structure
```
src/
├── Compiler/                              # Core native compiler
├── FSharp.Native.Compiler.LanguageServer/ # LSP (NTU-based)
├── FSharp.Native.Compiler.Interactive/    # Native REPL
├── FSharp.DependencyManager.Nuget/        # Package resolution
└── fnsi/                                  # Native FSI executable

reference/
└── FSharp.Core/                           # Archived patterns
```

## Key Insight

checkSynType callback removal (completed January 2026) was first step. SynType remains as syntax but resolution is now direct NTU lookup with `failwith "GREENFIELD"` markers showing where type resolution must be implemented.

See: `/home/hhh/repos/fsnative/docs/RESTRUCTURING_PLAN.md` for full details.

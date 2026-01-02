# FCS Infrastructure Preservation in FNCS

> **Created**: January 2026
> **Purpose**: Document what FCS infrastructure MUST be preserved in FNCS for design-time tooling

## Core Principle

FNCS changes the **type universe** (native types instead of BCL) but PRESERVES the **design-time infrastructure** from FCS. This enables FsNativeAutoComplete and editor integrations to work with native F# projects.

## What MUST Be Preserved

### Symbol Infrastructure

| Component | FCS Location | Purpose | Preservation Status |
|-----------|--------------|---------|---------------------|
| `FSharpSymbol` | `FSharp.Compiler.Symbols` | Symbol info for navigation | MUST PRESERVE |
| `FSharpSymbolUse` | `FSharp.Compiler.Symbols` | Symbol use tracking | MUST PRESERVE |
| `FSharpEntity` | `FSharp.Compiler.Symbols` | Type/module entities | MUST PRESERVE |
| `FSharpMemberOrFunctionOrValue` | `FSharp.Compiler.Symbols` | Member info | MUST PRESERVE |
| `FSharpField` | `FSharp.Compiler.Symbols` | Field info | MUST PRESERVE |

### Editor Service APIs

| API | Purpose | FNCS Requirement |
|-----|---------|------------------|
| `GetDeclarationListInfo` | Autocomplete | Provide native type completions |
| `GetToolTip` | Hover information | Show native type signatures |
| `GetDeclarationLocation` | Go to definition | Navigate to source/Alloy |
| `GetSymbolUseAtLocation` | Find symbol at cursor | Work with native symbols |
| `GetAllUsesOfAllSymbols` | Find all references | Cross-file reference tracking |
| `GetSemanticClassification` | Syntax highlighting | Semantic colorization |

### Source Location Tracking

All source locations and ranges MUST be preserved through the entire pipeline:
- Parser produces ranges on SynExpr nodes
- Type checker preserves ranges on typed nodes
- PSG carries ranges for Firefly diagnostics
- Editors can navigate to any symbol's definition

### Check Results

| Component | Purpose | Notes |
|-----------|---------|-------|
| `FSharpCheckFileResults` | Per-file analysis | Adapt to native types |
| `FSharpCheckProjectResults` | Project-wide analysis | PSG construction point |
| `FSharpParseFileResults` | Parse results | Use unchanged |

## What Changes

### Type Representations

| FCS Type | FNCS Equivalent |
|----------|-----------------|
| `System.String` | `NativeStr` (UTF-8 fat pointer) |
| `option<'T>` | `voption<'T>` (value type) |
| `System.Object` | **Does not exist** |
| BCL types (`System.*`) | **Rejected with FS8500** |

### Type Sources

| FCS | FNCS |
|-----|------|
| IL assemblies + source | Source only (no IL imports) |
| mscorlib/netstandard | Not referenced |
| Type providers | Not supported |

### SRTP Resolution

| FCS | FNCS |
|-----|------|
| Post-hoc overlay pass | During type checking |
| Runtime witness lookup | Compile-time resolution |
| BCL witnesses | Alloy witness hierarchy |

## Design-Time Tooling Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         FsNativeAutoComplete                                 │
│  • LSP server for native F# projects                                        │
│  • Detects .fidproj → uses FNCS                                             │
│  • Detects .fsproj → uses FCS (pass-through)                                │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                              FNCS APIs                                       │
│  • GetDeclarationListInfo → native type completions                         │
│  • GetToolTip → "NativeStr (UTF-8 fat pointer, 16 bytes)"                   │
│  • GetDeclarationLocation → navigate to Alloy source                        │
│  • GetSymbolUseAtLocation → find native symbols                             │
│  • GetAllUsesOfAllSymbols → cross-file references                           │
│  ALL PRESERVED - these APIs must continue to work                           │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Editor Extensions                                    │
│  • ionide-vscode-fsnative                                                   │
│  • Ionide-vim-fsnative                                                       │
│  NATIVE-SPECIFIC FEATURES:                                                  │
│  • Memory layout viewer (show struct size/alignment)                        │
│  • SRTP resolution display (show resolved witness)                          │
│  • Alloy symbol navigation (go to Alloy source)                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Alloy Phantom Hierarchy

Alloy source files should appear in editor file trees as navigable sources:

```
Project Explorer:
├── MyProject/
│   ├── Main.fs
│   └── Utils.fs
└── Alloy (Source Reference)/     ← Phantom hierarchy
    ├── Core.fs
    ├── Math.fs
    ├── Text.fs
    └── Console.fs
```

When hovering over `Console.Write`, the editor shows:
- Native type signature
- Link to Alloy source location
- Memory layout (if applicable)

## Implementation Checklist

- [ ] Audit existing FNCS code for FCS API preservation
- [ ] Ensure `FSharpSymbol` infrastructure is used
- [ ] Verify source locations flow through type checker
- [ ] Test GetToolTip with native types
- [ ] Test GetDeclarationLocation for Alloy functions
- [ ] Test GetAllUsesOfAllSymbols across project files
- [ ] Implement memory layout display for hover
- [ ] Implement SRTP resolution display

## References

- `~/repos/fsharp/src/Compiler/Service/` - FCS service layer
- `~/repos/fsharp/src/Compiler/Symbols/` - Symbol infrastructure
- `~/repos/FsNativeAutoComplete` - LSP server (future)

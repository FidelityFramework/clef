# FsNativeAutoComplete (FSNAC) - Native-First Architecture

## Architectural Mission

**FSNAC is the UNIFIED F# Language Server** for the Fidelity ecosystem.

```
FsNativeAutoComplete (Unified Server)
│
├── Project Detection
│   ├── .fidproj / .fsnx → Native Path (FNCS)
│   └── .fsproj / .fsx → Managed Path (FSAC delegation)
│
├── Native Path (PRIMARY FOCUS NOW)
│   ├── FNCS (F# Native Compiler Services)
│   ├── NativeServerState / AdaptiveFSharpNativeLspServer
│   └── Full native semantics, FS8xxx codes, native types
│
└── Managed Path (FUTURE)
    ├── Embedded/delegated FSAC ("classic")
    ├── Forward LSP requests for .fsproj files
    └── Enables Fable webview frontends in same workspace
```

**Key Value Proposition**: A Fidelity project with a Fable-based webview frontend gets ONE language server, ONE Ionide configuration, seamless tooling across native backend + web frontend.

**Development Phases**:
1. Native path first (current work) - FNCS integration
2. FSAC delegation later - enables mixed Fidelity+Fable workspaces
3. Single Ionide extension, no forks needed

The primary goal is making FSNAC a proper representative for fsnative and fsnative-spec, to be used by Serena for building the framework.

**Repository**: `/home/hhh/repos/FsNativeAutoComplete`
**FNCS Source**: `/home/hhh/repos/fsnative/src/Compiler/`

## Phase Status

| Phase | Description | Status |
|-------|-------------|--------|
| 1.1 | Add FNCS package reference | ✅ DONE |
| 1.2 | Create ProjectKind.fs | ✅ DONE |
| 1.3 | Create TOML parser (self-contained) | ✅ DONE |
| 1.4 | Create FidprojLoader (with workspace helpers) | ✅ DONE |
| 2 | NativeCompilerServiceInterface (FNCS wrapper) | ✅ DONE |
| 3 | Native workspace management (merged into FidprojLoader) | ✅ DONE |
| 4a | NativeServerState (state management) | ✅ DONE |
| 4b | AdaptiveFSharpNativeLspServer (native LSP handlers) | ✅ DONE |
| 5 | Script support (.fsnx) | PENDING |
| 6 | Custom LSP endpoints | PENDING |
| 7 | Testing | PENDING |
| 8 | Unified routing in AdaptiveFSharpLspServer | ✅ DONE |
| 9a | Native completions routing | ✅ DONE |
| 9b | Native diagnostics publishing | ✅ DONE |
| 9c | Native go-to-definition | ✅ DONE |

## Unified Server Routing (Completed 2026-01-01)

AdaptiveFSharpLspServer now routes requests to the appropriate backend:

**File Detection Logic**:
```fsharp
let isNativeFile (filePath: string) =
    nativeState.GetProjectForFile(filePath).IsSome ||
    nativeState.IsScript(filePath)
```

**Routed Endpoints**:
- `textDocument/hover` → NativeState.GetHoverInfo or FCS
- `textDocument/completion` → NativeState.GetCompletions or FCS
- `textDocument/definition` → NativeState.GetDefinition or FCS
- `textDocument/publishDiagnostics` → Published on open/change for native files

## Key Files Created

| File | Purpose |
|------|---------|
| `ProjectKind.fs` | Discriminates .fidproj/.fsnx (Native) vs .fsproj/.fsx (Standard) |
| `TomlParser.fs` | Self-contained TOML parser (no XParsec dependency) |
| `FidprojLoader.fs` | Parses .fidproj TOML + workspace helpers |
| `NativeCompilerServiceInterface.fs` | Wraps FNCS for LSP (conditional compilation) |
| `NativeServerState.fs` | Native project state management (ConcurrentDictionary-based) |
| `AdaptiveFSharpNativeLspServer.fs/.fsi` | Native LSP handlers (hover, completions, diagnostics) |

## Conditional Compilation

```xml
<PropertyGroup Condition="'$(TargetFramework)' != 'net8.0'">
  <DefineConstants>$(DefineConstants);HAVE_FNCS</DefineConstants>
</PropertyGroup>
```

- net8.0: Stub implementations, returns "FNCS not available" diagnostic
- net9.0+: Full FNCS integration with semantic graph, diagnostics, hover, completions

## Native Type Display

| Type | Display Format |
|------|----------------|
| `string` | `UTF-8 fat pointer { ptr: *u8, len: usize }` |
| `option<T>` | `voption<T> // value-type, stack-allocated` |
| `int` | `int // platform word (isize)` |
| `uint` | `uint // platform word (usize)` |
| `byref<T>` | Shows read-only, write-only, or mutable reference |
| `nativeptr<T>` | Native pointer (unsafe) |

## Error Codes (FS8xxx)

| Code | Message |
|------|---------|
| FS8011 | obj not supported in F# Native |
| FS8100 | null not supported; use ValueNone |
| FS8101 | uninitialized value not allowed |

## Standing Art Metaprogramming

FSNAC displays these F# features with their native-first semantic role:
- **Quotations**: Compile-time semantic carriers (not runtime evaluated)
- **Active Patterns**: Compositional structural recognition
- **Computation Expressions**: Continuation capture notation

See `standing_art_metaprogramming` memory for details.

## Notes

- FNCS remediation completed 2026-01-01 (spec alignment)
- FidprojLoader includes workspace helpers (findAllProjects, containsSourceFile, etc.)
- NativeProjectLoader.fs merged into FidprojLoader.fs and deleted
- See `fncs_fsnative_spec_audit` memory for spec alignment details

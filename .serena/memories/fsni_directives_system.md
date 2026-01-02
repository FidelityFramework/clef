# FSNI (F# Native Interactive) Directive System

> **Created**: January 1, 2026
> **Location**: FsNativeAutoComplete.Core.FsniDirectives

## Overview

FSNI directives are special comments in `.fsnx` (F# Native Script) files that configure native compilation settings. They are similar to F# Interactive directives but target native compilation.

## File Extension

- `.fsnx` - F# Native Script file

## Supported Directives

| Directive | Syntax | Purpose |
|-----------|--------|---------|
| `#target` | `#target "thumbv8m.main-none-eabihf"` | Set target triple |
| `#memory_model` | `#memory_model stack_only` | Set memory model |
| `#arena` | `#arena 4096` | Set arena size in bytes |
| `#platform` | `#platform "stm32l5"` | Set platform template |
| `#max_stack` | `#max_stack 8192` | Set max stack size |
| `#heap` | `#heap 16384` | Set heap size |
| `#require` | `#require "alloy"` | Require a dependency |
| `#include` | `#include "path/to/file.fs"` | Include another source file |
| `#load` | `#load "path/to/script.fsnx"` | Load another script |

## Memory Models

```fsharp
type MemoryModelDirective =
    | StackOnly     // All allocations on stack (embedded)
    | StaticPools   // Preallocated static pools
    | Arena         // Arena-based allocation
    | Standard      // Standard allocation (default)
```

## Example Script

```fsharp
// hello.fsnx
#target "thumbv8m.main-none-eabihf"
#memory_model stack_only
#platform "stm32l5"
#require "alloy"

open Alloy.Console

let main () =
    WriteLine "Hello from embedded F#!"
```

## Key Types

- `FsniDirective` - Discriminated union of all directive types
- `ScriptParseResult` - Result of parsing directives from source
- `FsnxScriptOptions` - Full parsed script with resolved paths

## LSP Integration

- Scripts auto-load when opened in editor
- Directive changes trigger re-parse on document change
- Diagnostics published for directive parse errors
- Workspace watches for .fsnx file changes

## Related Files

- `FsNativeAutoComplete.Core/FsniDirectives.fs` - Parser implementation
- `FsNativeAutoComplete/LspServers/NativeServerState.fs` - Script state management
- `FsNativeAutoComplete/LspServers/AdaptiveFSharpNativeLspServer.fs` - LSP handlers

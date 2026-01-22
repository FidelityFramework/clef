# Entry Point Elaboration Architecture

> **Status**: Implemented and validated (January 2026)
> **Location**: `fsnative/src/Compiler/Nanopass/IntrinsicElaboration.fs`

## Core Principle

Entry point generation is a **platform/linkage concern**, NOT F# language machinery.
Therefore it belongs in **Intrinsic Elaboration (Pass 1/2)**, NOT Baker (Pass 3/4).

```
Baker = F# language decomposition (HOF, Match, Seq, Lazy)
Intrinsic Elaboration = Platform linkage (entry points, syscalls)
```

## Entry Point Modes

| Mode | Entry Symbol | Who Provides | Use Case |
|------|-------------|--------------|----------|
| **Freestanding** | `_start` (generated) | FNCS elaboration | Bare metal, no libc |
| **Console** | `main` (libc calls it) | libc's `_start` | Standard apps |
| **Multi-Entry** | `[<EntryPoint("name")>]` | Future | "Many doors" pattern |

## Freestanding Mode Design

### F# Convention
F# `[<EntryPoint>]` main has type `string array -> int`, NOT C's `(int argc, char** argv)`.

### Generated `_start` Wrapper

```
_start:
    argv ← Sys.emptyStringArray()   // Empty array for now
    result ← main(argv)
    Sys.exit(result)                // Honors `int -> unit` type contract
```

### PSG Structure (9 nodes)
1. `Intrinsic Sys.emptyStringArray` - The intrinsic function
2. `Application` - Calling the intrinsic to get argv
3. `VarRef main` - Reference to user's main
4. `Application` - Calling main with argv
5. `Intrinsic Sys.exit` - The exit intrinsic
6. `Application` - Calling exit with result
7. `Sequential` - Ordering the calls
8. `Lambda` - The `_start` function body
9. `Binding` - The `_start` binding (marked as entry point)

### Key Insight: Intrinsics Wrapped in Applications
Standalone `Intrinsic` nodes return `WitnessOutput.empty` in Alex.
To produce actual values, intrinsics MUST be wrapped in `Application` nodes.

## Unit/Exit Type Story

`Sys.exit` has type `int -> unit`. Even though the syscall never returns:
- The binding emits a unit value (`i32 0`) after the syscall
- This honors the type contract
- LLVM optimizes away the unreachable code
- F# developers see consistent type semantics

**Principle**: Every unit-returning function returns `i32 0`. No exceptions.

## Platform Context Flow

```
fidproj (output_kind = "freestanding")
    ↓
ProjectChecker creates PlatformContext with FreestandingStartup
    ↓
PlatformContext set on graph BEFORE nanopass pipeline
    ↓
IntrinsicElaboration.elaborateEntryPoints checks graph.Platform
    ↓
If FreestandingStartup.IsSome → generate _start wrapper
```

## Alex Responsibility

Alex does NOT make platform decisions. It trusts the PSG:
- No `isMain` special-casing for function signatures
- `main` emitted with whatever signature PSG specifies
- If console mode needs C-style main, FNCS handles that transformation

**Removed anti-pattern**: Alex's `LambdaWitness.fs` had `isMain` check forcing C-style signature. This violated the principle that Alex trusts PSG.

## Validation

- Sample 07_BitsTest (freestanding) compiles and executes correctly
- `_start` wrapper visible in MLIR output
- No regressions in console mode samples (01-06, 08)

## Related Memories

- `psg_elaboration_fold_architecture` - Four-pass pipeline structure
- `baker_saturation_architecture` - Baker is for F# machinery, not entry points
- `fncs_architecture` - FNCS overall design

# Freestanding Entry Point - Knock List

> **Status**: Ephemeral working memory - dispose when design is baked in
> **Created**: January 2026
> **Context**: Sample 07 (BitsTest) segfaults because freestanding mode lacks `_start` wrapper

## The Problem

Freestanding binaries on Linux x86-64 need:
- Linker uses `-Wl,-e,_start` (expects `_start` symbol)
- MLIR only generates `main`
- Entry point defaults to first symbol in .text (happens to be `write`)
- Segfault on execution

## Design: Baker Ingredients + Recipes

### Slim Platform Data (NOT over-engineered EntryPointABI)

```fsharp
// Platform provides DATA only - no behavioral specifications
type FreestandingStartup = {
    ArgcStackOffset: int   // 0 on Linux x86-64 (at RSP)
    ArgvStackOffset: int   // 8 on Linux x86-64 (RSP + 8)
    ExitSyscall: int       // 60 on Linux x86-64
}
```

### Baker Ingredients (Intrinsics)

```fsharp
// New intrinsics for startup sequence
Sys.stackArgc    : unit -> int                         // Load from [rsp + offset]
Sys.stackArgv    : unit -> nativeptr<nativeptr<byte>>  // Load from [rsp + offset]
Sys.exit         : int -> unit                         // Already exists
```

### Baker Recipe (XParsec Pattern)

When:
- `OutputKind = Freestanding`
- Entry point `main : int -> nativeptr -> int` exists

Decompose to:
```
_start:
    argc ← Sys.stackArgc()
    argv ← Sys.stackArgv()
    result ← main(argc, argv)
    Sys.exit(result)
```

### PSG Output

Recipe adds synthetic `_start` node:
- Marked as actual entry point
- Has call edge to user's `main`
- Has edges to startup intrinsics

Alex sees complete PSG - no special cases needed downstream.

## Files to Modify

### Platform (Fidelity.Platform/Linux_x86_64)

- [ ] **Types.fs**: Slim down `EntryPointABI` → simple `FreestandingStartup`
- [ ] **Platform.fs**: Update platform descriptor with slim data

### FNCS

- [ ] **Ingredients**: Add `Sys.stackArgc`, `Sys.stackArgv` intrinsics
- [ ] **Recipe**: Create freestanding entry point recipe
- [ ] **Pipeline**: Detect OutputKind.Freestanding, apply recipe

### Firefly

- [ ] **Toolchain.fs**: Already correct (`-Wl,-e,_start`)
- [ ] **Alex witnesses**: May need witnesses for new intrinsics

## Related: Entry Point Modes

Full vision from "Farscape Modular Entry Points" blog:

| Mode | Entry Symbol | libc | Use Case |
|------|-------------|------|----------|
| Freestanding | `_start` (generated) | No | Bare metal, minimal binaries |
| Console | `main` (libc calls it) | Yes | Standard apps |
| Multi-Entry | Multiple `[<EntryPoint("name")>]` | Yes | "Many doors" shadow-api |
| Library | None | Optional | Shared libraries |

## Spec Placement

- **NOT** in IEC language spec (entry point isn't language syntax)
- **YES** in platform binding conformance spec
- Platform defines the data; Baker defines the behavior

## Open Questions

1. Should `FreestandingStartup` be part of `PlatformDescriptor` or separate?
2. How does multi-entry (`[<EntryPoint("name")>]`) interact with freestanding?
3. Does embedded mode differ from freestanding? (Different ABI?)

## Validation

When complete:
- [ ] Sample 07 (BitsTest) passes with `output_kind = "freestanding"`
- [ ] Console samples still work
- [ ] Generated MLIR includes `_start` function for freestanding

---

*Delete this memory once the design is implemented and validated.*

# Fidproj Platform Context Principle

## Core Principle (From User Guidance, Jan 2026)

> "Generics should still be a library or design-time consideration and SRTP is a compiler concern. So the point is to - as soon as platform and other constraints are known - and they should be known as soon as the fidproj file is read - that the SRTP resolution is affected."

## Architecture Update (January 2026)

Platform awareness now flows **FROM THE TOP** via quotation-based binding libraries:

```
.fidproj file
    ↓
Fidelity.Toml (separate TOML 1.0 library, NOT FNCS)
    ↓
Firefly CLI (orchestrator - all I/O happens here)
    ↓  extracts: Fidelity.Platform library path, sources
    ↓  loads: ~/repos/Fidelity.Platform/Linux_x86_64
    ↓  extracts: Expr<PlatformDescriptor> quotations
    ↓
FNCS (pure compiler - receives parameters, NO I/O)
    ↓  receives: sources, options, platform quotations
    ↓
PSG (carries platform quotation metadata)
    ↓
Alex (witnesses quotations → MLIR)
```

**Key Design Decisions**:
- **Fidelity.Toml**: Separate reusable TOML 1.0 library (not internal to FNCS)
- **Firefly**: Handles ALL file I/O, config parsing, dependency resolution
- **FNCS**: Pure compiler service receiving parameters only
- **Fidelity.Platform**: Platform monorepo at ~/repos/ with quotation-based bindings

## Implications

### 1. Platform Context is Known Early
```toml
# HelloWorld.fidproj
[build]
target = "native"  # or "x86_64-unknown-linux-gnu" or "thumbv8m.main-none-eabihf"
```

When fidproj is read, we KNOW:
- Target architecture (x86_64, ARM32, WASM32, etc.)
- Platform word size (64-bit or 32-bit)
- Endianness
- OS family (if applicable)

### 2. SRTP Resolution is Compiler Concern
- SRTP resolves at COMPILE TIME, not runtime
- Resolution should USE platform context
- When resolving `+` for `int`, compiler knows int = 64-bit on this target

### 3. Generics are Design-Time Abstraction
- Generic code (`List<'T>`) is library-level abstraction
- SRTP monomorphizes based on actual types at call sites
- Platform context affects what "platform word" means

## Architecture Gap (Current State)

```fsharp
// ProjectLoader.fs - fidproj parsed here
type ProjectConfig = {
    ...
    TargetTriple: string option  // EXTRACTED but...
}

// NativeService.fs - ...never passed here!
let checkParsedInputs (inputs: ParsedInput list) : CheckResult =
    let globals = ... // greenfield type resolution  // NO platform parameter!
    ...
```

## Required Changes

### 1. Platform Config Type
```fsharp
type PlatformConfig = {
    Architecture: Architecture  // X86_64 | ARM32 | ARM64 | WASM32
    WordSize: int               // 32 or 64
    OSFamily: OSFamily option   // Linux | Windows | MacOS | None (freestanding)
}
```

### 2. Parse from Target Triple
```fsharp
let parsePlatformConfig (targetTriple: string) : PlatformConfig =
    match targetTriple with
    | "native" -> detectHostPlatform()
    | triple when triple.StartsWith("x86_64") -> { Architecture = X86_64; WordSize = 64; ... }
    | triple when triple.StartsWith("thumbv") -> { Architecture = ARM32; WordSize = 32; ... }
    | triple when triple.StartsWith("aarch64") -> { Architecture = ARM64; WordSize = 64; ... }
    ...
```

### 3. Thread Through FNCS
```fsharp
// NativeService.fs
let checkParsedInputs (inputs: ParsedInput list) (platform: PlatformConfig) : CheckResult =
    let globals = ... // greenfield platform-aware type resolution  // Platform-aware!
    ...
```

### 4. Platform-Aware Type Creation
```fsharp
// (greenfield implementation)
// greenfield: platform-aware type resolution
    let wordSize = platform.WordSize / 8  // bytes
    let intTyCon = mkTypeConRef "int" 0 (TypeLayout.PlatformWord)
    // OR if we want early resolution:
    let intTyCon = mkTypeConRef "int" 0 (TypeLayout.Inline(wordSize, wordSize))
    ...
```

## Design Choice: Early vs Late Resolution

### Early Resolution (in FNCS)
- Platform known → sizes concrete immediately
- Simpler downstream (Alex sees concrete sizes)
- Less flexible for cross-compilation scenarios

### Late Resolution (in Alex)
- FNCS uses abstract `TypeLayout.PlatformWord`
- Alex resolves based on target
- More flexible, nanopass-pure
- PSG is platform-agnostic

**Recommended: Late Resolution** (nanopass-correct)

## Related Memories
- `fncs_platform_aware_type_resolution` - Detailed architecture
- `srtp_operator_architecture` - SRTP mechanism

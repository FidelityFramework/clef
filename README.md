# Clef Compiler Services (CCS)

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

<p align="center">
🚧 <strong>Under Active Development</strong> 🚧<br>
<em>This project is in early development and not intended for production use.</em>
</p>

**The parsing and type-checking frontend for the Clef programming language.**

## Overview

CCS (Clef Compiler Services) is the compiler frontend for [Clef](https://clef-lang.com), a concurrent programming language in the ML tradition. It parses Clef source, resolves types against the Native Type Universe (NTU), and produces a typed abstract syntax tree that flows into the Composer compiler's middle- and back-end pipeline. No .NET runtime required anywhere in the output.

Clef targets CPU, MCU, GPU, NPU, FPGA, and CGRA from a single source language. CCS is stage one of that compilation.

## The Fidelity Framework

CCS is part of the **Fidelity** compilation framework:

| Project | Role |
|---------|------|
| **[Composer](https://github.com/FidelityFramework/composer)** | Compiler and CLI: Clef → PSG → MLIR → Native binary |
| **[BAREWire](https://github.com/FidelityFramework/barewire)** | Binary encoding, memory mapping, zero-copy IPC |
| **[Farscape](https://github.com/FidelityFramework/farscape)** | C/C++ header parsing for native library bindings |
| **[XParsec](https://github.com/FidelityFramework/xparsec)** | Parser combinators powering PSG traversal and header parsing |
| **CCS** | Clef Compiler Services — this repository |
| **[clef-lang-spec](https://github.com/FidelityFramework/clef-lang-spec)** | Normative Clef language specification |

## Why Clef Exists

Heterogeneous compute is fragmented. Writing software that runs across CPUs, microcontrollers, GPUs, NPUs, and FPGAs today means maintaining separate codebases in separate languages — C for bare-metal, CUDA for GPUs, HLS for FPGAs, Python for ML inference pipelines. Each target brings its own toolchain, its own memory model, and its own failure modes. Integrating them requires hand-written glue at every boundary.

Clef is a single language that targets all of them.

**Concurrency is the programming model, not a library.** The actor model is built into the language. Every stateful interaction is a message. Actors are the unit of ownership, isolation, and scheduling — whether running on CPU threads, GPU streaming multiprocessors, or synthesized into FPGA logic.

**The type system carries hardware information.** Dimensional type inference propagates numeric format, memory region, access kind, and tensor shape through the type system invisibly, the way Hindley-Milner propagates polymorphism. The compiler knows whether a value lives in global DRAM, shared SRAM, a peripheral register, or read-only flash — and enforces those distinctions at compile time.

**Memory is deterministic and ownership-tracked.** There is no garbage collector, no managed heap, no runtime. Lifetimes are inferred from program structure. Arena allocation per actor means thousands of allocations freed together at actor scope exit. Pointers carry lifetime information through the type system.

**SRTP-based polymorphism costs nothing at runtime.** Statically resolved type parameters monomorphize at compile time against the Alloy witness hierarchy. Zero-cost abstractions are not aspirational — they are structural.

## The Language

Clef is ML-family syntax — records, discriminated unions, pattern matching, computation expressions, first-class functions — with native-first semantics throughout.

```clef
// Records are value types with struct layout
type Point = { x: float32; y: float32 }

// Discriminated unions are tag + payload — no heap allocation
type Shape =
    | Circle of center: Point * radius: float32
    | Rect   of origin: Point * width: float32 * height: float32

// Pattern matching is exhaustive and statically verified
let area = function
    | Circle (_, r) -> Float.pi * r * r
    | Rect (_, w, h) -> w * h

// SRTP-based polymorphism resolves at compile time — no vtables
let inline dot (a: ^Vec) (b: ^Vec) : float32
    when ^Vec : (member X : float32) and ^Vec : (member Y : float32) =
    a.X * b.X + a.Y * b.Y

// Actors are the concurrency primitive — no shared mutable state
actor Sensor (mailbox: Mailbox<Reading>) =
    let rec loop () = actor {
        let! reading = mailbox.receive ()
        do! publish (process reading)
        return! loop ()
    }
    loop ()
```

## The Compilation Pipeline

```
Clef Source (.clef)
    ↓
CCS (this repository)       ← Parsing, type checking, NTU resolution
    ↓
Program Semantic Graph (PSG)
    ↓
Alex (MiddleEnd)            ← Nanopasses, optimization, target selection
    ↓
MLIR → LLVM
    ↓
Native Binary / FPGA Bitstream / NPU Microcode
```

CCS hands a fully-typed tree to Composer. Every type is already native — NTU strings, value options, region-annotated pointers. Composer's nanopasses operate on resolved types, not BCL references.

## What CCS Provides

- **Parsing** — Full Clef syntax via the battle-tested FCS lexer and parser, extended for Clef constructs
- **Native Type Resolution** — String literals, options, and arrays resolve to NTU types at the type-checking stage
- **Memory Region Tracking** — Pointers carry region and access-kind annotations through the typed tree
- **SRTP Resolution** — Statically resolved type parameters resolve against the Alloy witness hierarchy, not .NET method tables
- **Typed Tree Output** — Complete `ClefExpr` output for downstream PSG construction in Composer
- **LSP Services** — Symbol resolution, type information, and semantic classification consumed by Lattice

## What CCS Does Not Provide

CCS is a focused frontend, not a complete compiler:

- **No IL generation** — Clef does not target .NET IL
- **No MSBuild integration** — Project files are `.fidproj`, handled by Composer
- **No NuGet resolution** — Package management is ClefPak (`cpk`)
- **No REPL** — Interactive scripting requires a managed runtime; Clef has none

CCS stops at the typed tree. Code generation happens in Composer via Alex and MLIR.

## Getting Started

CCS is consumed as a library by Composer:

```clef
// Composer uses CCS for parsing and type checking
let checker = CCSChecker.create ()
let results = checker.parseAndCheck sourceFiles config

// Results contain the typed tree with NTU type resolution
let typedTree = results.typedTree
let srtpResolutions = results.srtpResolutions
```

For most use cases, you will interact with CCS through Composer rather than directly.

## Implementation Status

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 1 | Structural pruning and namespace transformation | In Progress |
| Phase 2 | Native Type Universe (NTU) integration | Pending |
| Phase 3 | SRTP resolution against Alloy witnesses | Pending |
| Phase 4 | Memory region and access-kind annotations | Future |

See [docs/fidelity/CCS_Phase1_Transformation_Plan.md](docs/fidelity/CCS_Phase1_Transformation_Plan.md) for detailed phase status.

## Documentation

| Document | Description |
|----------|-------------|
| [docs/fidelity/README.md](docs/fidelity/README.md) | CCS architecture overview |
| [clef-lang-spec](https://github.com/FidelityFramework/clef-lang-spec) | Normative Clef language specification |
| [clef-lang.com](https://clef-lang.com) | Language documentation and design guides |

## Relationship to dotnet/fsharp

CCS descends from a surgical fork of Microsoft's [dotnet/fsharp](https://github.com/dotnet/fsharp). The FCS parsing and name-resolution machinery is the foundation; the type universe, memory model, and output interface are being replaced wholesale. We are grateful to the F# team and community for the compiler infrastructure on which this work builds.

Clef is a distinct language. It is not F# targeting native backends. The syntax is ML-family and will be familiar to F# developers, but the semantics — memory ownership, the actor model, dimensional types, hardware targeting — are Clef's own.

## License

This project is licensed under the MIT License — see the [LICENSE](LICENSE) file for details.

Original work is copyright Microsoft Corporation. Modifications are copyright SpeakEZ Technologies.

## Contact

CCS is developed by [SpeakEZ Technologies](https://speakez.tech) as part of the Fidelity native compilation framework.

---

*ML semantics. Hardware scale. No runtime.*

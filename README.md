# Clef Compiler Services (CCS)

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

<p align="center">
🚧 <strong>Under Active Development</strong> 🚧<br>
<em>This project is in early development and not intended for production use.</em>
</p>

**The parsing and type-checking frontend for the Clef programming language.**

## Overview

CCS (Clef Compiler Services) is the compiler frontend for [Clef](https://clef-lang.com), a concurrent programming language in the ML tradition. It parses Clef source, resolves types against the Native Type Universe (NTU), and uses Baker's elaboration and saturation nanopasses to construct the Program Semantic Graph and its joint constraints. Composer's Alex witnesses that graph into the admitted MLIR forms for the selected backend.

The bootstrap compiler is written in F# and runs on .NET. Its host dependencies
are distinct from Clef language semantics and target runtime requirements.

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
type Point = { x: float; y: float }

// Discriminated unions are tag + payload — no heap allocation
type Shape =
    | Circle of center: Point * radius: float
    | Rect   of origin: Point * width: float * height: float

// Pattern matching is exhaustive and statically verified
let area = function
    | Circle (_, r) -> Float.pi * r * r
    | Rect (_, w, h) -> w * h

// SRTP-based polymorphism resolves at compile time — no vtables
let inline dot (a: ^Vec) (b: ^Vec) : float
    when ^Vec : (member X : float) and ^Vec : (member Y : float) =
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

These examples describe the intended language surface. Exact implemented scope,
pending actor/CE work and compiler acceptance are tracked in Composer's
[PRD index](../Composer/docs/PRDs/README.md) and
[coverage waypoints](../Composer/docs/Language_Coverage_Waypoints.md).

## The Compilation Pipeline

```
Clef Source (.clef)
    ↓
CCS (this repository)       ← parsing, type checking in the NTU, saturation of the semantic graph
    ↓
Program Semantic Graph (PSG, a hypergraph: nodes, hyperedges, obligations, residence, layout)
    ↓
Composer / Alex             ← target-aware passive witnessing into admitted MLIR forms
    ↓
MLIR → target pathway (LLVM, CIRCT, MLIR-AIE, JSIR)
    ↓
Native binary / FPGA bitstream / NPU binary / JavaScript module
```

CCS hands Composer a **saturated graph**, not a typed tree. Every type is native (NTU strings as `memref`
views, value options, region-typed handles), every layout is a literal settled at saturation, and every
proof obligation is a graph citizen with its design-time evidence status recorded. Composer's middle
end witnesses that structure and selects an admitted form from the settled
platform/backend facts under the [lowering contract](../clef-lang-spec/spec/backend-lowering-architecture.md).
Required unresolved obligations remain explicit; creating an obligation does not
establish that it has been discharged.

## What CCS Provides

- **Parsing** — full Clef syntax via the inherited FCS lexer and parser, extended for Clef constructs
- **Native type resolution** — literals, options, arrays and strings resolve to NTU types at check time; dimensional types carry numeric format, memory region and access kind
- **SRTP resolution** — statically resolved type parameters resolve against source-defined witnesses, not .NET method tables
- **The Program Semantic Graph** — nodes and first-class hyperedges, saturated by Baker recipes: collections, closures, suspension, obligations
- **Proof obligations as graph citizens** — born at saturation, emitted as an SMT-LIB2 ledger, dispatched to cvc5 at design time and re-derived from the artifact at build time
- **Platform residence** — the platform description read structurally from the graph; buffers, spaces and layouts cited by name
- **Editor facts** — everything Lattice surfaces (types, dimensions, residence, obligation status) is read from the graph, never recomputed

## What CCS Does Not Provide

CCS is a focused front end, not a complete compiler:

- **No IL generation** — Clef does not target .NET IL
- **No MSBuild integration** — project files are `.fidproj`, loaded by CCS and driven by Composer
- **No NuGet resolution** — package management is ClefPak (`cpk`)
- **No inherited F# Interactive host** — native incremental/REPL work follows Clef's own contracts and roadmap
- **No code generation** — that is Composer's, through Alex and MLIR

## Getting Started

CCS builds as a .NET bootstrap library referenced by Composer. With the sibling
BAREWire and Fidelity.Data repositories available, its maintained local gates are:

```sh
dotnet build Clef.Compiler.Service.sln
dotnet test tests/Clef.Compiler.Service.Tests/Clef.Compiler.Service.Tests.fsproj
```

There is no separate CCS CLI. Compile Clef applications through Composer:

```
dotnet build /home/hhh/repos/Composer/src/Composer.fsproj
dotnet <Composer>/src/bin/Debug/net10.0/Composer.dll compile samples/RoundTrip/RoundTrip.fidproj
```

The design of record for the graph, its obligations and the retirement of earlier designs is
[docs/fidelity/phg/](docs/fidelity/phg/); run [`drift-gate.sh`](docs/fidelity/phg/drift-gate.sh)
before proposing a documentation change anywhere in the corpus.

## Documentation

| Document | Description |
|----------|-------------|
| [docs/fidelity/README.md](docs/fidelity/README.md) | CCS architecture overview |
| [clef-lang-spec](https://github.com/FidelityFramework/clef-lang-spec) | Normative Clef language specification |
| [clef-lang.com](https://clef-lang.com) | Language documentation and design guides |

## Relationship to dotnet/fsharp

CCS descends from a surgical fork of Microsoft's [dotnet/fsharp](https://github.com/dotnet/fsharp). The FCS parsing and name-resolution machinery is the foundation; the type universe, memory model, and output interface are being replaced wholesale. We are grateful to the F# team and community for the compiler infrastructure on which this work builds.

Clef is a distinct language. It is not F# targeting native backends. The syntax is ML-family and will be familiar to F# developers, but the semantics — memory ownership, the actor model, dimensional types, hardware targeting — are Clef's own.

## Repository history and scope

The maintained history starts at the February 18, 2026 CCS rename/migration.
Upstream branches, tags, unused language-server/interactive projects, obsolete
assembly-resolution code, localization resources and packaged build output have
been removed. The lexer/parser, parser generators, bootstrap support, Clef
compiler and current tests remain, with their licensing and attribution.

The [history migration record](docs/handoffs/Repository_History.md) explains the
boundary, commit-ID correspondence and checkout migration. Old clones must not
merge or push the retired history back into this repository.

## License

This project is licensed under the MIT License — see the [LICENSE](LICENSE) file for details.

Original work is copyright Microsoft Corporation. Modifications are copyright Braidpoint.

## Contact

CCS is developed by [SpeakEZ Technologies](https://speakez.tech) as part of the Fidelity native compilation framework.

---

*ML semantics. Hardware scale. No runtime.*

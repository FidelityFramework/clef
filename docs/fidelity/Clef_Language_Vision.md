# Clef: A Concurrent Programming Language for Heterogeneous Compute

> ML semantics are the foundation, hardware targeting creates the structure, and incrementalism is the keystone.

## What Clef Is

Clef is a concurrent programming language that happens to use functional idioms.

It compiles to CPU, GPU, NPU, FPGA, and CGRA via MLIR. It infers memory lifetimes, dimensional types, and hardware targeting from program structure alone.

Clef uses ML-family syntax with Python-like ergonomics, strong type inference, and a pure-functional programming model built on the actor paradigm.

## The Three Inferences

Most languages require the developer to specify at least one of these. Clef infers all three from the same architectural constraints.

### 1. Dimensional Type Inference

The Native Type Universe (NTU) carries five dimensional axes through the type system:

- **Width**: `int` resolves to 32 or 64 bits depending on platform, inferred from context
- **Memory Space**: global, shared, private, coherent - inferred from escape analysis and substrate
- **Numeric Format**: IEEE, posit, fixed-point, ternary - carried as type identity
- **Access Pattern**: normal, streaming, volatile, read-only - inferred from usage context
- **Tensor Shape**: scalar, vector, matrix - reserved for NPU/GPU vectorization

These dimensions flow through type inference the way polymorphism flows through Hindley-Milner - structurally, invisibly. Non-numeric units of measure are intrinsic to the type system.

### 2. Memory Lifetime Inference

Deterministic memory management with fully inferred lifetimes. The compiler derives ownership and allocation strategy from program structure alone.

- **Pure functional code** guarantees single-ownership - immutable values have unambiguous lifetimes
- **Actor boundaries** are ownership boundaries - each actor's memory is isolated
- **Escape analysis** determines whether values are stack-scoped, arena-allocated, or must survive their creating scope
- **Arena allocation per actor** - thousands of allocations freed together when an actor's scope ends

Architectural constraints (purity, actor isolation) give the compiler total visibility into data flow, which is sufficient to infer lifetimes at compile time.

### 3. Hardware Targeting Inference

The compiler determines which substrate should execute each part of the program:

- Pure data-parallel subgraph with streaming access → GPU candidate
- Posit accumulation with high-precision requirements → FPGA candidate
- Stateful actor with resource dependencies → CPU
- Matrix operations with fixed tensor shape → NPU candidate

This inference reads the program's *shape* - its dependency structure, dimensional types, access patterns, and purity. The dimensional type system carries exactly the information the compiler needs to make substrate dispatch decisions.

## The Computation Model

### Actors as the Computation Substrate

Clef programs are networks of communicating actors. Every stateful interaction is a message. The actor model is the programming model.

An actor is a delimited continuation that suspends at message receipt and resumes when a message arrives. The mailbox is a continuation prompt. Actors are *continuations scheduled by a dependency graph*.

### Incremental Computation as the Scheduler

Incremental<'T> is the scheduling substrate that makes actors, delimited continuations, and interaction nets cohere into a unified system.

- **For actors**: The dependency DAG determines the order of message propagation. An actor's output is an incremental node; downstream actors depend on it.
- **For delimited continuations**: Height-based stabilization determines when continuations resume via propagation wavefronts.
- **For interaction nets**: Cutoff semantics determine which graph reductions are worth performing - if inputs haven't changed, don't re-reduce.
- **For hardware**: Wave scheduling maps directly to GPU wavefronts, NPU tile firing order, and FPGA pipeline stages.

Incremental<'T> is the keystone of the architecture - the last piece placed, but the piece that makes the arch stand.

### Interaction Nets as Evaluation Strategy

Pure functional subgraphs compile to interaction nets - a graph rewriting system where nodes connect via ports and reduce via local rewriting rules. Interaction nets are inherently parallel: if two nodes can reduce independently, they do.

On a CPU, interaction net reduction is sequential (simulated). On a CGRA, NPU, or FPGA, it IS the native execution model.

## The Control-Flow / Data-Flow Pivot

This is the central architectural insight.

Traditional CPUs are **control-flow machines**: an instruction pointer moves through code sequentially. Emerging architectures - CGRAs, NPUs, FPGAs, spatial accelerators - are **data-flow machines**: computation is triggered by data availability.

Clef bridges this divide:

- **Pure functional code is inherently a data-flow graph.** Referential transparency means ordering follows data dependencies alone.
- **The same source code** lowers to a data-flow graph on spatial architectures (CGRA, NPU, FPGA) and to control-flow code on CPUs/GPUs.
- **The CPU version is a degraded fallback** with explicit "flow loss" - the structural parallelism that data-flow hardware exploits natively is serialized on a von Neumann machine.

This inverts the current industry assumption where CPU is primary and accelerators are optional add-ons. In Clef, the data-flow graph is the primary semantic representation. CPU execution is what you get when the natural parallelism must be serialized.

### How Each Component Enables the Pivot

| Component | Control-flow (CPU/GPU) | Data-flow (CGRA/NPU/FPGA) |
|---|---|---|
| Pure functional code | Sequential operations | IS a data-flow graph |
| Actors | Concurrent processes | Processing elements on spatial fabric |
| Interaction nets | Evaluation strategy (sequential simulation) | Native execution model |
| Incremental<'T> | Change propagation / scheduling | Routing and scheduling fabric |
| Delimited continuations | Actor suspension/resumption | Data-flow token semantics |
| Dimensional types | Memory layout and cache optimization | Hardware mapping contract |

## Why Clef Exists

The computing industry is fragmenting into heterogeneous architectures. Every major chip - AMD Strix Halo, Apple M-series, Intel Meteor Lake - integrates multiple compute substrates with shared or coherent memory. New processor types (CGRAs, NPUs, photonic accelerators, spatial architectures) are emerging at an increasing rate.

Every one of these architectures ships with a bespoke, low-level SDK. There is no high-level language that targets them. There is no C for the data-flow era.

The 40-50 year old operating model - write for a von Neumann machine, optimize later for accelerators - cannot scale to a world with five or six fundamentally different compute substrates on a single chip.

Clef is designed to break this impasse: a high-level language with strong type inference and ML-family ergonomics where the dimensional type system is the contract between software intent and hardware capability. When a new processor type appears, it is a new substrate kind with new dimensional resolutions, expressed in the same language and the same programming model.

## Relationship to F#

Clef uses F#-compatible syntax and inherits Don Syme's design philosophy of lightweight, accessible ML-family programming. Pure F# libraries that do not depend on .NET framework types can compile on Clef directly.

Clef is its own language with its own type system, execution model, and targets:

- NTU dimensional type system with intrinsic units of measure
- Actor-based execution with delimited continuations
- Native compilation via MLIR to CPU, GPU, NPU, FPGA, and CGRA
- Pure functional programming model
- Memory lifetime inference, dimensional type inference, and hardware targeting inference

The relationship is analogous to F* and F#: shared ML heritage and syntax familiarity, independent language with independent goals.

## Compiler Architecture

```
                    Clef Source (.clef)
                         |
                    +----------+
                    |   CCS   |  NTU types, dimensional inference
                    |  (pure)  |  Type checking, SRTP resolution
                    +----+-----+
                         |
                    +---------+
                    |  Baker  |  Type decomposition, saturation
                    +---------+
                         |
                    Program Semantic Graph (PSG)
                    with NTU dimensional types
                         |
              +----------+-----------+
              |   PSG Elaboration    |  Coeffects: SSA, escape analysis,
              |   (Nanopasses)       |  qualifiers, substrate awareness
              +----------+-----------+
                         |
         +-------+-------+-------+-------+
         v       v       v       v       v
      +-----+ +-----+ +-----+ +-----+ +-------+
      | CPU | | GPU | | NPU | |FPGA | | CGRA  |
      |Alex | |Alex | |Alex | |Alex | | Alex  |
      |LLVM | |AMDGPU |MLIR-AIE|CIRCT| |Spatial|
      +--+--+ +--+--+ +--+--+ +--+--+ +---+---+
         |       |       |       |         |
      native   ROCm    XDNA   System-  Spatial
      binary  kernel  runtime  Verilog  config
```

The fork between substrates happens at Alex (code generation). CCS, Baker, nanopasses, and PSG elaboration are all substrate-agnostic. They operate on NTU types with dimensional qualifiers - the substrate kind is carried through the pipeline and resolved at code generation time.

## Ecosystem

| | |
|---|---|
| **Language** | Clef |
| **File extension** | `.clef` |
| **CLI** | `ks` |
| **Search / SEO** | kslang |
| **Actor model** | Olivier (actors) / Prospero (supervisors) |
| **Type system** | Native Type Universe (NTU) |
| **Compiler frontend** | CCS (Clef Compiler Services) |
| **Code generation** | Alex (Elements / Patterns / Witnesses) |
| **Backend orchestration** | Composer |
| **Memory layout contracts** | BAREWire |
| **Scheduling substrate** | Incremental<'T> |

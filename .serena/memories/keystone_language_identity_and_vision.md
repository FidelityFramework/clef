# Keystone Language — Identity, Vision, and Naming

> **Created**: February 2026
> **Context**: Strategic conversation about language identity, divergence from F#, and the vision for
> a concurrent programming language targeting heterogeneous hardware.
> **Status**: FOUNDATIONAL — this captures the language's thesis statement and naming rationale.

## The Thesis

**Keystone is a concurrent programming language that happens to use functional idioms.**

Concurrency is the point. Functional purity is the mechanism that makes the concurrency safe.
The three defining capabilities — all inferred, not annotated:

1. **Dimensional type inference** — width, memory space, numeric format, access pattern, tensor shape
2. **Memory lifetime inference** — escape analysis + actor isolation + purity = no annotations needed
3. **Hardware targeting inference** — computation structure + coeffects + dimensional types = compiler decides substrate

## The Architectural Thesis: ML → Hardware → Incrementalism

> ML semantics are the foundation, hardware targeting creates the structure, and incrementalism is the keystone.

- **ML semantics (foundation)**: Pure functional programming, algebraic types, pattern matching, type inference.
  These provide the mathematical properties (referential transparency, no aliasing, no side effects) that
  make all three inferences possible. The foundation isn't the goal — it's the enabler.

- **Hardware targeting (structure)**: Multi-substrate compilation (CPU, GPU, NPU, FPGA, CGRA) via MLIR.
  The dimensional type system is the contract between software intent and hardware capability.
  This creates the structure — the arch that spans control-flow and data-flow architectures.

- **Incrementalism (keystone)**: Incremental<'T> as the scheduling substrate. The dependency DAG that
  determines when continuations resume, which interaction net reductions are worth doing, how actors
  coordinate, and how wave scheduling maps to hardware. Without it, the other pieces don't cohere.
  With it, the arch stands.

## The Control-Flow / Data-Flow Pivot

The central architectural insight: the same high-level code can lower to either:
- **Control-flow execution** (CPU/GPU) — sequential/SIMT, von Neumann model
- **Data-flow execution** (CGRA/NPU/FPGA) — data-triggered, spatial model

Pure functional code IS a data-flow graph (no side effects = no ordering beyond data dependencies).
The CPU version is a *degraded fallback* with explicit "flow loss" — the parallelism that data-flow
hardware would exploit natively is serialized.

This inverts the industry assumption: the data-flow graph is the primary semantic,
CPU execution is the compatibility fallback.

### Why Each Component Enables the Pivot

| Component | Control-flow role (CPU/GPU) | Data-flow role (CGRA/NPU/FPGA) |
|---|---|---|
| Pure functional code | Sequential operations | IS a data-flow graph |
| Actors | Concurrent processes | Processing elements on spatial fabric |
| Interaction nets | Evaluation strategy (sequential) | Native execution model (graph rewriting) |
| Incremental<'T> | Change propagation / scheduling | Routing/scheduling fabric |
| DCont | Actor suspension/resumption | Data-flow token semantics |
| Dimensional types | Memory layout, lifetime, cache | Hardware mapping contract |

## Naming: Why "Keystone"

### The Divergence from F#

The project has crossed all three thresholds for language independence:

1. **Superset/Subset threshold** (crossed): Valid F# programs are generally NOT valid Keystone programs
   (OO blocked, imperative restricted). Valid Keystone programs use constructs F# doesn't have
   (dimensional types, substrate qualifiers). The set relationship is broken in both directions.

2. **Shared semantics threshold** (crossed): Every semantic axis diverges simultaneously —
   types (NTU ≠ BCL), values (dimensional qualifiers are structural), effects (actor/mailbox model),
   memory (BAREWire + escape analysis), execution (multi-substrate).
   `int` means `NTUint(Resolved Register)`, not `System.Int32`.

3. **Developer expectation threshold** (approached): Already encountered in F# Discord —
   developers expect drop-in compatibility and are confused when told the model is different.

### Comparison to Precedents

| | F* | OxCaml | HardCaml | **Keystone** |
|---|---|---|---|---|
| Relationship to parent | Independent language, shared ancestry | Compiler fork, backward-compatible superset | Library / embedded DSL | **Independent language, F#-compatible syntax** |
| Type system | Replaced (dependent types) | Extended (modes, kinds) | Unchanged | **Replaced (NTU dimensional)** |
| Runtime | Extracts to other languages | Same native target | Standard OCaml | **MLIR → native (multi-substrate)** |
| Semantics | Total-by-default, proofs | Additive (uniqueness, locality) | Unchanged | **Actor-centric, pure functional, concurrent-first** |

Keystone is in the F* category: independent language, acknowledge heritage, don't claim identity.

### The Fable Parallel

Fable (F# → JavaScript) is a **target shift**: same idioms, different platform.
Keystone is an **idiomatic shift**: same syntax, different way of thinking.

Fable-compatible = "F# minus platform dependencies."
Keystone-compatible = "rearchitect around actors, incremental, dimensional types."

When the idioms change, the language has changed — even if the syntax hasn't.

### Why "Keystone" Specifically

- Don Syme pointed to Incremental<'T> — the keystone that made DCont + INet + actors cohere
- A keystone distributes forces → the scheduler distributes computation across substrates
- A keystone is the last piece placed but the most structurally critical
- Evokes construction/engineering, not academia
- Two syllables, memorable, no reference to another language

### Ecosystem Naming

| Concern | Convention |
|---|---|
| Search/SEO | **kslang** |
| GitHub org | **ks-lang** |
| CLI command | **`ks`** |
| File extension | **`.ks`** |
| Domain | **kslang.org** or **ks-lang.org** |

### The Positioning

> **Keystone** is a concurrent programming language where memory lifetimes, dimensional types,
> and hardware targeting are all inferred — no annotations, no runtime, no ceremony.
> It uses ML-family syntax and compiles to CPU, GPU, NPU, and FPGA via MLIR.

This pitch:
- Makes Rust people say "how?"
- Makes Go people say "I want that"
- Makes Python people say "finally"
- Makes FPGA engineers say "wait, really?"
- None of them need to know what F# is

## Why .NET Was Outgrown

Incremental<'T> is the proof: it's a fundamentally cold/lazy computation model, and .NET is
a fundamentally hot/eager runtime. The impedance mismatch isn't a library problem — it's a
substrate problem.

| What Incremental needs | What .NET provides | The conflict |
|---|---|---|
| Cold computation | Eager evaluation | Everything wrapped in Lazy<T>/closures = heap pressure |
| Height-based stabilization | ThreadPool scheduling | Scheduler fights stabilization order |
| Arena lifetime | GC-managed heap | Can't batch-deallocate incremental scopes |
| Continuation suspension | Task<T> promises | async/await is limited, non-composable continuation |

The runtime change enables the language. The language divergence is a consequence of runtime requirements.

## The "New Normal" — Hardware/Software Codevelopment

Keystone is a hardware/software codevelopment platform:
- **C + Unix (1970s)**: Language + OS co-designed for portable systems programming
- **CUDA + GPU (2007)**: Language extension + hardware co-designed for data-parallel compute
- **Keystone (2026)**: Language + dimensional type system co-designed for heterogeneous compute

When a new processor type appears, it's a new substrate kind with new dimensional resolutions,
not a new language. The type system IS the hardware abstraction layer.

## The Pitch (Various Audiences)

- **Rust**: "Concurrent actor language with compile-time safety, targets the same hardware, no lifetime annotations"
- **Go**: "Like goroutines and channels, but the compiler proves your concurrency is safe and dispatches to GPUs"
- **Python ML**: "Write high-level code, target NPU/GPU natively, no C++ escape hatch"
- **Erlang**: "Actor model you already understand, compiles to bare metal and FPGAs"
- **FPGA**: "Write in a real language instead of SystemVerilog, get the same hardware"
- **F#**: "You can already read the syntax. The model is MailboxProcessor taken to its logical conclusion."

## Cross-References

- `firefly_multi_substrate_fanout_architecture` — Multi-substrate fan-out design
- `ntu_dts_lingua_franca` — NTU dimensional type system as cross-substrate lingua franca
- `ntu_type_system` — NTU implementation (width axis)
- `escape_analysis_generalized_design_feb2026` — Memory lifetime inference foundation
- `coeffect_analysis` — Coeffect infrastructure enabling hardware targeting inference
- `psg_control_flow_vs_data_flow_witness_architecture` — Control-flow / data-flow pivot
- `alex_compositional_architecture_elements_patterns_witnesses` — Alex three-layer model
- `resource_management_architecture` — Actor-based resource management
- `fncs_architecture` — FNCS pipeline overview

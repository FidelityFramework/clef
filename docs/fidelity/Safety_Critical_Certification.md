# Safety-Critical Certification and Industrial Control Systems

> Keystone's nanopass architecture, graph-native compilation, and proof-carrying pipeline satisfy safety-critical certification requirements by construction.

## The Industry Problem

Safety-critical certification standards (DO-178C for avionics, IEC 61508 for industrial, ISO 26262 for automotive) demand full traceability from source code to generated assembly, structural coverage of all control flow paths, and deterministic behavior. Monolithic compilers with complex optimization passes obscure the mapping from source to assembly, making certification prohibitively expensive.

As of early 2026, no Rust component has achieved DO-178C certification. The Rust compiler hides control flow paths through MIR transformations and LLVM optimization passes, complicating the traceability that auditors require.

## How Keystone Satisfies Certification by Construction

### Source-to-Object Traceability

The PSG preserves source ranges through every nanopass phase. PSG nodes carry their origin location from source construction through typed tree overlay, through every nanopass enrichment, through coeffect analysis, through Alex code generation to MLIR to native code.

The nanopass architecture means each transformation is:
- Small (one concern per pass)
- Auditable (each pass does one well-defined thing)
- Non-destructive (soft-delete preserves graph structure)
- Observable (Atelier's Pipeline Inspector visualizes every phase)

A certification auditor can step through each nanopass and verify the transformation is correct. This is fundamentally different from auditing the entirety of LLVM's optimization pipeline.

### Structural Coverage

In a graph-native language, every control flow path is visible in the PSG. There are no hidden paths because the program IS the data-flow graph, pure functional code has no side effects creating implicit control paths, and the actor model makes concurrency structure explicit.

Flow loss analysis enumerates exactly where and why the compiler introduced control flow during CPU lowering. Every introduced branch traces to a specific edge in the PSG. A certification auditor does not need to reverse-engineer which source construct generated a branch instruction.

### Tool Qualification

Each nanopass is a small, defined transformation that can be independently qualified. This is a fundamentally different proposition from qualifying a monolithic compiler. MLIR is a well-defined, well-documented intermediate representation with a large verification community.

### Proof-Carrying Compilation

The F*/SMT connection enables proof obligations attached to PSG nodes. Invariants over subgraphs are machine-checked. Lemmas carry through the hypergraph from source to native code. Incremental proof checking means changes only re-verify affected subgraphs.

This provides formal verification integrated into the compilation pipeline, stronger than the MC/DC coverage and independent verification that certification standards require.

### Deterministic Behavior

- Pure functional language with deterministic semantics
- Deterministic memory management (escape analysis + arenas, no GC)
- No undefined behavior by construction (no unsafe blocks, no null, no uninitialized memory)
- MLIR is a deterministic IR; nanopass pipeline applies transformations in fixed order
- Same source produces same binary every time

## Mapping to Certification Standards

| Requirement | DO-178C (Avionics) | IEC 61508 (Industrial) | ISO 26262 (Automotive) |
|---|---|---|---|
| Traceability | Full source-to-object | Requirements to implementation | ASIL-dependent |
| Structural coverage | MC/DC at Level A | Branch coverage at SIL 3-4 | MC/DC at ASIL D |
| Tool qualification | DO-330 | Proven-in-use or qualified | ISO 26262 Part 8 |
| Deterministic behavior | Required | Required | Required |
| Formal verification | Recommended for Level A | Recommended for SIL 4 | Recommended for ASIL D |

All five requirements are addressed by Keystone's architecture: PSG traceability, graph-native structural coverage, nanopass tool qualification, pure functional determinism, and proof-carrying formal verification.

## Control Systems as Natural Fit

Industrial control systems are networks of communicating agents (sensors, controllers, actuators, supervisors) operating across multiple compute substrates (PLCs, embedded processors, SCADA servers, HMI workstations). This maps directly to Keystone's programming model.

### The Actor Model Maps to Control Architecture

| Control System Component | Keystone Equivalent |
|---|---|
| Sensors | Actors that emit readings |
| Controllers (PID, state machines) | Actors that process inputs and emit commands |
| Actuators (valves, motors) | Actors that receive commands |
| Safety systems, SCADA | Prospero supervisors managing actor networks |
| Communication buses (CAN, Modbus, OPC-UA) | BAREWire contracts across substrate boundaries |

The Olivier/Prospero actor/supervisor model describes the system topology directly. The programming model matches the physical architecture.

### Incremental<'T> Maps to the Control Loop

A control system propagates changes through a dependency graph: sensor reading changes, controller updates, actuator responds. This is Incremental<'T> with height-based stabilization:

- Sensor nodes at the leaves of the dependency DAG
- Controller nodes at intermediate heights
- Actuator nodes at the top
- Cutoff semantics: if a sensor reading hasn't changed beyond threshold, don't propagate (directly analogous to deadband in control systems)

### Multi-Substrate Targeting Maps to the Hardware Reality

A refinery control system already spans multiple compute substrates. Today these are programmed in separate languages (ladder logic for PLCs, C for embedded, C++ for SCADA, JavaScript for HMI) with separate toolchains and no type safety across boundaries.

Keystone compiles a single codebase to all substrates with BAREWire contracts ensuring type-safe communication at every boundary:

| Substrate | Control System Role | Keystone Target |
|---|---|---|
| FPGA / PLC | Safety interlocks, fast inner loops | CIRCT → SystemVerilog |
| Embedded CPU | Control algorithms, protocol handling | LLVM → native binary |
| Server CPU | SCADA supervision, data logging, optimization | LLVM → native binary |
| NPU | Predictive analytics, anomaly detection | MLIR-AIE → XDNA runtime |
| GPU | Operator visualization, simulation | AMDGPU → ROCm |

### Dimensional Types Carry Safety Information

- Memory space qualifiers map to PLC memory areas (input, output, markers, data blocks)
- Access patterns (volatile, streaming) map to I/O access semantics
- Numeric format (fixed-point for control loops, posit for high-precision accumulation) carried in the type
- Units of measure are intrinsic: `temperature<celsius>` and `pressure<bar>` are distinct types that prevent unit confusion (the kind of error that crashed Mars Climate Orbiter)

### Deterministic Execution for Real-Time

Control systems require predictable timing. Keystone provides:

- Deterministic memory via escape analysis and per-actor arenas (no GC pauses)
- Delimited continuations as compiler transformations (no async runtime)
- Actor isolation prevents priority inversion
- Arena-per-actor means predictable allocation and deallocation timing
- Flow loss analysis quantifies worst-case execution on CPU targets

## Industry Applications

### Oil and Gas
- Well control systems (safety-critical interlocks on FPGA, supervisory control on CPU)
- Pipeline SCADA (field instruments → RTUs → control center, all type-safe via BAREWire)
- Refinery process control (PLC safety interlocks + DCS control loops + operator HMI)

### Power Grid
- Protection relays (FPGA for sub-cycle response, CPU for coordination)
- SCADA/EMS (supervisor actors over substation actors)
- Renewable integration (NPU for generation forecasting, CPU for economic dispatch)

### Automotive (ISO 26262)
- ADAS sensor fusion (NPU for perception, CPU for planning, GPU for visualization)
- Powertrain control (FPGA for fast inner loops, CPU for supervisory control)
- Vehicle networks (actors map to ECUs communicating via BAREWire over CAN/Ethernet)

### Medical Devices (IEC 62304)
- Patient monitoring (streaming sensor data with real-time analysis)
- Infusion pumps (safety-critical control loops with formal verification)
- Diagnostic imaging (GPU for reconstruction, CPU for analysis, FPGA for signal acquisition)

# Safety-Critical Certification and Control Systems

> **Created**: February 2026
> **Context**: Keystone's architectural properties satisfy safety-critical certification requirements (DO-178C, IEC 61508, ISO 26262) by construction, and the programming model maps naturally to industrial control systems.

## DO-178C Certification (Avionics)

LaurieWired identified that Rust lacks verification tools for DO-178C (FAA standard). The core problem: monolithic compilers with complex optimization passes obscure the mapping from source code to assembly, preventing the full traceability that certification demands.

Keystone's architecture satisfies DO-178C requirements by construction:

### Source-to-Object Traceability

The PSG preserves source ranges through every nanopass phase to MLIR to native code. At no point is the source-to-intermediate mapping destroyed. Nanopass architecture means each transformation is small, auditable, and non-destructive (soft-delete preserves structure).

Atelier's Pipeline Inspector visualizes every step: Source → PSG → Nanopass Phases → Coeffects → MLIR → LLVM IR → Assembly. This IS the traceability document DO-178C demands.

### Structural Coverage (MC/DC)

In a graph-native language, every control flow path is visible in the PSG. There are no hidden paths because:
- The program IS the data-flow graph
- No side effects means no hidden state transitions creating implicit control paths
- The actor model makes concurrency structure explicit
- Flow loss analysis enumerates exactly where and why control flow was introduced during CPU lowering

### Tool Qualification

Nanopass architecture: each pass is small, independently auditable, independently qualifiable. This is fundamentally different from qualifying the entirety of LLVM. MLIR is a well-defined, well-documented IR with a large verification community.

### Proof-Carrying Compilation

Goes beyond DO-178C requirements. F*/SMT connection means proof obligations are attached to PSG nodes, invariants over subgraphs are machine-checked, and lemmas carry through compilation. This provides formal verification integrated into the pipeline, stronger than the MC/DC coverage and independent verification that DO-178C Level A requires.

### Deterministic Compilation

Same source produces same binary every time. Pure functional language (deterministic semantics), MLIR is deterministic, nanopass pipeline applies transformations in fixed order.

## Mapping to Certification Standards

| Requirement | DO-178C (Avionics) | IEC 61508 (Industrial) | ISO 26262 (Automotive) | Keystone Answer |
|---|---|---|---|---|
| Traceability | Full source-to-object | Requirements to implementation | ASIL-dependent | PSG source ranges through all phases |
| Structural coverage | MC/DC at Level A | Branch coverage at SIL 3-4 | MC/DC at ASIL D | Graph-native: all paths visible in PSG |
| Tool qualification | DO-330 | Proven-in-use or qualified | ISO 26262 Part 8 | Nanopass: small passes, individually qualifiable |
| Deterministic behavior | Required | Required | Required | Pure functional, no undefined behavior |
| Formal verification | Recommended for Level A | Recommended for SIL 4 | Recommended for ASIL D | Proof-carrying compilation via F*/SMT |

## Control Systems as Natural Fit

Industrial control systems (oil and gas, power grid, refinery, manufacturing) map directly to Keystone's programming model:

### The Actor Model IS the Control Architecture

Control systems are networks of communicating agents:
- Sensors (data sources) → actors that emit readings
- Controllers (PID loops, state machines) → actors that process inputs and emit commands
- Actuators (valves, motors, switches) → actors that receive commands
- Supervisors (SCADA, safety systems) → Prospero supervisors managing actor networks

The Olivier/Prospero actor/supervisor model matches the physical architecture of industrial control systems. The programming model describes the system topology directly.

### Incremental<'T> IS the Control Loop

A control system propagates changes through a dependency graph: sensor reading changes → controller updates → actuator responds. This IS Incremental<'T> with height-based stabilization:
- Sensor nodes at the leaves
- Controller nodes at intermediate heights
- Actuator nodes at the top
- Cutoff: if a sensor reading hasn't changed beyond threshold, don't propagate

### Multi-Substrate Targeting IS the Hardware Reality

A refinery control system already spans multiple compute substrates:
- PLCs (essentially FPGAs) running safety-critical interlocks
- Embedded processors running control algorithms
- SCADA servers running supervision and data logging
- HMI workstations running operator interfaces

Today these are programmed in four different languages (ladder logic, C, C++, JavaScript) with four different toolchains and no type safety across boundaries. Keystone with BAREWire contracts provides type-safe communication across all substrate boundaries.

### Dimensional Types Carry Safety Information

- Memory space qualifiers map to PLC memory areas (input, output, markers, data blocks)
- Access patterns (volatile, streaming) map to I/O access semantics
- Numeric format (fixed-point for control loops, IEEE for HMI display) carried in the type

### Deterministic Execution for Real-Time

- No GC pauses (deterministic memory via escape analysis + arenas)
- No async runtime (delimited continuations are compiler transformations)
- Actor isolation prevents priority inversion
- Arena-per-actor means predictable allocation/deallocation timing

## Specific Industry Applications

### Oil and Gas
- Well control systems (safety-critical, needs DO-178C/IEC 61508 equivalents)
- Pipeline SCADA (multi-substrate: field instruments → RTUs → control center)
- Refinery process control (PLC interlocks + DCS control + HMI)

### Power Grid
- Protection relays (FPGA for speed, CPU for coordination)
- SCADA/EMS (supervisor actors over substation actors)
- Renewable integration (NPU for forecasting, CPU for dispatch)

### Automotive (ISO 26262)
- ADAS sensor fusion (NPU for perception, CPU for planning, GPU for visualization)
- Powertrain control (FPGA for fast inner loops, CPU for supervisory control)
- Vehicle network (actors = ECUs communicating via BAREWire over CAN/Ethernet)

### Medical Devices (IEC 62304)
- Patient monitoring (streaming sensor data, real-time analysis)
- Infusion pumps (safety-critical control loops)
- Diagnostic imaging (GPU for reconstruction, CPU for analysis, FPGA for acquisition)

## Cross-References

- `keystone_language_identity_and_vision` - Language thesis and control-flow/data-flow pivot
- `hypergraph_compilation_and_competitive_differentiation` - Proof-carrying compilation through hypergraph
- `flow_loss_tooling_and_hardware_partnerships` - Flow loss metrics and hardware partnerships
- `firefly_multi_substrate_fanout_architecture` - Multi-substrate fan-out design
- `escape_analysis_generalized_design_feb2026` - Deterministic memory management
- `resource_management_architecture` - Actor-based resource management

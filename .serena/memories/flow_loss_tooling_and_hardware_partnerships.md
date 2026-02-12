# Flow Loss Tooling and Hardware Partnership Strategy

> **Created**: February 2026
> **Context**: LSP/tooling feature concept for quantifying data-flow parallelism lost when targeting CPU.
> **Status**: DESIGN CONCEPT - captures the vision and strategic rationale.

## The Concept

A Keystone LSP feature that shows "data flow loss" for programs targeting CPU. Because the compiler has both representations - the data-flow graph (PSG / interaction net) and the control-flow lowering (CPU Alex output) - the delta between them is computable. This delta is the flow loss: a quantitative measure of parallelism that exists in the program but is serialized by the CPU target.

This feature is only possible because Keystone is graph-native. The program IS the data-flow graph. The CPU lowering is a derived artifact. Comparing them is a natural operation within the compilation pipeline.

## Metrics

### Parallelism Ratio

How many operations could fire simultaneously on a data-flow fabric vs. how many the CPU must serialize. A function with 200 independent operations serialized to a single thread has a very different ratio than one with a deep dependency chain.

### Critical Path vs. Total Work

The ratio between the longest dependency chain (critical path length) and total operations. This is a well-understood metric from parallel computing theory:
- Ratio near 1.0: computation is inherently sequential, minimal flow loss
- Ratio near 0.01: 99% of work could execute concurrently on a spatial architecture

### Serialization Points

Specific source locations where the compiler introduced ordering that does not exist in the data-flow graph. Surfaced as inline LSP annotations: "this operation waits for N predecessors that could execute concurrently on a data-flow substrate."

### Memory Movement Overhead

Data that would be local to a processing element on a spatial architecture but must traverse the CPU cache hierarchy. The dimensional types (memory space, access pattern) make this quantifiable. Streaming access patterns that would be zero-cost channels on a CGRA become cache-dependent loads on CPU.

### Substrate Comparison Estimates

With a substrate performance model for a specific architecture: "this subgraph: 47 cycles on Tenstorrent Wormhole, 3200 cycles on x86." Requires per-substrate cost models, which hardware partners could provide.

## LSP Visualization

- **Heat map over source code**: regions heavily penalized by CPU serialization glow hot, inherently sequential regions stay cool. Developers see where data-flow parallelism is wasted.
- **Inline annotations**: serialization points marked with parallelism potential ("12 independent operations serialized here")
- **Function-level summary**: each function/actor gets a flow loss score, visible in code lens or hover
- **Substrate comparison panel**: side-by-side estimated performance across available substrate targets

## Implementation Path

The metrics derive from analysis that largely already exists or is planned:

1. **PSG structure** provides the data-flow graph (node count, edge structure, dependency chains)
2. **Interaction net representation** provides the ideal parallel execution model
3. **Incremental<'T> DAG** provides the height-based structure (height = critical path through that subgraph)
4. **Escape analysis / coeffects** provide memory movement information
5. **CPU Alex output** provides the serialized instruction sequence

The flow loss computation is essentially: compare the interaction net's parallel reduction potential against the CPU's sequential instruction stream. The infrastructure for both representations already exists in the compiler pipeline.

## Strategic Value: Hardware Partnerships

The flow loss tooling turns Keystone into a demand generation tool for data-flow hardware companies.

**The pitch to hardware companies**: "Here's a language where developers write high-level code and the tooling shows them quantitatively how much performance they're leaving on the table by running on a CPU. Your hardware is the answer to that gap. Ship Keystone support as the programming model for your architecture."

**Target partners**:
- **Tenstorrent**: RISC-V mesh architecture (Wormhole, Blackhole). Data-flow oriented, would benefit directly from showing developers how much parallelism their code has that x86 wastes.
- **NextSilicon**: Runtime reconfigurable compute. Their architecture dynamically adapts to computation patterns - the flow loss metric shows exactly the patterns their hardware exploits.
- **Cerebras**: Wafer-scale spatial architecture. Massive parallelism that conventional languages cannot express or exploit.
- **AMD XDNA (NPU)**: Already in the multi-substrate fan-out architecture. Flow loss on CPU vs. NPU tile array.
- **FPGA vendors (AMD/Xilinx, Intel/Altera)**: Flow loss for computations that would map naturally to spatial hardware.

**The dynamic**: the hardware company does not have to convince developers their architecture is worth learning. The developer's own IDE shows them the flow loss, and the hardware is the obvious answer. This inverts the traditional relationship where hardware companies struggle to get developer adoption for new architectures.

## Competitive Moat

This feature is structurally impossible for languages where the program is conventional control-flow code:
- Mojo/Python: the program is imperative control-flow. You'd have to *infer* the data-flow graph from the control-flow, which is the inverse problem and much harder.
- CUDA/OpenCL: the programmer manually specifies the parallelism. There's no "ideal parallel version" to compare against because the programmer already made the parallelism decisions.
- Rust/Go/C++: same as above - conventional control-flow languages with manual parallelism.

Keystone can do this because the program IS the data-flow graph. The flow loss is a natural measurement, not a heroic analysis.

## Cross-References

- `keystone_language_identity_and_vision` - The "control-flow / data-flow pivot" section
- `hypergraph_compilation_and_competitive_differentiation` - Hypergraph compilation model
- `firefly_multi_substrate_fanout_architecture` - Multi-substrate targets
- `psg_control_flow_vs_data_flow_witness_architecture` - PSG witness architecture for CF/DF
- `alex_compositional_architecture_elements_patterns_witnesses` - Alex three-layer model (where lowering happens)

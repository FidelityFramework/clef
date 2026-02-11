# Firefly Multi-Substrate Fan-Out Architecture

> **Created**: February 2026
> **Context**: Downstream Firefly design determined by FNCS NTU dimensional extensions.
> **Status**: SPECULATIVE DESIGN — complete problem space mapping, not implementation.
> **Premise**: "Whole baby" — design ALL substrates up front, implement incrementally.
> Do NOT over-index on CPU. The fan-out IS the new normal for compute.

## The Anti-Pattern We're Avoiding

The current Alex architecture is CPU-only: Elements emit LLVM dialect, Patterns compose
LLVM operations, Witnesses assume a single MLIR target. This is the **exact myopia** that
leads to retooling when GPU/NPU/FPGA support is needed. The fix is not "bolt on GPU support"
— it's designing the substrate dispatch at the foundation so ALL targets are first-class
from day one of the architecture, even if implementation is incremental.

## The Fan-Out Model

```
                    F# Source (.fidsln)
                         │
                    ┌────┴────┐
                    │  FNCS   │  ← NTU types, qualifiers, SubstrateKind
                    │  (pure) │     ALL substrate-agnostic
                    └────┬────┘
                         │
                    SemanticGraph (PSG)
                    with NTU dimensional types
                         │
              ┌──────────┴──────────┐
              │   PSGElaboration    │  ← Coeffects: SSA, escape, qualifiers
              │   (Firefly Middle)  │     Substrate-aware analysis
              └──────────┬──────────┘
                         │
                   TransferCoeffects
                   + SubstrateKind
                         │
         ┌───────────────┼───────────────┐───────────────┐
         ▼               ▼               ▼               ▼
    ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐
    │ CPU Alex│    │ GPU Alex│    │ NPU Alex│    │FPGA Alex│
    │  LLVM   │    │GPU/AMDGPU   │ MLIR-AIE│    │  CIRCT  │
    └────┬────┘    └────┬────┘    └────┬────┘    └────┬────┘
         │              │              │              │
    LLVM IR        ROCm kernel    AIE overlay    SystemVerilog
         │              │              │              │
    native binary  HSA dispatch   XDNA runtime   bitstream
```

The fork happens at Alex, not before. FNCS, Baker, nanopasses, PSGElaboration are
ALL substrate-agnostic. They operate on NTU types with qualifiers — the SubstrateKind
is carried through but doesn't change the analysis.

## Alex Substrate Dispatch Architecture

### The Three-Layer Model Stays — But Elements Fork

The Elements → Patterns → Witnesses architecture is correct. What changes:

```
Elements/
  Common/              ← arith, memref, func (shared across ALL substrates)
  LLVM/                ← llvm.alloca, llvm.call, llvm.getelementptr (CPU)
  GPU/                 ← gpu.launch, gpu.barrier, amdgpu.buffer_load (GPU)
  AIE/                 ← aie.tile, aie.flow, aie.dma, objectfifo (NPU)
  CIRCT/               ← hw.module, comb.add, seq.reg, handshake.fork (FPGA)

Patterns/
  Common/              ← Substrate-agnostic compositions (struct layout, etc.)
  Memory/              ← pAllocValue reads SubstrateKind → dispatches to substrate elements
  Arithmetic/          ← pBinaryOp: arith dialect is shared, but memory ops differ
  Transfer/            ← NEW: BAREWire cross-substrate data movement patterns
  Substrate/
    CPU/               ← CPU-specific pattern compositions
    GPU/               ← Kernel launch, coalescing, AoS→SoA patterns
    NPU/               ← Tile configuration, ObjectFIFO, DMA descriptor patterns
    FPGA/              ← Module instantiation, port mapping, pipeline patterns

Witnesses/
  ← UNCHANGED. Witnesses observe PSG structure, delegate to Patterns.
  ← SubstrateKind flows through coeffects, not witness logic.
  ← A witness for LazyExpr calls pBuildLazyStruct regardless of substrate.
  ← The Pattern dispatches to the right Elements based on coeffects.
```

**Key insight**: Witnesses are substrate-agnostic because they match PSG *structure*,
which is the same regardless of target. The substrate difference lives in how that
structure *materializes* — which is the Pattern → Element composition.

### Substrate Dispatch Mechanism

Patterns read `SubstrateKind` from coeffects:

```fsharp
// Pattern dispatches based on substrate
let pAllocValue (ssas: SSA list) : PSGParser<MLIROp list> =
    parser {
        let! state = getUserState
        match PlatformContext.substrateKind state.Platform with
        | SubstrateKind.CPU ->
            // Stack or heap via escape analysis (existing logic)
            return! pAllocValueCPU ssas
        | SubstrateKind.GPU ->
            // Global, Shared, or Private based on NTUMemorySpace qualifier
            return! pAllocValueGPU ssas
        | SubstrateKind.NPU ->
            // Tile-local SRAM or data memory
            return! pAllocValueNPU ssas
        | SubstrateKind.FPGA ->
            // BRAM, registers, or AXI interface ports
            return! pAllocValueFPGA ssas
    }
```

This is NOT a massive switch statement in every pattern. Most patterns compose
Common elements (arith, memref) that are substrate-agnostic. Only patterns that
touch memory allocation, calling conventions, or hardware-specific features need
the dispatch.

### What's Shared vs Substrate-Specific

| Concern | Shared | Substrate-Specific |
|---------|--------|-------------------|
| Integer arithmetic | arith.addi, arith.muli | — |
| Float arithmetic | arith.addf, arith.mulf | — |
| Posit arithmetic | — | CPU: software lib calls; FPGA: CIRCT hw pipeline |
| Stack allocation | — | CPU: llvm.alloca; GPU: private mem; FPGA: registers |
| Heap allocation | — | CPU: memref.alloc; GPU: global alloc; NPU: tile mem |
| Function calls | func.call (for pure) | CPU: llvm.call; GPU: gpu.launch; FPGA: hw.instance |
| Struct layout | Shared (BAREWire) | Transfer format may vary at boundaries |
| Control flow | cf.br, cf.cond_br | GPU: warp divergence; FPGA: handshake fork/join |
| Closures | Capture layout shared | Allocation strategy substrate-specific |
| Seq/Lazy thunks | PSG structure shared | Materialization substrate-specific |

**Important**: arith and memref dialects are the *lingua franca* of MLIR.
They work on all substrates. The substrate-specific dialects layer ON TOP of them.
This means a large fraction of existing Alex code (Common Elements + arithmetic
Patterns) transfers directly. The new work is substrate-specific memory management,
calling conventions, and hardware features.

## PSGElaboration Coeffect Extensions

### Existing Coeffects (unchanged)
- SSA Assignment
- Mutability Analysis
- Capture Analysis
- Pattern Binding Analysis
- String Collection
- Escape Analysis (needs substrate awareness — see below)

### Escape Analysis → Substrate-Aware Allocation

Current `EscapeKind`:
```fsharp
type EscapeKind =
    | StackScoped            // CPU: stack; GPU: private; NPU: tile SRAM; FPGA: registers
    | EscapesViaClosure      // CPU: heap; GPU: global; NPU: data mem; FPGA: BRAM
    | EscapesViaReturn       // CPU: heap; GPU: global/shared; NPU: output port; FPGA: AXI
    | EscapesViaByRef        // CPU: pin; GPU: global; FPGA: MMIO port
```

The EscapeKind DU itself doesn't need to change — it describes *escape behavior*,
not *allocation strategy*. What changes is how `pAllocValue` (in Alex) interprets
the EscapeKind *in the context of SubstrateKind*:

| EscapeKind | CPU | GPU | NPU | FPGA |
|------------|-----|-----|-----|------|
| StackScoped | llvm.alloca | private mem | tile SRAM | registers |
| EscapesViaClosure | memref.alloc (arena) | global alloc | data memory | BRAM |
| EscapesViaReturn | memref.alloc (arena) | global/shared | output FIFO | AXI port |

### New Coeffect: QualifierResolution

When `TypeConRef.Qualifiers` is `Some`, a new PSGElaboration pass resolves qualifiers
against the substrate:

```fsharp
type QualifierResolution = {
    NodeId: NodeId
    ResolvedMemorySpace: MLIRAddressSpace  // concrete MLIR address space int
    ResolvedAccessPattern: AccessSemantics  // non-temporal, volatile, etc.
}
```

CPU: most qualifiers resolve to default (escape analysis dominates)
GPU: Global→1, Shared→3, Private→5 (AMDGPU address space convention)
NPU: maps to MLIR-AIE memory tile configurations
FPGA: maps to port types (AXI4, AXI-Lite, AXI-Stream)

### New Coeffect: SubstrateTransfer (for cross-substrate edges)

When a value crosses substrate boundaries (via BAREWire), PSGElaboration computes:

```fsharp
type SubstrateTransfer = {
    SourceNode: NodeId
    SinkNode: NodeId
    SourceSubstrate: SubstrateKind
    SinkSubstrate: SubstrateKind
    TransferStrategy: TransferStrategy
}

type TransferStrategy =
    | ZeroCopy           // HSA coherent (CPU↔GPU↔NPU on Strix Halo)
    | DMATransfer        // CPU↔FPGA via PCIe/AXI
    | FormatConversion   // e.g., posit bits on FPGA → IEEE float on CPU
    | Broadcast          // One source, multiple sink substrates
```

## The Posit Story (Corrected)

**CPU does NOT understand posit arithmetic.** There are no posit ALU instructions.

What CPU CAN do:
- **Store** posit bits as uint{8,16,32,64} — same NTUKind, different type identity
- **Batch-move** posit bits in AVX2/AVX-512 registers (container, not compute)
- **Software decode/encode** — vectorizable but still software
- Quire32 = 64 bytes = one AVX-512 register = one cache line (storage, not compute)

What FPGA DOES:
- **Dedicated posit hardware pipelines** — PACoGen-style combinational circuits
- **Native posit arithmetic** — add, multiply, FMA, accumulate in hardware
- This is the ONLY substrate that "understands" posit semantics natively

The flow:
1. CPU marshals posit bits into BAREWire-compatible layout
2. DMA transfers to FPGA over PCIe/AXI
3. FPGA computes with native posit hardware
4. Results DMA back to CPU as posit bits
5. CPU stores results (or converts to IEEE float at boundary)

For Alex:
- CPU Alex: `NTUposit` → `i{8,16,32,64}` (same LLVM integer types, different NTUKind identity)
- FPGA Alex: `NTUposit` → CIRCT `hw` pipeline with posit semantics
- The NTUKind distinction (`NTUposit ≠ NTUfloat`) prevents accidental IEEE interpretation

## Inter-Substrate Communication (BAREWire)

### Transfer Topology (Strix Halo + external FPGA)

```
CPU ↔ GPU:   HSA coherent memory (ZeroCopy — same virtual address space)
CPU ↔ NPU:   HSA coherent memory (ZeroCopy — XDNA 2 shares address space)
GPU ↔ NPU:   HSA coherent memory (ZeroCopy — all on-die)
CPU ↔ FPGA:  PCIe/AXI (DMATransfer — external device, BAREWire defines layout)
GPU ↔ FPGA:  Not direct — route through CPU (CPU mediates PCIe DMA)
NPU ↔ FPGA:  Not direct — route through CPU
```

### BAREWire's Role

BAREWire defines the memory layout contract at substrate boundaries:
- Both sides compute TypeLayout from the same NTU types
- `TypeLayout.baseLayout` strips qualifiers → identical size/align on both sides
- Qualifier MISMATCH at boundary → triggers transfer pattern selection
- Posit bits are trivially serializable (bits ARE the representation, no endian issues)

### Transfer Pattern Selection

```fsharp
let selectTransferPattern (source: SubstrateKind) (sink: SubstrateKind) 
                          (qualifiers: NTUQualifiers option) : TransferStrategy =
    match source, sink with
    | CPU, GPU | GPU, CPU | CPU, NPU | NPU, CPU | GPU, NPU | NPU, GPU ->
        ZeroCopy  // HSA coherent on Strix Halo
    | CPU, FPGA | FPGA, CPU ->
        match qualifiers with
        | Some q when q.AccessPattern = Some NTUAccessPattern.Streaming ->
            DMATransfer  // AXI-Stream for streaming data
        | _ ->
            DMATransfer  // AXI-Lite for random access
    | _, FPGA | FPGA, _ ->
        // GPU/NPU to FPGA routes through CPU
        DMATransfer
```

## Incremental<'T> as the Compute Graph Substrate

The incremental dependency DAG is what makes the multi-substrate model *coherent*:

- **Height-based stabilization = wave scheduling**: 
  NPU tiles fire in height order; GPU wavefronts batch by stabilization level.
  The same PSG structure drives scheduling across all substrates.

- **Cutoff bounds propagation across substrates**:
  If a CPU node's cutoff determines "unchanged," downstream GPU nodes skip entirely.
  BAREWire transfer is elided — no data moved, no kernel launched.

- **Applicative subgraphs = static hardware configuration**:
  On NPU: static AIE overlay (tile placement + stream routing at compile time)
  On FPGA: static hardware module instantiation
  On GPU: pre-allocated dispatch groups

- **Monadic subgraphs = dynamic dispatch**:
  On NPU: ERT ctrlcode selects active tiles
  On GPU: runtime kernel selection
  On CPU: standard conditional execution

- **Cross-substrate dependency edges**:
  `Incremental<FeatureMap, npu_tile>` depending on `Incremental<SensorData>`(CPU) 
  → BAREWire transfer at the edge, with DMA descriptor from type layout
  → Qualifier mismatch (Default on CPU → Shared on NPU) selects transfer strategy

## The fidsln/fidproj Orchestration Model

### Firefly BackEnd Responsibilities (NEW)

```
my-app.fidsln
├── shared/          ← BAREWire contracts, shared NTU types (compiles to: type validation artifact)
├── cpu.fidproj      ← SubstrateKind = CPU (compiles to: native binary)
├── gpu.fidproj      ← SubstrateKind = GPU (compiles to: HSA kernel binary)
├── npu.fidproj      ← SubstrateKind = NPU (compiles to: AIE overlay + tile ELFs)
└── fpga.fidproj     ← SubstrateKind = FPGA (compiles to: bitstream via synthesis)
```

Firefly BackEnd must:
1. Parse fidsln to discover substrate projects
2. Construct per-project SubstrateContext (PlatformContext + substrate fields)
3. Type-check shared/ project → validate BAREWire contracts
4. Compile each fidproj through FNCS → PSGElaboration → Alex (with substrate dispatch)
5. Link/package heterogeneous outputs into a deployable artifact
6. Generate runtime orchestration code (HSA dispatch, DMA setup, FPGA configuration)

### shared/ Project Semantics

The `shared/` project defines types that cross substrate boundaries:
- BAREWire layout contracts (deterministic memory representations)
- NTU type definitions used by multiple substrates
- Inter-substrate message/data type declarations

It compiles to a **type validation artifact** — not executable code.
Each substrate project imports shared types and validates layout agreement.
If `shared/` defines `type SensorReading = { timestamp: int64; value: posit32 }`,
then cpu.fidproj and fpga.fidproj must agree on the BAREWire layout of that type.

## Milestones (Speculative, Not Prioritized)

### GPU "Hello Compute" (first non-CPU substrate)
- fidsln with cpu.fidproj + gpu.fidproj + shared/
- Shared type: array of floats
- CPU fills array, GPU computes (e.g., vector add), CPU reads result
- HSA zero-copy: no DMA, just pointer handoff via BAREWire
- Exercises: GPU Elements, gpu.launch Pattern, SubstrateKind dispatch

### FPGA "Hello Blinky" (first hardware synthesis)
- fidsln with cpu.fidproj + fpga.fidproj
- FPGA toggles LED at a rate
- CPU sends configuration via PCIe/AXI (BAREWire message)
- Exercises: CIRCT Elements, hw.module Pattern, DMA transfer Pattern
- Validates: MLIR → CIRCT → handshake → hw/comb/seq → SystemVerilog → bitstream

### Posit Coprocessor (first cross-substrate compute)
- fidsln with cpu.fidproj + fpga.fidproj + shared/
- Shared: posit32 type + BAREWire layout
- CPU marshals posit bits, DMA to FPGA, FPGA computes, DMA back
- Exercises: NTUposit type flow end-to-end, FormatConversion transfer patterns

### Incremental Multi-Substrate (the full vision)
- fidsln with cpu + gpu + npu + shared
- Incremental dependency DAG spanning CPU→NPU→GPU
- Height-based wave scheduling across substrates
- Cutoff propagation elides unnecessary cross-substrate transfers
- Exercises: Everything

## Relationship to Existing Architecture

| Component | Current | Multi-Substrate Extension |
|-----------|---------|--------------------------|
| FNCS | Substrate-agnostic (already) | NTUposit, NTUQualifiers, SubstrateKind (DONE) |
| Baker | Substrate-agnostic | Possible AoS→SoA for GPU (future) |
| Nanopasses | Substrate-agnostic | Unchanged |
| PSGElaboration | CPU-focused escape analysis | Substrate-aware allocation + QualifierResolution + SubstrateTransfer |
| Alex Elements | LLVM-only | Per-substrate element modules (LLVM, GPU, AIE, CIRCT) |
| Alex Patterns | LLVM-focused | Substrate-dispatching patterns + Transfer patterns |
| Alex Witnesses | Already substrate-agnostic conceptually | Unchanged (this is the beauty of the architecture) |
| Firefly BackEnd | Single fidproj | Multi-project orchestration (fidsln model) |
| BAREWire | Intra-process layout | Inter-substrate layout + transfer protocol |

## The "New Normal" Thesis

Multi-substrate computation is not a niche feature. It's the architectural direction
of computing: CPUs coordinate, GPUs parallelize, NPUs infer, FPGAs specialize.
Every major chip (Strix Halo, Apple M-series, Intel Meteor Lake) integrates
multiple compute substrates with shared or coherent memory.

Designing the compiler for a single substrate and bolting on others later creates
exactly the kind of impedance mismatch that NTU was designed to prevent at the type
level. The NTU dimensional type system (qualifiers, memory spaces, substrate kinds)
exists precisely so that the type system expresses the full problem space from the
start, even if code generation catches up incrementally.

The fan-out is not optional. It's the architecture.

## Cross-References

- `ntu_dts_lingua_franca` — NTU dimensional type system (FNCS side, IMPLEMENTED)
- `alex_compositional_architecture_elements_patterns_witnesses` — Current Alex three-layer model
- `escape_analysis_generalized_design_feb2026` — Current escape analysis (needs substrate awareness)
- `coeffect_analysis` — Coeffect infrastructure (PSGElaboration → Alex)
- `ntu_type_flow_prd_guidance` — Type flow through MLIR (needs substrate extension)
- `posit_universal_numbers_design` — Posit type design and FPGA acceleration
- `fncs_architecture` — FNCS/Firefly boundary (Firefly orchestrates, FNCS is pure)
- fsnative-spec: `spec/incremental-computation.md` — Incremental<'T> hardware lowering

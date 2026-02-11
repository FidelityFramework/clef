# NTU Dimensional Type System — Lingua Franca Design

> **Created**: February 2026
> **Context**: Multi-substrate compilation where NTU becomes the universal type substrate
> across CPU, GPU, NPU, and FPGA, with BAREWire as the inter-substrate memory contract.

## The Vision

A Fidelity **solution** (`fidsln`) contains multiple **projects** (`fidproj`), each targeting
a different compute substrate. The NTU is the "lingua franca" — a type system that expresses
types across all substrates. BAREWire is the "Rosetta Stone" — memory layout contracts that
ensure type-safe data handoff between substrates.

```
my-app.fidsln
├── shared/          BAREWire contracts, shared NTU types
├── cpu.fidproj      x86_64 Zen 5 → MLIR → LLVM → native (libc bindings)
├── gpu.fidproj      RDNA 3.5 → MLIR → GPU/AMDGPU → ROCm
├── npu.fidproj      XDNA 2 → MLIR → MLIR-AIE → AI Engine runtime
└── fpga.fidproj     Xilinx FPGA → MLIR → CIRCT → handshake → hw/comb/seq → SV
```

**Concrete hardware target**: AMD Strix Halo — CPU, GPU, NPU share HSA coherent memory
(zero-copy via BAREWire layout agreement). External FPGA connects via PCIe/AXI
(BAREWire defines layout + transport protocol).

**Driving use case**: Posit arithmetic on FPGA as coprocessor. CPU orchestrates, GPU handles
data-parallel work, NPU handles inference, FPGA provides posit math that has no CPU equivalent.

## NTU Dimensional Axes

Width was the **first** dimensional axis (Feb 2026). The multi-substrate world needs five axes:

### Axis 1: Width (IMPLEMENTED)

```fsharp
type NTUWidth = Fixed of bits: int | Resolved of WidthDimension
type WidthDimension = Pointer | Register
```

### Axis 2: Memory Space (DESIGN)

```fsharp
type NTUMemorySpace =
    | Default       // Substrate chooses (escape analysis on CPU, compiler on GPU)
    | Stack         // Function-local (universal concept across substrates)
    | Global        // Main memory / VRAM / HBM
    | Shared        // Explicitly managed cache (GPU shared mem, NPU tile mem)
    | Private       // Per-thread/per-PE (GPU registers, NPU private mem)
    | Coherent      // HSA unified (CPU↔GPU↔NPU on Strix Halo — zero-copy)
    | External      // Cross-device (FPGA BRAM from CPU perspective)
    | Peripheral    // MMIO (volatile access from BAREWire patterns)
```

Resolution per substrate:
- **CPU**: Default → stack/heap via escape analysis; Coherent → normal pointer in HSA space
- **GPU**: Global → HBM; Shared → per-SM shared memory (100x faster); Private → registers
- **NPU**: Shared → tile memory; Global → data memory via MLIR-AIE
- **FPGA**: External → AXI interface ports; Shared → BRAM

### Axis 3: Numeric Format (DESIGN)

```fsharp
type NTUNumericFormat =
    | IEEE              // Standard IEEE 754 (default)
    | Posit of es: int  // Gustafson posit (es=0,1,2,3)
    | FixedPoint of fractionalBits: int
    | Ternary           // BitNet {-1, 0, +1}
    | Quaternary        // BitNet + sparsity marker
    | SubstrateNative   // Whatever the substrate does natively (NPU INT8, etc.)
```

This is where the posit story lives. A `Posit32` is `NTUint(Fixed 32)` with
`NumericFormat.Posit(es=2)`. Same NTU type, different substrate resolution:
- **CPU**: i32 storage + software decode/encode (or AVX-512 vectorized)
- **FPGA**: Dedicated posit32 hardware pipeline via CIRCT (PACoGen-style)
- **NPU**: Quantized representation with conversion at boundary

### Axis 4: Access Pattern (DESIGN)

```fsharp
type NTUAccessPattern =
    | Normal        // Regular read/write
    | Streaming     // Sequential, don't cache (non-temporal on CPU, coalesced on GPU)
    | Volatile      // MMIO / peripheral
    | ReadOnly      // Immutable view (enables sharing without coherency cost)
    | WriteOnly     // Producer-only (enables GPU write-combine)
```

Driven by cache-aware compilation articles:
- CPU: Streaming → non-temporal moves bypassing cache hierarchy
- GPU: Streaming → coalesced access; Normal → may need AoS↔SoA transformation
- FPGA: Streaming → AXI stream interface vs AXI-Lite memory-mapped

### Axis 5: Tensor Shape (FUTURE)

```fsharp
type NTUTensorShape =
    | Scalar
    | Vector of length: int
    | Matrix of rows: int * cols: int
    | Shaped of dims: int list
```

NPU needs tile dimensions. GPU needs warp-width vectorization. Deferred — not needed for
initial multi-substrate support but the axis slot should be reserved.

## Representation Options

### Option A: Flat Dimensional Record

```fsharp
type NTUDimensions = {
    Width: NTUWidth
    MemorySpace: NTUMemorySpace option      // None = substrate-default
    NumericFormat: NTUNumericFormat option   // None = IEEE
    AccessPattern: NTUAccessPattern option   // None = Normal
    TensorShape: NTUTensorShape option       // None = Scalar
}
```

Pro: Extensible, no combinatorial explosion. Con: loses "invalid states unrepresentable".

### Option B: Dimensions on NTUKind cases selectively

Width stays on the numeric kinds (already there). Other axes live in a separate
`NTUAnnotations` or `NTUQualifiers` record that attaches to `TypeConRef`.

This is likely the right approach — Width is intrinsic to numeric type identity,
while Memory Space and Access Pattern are **qualifiers** that can be added/removed
without changing the type's identity. Numeric Format is a middle case — it affects
identity (Posit32 ≠ float32) but could be expressed as a separate type rather than
a dimension on NTUint.

### Recommended: Hybrid — Width intrinsic, qualifiers external

```fsharp
// Width stays intrinsic to NTUKind (existing, identity-affecting)
type NTUKind =
    | NTUint of NTUWidth | NTUuint of NTUWidth | NTUfloat of NTUWidth
    | NTUposit of NTUWidth * es: int   // NEW: posit as first-class numeric kind
    | NTUptr | NTUfnptr | NTUsize | NTUdiff
    | NTUstring | NTUbool | NTUchar | NTUunit | NTUdecimal
    | NTUlazy | NTUseq
    | NTUarray | NTUlist | NTUmap | NTUset
    | NTUuuid | NTUdatetime | NTUtimespan

// Qualifiers are external — don't affect type identity in FNCS
type NTUQualifiers = {
    MemorySpace: NTUMemorySpace option
    AccessPattern: NTUAccessPattern option
    TensorShape: NTUTensorShape option
}
```

Rationale: Posit gets its own NTUKind case because `Posit32 ≠ float32` is a type identity
distinction. Memory Space and Access Pattern are qualifiers — `int in Global` and `int in Shared`
are the same type placed differently, not different types. This matches how MLIR handles
address spaces (attribute on memref, not a different type).

## Three-Layer Resolution Model

```
Layer 1: FNCS (Type Identity)
  NTU dimensions are ABSTRACT. Type identity enforced.
  Posit32 ≠ float32. NTUint(Resolved Register) ≠ NTUint(Fixed 64).
  Qualifiers attached but not used for type identity.

Layer 2: Coeffects (Execution Strategy)
  Context-aware compilation determines substrate routing:
  - Pure data-parallel computation → candidate for GPU/NPU
  - Resource-dependent → stays on CPU (delimited continuations)
  - Temporal/streaming → NPU or CPU SIMD pipeline
  - Posit accumulation → route to FPGA coprocessor
  Coeffects are SEPARATE from types — they analyze the PSG, not the NTU.

Layer 3: Alex / Substrate Generators (Concrete Resolution)
  Per-substrate MLIR emission:
  - CPU Alex:  MLIR → LLVM dialect → LLVM backend
  - GPU Alex:  MLIR → GPU/AMDGPU dialects → ROCm
  - NPU Alex:  MLIR → MLIR-AIE → XDNA runtime
  - FPGA Alex: MLIR → CIRCT → handshake → hw/comb/seq → SystemVerilog
```

## Cascade Impact Analysis

| Layer | What Changes | Blast Radius |
|-------|-------------|-------------|
| **NTUKind DU** | NTUposit case; NTUQualifiers record | Every `match` on NTUKind; TypeConRef |
| **TypeConRef** | Add NTUQualifiers field | FNCS unification (qualifiers ignored for identity) |
| **Baker** | Mostly untouched — types flow through | Possible AoS↔SoA for GPU substrate |
| **PSGElaboration** | Escape analysis becomes substrate-aware | EscapeKind may grow; memory space informs allocation |
| **Alex** | Substrate-polymorphic or sibling generators | Elements shared, Patterns per-substrate, Witnesses thin |
| **BAREWire** | Inter-substrate serialization contracts | New: contract validation across substrates |
| **fidsln/Firefly** | Solution orchestration, multi-project compilation | New Firefly capability needed |
| **PlatformContext** | Becomes SubstrateContext with richer topology | Each fidproj gets its own SubstrateContext |

**Critical architectural insight**: Dimensions don't erase after type checking — they flow
through the PSG and inform code generation for each target. But they DO NOT change the
pipeline structure. The fork between substrates happens *after* Alex emits MLIR.

## Key Principles from Blog Articles

### From CPU Cache-Aware Compilation
- BAREWire deterministic layouts enable compile-time cache analysis
- Per-actor arenas eliminate false sharing by construction
- Access Pattern (Streaming vs Normal) determines cache bypass strategy
- Cache line size varies by architecture (64-byte x86, 128-byte Apple Silicon)
  → resolved from SubstrateContext, not hardcoded

### From GPU Cache-Aware Compilation
- GPU memory: coalescing imperative (32 threads must access consecutive memory)
- AoS → SoA transformation critical for GPU performance
- Memory spaces (Global/Shared/Private) are first-class in GPU programming
- SIMT execution model: no false sharing, but warp divergence matters
- Actor model for CPU↔GPU ownership transfer via BAREWire

### From Context-Aware Compilation
- Coeffects determine execution strategy:
  - Pure → Interaction nets → GPU/NPU candidate
  - Resource-dependent → Delimited continuations → CPU
  - Temporal → Streaming pipeline → NPU or CPU SIMD
- Coeffects are SEPARATE from PSG structure (external analysis maps)
- Automatic substrate selection based on computation pattern

### From Posit Arithmetic Article
- "Same compiler, four targets": F# → PSG → MLIR → {CPU, GPU, NPU, FPGA}
- FPGA path: MLIR → CIRCT (handshake → hw/comb/seq → SystemVerilog)
- Fork between CPU and FPGA targets happens AFTER Alex emits MLIR
- "No changes to FCS, PSG, nanopasses, or zipper traversal" for FPGA path
- Posit as concrete types (Posit8/16/32/64), not parameterized generics
- AVX-512 vectorized posits: Vector512<uint32> as primitive type
- Quire32 = 64 bytes = exactly one cache line (fortuitous alignment)
- BAREWire serialization of posits is trivial: bits are the representation

## Inter-Substrate Communication

```
CPU ↔ GPU:  HSA coherent → BAREWire layout agreement, same pointer space
CPU ↔ NPU:  HSA coherent → BAREWire layout, may need format conversion
CPU ↔ FPGA: PCIe/AXI → BAREWire layout + transport protocol + DMA
GPU ↔ NPU:  HSA coherent → BAREWire contract for format bridging
```

The `shared/` project in fidsln defines types using NTU + BAREWire contracts.
Each substrate project resolves those shared types against its SubstrateContext.

## Confirmed Design Decisions (February 2026 Implementation)

1. **NTUposit as NTUKind case** — CONFIRMED and IMPLEMENTED.
   `NTUposit of NTUWidth * es: int` on NTUKind. Posit32 ≠ float32 is type identity.
   Standard types: posit8 (es=0), posit16 (es=1), posit32 (es=2), posit64 (es=3).

2. **TypeLayout as qualifier home** — CONFIRMED and IMPLEMENTED.
   `TypeLayout.Qualified of inner: TypeLayout * qualifiers: NTUQualifiers`
   Qualifiers do NOT affect type identity. `int @Global` and `int @Shared` unify as same type.
   `TypeLayout.baseLayout` strips qualifiers for size/align calculations.

3. **SubstrateContext as gradual PlatformContext extension** — IMPLEMENTED.
   Three new optional fields on PlatformContext: SubstrateKind, AvailableMemorySpaces, DefaultMemorySpace.
   `type SubstrateContext = PlatformContext` (type alias for gradual migration).

4. **TypeConRef.Qualifiers** — IMPLEMENTED.
   Optional `NTUQualifiers` on TypeConRef. All construction helpers default to `None`.
   Unification is qualifier-blind (Name + Module only for identity).

## Incremental<'T> Integration Points

When `TIncremental of element: NativeType * targetMeasure: MeasureType option` is added:
- Inner type `T` carries NTUQualifiers → substrate placement
- Cross-substrate dependency edges trigger BAREWire transfer based on qualifier mismatch
- Cutoff functions respect NTU type identity (NTUposit cutoff ≠ NTUfloat cutoff)
- Height-based stabilization → hardware wave scheduling (NPU tiles, GPU wavefronts)
- Applicative subgraphs → static tile overlays (NPU) or fixed dispatch groups (GPU)

## Remaining Open Questions

1. **AoS↔SoA transformation**: Where does this happen? Baker (substrate-aware decomposition)?
   A new nanopass between Baker and Alex? Or Alex-internal? The GPU article suggests compiler
   transformation; needs design.

2. **shared/ project semantics**: Does it compile to a PSG? A contract-only artifact?
   Type declarations that each substrate validates against?

3. **Substrate-aware SRTP**: Does `+` on Posit32 resolve differently on CPU (software) vs
   FPGA (hardware instruction)? If yes, SRTP needs SubstrateContext.

4. **Incremental + Coeffect routing**: How does coeffect-to-substrate routing interact with
   the incremental dependency DAG? The compute graph structure should inform substrate selection.

## Related Memories

- `ntu_type_system` — Current NTU implementation (Width axis)
- `ntu_type_flow_prd_guidance` — Type flow through MLIR pipeline
- `ntu_collection_architecture` — Collection types in NTU
- `posit_universal_numbers_design` — Posit type design and FPGA acceleration
- `fncs_architecture` — FNCS pipeline overview
- `baker_saturation_architecture` — Baker decomposition model
- `alex_compositional_architecture_elements_patterns_witnesses` — Alex three-layer model
- `escape_analysis_generalized_design_feb2026` — Substrate-aware escape analysis foundation
- `coeffect_analysis` — Coeffect infrastructure
- `memory_layout_and_raii` — Memory regions, access patterns, RAII model
- `resource_management_architecture` — Actor-based resource management
- `firefly_multi_substrate_fanout_architecture` — **CRITICAL**: Downstream Firefly design for multi-substrate fan-out

## Source Material

- SpeakEZ Blog: "Cache-Conscious Memory Management: CPU Edition" (Sep 2025)
- SpeakEZ Blog: "GPU Cache-Aware Compilation" (Sep 2025)
- SpeakEZ Blog: "Context-Aware Compilation" (Jul 2025)
- SpeakEZ Blog: "Bringing Posit Arithmetic to F#" (Dec 2025)
- fsnative-spec: `ntu-dimensional-architecture.md`

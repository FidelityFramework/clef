# SMT Integration Strategy: From F\* Bridge to Native Keystone Verification

> **Status**: Strategic Design Document
> **Date**: February 2026
> **Patent**: US 63/786,264, "System and Method for Verification-Preserving Compilation Using Formal Certificate Guided Optimization"

## 1. The Architecture: Two Places Where SMT Lives

The position of this document, and the subject of the patent, is to detail how verification in Keystone operates in two complementary modes. Together they form a "double-entry accounting" system for correctness. One mode is interactive, operating at design time in the developer's editor. The other is structural, operating inside the compilation pipeline. Neither is sufficient alone. Their agreement is what constitutes a verified system.

The metaphor is deliberate. In accounting, every transaction has two entries that must balance. A debit without a credit is an error. The same principle applies here: a proof that exists only at design time, with no evidence of its preservation through compilation, is an unverified claim. A proof artifact in compiled output that was never established interactively is ungrounded. The system's integrity comes from the reconciliation of both sides.

### 1.1 Design-Time SMT: Interactive Proof Checking

The first mode is an interactive, LSP-driven proof checker that operates during development. This takes its inspiration directly from F\*'s interactive verification experience, which itself draws from the F# Interactive (FSI) model. The developer writes `[<SMT Requires("...")>]` and `[<SMT Ensures("...")>]` annotations on functions. The LSP dispatches these as SMT queries to a solver (Z3, cvc5) in real time. The developer receives immediate feedback: proven, unproven, or counterexample.

What made F\*'s interactive mode compelling was not the power of the underlying solver but the tightness of the feedback loop. The developer did not need to invoke a separate tool, switch to a different language, or wait for a batch process. Proof checking was part of editing. This is the experience Keystone preserves.

Over time, parameterized lemma libraries provide reusable proof templates that can be applied with a single annotation. The developer's experience is: write code, annotate key properties, see green checks or red diagnostics. No separate verification language. No context-switching to a proof assistant.

This is the "debit" side of the double-entry ledger. It records what the developer claims about their code.

### 1.2 Compilation-Path SMT: Verification-Preserving Lowering

The second mode is proof-carrying compilation through the MLIR pipeline using the upstream SMT dialect contributed to LLVM by Fehr et al. (PLDI 2025). This ensures that properties proven at design time are preserved through every compilation transformation.

The compilation path works as follows:

1. Design-time proof obligations attach to PSG nodes as metadata
2. Alex code generation lowers these to `smt.assert` operations in the MLIR output
3. Each nanopass transformation must preserve the assertions
4. Translation validation (provided by the MLIR SMT dialect) can verify each pass
5. Proof artifacts survive through to native code as certification evidence

This is the "credit" side of the double-entry ledger. It is the compiler's guarantee that what was claimed was actually preserved.

The patent (US 63/786,264) covers this verification-preserving compilation specifically: the method by which formal certificates guide optimization while maintaining correctness guarantees across the compilation pipeline, including across heterogeneous hardware targets.

### 1.3 The Double-Entry Principle

The two modes are complementary and must balance.

| | Design-Time (Debit) | Compilation-Path (Credit) |
|---|---|---|
| **What** | "This function satisfies these properties" | "These properties survived compilation" |
| **When** | During editing, via LSP | During compilation, via nanopass pipeline |
| **How** | SMT solver checks annotations against source | MLIR smt dialect carries assertions through lowering |
| **Tool** | Z3/cvc5 subprocess, interactive | Translation validation, pass verification |
| **Artifact** | Proof status in IDE (green/red) | Proof certificate in compiled output |
| **Audience** | Developer | Certification auditor, safety engineer |

A property that is proven at design time but not preserved through compilation is a broken promise. A property that appears in compiled output but was never established at design time is ungrounded. The double-entry system ensures both sides agree.

## 2. What We Gain: Native SMT in Keystone

### 2.1 One Language, One Type System, One Pipeline

The original approach presupposed that the solution would negotiate two languages (F# and F\*), two type checkers, and a bridge between them, on one coherent experience. The `[<F\* Requires>]` attribute was a call-out to a foreign language's type checker. Every annotation was a boundary crossing with impedance mismatch. It was a "good fences makes good neighbors" rationale that thought this would be the path to a relatable development experience.

With a fully fused `[<SMT Requires>]` in the core infrastructure as a native Keystone annotation, the type checker that resolves NTU dimensions is the same system that generates proof obligations. The pipeline that lowers function bodies to MLIR is the same pipeline that lowers proofs to `smt.assert`. There is no chasm to cross between systems, no impedance mismatch, and no two-system friction. "Good fences makes good neighbors" seemed like a reasonable choice outside of building an entire dimensional types system in the NTU. Once that new strata developed organically through iteration, the full fusion of the concepts and effectively "leaving behind" the baggage of F# and F\* became self-evident.

### 2.2 Substrate-Aware Proofs

F\*'s proofs operate on a single computational substrate. F\* extracts to C (via KaRaMeL) or OCaml, one target at a time. It has no concept of a proof that spans a CPU-to-GPU boundary or a CPU-to-FPGA data transfer.

This limitation was not obvious at first. Early work on the Fidelity framework focused on CPU-targeted compilation where F\*'s single-substrate assumption was not a constraint. The limitation became visible as the PSG hypergraph architecture matured and multi-substrate compilation became not just possible but central to the framework's value proposition. A proof system that cannot follow data across a substrate boundary is a proof system that stops at the most interesting part of the problem.

Keystone's proofs attach to PSG hyperedges that can span multiple substrates. A BAREWire contract between CPU and GPU code is a proof obligation on a hyperedge connecting nodes in both substrates. A memory safety proof for an arena that transfers ownership across a substrate boundary is substrate-aware by construction. The MLIR smt dialect is the same infrastructure that CIRCT uses for hardware verification, which means Keystone's software proofs and CIRCT's hardware proofs share a common foundation.

This is a capability that F\* structurally cannot provide.

### 2.3 NTU Dimensional Types as Structured Refinements

The term "dimensional types" requires definition, as it is not established terminology in formal methods. The concept originates in F#'s Units of Measure system (and its community extension, FSharp.UMX), which attaches phantom type parameters representing physical units — meters, seconds, kilograms — to numeric types. The compiler enforces dimensional algebra (`meters/seconds * seconds = meters`) and rejects inconsistent operations, all at zero runtime cost because the annotations erase before code generation.

Keystone's NTU (Native Type Universe) takes this mechanism and generalizes it in two directions. First, the vocabulary of "dimensions" extends beyond physical units to encompass memory access modes (`ReadOnly`, `WriteOnly`), platform predicates, wire layout constraints, tensor axis identities, and other structured properties relevant to systems programming. Second, and critically for this strategy, dimensions do not erase. They survive through the Program Semantic Graph and inform code generation, substrate targeting, and proof obligation generation throughout the compilation pipeline.

In formal methods terms, dimensional types are **refinement types restricted to decidable SMT theories**. Where F\*'s refinement types allow arbitrary predicates — `x:int{phi(x)}` where `phi` can be any F\* term — dimensional types draw their predicates from a fixed, structured vocabulary. This restriction is the key design choice. F\*'s generality forces a universal `Term` sort with boxing and unboxing, fuel-based termination heuristics, and an encoding layer that the solver may not terminate on. That generality is necessary for F\*'s mission of full dependent types, but it is not necessary for Keystone's design goals.

Each dimensional constraint maps directly to a specific SMT theory:

- Width constraints → bitvector theory
- Memory space compatibility → enum sorts
- Platform predicates → boolean theory
- BAREWire layout contracts → bitvector arithmetic
- Access pattern compatibility → enum sorts
- Value-level refinements (via `[<SMT>]` annotations) → decidable arithmetic

Because each theory is decidable, the solver always terminates with a definitive answer: satisfied, unsatisfied, or counterexample. There is no fuel, no encoding heuristic, no "unknown" result. This is not a limitation of the system; it is a deliberate restriction to the decidable fragment of refinement typing. The NTU does not need arbitrary dependent types because it captures the constraints that matter for systems programming — physical consistency, memory safety, cross-substrate data integrity — through structured dimensions rather than open-ended predicates.

The closest precedents in deployed systems are Ada's derived numeric types (which enforce dimensional consistency but do not survive to guide code generation) and VHDL's physical types (which carry units through synthesis to inform hardware resource allocation). Keystone's dimensional types occupy a similar design point: structured, domain-specific constraints that serve both verification and compilation, rather than a general-purpose predicate logic.

### 2.4 Farscape as Proof-Obligation Generator

Farscape's tooling that can generate shadow APIs presumes to generate drop-in replacements for C tools (see the "Farscape's Modular Entry Points" blog post and its OpenSSL case study). With native SMT integration, Farscape generates not just type-safe bindings but provably safe ones.

The key insight is that C headers already contain implicit proof obligations. Farscape makes them explicit:

- C pointer parameters → `[<SMT Requires("param <> null")>]`
- Size parameters paired with pointers → `[<SMT Requires("size <= buffer_capacity(ptr)")>]`
- `const` qualifiers → `[<SMT Ensures("source_unchanged(param)")>]`
- `restrict` qualifiers → `[<SMT Requires("no_alias(a, b)")>]`
- Domain-specific contracts → curated lemma library (crypto key sizes, cipher block sizes, etc.)

The shadow API supports verification, with proof obligations derived automatically from C header metadata. Every C library wrapped through Farscape ostensibly contributes to a growing body of safe, proven interface contracts.

### 2.5 Parameterized Lemma Libraries

Over time, reusable proof templates accumulate as a standard library:

- `Lemma.NonNull<'T>` : pointer is non-null
- `Lemma.BoundsChecked<'T>(ptr, size)` : pointer valid for size bytes
- `Lemma.NoAlias<'T>(a, b)` : two pointers do not overlap
- `Lemma.Immutable<'T>(ptr)` : pointee unchanged through call
- `Lemma.SecureZeroed<'T>(ptr, size)` : memory cleared on disposal
- `Lemma.ValidKeySize(n, min, max)` : crypto key size in valid range

Each lemma is parameterized, proven sound once, and lowers to a known-good SMT pattern. Farscape stamps them onto generated bindings. The library grows monotonically: every new C library wrapped contributes patterns that apply to the next one. This is the compounding effect that makes the approach viable at scale. The hundredth library wrapped is dramatically easier than the first because the lemma library already covers most of its interface patterns.

### 2.6 Patent-Protected Innovation

The verification-preserving compilation approach is covered by US 63/786,264. This is original IP, not borrowed from F\* and not dependent on INRIA's work. The parameterized lemma library as a reusable proof infrastructure for FFI boundary verification is a natural extension worthy of additional IP protection.

### 2.7 MLIR SMT Dialect: Independent Credibility

The upstream MLIR smt dialect (Fehr, Fan, Pompougnac, Regehr, Grosser, PLDI 2025) provides independent academic credibility:

1. Published at PLDI, a top-tier PL venue
2. Contributed to upstream LLVM as an MLIR dialect
3. Provides tools for translation validation, peephole rewrite verification, and dataflow analysis verification
4. Dialect-agnostic: works with any MLIR dialect that provides semantic lowerings
5. Active research community spanning Cambridge, Utah, Edinburgh, and INRIA Grenoble

The existence of this dialect is significant for the strategic positioning. It means the compilation-path side of the double-entry system is built on independently peer-reviewed infrastructure, not on a custom encoding that would require its own credibility campaign.

## 3. What We Lose, and What We Consciously Avoid

### 3.1 The F\* Credibility Chain

The F\* ecosystem has a proven track record in high-assurance systems:

1. **HACL\***: Verified cryptographic library, deployed in Firefox and the Linux kernel
2. **EverCrypt**: Unified cryptographic API with verified implementations
3. **miTLS**: Verified TLS 1.3 implementation
4. **Project Everest**: End-to-end verified HTTPS stack (Microsoft Research + INRIA)
5. **Low\***: Subset of F\* that extracts to C via KaRaMeL with verified memory safety
6. **Vale**: Verified assembly language for cryptographic primitives

Being able to say "we use the same verification infrastructure that proved TLS 1.3 correct" is a powerful credibility signal. It carries weight with safety-critical customers in aerospace, automotive, and medical domains. It matters for government and defense procurement at Common Criteria EAL 5+ and above. It resonates with academic collaborators in formal methods and with European research funding bodies through the INRIA relationship.

Walking away from this credibility chain is not taken lightly. The decision is rooted in the judgment that the chain's value is borrowed, and borrowed credibility can become borrowed liability when the lender's interests diverge from the borrower's. Given the anticipated pivot in emphasis toward novel processor architecture and post-quantum certification in the coming years, establishing an independent stance is both structural (rooted in Keystone's unique type system) and sober market positioning.

### 3.2 Established Academic Trust

F\* has a publication track record at POPL, ICFP, S&P, and other top venues. The formal methods community knows and trusts it. A new, unproven proof system faces skepticism regardless of its technical merits. This is the "cold start" problem, and it is real.

### 3.3 The "Proven in Production" Argument

Low* code extracted via KaRaMeL runs in Firefox (HACL\* crypto) and the Linux kernel. This is concrete evidence that F\*-verified code works in production. Keystone's proof system has no production track record yet. Every new system must earn this trust through deployment, and there is no shortcut.

### 3.4 Talent Pool

Engineers who know F\* exist in small but growing numbers. Engineers who know Keystone's proof system do not exist yet. Hiring and collaboration could encounter early friction with what is perceived as a bespoke system until a community forms around it.

This concern is tempered by a deliberate design decision: Keystone preserves F# syntax and idioms wherever possible. An F# developer reading Keystone code should find the surface language familiar. Similarly, the `[<SMT Requires>]` annotation form is a direct descendant of the `[<F* Requires>]` pattern, recognizable to anyone who has worked with F*'s verification annotations. The proof system is new; the language it lives in is not. The ramp-up cost is learning what the annotations mean, not learning a new syntax for writing them.

### 3.5 The Risk of "Not Invented Here"

The formal methods community is wary of reinvented wheels. A new proof system must demonstrate clear advantages over existing ones, or it will be dismissed as NIH syndrome. The multi-substrate capability is the answer to this objection, but it must be demonstrated convincingly, not merely asserted.

### 3.6 The Explanation Cost of a Novel Type System

The dimensional type system introduces terminology that does not exist in the formal methods vocabulary. A researcher with decades of experience in refinement types, dependent types, and abstract interpretation will hear "dimensional types" and not know what category of type-theoretic object is being described. This is a barrier that operates before any technical evaluation begins.

Section 2.3 provides the formal methods bridge: dimensional types are refinement types restricted to decidable SMT theories, with predicates drawn from a structured vocabulary rather than arbitrary terms. The lineage from F#'s Units of Measure through FSharp.UMX to the NTU is traceable and principled. The Ada and VHDL precedents anchor the concept in deployed systems the audience already respects. But none of this matters if the audience disengages at the terminology before reaching the explanation.

This is distinct from the NIH risk (section 3.5). NIH resistance assumes the audience understands the concept and doubts the need for a new implementation. The vocabulary barrier is upstream: the audience does not yet have a mental model for what is being proposed. The explanation must land before the evaluation can begin. For a community that has spent decades refining a shared vocabulary around refinement types, dependent types, liquid types, and indexed families, a new term is a signal that demands immediate justification.

The mitigation is not to avoid the term but to always lead with the bridge: "refinement types restricted to decidable theories" is the formal methods entry point; "dimensional types" is the name for that specific restriction applied to systems programming constraints. The explanation sequence matters.

### 3.7 Platform Risk: What Building on F\*/F# Actually Means

The credibility of F\* and F# comes at a price: platform dependency on Microsoft.

F\* is a Microsoft Research project, developed jointly with INRIA. F# is a Microsoft language running on an MLIR-lowered platform. Building on both means building entirely on Microsoft's stack. This creates a specific and serious risk.

Consider the co-option scenario. SpeakEZ presents "verification-preserving compilation for heterogeneous hardware, built on F# and F\*" at a defense conference or to a DARPA program manager. The PM asks Microsoft for a technical assessment. Microsoft's institutional incentive is to say "interesting, but our research labs have been exploring this space," even if they have not built anything comparable. An executive assembles an MSR group. They have full access to F\*'s internals, to FCS, to .NET's runtime team. They do not need to replicate the code; they replicate the approach on their own stack with ten researchers and institutional momentum. A two-year head start evaporates because the perception is that the platform underneath the smaller company belongs to them.

This is not hypothetical. It is the standard dynamic between small innovators and platform owners. The innovation happens at the edge, the platform owner absorbs it. Building on F# and F\* means every layer of the stack (language, type checker, runtime, proof tool) is owned by one company, and that company has the resources to outrun a smaller competitor on its own infrastructure.

Government and defense program managers are wary of funding work that enriches a large vendor's platform. "Built on Microsoft's proprietary language ecosystem" is a yellow flag in procurement. It implies single-vendor lock-in, limited competition, and potential IP entanglement. "Built on open MLIR infrastructure with independent patents" is what program managers want to hear: portable results, performer-owned IP, no vendor dependency.

Moving to Keystone with native SMT on MLIR eliminates the platform risk:

1. **MLIR is open infrastructure**, owned by the LLVM Foundation and contributed to by Google, Intel, AMD, Qualcomm, and dozens of universities. No single vendor controls it.
2. **NTU is original**, not derived from FCS or F\*'s type checker. Novel architecture, coupled with independent patented protection.
3. **The smt dialect is academic**, with authors at Edinburgh, Cambridge, and Utah. No corporate research lab involvement.
4. **Patent US 63/786,264 is SpeakEZ's**, covering verification-preserving compilation. This is owned IP regardless of what any platform vendor does.

When SpeakEZ presents Keystone to DARPA, Microsoft cannot say "we have been doing this" because they have not. F\* does not do multi-substrate verification. MLIR is not their infrastructure. They have no equivalent to the hypergraph proof-carrying architecture. They would have to start from scratch, on infrastructure they do not control, solving a problem their existing tools do not address.

The tradeoff is real: the borrowed credibility of "same tools as TLS 1.3" is forfeited. But the gain is something more durable: a competitive position that cannot be absorbed by the platform owner, because there is no platform owner.

## 4. The Counter-Narrative: Multi-Substrate Verification

### 4.1 The Core Argument

F\* proved TLS 1.3 was correct on a CPU. Keystone proves that a system is correct across CPU, GPU, and FPGA simultaneously.

F\*'s verification model assumes a single computational substrate. It extracts to C or OCaml, one target. It cannot express that a property holds across a CPU-to-GPU data transfer, or that an arena's lifetime is safe across a substrate boundary, or that a BAREWire contract correctly bridges two memory spaces, or that an interaction net reduction on GPU preserves the invariant established on CPU.

These are the verification challenges of modern heterogeneous systems. Safety-critical standards (DO-178C, IEC 61508, ISO 26262) increasingly involve multi-substrate architectures: sensor fusion on NPU, control logic on CPU, actuation on FPGA. The auditor needs proof that spans the boundaries, not just proof of individual substrates.

### 4.2 The MLIR Advantage

The MLIR smt dialect is the same infrastructure that CIRCT uses for hardware design verification. Software proofs (Keystone to MLIR to smt dialect) and hardware proofs (CIRCT to smt dialect) share a common foundation. A proof that spans a CPU-to-FPGA boundary can be expressed in a single framework. The hardware verification community is already investing in this infrastructure.

F\* has no connection to hardware verification. Keystone, through MLIR, has a natural bridge. This convergence was not planned from the outset, but it is a direct consequence of choosing MLIR as the compilation substrate. The infrastructure simply connects in ways that a standalone proof tool cannot.

### 4.3 The Audience Difference

F\*'s primary audience is formal methods researchers and verified cryptography specialists. Keystone's audience is engineers building systems on real hardware: systems polyglots, hardware engineers, embedded developers, safety-critical practitioners.

These audiences value different credibility signals. Formal methods researchers ask about publication records, theorem prover pedigree, and proof assistant heritage. Systems engineers ask whether it works on their hardware, whether it catches the bugs they actually hit, and whether it integrates with their build system.

The multi-substrate story resonates with the systems audience in a way that "we use F\*" does not.

### 4.4 The Certification Angle

For DO-178C Level A, the question is not "which proof assistant did you use?" The question is "can you demonstrate traceability from requirements to object code?" Keystone's nanopass architecture with proof-carrying compilation provides:

1. Source-to-object traceability through the PSG
2. Modular tool qualification (each nanopass qualifies independently)
3. Proof certificates as compilation artifacts
4. Multi-substrate coverage in a single certification package

A certification lab does not care about F\* brand recognition. It cares about evidence quality. The double-entry accounting system (design-time proofs balanced against compilation-path preservation) provides stronger evidence than a disconnected external proof tool.

### 4.5 Defense Positioning

For DARPA and defense program managers, the Keystone story resolves several concerns simultaneously:

1. **IP ownership**: performer-owned patents on open infrastructure, not derivative work on a vendor's platform
2. **No vendor lock-in**: built on MLIR/LLVM (multi-vendor, open governance), not .NET (single-vendor)
3. **Novel capability**: multi-substrate verification is a new contribution to the field, not an application of existing tools
4. **Hardware relevance**: the proof infrastructure that verifies software connects to CIRCT for hardware, enabling co-verification in a single framework
5. **Transition path**: results built on MLIR are portable to any organization that uses LLVM, which is effectively everyone

The pitch is not "we made F\* work better." The pitch is "we built a new capability for proving correctness across heterogeneous compute, on open infrastructure, with our own IP."

## 5. Mitigation Strategies

### 5.1 Maintain F\* as Reference, Not Dependency

F\* remains valuable as a reference implementation for SMT encoding patterns, type-theoretic design decisions, and proof strategies. The FNCS codebase already treats F\* this way. The F\* source is studied for its encoding of refinement types, its solver interaction protocol, and its approach to termination checking. None of this requires making F\* a runtime dependency.

### 5.2 MLIR Community Engagement

The smt dialect authors (Fehr, Grosser, Regehr) are natural allies. Contributing Keystone's semantic lowerings back to the MLIR ecosystem builds credibility through the compiler community rather than the proof assistant community. This is a different credibility channel than F\*'s, but it is equally legitimate and arguably more durable given the breadth of MLIR adoption.

### 5.3 Certification Lab Partnerships

Partnering with certification labs early is essential. Show them the double-entry accounting system. Let the proof artifacts speak for themselves. Certification credibility comes from lab endorsement, not from tool pedigree.

### 5.4 Open-Source Lemma Libraries

Publishing the parameterized lemma libraries (FFI boundary proofs, memory safety lemmas, crypto domain constraints) as open source builds trust through transparency. The community can validate and extend them.

### 5.5 Academic Publication Strategy

Publish on multi-substrate verification, the capability F\* cannot match. Target venues by focus area:

1. **Compiler architecture / proof-preserving compilation**: PLDI, OOPSLA
2. **Formal verification of heterogeneous systems**: CAV, FMCAD
3. **Hardware/software co-verification via MLIR**: DAC, DATE
4. **Safety-critical multi-substrate systems**: EMSOFT, RTAS

The publication angle is novel contribution, not reinvented wheel.

### 5.6 Establishing the DTS Vocabulary

The dimensional type system will face explanation resistance proportional to its novelty. The mitigation is to establish the terminology through multiple channels before it encounters skepticism in high-stakes settings.

1. **Lead with the bridge in every context.** "Refinement types restricted to decidable SMT theories" is the entry point for formal methods audiences. "Dimensional types" is introduced as the name for that restriction, not as a standalone concept. The explanation sequence, familiar category first, novel name second, must be consistent across papers, talks, and documentation.
2. **Publish the type-theoretic foundations separately.** A paper establishing the formal relationship between dimensional types, F#'s Units of Measure, and decidable refinement types gives the FM community a citable reference. Without it, reviewers at CAV or POPL will treat the terminology as ad hoc. This initiative should target ICFP or POPL for this foundational work.
3. **Use the Ada/VHDL precedent actively.** The embedded and safety-critical communities already understand that types can guide code generation. Framing dimensional types as "Ada's derived types generalized to multi-substrate compilation" is an entry point for that audience that requires no new vocabulary.
4. **The "Doubling Down" blog post traces the lineage.** The public record of the evolution from F#'s Units of Measure through FSharp.UMX to the NTU provides a traceable design narrative. This is not academic publication, but it demonstrates that the concept was developed through principled iteration rather than invented whole-cloth.

### 5.7 The Farscape Story

The shadow-api capability is a concrete, demonstrable result that does not require explaining type theory to communicate. Take an existing C library like OpenSSL and generate a provably safe drop-in replacement with automatically derived SMT proof obligations. "We can take OpenSSL and prove the replacement is memory-safe" resonates with practitioners in a way that the theoretical foundations cannot.

### 5.8 The Posit Proof Story

Where Farscape demonstrates verification at language boundaries (F# calling C), the posit proof-of-concept demonstrates verification across hardware boundaries. It is the concrete artifact that answers the question section 4 raises: does multi-substrate verification actually work?

The demonstration targets an AMD Strix Halo system — Zen 5 CPU, RDNA 3.5 GPU, and XDNA 2 NPU on-die with HSA coherent shared memory — paired with a Xilinx FPGA development board connected over USB. This configuration spans all four substrate kinds that the NTU dimensional type system addresses: CPU for orchestration, GPU for data-parallel computation, NPU for inference workloads, and FPGA for posit arithmetic that no other substrate can execute natively.

Posit numbers (Gustafson's Type III Unum) are the ideal verification use case because the type safety requirement is not optional — it is existential. A posit32 and an IEEE float32 are both 32-bit values, but interpreting one as the other produces silently wrong results. There is no runtime signal, no exception, no NaN. The bits are valid in both formats; the semantics are incompatible. The NTU's type identity distinction (`NTUposit ≠ NTUfloat`) is the only thing standing between correct computation and undetectable corruption.

The verification story operates on three levels:

1. **Type identity across substrates.** The NTU carries `NTUposit(width=32, es=2)` as a distinct type through the entire pipeline. On CPU, Alex lowers this to `i32` storage with software encode/decode. On FPGA, Alex lowers it through CIRCT to a dedicated posit hardware pipeline. The type identity survives the fork — both substrates agree on what the bits mean, even though they execute the arithmetic differently. An `[<SMT Requires("format_posit32(x)")>]` annotation at the source level generates proof obligations on both substrate paths.

2. **BAREWire contracts at substrate boundaries.** When the CPU marshals posit bits for DMA transfer to the FPGA, a BAREWire layout contract defines the memory representation. Both substrates compile against the same shared type definition. The double-entry system verifies this: design-time proofs confirm that the contract is consistent (the debit), and compilation-path assertions in the MLIR smt dialect confirm that both substrate code generators honor it (the credit). A mismatch — one side interpreting posit32 as IEEE float32 — is a type error caught at compile time, not a silent data corruption discovered in production.

3. **Cross-substrate proof obligations on the PSG.** The hypergraph representation connects computation nodes across substrates. A posit dot-product that accumulates in a 512-bit quire on the FPGA and returns a posit32 result to the CPU is a hyperedge spanning two substrates. The proof obligation — that the quire accumulation preserves precision guarantees — attaches to this hyperedge and must be satisfied on both sides of the substrate boundary. This is the verification capability that section 4.1 claims and that F\* structurally cannot provide: a proof that spans hardware boundaries.

The demonstration is built incrementally. The first milestone is CPU-only posit arithmetic — software encode/decode compiled through the standard MLIR/LLVM path, proving the type identity and BAREWire contract infrastructure end-to-end. The second milestone adds the FPGA substrate — CIRCT code generation for posit hardware pipelines, DMA transfer contracts, and cross-substrate proof obligations. Subsequent milestones bring in GPU (data-parallel posit batch operations via ROCm) and NPU (quantized inference with posit accumulation).

For the audiences identified in section 4.3, the posit demo provides different entry points. For formal methods researchers, it is a concrete instance of cross-substrate refinement type preservation — the dimensional type system in action, not in theory. For systems engineers, it is an HPC application running on real hardware with verified data integrity across four compute substrates. For defense program managers, it is a demonstration of the patent's claims (US 63/786,264) on independently owned infrastructure targeting heterogeneous hardware. For certification auditors, it is a complete double-entry evidence package: design-time proofs of posit precision properties balanced against compilation-path proof certificates from every substrate in the system.

## 6. Migration Path

### 6.1 Blog Posts

"Verifying F#" (May 2025) is historically interesting but architecturally outdated. Annotations change from `[<F\* ...>]` to `[<SMT ...>]`. The MLIR lowering examples it contains remain valid. "Proof-Aware Compilation" (August 2025) is largely still current. The hypergraph proof architecture is unchanged. The patent reference is correct.

### 6.2 Patent Applications

1. **US 63/786,264**: Verification-preserving compilation. Describes the MLIR-based approach. Independent of F\*. No migration needed.
2. **US 63/786,247**: BAREWire zero-copy IPC. Independent. No migration needed.
3. **Potential new filing**: Parameterized lemma libraries for automated FFI boundary verification (Farscape + SMT).

### 6.3 Codebase

1. Annotation attribute name: `[<F\* ...>]` → `[<SMT ...>]` throughout
2. Remove F\* subprocess dependency from compiler
3. Z3/cvc5 as solver subprocesses (same solvers F\* uses, invoked directly)
4. MLIR smt dialect for compilation-path proofs (upstream LLVM dependency)

### 6.4 Naming

1. Annotations: `[<SMT Requires>]`, `[<SMT Ensures>]`, `[<SMT Invariant>]`
2. Design-time checker: part of the Keystone LSP (Atelier)
3. Compilation-path proofs: MLIR smt dialect operations
4. Lemma library: Keystone module (e.g., `Keystone.Verification.Lemmas`)

## 7. Open Questions

1. **Lemma library scope.** What is the initial set of parameterized lemmas? Should the starting point be FFI boundary proofs driven by Farscape, or general memory safety lemmas?

2. **LSP proof experience.** How much of F\*'s interactive proof experience should Keystone replicate? Full incremental proof checking, or lighter-weight annotation validation?

3. **Solver choice.** Z3 only, or multi-solver support including cvc5 and Bitwuzla for bitvector-heavy substrate proofs?

4. **Compilation-path granularity.** Translation validation after every nanopass, or only at major lowering boundaries (PSG to MLIR, MLIR to LLVM)?

5. **Community timing.** When to publish the multi-substrate verification story? Before or after a working prototype?

## References

- Fehr, Fan, Pompougnac, Regehr, Grosser. "First-Class Verification Dialects for MLIR." PLDI 2025. https://doi.org/10.1145/3729309
- SpeakEZ Blog: "Doubling Down on DMM and DTS" (January 2026)
- SpeakEZ Blog: "Proof-Aware Compilation Through Hypergraphs" (August 2025)
- SpeakEZ Blog: "Verifying F#" (May 2025)
- SpeakEZ Blog: "Farscape's Modular Entry Points" (June 2025)
- US 63/786,264: "System and Method for Verification-Preserving Compilation Using Formal Certificate Guided Optimization"

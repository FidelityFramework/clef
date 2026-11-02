# Clef native inference: strategy and guide

**Recommendation — November 1, 2026**

**Clef is a concurrent programming language with ML-family syntax and its own native type universe.** It is lazy by default, and its compiler is designed to carry the relationships among values, resources, suspended computations and communicating services into native execution. That remit is the reason to move beyond F#'s inference architecture.

**Build Clef's inference around native constraint-preserving elaboration, with dimensional and negative/fractional obligations integral to the language.** Retain ML-style local inference where it serves that contract. Extend it with qualified schemes, measured structural rows and annotation-guided higher-rank interfaces. Treat numeric representation, platform capability and foreign ABI as evidence-bearing realization constraints rather than importing the compiler host's type universe.

[Negative and fractional types](https://arxiv.org/abs/2606.04352) (NFT) belong at the center of this direction because restoration, directed computation, value identity and one-shot completion require more information than ordinary carrier types retain. Their elaboration rules are the immediate work. A general adapter/subtyping correspondence is a longer-term opportunity.

F# remains a valuable syntax, tooling and inference starting point. Compatibility with every F# restriction is not the goal. Clef's contract must cover measured computation, native resources, deferred precision, state transitions and proof-preserving realization across CPU, FPGA, NPU, MCU, other accelerators and even JavaScript targeting through JSIR.

**Richer Tier 1 proof expression is a primary delivery criterion.** The change must make useful native relationships expressible and checkable through ordinary compilation, then retain their derivations for later use. Each experiment compares standard F# tooling, the relevant mechanism in `write-you-an-inference-in-fsharp`, and the proposed Clef contract. The strategy chapter shows the H1.1 language change in code and identifies the extra field, scope and resource statements Clef must establish. Existing F# measure and member-constraint capabilities receive credit in that comparison.

## The choices to make now

| Area | Recommended decision | Why this is better for Clef in this case |
|---|---|---|
| Core inference | Qualified schemes with retained native constraints, using HM(X)-style interfaces and local rank-1 inference | Preserves familiar inference while exposing obligations ordinary unification cannot discharge. No stock combined theorem is assumed. |
| Dimensions and NFT | Keep measure unification and add explicit directed/value-indexed/use judgments | Distinguishes dimensional compatibility, restoration equality and permission to consume a particular live instance. |
| Stateful services and continuations | Reconstruct and check a bounded coexponential service fragment, retaining partial results and explicit residuals | Connects client pools, exclusive state, suspended frames, reply identity and wait dependencies to the same native contract. |
| Structural records | Unique-label measured rows, with explicit replacement/update | Preserves an unknown tail and its dimensional relationships directly and gives native and JS implementations a clear field contract. |
| Nominal members and foreign identities | Qualified operation requirements and explicit admitted views | Avoids premature nominal selection without erasing getters, effects, equality, handle identity or ABI provenance. |
| Higher rank | Annotation-guided bidirectional checking at interfaces | Supports rich callbacks and libraries without making unrestricted polymorphic inference a dependency of ordinary code. |
| Algebraic subtyping | Keep unrestricted global subtyping outside the core rollout. Allow specific checked views | Rows and qualified constraints meet the immediate structural needs with fewer interactions to settle. Reopen for demonstrated gaps. |
| Numeric and target selection | Preserve range, exactness/error and intermediate facts until a justified construction can be selected | One source quantity can have several faithful realizations. Width does not determine its source identity. |
| Hypergraph and differential compilation | Use revisioned multi-participant relations and dependency-complete evidence from the start. Measure unnecessary graph work | The hypergraph connects all participants of a judgment. Stable schemes can reduce avoidable invalidation while changed ABI, resource or platform premises still propagate. |

Separate procedures solve dimensions, rows, qualified requirements, resource use, ranges and target eligibility under one source contract. Their interfaces and composition rules are part of the architecture.

This is a measurable departure from F#, which already infers generic types and units of measure, and its member constraints support useful forms of polymorphism. It resolves record fields against a named record type or a fixed anonymous-record shape. The proposed Clef approach adds structural rows that can retain an unknown set of fields, along with qualified native constraints that carry resource uses and proof obligations beyond the inferred type. For example, a function could preserve a caller's extra record fields while retaining a field's measure and a separately tracked completion right. Baker would settle those relationships, and CCS would publish their evidence for later compilation. The [worked F# comparison](04-horizons-and-experiments.md) shows the proposed language change and the checks needed to establish it.

Clef's lazy-by-default execution is integral to those rules. Its evaluation model differs from the eager defaults familiar in F# and many ML-family languages. Haskell's non-strict execution is a closer point of familiarity. Evaluation strategy and type inference are different choices, but demand and sharing change which effects, captures and resource facts remain valid when inference generalizes a binding. The language commitment is fearless concurrency and parallelism with no `unsafe` escape, including library code. Access, lifetime, arithmetic and protocol obligations must be established through the admitted source and boundary contracts. The [audience document](07-explaining-clefs-position.md) connects these choices to Haskell and Rust as well as F#, Scala and C/C++.

## JavaScript should receive the native contract

Use Composer's proposed JSIR route to realize settled native judgments and selected numeric constructions. Use `Number` when its operations satisfy the admitted contract. Use exact integer/fixed-point constructions, wider accumulators or compensated constructions where their premises and the source contract require them. Preserve named rounding, intermediate capacity, value semantics and boundary validation.

For JavaScript, the language can select and justify a construction whose meaning exceeds one host scalar, while making its limits visible. It must also retain input/job identity, contribution multiplicity and recovery state. An exact accumulator alone cannot prevent counting the same work twice. The working Fickl/Fable substrate supplies valuable application behavior and regression cases for this native design. [JavaScript and numeric strategy](02-js-numerics-and-interop.md)

## Horizons and delivery order

Horizons describe increasing evidence and commitment without setting dates. The detailed work items, 52 discriminators and gates are in the [strategy chapter](04-horizons-and-experiments.md).

| Horizon | Direction | Delivery criterion |
|---|---|---|
| **1 — establish the native contract** | Implement the bounded scheme/evidence contract, NFT elaboration, deferred numeric rules and a finite service-inference slice. Add unique-label rows and qualified nominal requirements. Exercise one JS numeric and one Farscape boundary path, and measure graph work. | Checked rules and examples, explicit unsupported cases, mutation rejection, and a source-to-realization account for the selected paths. |
| **2 — integrate and broaden production support** | Extend existing CCS/Baker owners and carry settled evidence through PSG, passive Alex and Composer. Expand numeric constructions, structural interfaces, admitted resource aggregates and faithful targets incrementally. | Valid incremental reuse, artifact-bound realization evidence, measured design-time costs and required compiler acceptance gates. |
| **3 — extend the theory where it pays** | Investigate NFT-informed adapter correspondence, selected subtype capabilities and bounded Atelier Transpose fragments. Broaden probabilistic/circuit interpretations with their own laws. | A concrete capability gain and the corresponding observation, coherence, resource or translation result. |

Unrestricted impredicative inference, a universal negative/fractional quotient theory, arbitrary OO translation and proof of arbitrary foreign algorithms fall outside the current rollout. They are not prerequisites for leaving F#-only inference behind. A failing feature gate narrows that feature. It does not keep the entire native direction undecided.

## Why this direction follows from the evidence

Dave's `write-you-an-inference-in-fsharp` provides a paved route to implementing the mechanisms. Pure and mutable HM and split solving illustrate implementation and scheduling choices. Rows and rank-N explore changes to the language. The project began in 2018 and the inspected checkout includes later maintenance and rank-N work. Its examples make the available mechanisms concrete. [Inference decisions](01-inference-landscape.md)

Deferred inference supplies the bridge from reusable source schemes to richer numerics. FPGA exposed per-field width and Mealy/Moore dependencies, but they apply across targets. Fidelity.Platform quotations and other supported declarations constrain realization while preserving provenance. NFT adds a further requirement: selected equality and distinct live instances must survive that realization. These fit a retained-constraint elaborator better than early carrier selection. [Numeric and stateful analysis](02-js-numerics-and-interop.md)

The [coexponential service account](https://arxiv.org/abs/2610.12911) connects data flow to control flow through invocation. A suspended continuation retains a return point, live values and state or resource ownership while a client waits for its particular reply. The proposed inference makes that structure visible without requiring application authors to write the underlying logic. This provides a foundation for concurrent services across targets. [Service inference and experiments](04-horizons-and-experiments.md)

The [compiler proof strategy](04-horizons-and-experiments.md#a-compositional-proof-strategy-for-the-compiler) develops a two-dimensional account of translations and their comparison witnesses. Its first case carries a finite suspended service through inference and one target realization, preserving the premises behind the dimensional, resource and reply claims. The resulting interfaces give the self-hosted compiler proof a concrete starting point.

The same foundation matters to AI and quantum work. A distributed learned-model update can need the identity of a shared sample as well as the types of its replies. A quantum circuit description is classical data, while its execution uses live resources under a separate interpretation. Those relationships motivate concrete cross-domain experiments now. Neither case makes convergence, unitarity or physical fidelity automatic. [AI and quantum cases](04-horizons-and-experiments.md)

Farscape makes the same distinction concrete at a foreign boundary: source numeric spelling is separate from ABI family, width and measured layout. Those facts feed native lowering and proof to the marshaled boundary under explicit foreign hypotheses. They also test differential compilation: retain unaffected source judgments, invalidate changed boundary evidence, and never merge effectful calls merely because arguments are equal. The “quieter graph” benefit is a measurement target, not an announced speedup. [FFI strategy](02-js-numerics-and-interop.md)

This direction is already underway in the current Clef project. Native type unification uses mutable union-find and a separate dimension algebra. Baker has bounded first-demand analysis, continuation ingredients and recipes that retain proof-obligation participants. Farscape records ABI family, width and provenance separately from the source-facing type. These pieces do not amount to the complete proposed inference theory, but they show where its mechanisms can extend existing work. The [implementation triangulation](04-horizons-and-experiments.md) compares them with the inference corpus and identifies the next boundaries.

The selected contract creates work for DTS+DMM, PHG, NFT and the coexponential manuscript: explicit inference/elaboration rules, dependencies, communication and continuation judgments, equality/representation correspondence and implementation evidence. A significant finding may change any published work or specification. Prior wording is not a veto. The [manuscript review](05-manuscript-implications.md) identifies the exact revision sites. Principality, soundness, termination, precision and performance remain separate claims after choosing the architecture.

## Read and use this guide

1. [Specific strategy, horizons and gates](04-horizons-and-experiments.md): the engineering direction and implementation sequence.
2. [Explaining Clef's approach](07-explaining-clefs-position.md): the final positioning document and language for explaining the move beyond conventional ML/HM inference.
3. [Inference decisions and rationale](01-inference-landscape.md): selected mechanisms, alternatives and reasons.
4. [JavaScript, numerics and FFI](02-js-numerics-and-interop.md): concrete source-to-realization decisions.
5. [NFT, subtyping and Transpose](03-subtyping-nft-and-transpose.md): what belongs in the core, what is selective, and what remains beyond the current remit.
6. [Manuscript implications](05-manuscript-implications.md): DTS+DMM, PHG, NFT and coexponential revisions.
7. [Evidence and review record](06-evidence-and-review.md): revisions, model bindings, disagreements, validation and remaining obligations.

CCS/Baker owns source semantics, elaboration, numeric selection and proof premises. Publication copies settled rows into Fidelity.PSG. Alex composes passively, and Composer realizes the target. This direction extends those owners. It does not move missing inference into publication or a backend.

This guide makes a design recommendation now. Implementation and theorem gates remain visible so the recommendation can be carried into engineering without overstating what already works.

**Document owner and growth reason:** this inquiry owns the strategy guide and its evidence, with no new compiler or language authority.

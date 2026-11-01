# Recommended inference architecture for Clef's native type universe

Adopt **native elaboration that preserves constraints**, with dimensions and a finite NFT interpretation in the core contract. Retain rank-1 ML inference for ordinary functions and let-bound polymorphism where its generalization rules remain lawful. Extend source schemes through explicit constraint interfaces, introduce unique-label measured rows for structural records, and check higher-rank interfaces bidirectionally under annotations. Keep nominal member relationships explicit. Do not make unrestricted algebraic subtyping the core inference theory now.

Clef is a concurrent programming language with ML-family syntax and its own native type universe. Its central judgment must retain source types together with dimensional relationships, permitted resource uses, communication and demand relationships, and obligations awaiting further evidence. Numeric range, accuracy, and representation remain deferred graph judgments. Platform and foreign-boundary facts constrain their discharge with explicit provenance. Multiple domain procedures implement this source contract inside CCS and Baker.

This preserves ML's useful local inference while making native quantities, restoration, resources, and boundaries first-class obligations. A global subtype relation would not discharge those obligations. The [overview](README.md) sets the remit. [Horizons and experiments](04-horizons-and-experiments.md) defines implementation and proof gates. These are proposed changes, not claims of completed implementation or proof.

## Evidence binding

Local citations below use these repository bindings:

| Key | Repository | Inspected revision |
|---|---|---|
| I | `write-you-an-inference-in-fsharp` | `4a6f852f36115ad45ac9640753a0bd38f551300c` |
| P | `arxiv-papers` | `d2bab3376032929dc7a4eca7e0bc807247a88c03` |

These outside-index repositories permit scoped direct reads. Retained fresh/latest retrieval snapshot: `1eaf58131802b85f0789664c072e5cb5d6d8047423b77c2be4390d224fdc6311`, generation 71. New indexed facts require schema → pinned find → pgq → sources. Citations bind paths and lines to these revisions. Manuscripts establish design claims and examples establish inspected code, not execution acceptance. See [evidence and review](06-evidence-and-review.md).

## Four decisions often called “the inference algorithm”

**Source theory:** which types and judgments exist, including polymorphism, structural compatibility, resources, effects and dimensions. Open records change this level.

**Inference schedule:** when constraints are generated, propagated, solved and generalized. Schedules can share semantics but differ in diagnostics and interactive cost.

**Implementation representation:** substitutions, mutable links, variable levels and worklists. A faster representation does not itself admit new programs.

**Domain procedure:** solving measure equations, row equations, subtype bounds or representation admissibility. Their interfaces need explicit composition rules.

The F# corpus illustrates these axes: its HM entries vary representation, schedule and rank, while rows add a structural theory. **Evidence:** `I: README.md:8–19`; `Hindley-Milner-Mutable.md:3–9`; `Hindley-Milner-Split-Solver.md:3–5`.

Clef has already begun to build this foundation. Its native type checker uses union-find and measure-aware unification, while Baker supplies distinct demand, continuation, boundary and obligation ingredients. Mutable union-find is familiar inference engineering. The relation to the corpus is both an implementation comparison and a language-design comparison. Extend the relevant current pass when it already supplies the mechanism, and identify the missing judgment before proposing another one. The scoped source bindings and the distinction between existing mechanisms and proposed capabilities are in [H1.9](04-horizons-and-experiments.md).

## Decisions across the candidate families

| Family | Decision | Why it fits or waits | Required boundary |
|---|---|---|---|
| Rank-1 HM and pure/mutable variants | Retain the lawful fragment | Predictable ordinary function inference. Implementation choices remain open. | Scope, occurs checks, generalization and resource restrictions |
| Split constraint solving | Adopt retained constraints and staged discharge | Fits graph provenance and design-time pending obligations | Generalization cannot ignore unresolved relevant constraints |
| HM(X)/qualified constraints | Adopt as an architectural model | Makes domain relations explicit in reusable schemes | Define entailment, ambiguity, simplification and admissible schemes. No inherited universal theorem. |
| Row polymorphism | Add unique-label measured structural rows | Preserves unknown fields and their native types | Absence, replacement, mutation and nominal separation |
| Algebraic subtyping/Simple-sub | Defer as a general core. Study checked views later. | Valuable directional compatibility, but a larger combined theory | Variance, coherence, bounds, effects and resource behavior |
| Bidirectional higher-rank typing | Add at annotated interfaces | Supports useful polymorphic callbacks without unrestricted inference | Predicativity, skolem scope and annotation policy |
| SuperF | Keep as a research comparator | Broader first-class polymorphism at greater semantic/algorithmic cost | Termination heuristic and incomplete acceptance |
| Measures, effects and resource constraints | Core obligations with distinct procedures | Express native meaning and permitted use | Transfer laws, sharing, demand and evidence transport |
| NFT-directed elaboration | Adopt a finite initial interpretation | Connects directed operations, indexed restoration and live resources | Equality discharge, instance rigidity, branch/closure use and lifetime premises |
| Coexponential/session inference | Adopt a bounded service-reconstruction and witness-checking path | Connects client pools, state ownership, communication and suspended control | Finite interface, reply provenance, wait completeness and explicit unresolved boundaries |
| AI and quantum interpretations | Exercise native evidence on bounded learning and circuit cases | Tests joint sample identity, geometric support, circuit descriptions and live resources | Numeric/statistical and quantum interpretations, gate laws, effects and target correspondence |
| Numeric/state analysis and deferred selection | Preserve as graph judgments | Keeps reusable source meaning separate from contextual realization | Coverage, recurrence, accuracy, invalidation and platform provenance |

### HM variants and split solving

Keep HM's ordinary abstraction, application and rank-1 instantiation for `id`, `map`, and local composition. Mutable links, substitutions and variable levels remain engineering choices. The corpus's speed claim is not a Clef benchmark, and printed examples are not a soundness suite. **Evidence:** `I: Hindley-Milner-Mutable.md:5–9`; `HMPure-Rowpolymorphism/Program.fs:55–77`.

Split solving fits retained constraints and provenance. It still respects generalization boundaries: the example solves let-bound constraints before generalizing against the substituted environment. [Heeren, Hage and Swierstra](https://ics-archive.science.uu.nl/research/techreps/repo/CS-2002/2002-031.pdf) give the broader framework, including W and M. **Evidence:** `I: HMSplitSolve/HMSplitSolve.fs:232–257`.

Use staged constraint discovery and discharge, retaining scope and proof premises. Generalize only the variables and residual constraints the scheme rules admit. A pending nominal member or a live resource cannot become fresh, unconstrained polymorphism merely because solving has been delayed.

### HM(X) and qualified constraints

[Sulzmann, Odersky and Wehr's constrained-type framework](https://edocs.tib.eu/files/e001/249661470.pdf) makes the constraint domain an explicit parameter. This provides a vocabulary for studying a heterogeneous NTU without pretending that every discipline is ordinary type equality.

Choose this architectural model, but do not import a stock HM(X) theorem as a theorem about Clef. Specify admissible qualified schemes and their entailment, simplification, ambiguity and generalization rules. A source scheme may quantify carrier, measure or row variables under those rules. A resource instance tied to an existing live pairing stays rigid. Per-invocation range evidence also stays attached to that invocation rather than becoming universally true.

Qualified member/equality obligations retain receiver and operation constraints. Resolution binds the nominal declaration, effects and use conditions. [OutsideIn(X)](https://simon.peytonjones.org/outsideinx/) informs implication constraints and disciplined generalization without deciding Clef's rules.

Select effect/coeffect-indexed generalization, starting with conservative rules for pure immutable bindings. Examine what produces the shared bound value at its actual first demand. Include allocation, mutable reads/writes, foreign effects and captured live rights. Wrapping a computation in a thunk does not make it safe to generalize.

Quantify only admitted flexible variables independent of the environment and shared storage/resource assumptions. Retain admissible qualified requirements in the scheme. Keep affected variables monomorphic when generalization-safety evidence is unavailable.

Latent effects performed on each function call are distinct from effects of producing the shared binding. Effectful functions are not categorically excluded from polymorphism. E05/E06/E24 must exercise this distinction.

### Select unique-label measured rows

For ordinary shareable records, `forall a rho. {Value:a | rho} -> a` retains the unknown remainder in the input scheme. The corpus implements selection, extension and restriction. **Evidence:** `I: HMPure-Rowpolymorphism/HMPureRowpolymorphism.fs:145–223`; `HMMutable-RowPolymorphism/HMMutableRowpolymorphism.fs:208–235,311–348`.

Choose unique labels for the new structural fragment. Extension requires the label to be absent. Replacement is an explicit operation with a declared result type. Mutation requires separate alias/use conditions.

Do not adopt the corpus's [Leijen-derived scoped duplicate labels](https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels/), where restricting an outer `x:Bool` can expose an older `x:Int`. That behavior is useful in its own calculus but adds hidden layering to the record abstraction recommended here.

“Measured rows” retain field types, dimensions, range and resource obligations. Projection cannot silently discard consumable fields in the remainder: it needs an admitted borrow or use rule. Rows establish neither physical ABI layout nor magnitude bounds. Optional presence and effect rows remain distinct judgments.

This deliberately enlarges the source theory. Clef currently documents non-inline `let project x = x.Value` as monomorphic while a nominal member relation remains pending. Introduce structural abstraction explicitly instead of silently reinterpreting every nominal projection as a row. Nominal getters and methods remain qualified operations. This serves native interfaces as well as JavaScript. **Evidence:** `P: dts-dmm-paper.md:94–109`; [JS numerics and interoperation](02-js-numerics-and-interop.md).

### Algebraic subtyping and Simple-sub

[Dolan's thesis](https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf) studies directional compatibility rather than collapsing every constraint to equality. Its polar discipline separates input and output types. Bounds and arrow variance support principal inference in its specified calculus. [Parreaux's Simple-sub](https://cse.hkust.edu.hk/~parreaux/publication/icfp20/) offers a more approachable implementation account of this approach.

Defer unrestricted algebraic subtyping as the core. This is not an objection to structural subtyping or an association with OO inheritance. It is a sequencing decision: rows cover the selected structural abstraction, qualified constraints retain nominal operations, and native resource/numeric obligations still need their own proofs. Adding pervasive bounds, joins and meets now expands the combined proof problem without removing those obligations.

Pursue selective checked views later where branch joins, foreign interfaces or Transpose need them. A view needs a justified transformation, variance and resource behavior. Neither an arbitrary function nor NFT notation alone supplies substitutability. Use Simple-sub as a serious comparator on those cases. [Subtyping, NFT and Transpose](03-subtyping-nft-and-transpose.md) develops the correspondence questions.

### Higher-rank checking and SuperF

The corpus adds annotations, synthesis/checking, subsumption and skolem handling: a source capability beyond rank-1 HM. **Evidence:** `I: HMRankN/HMRankN.fs:31–37`; `Hindley-Milner-RankN.md:72–119`.

[Peyton Jones and colleagues](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/putting.pdf) and [Dunfield–Krishnaswami](https://arxiv.org/abs/1306.6032) provide distinct annotation-guided accounts. Select a predicative bidirectional interface discipline: infer ordinary rank-1 code and check explicitly polymorphic interfaces against annotations. Preserve skolem scope and qualified native obligations through that check. Completeness for the selected calculus does not mean inference of every unannotated polymorphic term.

[SuperF](https://cse.hkust.edu.hk/~parreaux/publication/popl24/) explores first-class polymorphism through multiple lower and upper bounds. Its recursion-avoiding heuristic rejects some valid programs to ensure termination. Defer that broader design. Retain it as a comparator if the chosen interface discipline imposes demonstrable, important limitations.

## Deferred inference changes the comparison

The site's **The Gift of Deferred Inference** distinguishes a principal dimensional scheme, later specializations, unresolved variables, established ranges and distributions. It preserves integer-affine relationships rather than reducing every fact to an independent interval. A source `float<newtons>` does not imply a magnitude bound or select a physical representation. **Evidence:** `clef-lang-site@15d381634f7a08c2a44884a0598d0e634083b313`, `hugo/content/blog/deferred-inference.md:36–44,58–96`.

The selected scheme architecture must retain these obligations at each use. Generalization must not export one invocation's range as a universal fact. A shared realization needs a justified envelope for its admitted uses. Specialization may use narrower contextual facts. Neither may choose a host width merely to close an unresolved variable.

Lazy demand determines when mutable observations must remain valid. It does not postpone representation obligations past commitment. The article fixes FPGA widths before synthesis. ABI, memory-layout and numeric commitments impose the same distinction on other targets. **Evidence:** same article, 96,160–198,202–250.

Keep numeric solving outside ordinary type unification while preserving its dependencies in the same graph. A most-general source scheme, a sound numeric enclosure and an accuracy-optimal admitted representation answer different questions. The article excludes cost, latency and area from its numeric accuracy objective. Target mapping and physical cost remain separate obligations. **Evidence:** same article, 64–86,132–140,204; [cross-target cases](02-js-numerics-and-interop.md).

Reusable schemes and delayed commitments may improve differential compilation, but measure that claim against full recomputation. H1.7 checks semantic results, revisited recipes, valid evidence reuse and edit-to-result cost. Fewer updates count as a gain only with complete dependencies. Never coalesce NFT live identities or effectful occurrences to obtain a quieter graph.

## Native disciplines and Tier 1 evidence

The current manuscripts already separate measure unification from other analyses. Integer-exponent measure equations have a principal-solution account under stated generalization conditions. Blade support, lifetime, range and capabilities need their own transfer laws and termination arguments. Separate queries suffice only when the constraint relation factors. Exchanging facts requires explicit dependencies and repeated-solving rules. **Evidence:** `P: decidable-by-construction.md:45–61,75–88`; `dts-dmm-paper.md:131–143`.

Keep three results distinct: a most-general scheme, a least propagation fixed point, and a preferred target realization. A satisfying substitution need not be principal. A sound enclosure need not be maximally precise.

Start NFT with the manuscript's finite immutable data, decidable equality and absence of hidden consumable resources inside the indexed data. Distinguish a creation value from its live pairing instance: equal values can have different instances. The instance remains rigid, even when the surrounding carrier or measure scheme is polymorphic. Shared lazy evaluation cannot create additional consumption rights. Physical release also requires lifetime and alias premises. This is a finite starting contract, not a restriction that all future NTU values must be finite or immutable. **Evidence:** `P: negative-fractional-types-in-fidelity.md:163–188`.

Tier 1 should certify admitted structural compatibility, dimensional relationships and permitted uses. Restoration equalities, inverse laws and foreign effects need their applicable additional premises. Effects and demand qualify parametricity as well. No universal principality, completeness or decidability theorem for this combined design is claimed. State and prove the selected fragments, their interfaces and their limits. **Evidence:** `P: decidable-by-construction.md:197–216,440–446`; `negative-fractional-types-in-fidelity.md:192–208`; `fixed-point-scaffolding.md:274–284`.

H1 now validates this selected direction: specify the finite core and qualified schemes, prototype structural rows and annotated interfaces, and produce discriminating derivations and refusals. Competing procedures serve as controls and can expose a reason to revise the decision. Choosing among them is no longer the sole deliverable.

H2 integrates proved fragments into existing owners. H3 explores more general adapters, subtyping/NFT correspondence and multilingual Transpose. Targets influence admissibility and realization. Source-rule differences require an explicit profile contract.

Farscape's ABI descriptions can differ while source numeric spelling stays the same. Keep source, representation and dynamic resource identity distinct. [Chapter 2](02-js-numerics-and-interop.md) binds implementation and proof limits. H1.8 tests lowering and reuse.

The selected design preserves CCS/Baker's semantic ownership, passive Alex witnessing, publication of settled rows, and Composer's target realization. [Manuscript implications](05-manuscript-implications.md) identifies the resulting obligations for DTS+DMM, PHG and NFT.

---

New-file justification: inquiry-owned comparative research chapter, with no new semantic authority.

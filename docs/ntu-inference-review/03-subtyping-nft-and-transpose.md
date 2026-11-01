# Subtyping, negative/fractional types, and Transpose

**Recommendation:** organize Clef inference around dimensional and NFT constraints preserved through elaboration. Retain a rank-1 ML core, extend its schemes with explicit qualified constraints, and use unique-label measured rows for structural records. Nominal identity and getter/method requirements belong in qualified contracts. Higher-rank uses require annotations.

Admit checked structural views where their semantics are established. Do not make unrestricted algebraic subtyping the organizing rule of the NTU, or treat a general NFT ratio as an already established replacement for it.

This is a choice to develop beyond F# inference, not a claim that F# already supplies the required combination. “HM(X)-style” describes qualified schemes over cooperating constraint domains. No stock theorem proves this proposed combination. The [inference landscape](01-inference-landscape.md) develops the architecture. [JavaScript, numerics and interop](02-js-numerics-and-interop.md) supplies its boundary cases. The recommendation is concrete, while implementation and theorem acceptance remain subject to [the experiment gates](04-horizons-and-experiments.md).

## What structural subtyping would contribute

Structural subtyping concerns the interfaces a value can safely support. Inheritance concerns mechanisms such as reuse, lookup, initialization and dispatch. A language can study the former without making the latter its native organizing model. OCaml provides a useful comparison: its object types enumerate method signatures, while objects, classes and types remain distinct concepts. Its manual explicitly cautions against importing the relationships found in Java or C++. [OCaml object manual](https://ocaml.org/manual/5.5/objectexamples.html)

The strongest algebraic-subtyping case is directional information: inputs constrain what is acceptable, while outputs describe what can be produced. That can preserve distinctions lost by replacing subtype inequalities with equalities.

Dolan's calculus combines ML-style polymorphism and subtyping with principal types and decidable subsumption. Its polarity discipline permits joins in output positions and meets in input positions. Function arguments reverse polarity. These restrictions belong to the result's scope. They do not establish the same properties for every NTU extension. [Dolan, *Algebraic Subtyping*, summary, §5.1 and chapter 9](https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf)

The [video considered in this review](https://www.youtube.com/watch?v=OenHweMNVeY) illustrates record width and variant inclusion at 7:50–8:26 and function variance at 15:02–16:13. It gives an either-input result `β → γ → β ∨ γ` at 17:18–17:45 and separate mutable write/read bounds at 20:08–21:07. These concern structural compatibility and information flow, not necessarily class hierarchies.

Video evidence here is limited to the supplied transcript through 28:27. Diagrams were not inspected, and transcription ambiguities were checked against primary literature.

Rows express relationships involving an unknown record tail, particularly transformations that preserve it. Subtype bounds and unions address additional relationships, including heterogeneous alternatives and consumer requirements. A limitation of one equality-row example is not a universal impossibility result for row systems. Conversely, choosing rows does not make those additional relationships disappear. Simple-sub also distinguishes theory from implementation: algebraic subtyping does not require one particular biunification implementation. [Parreaux, *The Simple Essence of Algebraic Subtyping*](https://cse.hkust.edu.hk/~parreaux/publication/icfp20/)

## Why measured rows and selective views come first

The recommendation favors preserving explicit relationships that Clef already needs to explain. A function projecting a measured field should retain its measure and the relationship to the unknown tail. Adding a fresh field and replacing an existing field should be distinct operations. Unique labels with explicit replacement make that distinction visible.

Unique labels also avoid requiring an ordinary JavaScript object to represent two simultaneously accessible occurrences of the same label. Scoped duplicate-label calculi remain legitimate alternatives. They require their own representation and lookup contract.

The same design can keep nominal identity separate from structural access. A field requirement does not establish a getter's effects, a method's receiver behavior, record equality or a foreign handle's lifetime. Qualified contracts carry those requirements without silently making every object a structural record. An admitted view must state whether it is a projection, wrapper or shared reference, and what it preserves. The collection and foreign-boundary cases in [chapter 02](02-js-numerics-and-interop.md) make these differences observable.

Implicit measured unions should not be the default response to conflicting branch results. Prefer an explicit tagged/sum contract when alternatives carry distinct dimensions or interpretations. A safe union is not unsound. A subtyping system can also reject an invalid operation across dimensions.

The reason for this choice is that a clear dimensional disagreement should remain a clear obligation at the branch or consumer. An inferred union would need additional elimination and diagnostic rules. Comparable examples must test whether this explicitness costs too much annotation.

Global subtyping would add bounds, joins, meets and variance to a combination already responsible for value indices, demand, resources and numeric refinements. Its published results do not discharge that combination's obligations. Measured rows and qualified constraints provide a narrower first contract with useful structural reuse. That is the present engineering and language-design judgment, not a theorem that algebraic subtyping cannot express the remit.

Retain the competing implementation in bounded comparisons, especially for foreign APIs, heterogeneous branch joins and future Transpose fragments. Reopen the core choice if it yields materially clearer programs and checked evidence without losing the required distinctions.

## What NFT makes more direct

Clef's negative/fractional manuscript addresses directed execution, value-indexed matching and resource uses. Several similar-looking terms denote different judgments:

| Term | Meaning relevant to this inquiry |
|---|---|
| Negative occurrence | An input or contravariant position in a particular subtype calculus. |
| Type complement | A set-theoretic operation requiring a specified universe and interpretation. |
| Linear dual | A dual interface whose laws depend on a particular resource calculus. |
| Clef `Neg<A>` | A value participating in admitted turns of directed evaluation. |
| Clef `Recip<A>` / `1/v` | A reciprocal indexed by a particular value, with matching and live-instance use rules. |

The NFT manuscript distinguishes these constructions from reciprocal physical units: `Recip<float<N>>` is not `float<N^-1>`. It also distinguishes value-indexed matching from unrestricted logic-variable search. [N:51–105,190–206]

Its controlled-XOR example provides a particularly useful test. A zero-valued workspace is paired with its reciprocal, used, restored to zero, and eliminated under the matching contract. Omitting the restoring operation can leave the carrier type correct while violating the indexed obligation. This is an **NFT manuscript example**, not an example established by the video. An ordinary subtype fact about the workspace's interface does not prove restoration. [N:113–145,159–178]

Similarly, a deferred result can carry a single completion right that two consumers must not duplicate. Sharing a lazy result does not create another consumable right. NFT makes that obligation explicit. DMM must still account for storage lifetime. This could simplify application contracts, but comparative annotation burden and inference cost remain to be measured. [N:149–155,182–188]

The underlying negative/fractional literature does not license a universal inverse. Chen and Sabry's erratum identifies a missing uniqueness condition and a counterexample to the original inverse-category conclusion. The Clef manuscript records this limitation. [N:80; Chen–Sabry [paper](https://par.nsf.gov/servlets/purl/10296315) and [erratum](https://homes.luddy.indiana.edu/sabry/files/2021/02/errata.pdf)]

## NFT as an organizing contract

NFT belongs in elaboration now because a reusable source scheme must connect to live value-indexed obligations at each use. A branch can preserve the same printed type while consuming a different right. A closure can capture a right without gaining permission to duplicate it. A deferred numeric conversion can preserve range while losing the exact equality needed for elimination.

These are inference and elaboration questions even when no implicit subtype coercion occurs. They justify developing NFT's own judgments without first proving that NFT subsumes structural subtyping. [N:159–194,216–224; manuscript review in chapter 5]

The immediate implementation guide is a finite, explicit elaboration fragment. Structural inference contributes a qualified scheme. Resource rules track permitted live-instance changes. Admitted numeric and transition procedures supply their premises. Generalization must preserve the relevant obligations rather than duplicate a captured right or discharge a use-site premise.

The existing CCS/Baker owners remain responsible. “Fragment” describes a research judgment and executable reference, not a new production intermediate language or parallel semantic owner.

The manuscript's initial reciprocal core admits finite immutable data with pure decidable equality and no hidden consumable resources. A record can carry a separately tracked completion right, but placing such a record inside the indexed data domain requires an additional admission rule. Mutable objects and unrestricted foreign equality cannot be admitted just by assigning them an ordinary carrier type. A handle needs an explicit identity and lifetime protocol, including the observations permitted before and after release. [N:163–180]

Use an extension of the current inference regime with equivalent resource/effect constraints as a control. The NFT-directed account must earn clearer derivations, fewer special cases, useful accepted programs, stronger checked evidence or better diagnostics. Its constructors expose their value index. Proving that a later value matches it remains a separate task, not arbitrary inverse-value search. This comparison tests the selected direction without making a survey the endpoint.

The direct review of the NFT paper in [chapter 5](05-manuscript-implications.md) therefore belongs to H1. The broader claim that negative/fractional constructions can unify or replace structural subtyping belongs to the adapter research below and must earn a correspondence theorem.

## The proposed adapter bridge

An adapter notation such as `B/A` could describe an admitted route from interface `A` to interface `B`. This is a **proposed contract**. The inspected NFT manuscript defines value-specific `1/v`. It does not already identify general type ratios with subtyping.

An arbitrary `A -> B` is insufficient justification for implicit substitutability. A constant function discards its input, and two functions with identical endpoint types can produce different observable answers. The bridge therefore needs explicit admission and coherence rules:

1. State which observations, effects, demand behavior and identities an adapter preserves.
2. Define identities, composition and the equivalence required of alternative adaptation paths.
3. Account for resources hidden, transferred, retained or discarded by the adaptation.
4. Specify variance, joins/meets and generalization, together with the claimed inference properties.

For example, adapting a function requires a route from the new accepted inputs to the original inputs, and a route from original results to the promised results. That composition explains the direction of arrow variance. Replacing its input type with `Neg<A>` does not establish the rule.

A record projection from `{x:A; y:B}` to `{x:A}` is another discriminating case. If `y` carries a completion right, projection cannot silently erase it. A reversible route must retain a suitable residual, while a destructive route needs justified disposal. Reconstructing the original from the projected record alone is generally unavailable. The adapter correspondence and any translation lemma remain unproved proposals.

## Challenges that could reopen the choice

| Selected decision | Strongest challenge | Evidence needed to change the decision |
|---|---|---|
| **NFT judgments participate directly in elaboration.** | Equivalent qualified resource constraints might achieve the same result more simply. | Comparable restoration, completion and lazy-capture examples show no useful derivation or diagnostic gain, or the proposed rules lose branch/index/resource distinctions. |
| **Unique-label measured rows govern structural records.** | Algebraic subtyping can infer useful joins and consumer interfaces with fewer annotations. | Repeated representative cases favor its interfaces and diagnostics while a checked combination preserves measures, indices, resources and demand. |
| **Structural views are selectively admitted.** | Explicit views might multiply wrappers or obscure useful interface relationships. | A coherent implicit-view fragment preserves identity, effects, equality and lifetimes, with manageable inference and faithful lowering. |
| **Higher-rank uses are annotation-guided.** | More general inference could improve callbacks and reusable interfaces. | A named fragment demonstrates acceptable completeness, termination/resource bounds and diagnostics alongside the required NTU constraints. |
| **General `B/A` correspondence remains H3.** | An adapter calculus might explain several current judgments with fewer independent rules. | Identity, composition, observations, resource transfer and a correspondence result are established for a useful fragment. Endpoint types alone do not suffice. |

First-class polymorphism particularly needs precision: SuperF offers a promising bounded-constraint approach, but its authors use a termination heuristic that rejects some valid programs. Its expressiveness is not evidence of complete unrestricted inference. That is a reason to investigate its admitted fragments alongside annotation-guided higher rank, not to promise unrestricted inference now. [*When Subtyping Constraints Liberate*](https://cse.hkust.edu.hk/~parreaux/publication/popl24/)

## Transpose as a preservation remit

Future Atelier Transpose would interpret or port admitted fragments of OCaml, C#, Scala and C++ object patterns into Clef's constructs. Preserving source object behavior does not require classes or inheritance to organize Clef's NTU. It does require more than matching method names and types.

The current evidence is preliminary. Atelier's README describes a design project, and `docs/10_transcribe.md` remains a placeholder owner for related migration ideas. Its analysis requirements distinguish language-specific semantics from pattern recognition. Naming a callback/environment/destruction relationship does not prove it. “Transpose” here names the future remit, without claiming an implemented multilingual translator or renaming that source document. [A:README.md:7,13,77; docs/10_transcribe.md:3–5,77–99]

| Porting case | Preservation obligation and counterexample |
|---|---|
| Dynamic dispatch | A call through a base/interface view must retain the selected override, receiver and effects. Substituting the base body can change behavior. |
| Aliased mutation and identity | Two views must retain the source's shared state and identity observations. Copying a structural record can sever the alias. |
| Initialization and exceptions | Preserve required evaluation order, failures and cleanup. Lazy-default Clef bindings must not defer an effect the source requires earlier. |
| Destruction, moves and capture | Retain lifetime and permitted invocation counts. A copied closure must not duplicate a one-shot completion right. |
| Multiple interface/base views | Preserve the admitted source fragment's object or subobject correspondence and dispatch adjustment, rather than treating every view as an independent record. |

Tier 1 may establish scoped interface compatibility and permitted uses under admitted structural rules. General behavioral preservation requires the appropriate state, effect, lifetime and relational premises as well. An NFT restoration fact is useful evidence within such a proof, not the entire proof. Broader applications of NFT must therefore name their admitted interpretation and checking procedure. The notation does not automatically confer arithmetic, runtime or translation evidence.

Farscape's elicited declarations and separate ABI evidence provide a concrete, narrower precedent for this separation. They do not establish C++ object behavior, arbitrary foreign lifetimes or a full Transpose translation. Reuse that provenance and boundary discipline while stating the additional source-language preservation obligations. Applying NFT to foreign handles first needs an admitted equality/identity and lifetime account. [FFI analysis and source bindings](02-js-numerics-and-interop.md)

The proposed ownership remains language-specific analysis and translation obligations, followed by ordinary Clef elaboration and CCS/Baker settlement. Atelier presents recipes, gaps and evidence. Alex remains passive. PSG publication copies settled facts. Composer realizes the target. This is a proposed division of work, not an accepted translation theorem. [A; P:84–120]

## Recommendations by horizon

**Horizon 1 — develop the selected core now.** Build bounded proof/fixture prototypes for qualified ML schemes, unique-label measured rows and NFT elaboration. Make fresh extension versus replacement, measured projection and branch-correlated records acceptance cases. Include lazy captured rights, annotation-guided callbacks, exact workspace restoration and one-shot completion.

Run qualified-member and algebraic-subtyping controls on the same corpus. Compare derivations, rejected mutations, annotations and diagnostics. A small explicit adapter correspondence example belongs here, while the general theory remains H3.

**Horizon 2 — integrate admitted fragments.** Put successful judgments and constraint settlement in the existing CCS/Baker owners, preserving qualified schemes and use-site premises through publication. Bind incremental reuse to the relevant evidence and dependencies, and establish faithful target/library realization. Admit structural views where their particular contracts pass these gates.

Component soundness does not automatically establish soundness, principality or termination for the combination. Those claims require their own scoped argument.

**Horizon 3 — broader adapter and porting research.** Investigate general NFT/adaptation correspondence and multiple Transpose source languages after bounded cases establish useful laws. Require explicit supported fragments and preservation criteria. DTS+DMM, PHG and NFT are revision candidates if this work establishes new judgments, a stronger evidence contract or demonstrated inference benefits. Plurality alone is already contemplated. See [manuscript implications](05-manuscript-implications.md).

## Source binding and limits

`N` identifies `arxiv-papers@d2bab3376032929dc7a4eca7e0bc807247a88c03`, `negative-fractional-types-in-fidelity.md`. `P` identifies the same revision's `program-hypergraph-paper.md`. `A` identifies `Atelier@7ef996603c3b83d1a53fdc639c970d44634f5482` and the paths cited above. Both repositories were outside retrieval generation 71, snapshot `1eaf58131802b85f0789664c072e5cb5d6d8047423b77c2be4390d224fdc6311`. Scoped direct reading was the applicable exception. Indexed evidence uses fresh/latest schema → snapshot-pinned find → pgq → sources. This chapter reuses retained evidence and adds no indexed-source discovery.

This review chapter is owned by the NTU research review. This revision extends that existing owner with a concrete design recommendation and adds no production semantic authority. The uncommitted chapter was inspected through `git diff`. No new source discovery, compiler changes or acceptance gates were performed. Detailed provenance and review limits are in [Evidence and review](06-evidence-and-review.md). The [review index](README.md) connects the complete argument.

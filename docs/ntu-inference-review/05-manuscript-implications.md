# Implications for DTS+DMM, PHG, NFT and the coexponential paper

Revise the manuscripts' architectural account around the selected native elaboration direction: qualified schemes, dimensional and NFT judgments, unique-label measured rows, deferred numerics, service inference and evidence-preserving realization. NFT supplies a central contract for value identity and resource use. The coexponential paper connects service, client and continuation structure to communication and control. DTS+DMM and PHG explain their analysis and incremental integration. This chapter recommends the changes and separates design commitments from theorem and implementation claims that need additional evidence. The manuscript files themselves were not edited during this work.

These first concrete impact sites can lead to changes throughout the published work, specifications, design documents and implementation accounts. Propagate supported claims with their premises, and revise conflicting downstream accounts as evidence warrants.

The central contribution to test is an enlarged set of native relationships that Tier 1 can express and check. The manuscripts should show a standard F# result, the relevant mechanism from `write-you-an-inference-in-fsharp`, and the additional Clef judgment with its derivation and failing control. DTS+DMM should explain the new schemes and admissible generalization. NFT should make the value/instance/use rules explicit. PHG should show how those derivations compose and when an edit invalidates them. The worked comparison and mandatory experiment format are in chapter 4. Existing F# dimensional inference is part of the baseline, not a newly discovered Clef advantage.

## Source binding

The manuscripts are in `arxiv-papers@d2bab3376032929dc7a4eca7e0bc807247a88c03`:

- `dts-dmm-paper.md` — DTS+DMM.
- `program-hypergraph-paper.md` — PHG.
- `negative-fractional-types-in-fidelity.md` — NFT, whose current source identifies itself as a working draft at lines 1–7.
- `coexponential-exploration.md` — the coexponential service, continuation, communication and realization account.

The inspected manuscript files had no working-tree diff. Existing unrelated changes in that repository were preserved. The requested AGENTS primer was read first. It directs primary claims to the manuscripts, rather than making itself the scientific authority.

DTS+DMM 131–143 already distinguishes dimensional, range, lifetime, representation and accuracy evidence. PHG 94–108 already gives different predicates distinct procedures and admits symbolic solving, fixed points, search and pending obligations. PHG 118 already binds reuse to revision, participant correspondence and completeness dependencies. Therefore, “several algorithms can cooperate” is not by itself the new contribution.

## Candidate revision sites

| Site | Current account | Finding that would justify revision | Evidence required |
|---|---|---|---|
| **DTS+DMM §2.2,84–109** | Kennedy-style measure inference under host generalization. Ordinary unresolved non-inline member access remains monomorphic pending nominal context at line 107. | An admitted measured-row or qualified-member fragment gives useful reusable schemes while preserving scope, effects, demand and resource premises. | Declarative distinction between structural fields and nominal operations; positive/negative derivations; soundness and the claimed principality/qualified-principality result. E01–E06, E18. |
| **DTS+DMM §2.4,131–143** | Different procedures supply property-specific evidence and premises. | A concrete interface for alternative proof-producing procedures, or an NFT-informed compatibility judgment, supplies checkable structural derivations with clear composition conditions. | Named judgments, evidence/checking rules, producer premises, instantiation/generalization binding and corrupted-evidence rejection. A serialized answer is insufficient. |
| **DTS+DMM incremental sections,351–382** | Typed/pending states, later-use member constraints, complete write sets and qualified reuse/cost claims. | A working incremental procedure improves design-time behavior while reusing only valid evidence. | Comparison with full recomputation, hidden-dependency mutations, source/configuration bindings, and measured latency/evidence cost. E14, E15, E18. |
| **PHG §2.1–2.2,84–100** | Ordered participants, relation identity, unresolved variables, assumptions and predicate-specific procedures. | A candidate requires a binder, instantiation, correlation or live-index fact that the current representation cannot yet state explicitly. | Demonstrate the failure without that fact and its checked encoding in the existing owner. If the current relation suffices, add a worked example rather than inventing another graph. E03, E05, E06, E13. |
| **PHG §2.3 and design-time integration,102–120,324–339** | Finite-height monotone fair scheduling under stated conditions; distinct pending/search cases; revision-bound evidence and editor status. | A concrete strategy policy improves responsiveness or precision without changing the meaning of proved, approximate, pending and contradictory results. | Stated dispatch/fairness/termination conditions; evidence compatibility; measurements and invalidation examples. Timeout must not become contradiction or proof. |
| **PHG §8.3,453–463** | Supported combinations, principality, termination and cost bounds remain future work. | One useful combined structural fragment is established, or a checked adapter/Transpose correspondence expands the admitted remit. | Name the language and input encoding. Establish the actual typing/resolution or preservation properties. Expose unsupported cases and measure any claimed performance. |
| **DTS+DMM §2.4/incremental account,131–143,351–382** | Numeric, representation and other property evidence remain distinct and dependency-bound. | Reusable source schemes retain contextual numeric obligations through generalization, demand and selected platform changes, with a demonstrated precision or differential-compilation gain. | E19–E20/E26; scope and dependency rules; correspondence to full recomputation; separate inference, checking and realization measurements. |
| **PHG §2.1–2.3,84–120** | Relation participants and assumptions govern predicate-specific evidence and reuse. | One worked NFT/stateful/numeric example shows the needed identities and transitions, or exposes a missing relation. | E21–E26; creation/live-instance identity, equality, state/output dependency, snapshot and platform bindings. Reuse existing relations if sufficient. Add a new one only for an exhibited gap. |

Experiment identifiers refer to [chapter 04](04-horizons-and-experiments.md). These are revision conditions, not a claim that any current theorem is false.

## Coexponential services: what the manuscript contributes

The paper provides a foundation for inference. Its finite actor fragment relates a service and client pool to a state protocol. Its continuation account associates each invocation with a return point, live environment, resource ownership and one completion right. Its communication summary and wait relation describe additional facts about that same source. **Evidence:** `coexponential-exploration.md:116–161,196–248,260–310`.

The paper states finite service, ownership and reply-preservation results under named premises. Its service-order theorem requires both the same final state and the same reply for each labelled request. Its finite-batch completion result additionally requires complete wait coverage, whole-continuation progress and the stated scheduling, selection and external-outcome assumptions. These are source results with explicit scope. The proposed source-to-session reconstruction algorithm and target-runtime correspondence remain separate work. **Evidence:** `coexponential-exploration.md:226–238,280–310,312–346,665–682`.

The inference research sharpens the implementation choice: begin with a finite interface and a checkable witness. Retain partial facts and residuals only under a sound composition rule, or withhold the whole-interface claim while preserving independent local evidence. A finite summary, checking a supplied derivation, reconstructing a protocol and transferring its property to a runtime are four different tasks. **Evidence:** `research/coexponential-inference/04-inference-ladder-design.md:7–57`, `05-decidability-map.md:7–38,54–72`.

| Revision site | Recommended change and evidence |
|---|---|
| **§§3–4: service and continuation construction** | Give the native inference interface for message alternatives, state ownership, fresh invocation identity, captured values and completion rights. Show one checked finite derivation and a failed duplicate/escape control. E34, E36–E38. |
| **§5: summaries and completion** | Distinguish an inferred finite may-wait abstraction, its complete dependency scope, a checked protocol witness and the stronger completion theorem. State the result when a callback or endpoint remains unresolved. E35, E40–E41. |
| **§6: scheduling** | Make preservation of the request-labelled reply map as well as final state the criterion for reordering. Retain the old-value counter as the negative case. Stochastic sampling and external effects need their own observation relation. E39. |
| **§§7–10: boundary, evidence and realization** | Bind message shape, endpoint provenance, storage, representation, proof dependencies and target correspondence to the same interaction. Preserve frames already suspended under an earlier revision or establish a migration. E42–E44. |
| **Recursive protocols and logic interfaces** | Name the reconstructed fragment, proof-object language and checker before claiming completeness or principality. Relate runtime fairness and validity to the selected theorem. Do not infer a combined adjoint/coexponential metatheory merely from similar terminology. E45. |

The paper's `§10.1` already places message/session structure, local checks, reusable protocol laws and relational claims at distinct tiers. The revision should show which new inference evidence supplies each application, without moving an unresolved local or relational obligation into Tier 1 by changing its name. Its `§10.7` provides the dependency-complete replacement account for the expanded differential experiments. **Evidence:** `coexponential-exploration.md:665–682,729–780,856–879`.

### AI and quantum implications

The coexponential paper's distributed metric example binds each direction, sampled execution, parameter point and contribution to one job. Its cross term shows a genuine inference and evidence need: separately correct marginal values can yield the wrong metric if a shared sample is silently replaced with an independent draw. Revise the service-inference interface around the identities and coupling premises that this example actually consumes. Keep exactly-once receipt, arithmetic error and statistical confidence as distinct claims. **Evidence:** `coexponential-exploration.md:578–660`; E47–E49.

NFT's quantum section already distinguishes classical circuit descriptions, live quantum wires, checked unitary gates, coherent uncomputation and measurement/reset. Make the selected inference fragment preserve those distinctions and name the interpretation used for each. An older quantum research note makes broader claims that negative/fractional notation automatically yields unitarity. The current NFT manuscript instead requires a checked gate interface and its laws. Follow the manuscript's scoped contract and reconcile the older note through its owner. E50–E52 test the distinction. **Evidence:** `negative-fractional-types-in-fidelity.md:535–624`; `research/quantum/circuit-as-typed-value-substrate-neutrality.md:1–25,70–94`.

For ADM, retain a bivector support across an admitted update and separately establish dimensional compatibility, numerical error, optimizer and realization conditions. A support proof is not a convergence theorem, nor does a shape prove a rotor invariant. **Evidence:** `adaptive-domain-models.md:88–104,477–491`; E47–E48.

## NFT: what the manuscript contributes

NFT supplies more than a suggestive analogy for subtyping. Its directed `Neg<A>` operations, value-indexed `Recip<A>` operations and finite resource map distinguish several facts that an ordinary carrier type cannot express alone. A restored workspace may have the same carrier type as an unrestored one. Two equal creation values may own different live reciprocal instances. Sharing a deferred result does not duplicate its permitted consumption. The manuscript already states these distinctions and keeps live resource variables rigid through generalization. **Evidence:** NFT49–105,113–188.

Its initial reciprocal domain is finite immutable data with pure decidable equality and no hidden consumable resources. Negative direction is not type complement or subtype polarity. A reciprocal is not an inverse physical unit. The paper acknowledges the inverse-category erratum and requires library inverses to establish their own round-trip laws. These are strengths to preserve, not missing cautions to invent. **Evidence:** NFT80,163–180,190–208.

The manuscript contains local written proofs, including XOR restoration, representation matching under injective encodings, independent successful resource deletion and finite exact reconstruction. It also explicitly keeps approximate reconstruction from justifying exact elimination. Those conditional results do not amount to a complete inference algorithm, global principality theorem, general inverse-discovery procedure or whole-compiler preservation proof.

The full manuscript body,1–686, was read conceptually for this assessment. Its domain mathematics was not independently re-proved. **Evidence:** NFT139–145,220–236,274–278,335–368.

## NFT revision sites and acceptance criteria

| Site | Assessment | Revision or evidence to pursue |
|---|---|---|
| **§§2–4,49–105,149–208: inference/elaboration** | Operational resource updates and use rules are present. A complete let/branch/closure/call/instantiation judgment and inference theorem are not supplied. Constructor-index inference is different from proving a later value matches. | H1.6: state the finite fragment, scope and branch rules, packaging/escape policy, actual-demand premises and unsupported cases. Distinguish flexible type/measure variables, retained creation values and rigid generative live identities. Establish only the soundness, principality, completeness or termination properties actually proved. |
| **§§3–4,139–208: width and equality** | The XOR example fixes mathematical word width `W_w` through its enclosing interface. That does not yet connect the interface to deferred NTU representation selection. Illustrative `Recip<float<N>>` also needs a selected equality interpretation. | Connect source operation, mathematical word domain and target carrier explicitly. Define equality for any admitted floating domain, including relevant NaN/signed-zero behavior or exclusions. Range coverage and exact restoration remain different obligations. E19,E25. |
| **§5.1,218–226: representation preservation** | Proposition2 requires injective value encoding and injective live-instance renaming. An abstract equality needs preservation and reflection. This is a local matching result, not preservation of every operation. | Show one admitted carrier change and rejected lossy encoding/identity collision. Bind the reachable domain, equality, success/mismatch branches and resource effects. A wider carrier can qualify. Its width alone is insufficient. E23,E25. |
| **§§4.2/6.3,184–188,313–325: deferred snapshots** | Captured mutable storage is already distinguished from a value. The illustrative recovery tuple states a snapshot contract without demonstrating its timing under lazy defaults. | Make evaluation, `readInputs` and `rules.version` share the same immutable input and rule implementation/version at actual demand. Constructing a lazy tuple does not eagerly freeze observations. Add mutation/version-change and valid shared-demand cases. E26. |
| **§§6–7,278–303,335–414: numerical reconstruction** | Schedule, external/random observations, rounding defects, sensitivity and anchor error are retained premises. Approximate reconstruction is expressly insufficient for exact elimination. | Connect those premises to the inference fragment. At line 412, specify a guard's own safe evaluation and checked fallback/branch-refinement contract. A check after invalid arithmetic cannot repair it. Measure retained captures, anchors, inverse workspace and recomputation together before claiming memory or speed benefit. |
| **§§5/8,212–250,437–461: platform/protocol effects** | Resource deletion commutes only under stated equality, ownership, failure-order and scheduling assumptions. Protocol ownership is separate from value matching. | Give one end-to-end example binding source instance, demand, equality/representation and protocol owner. Reject delayed/duplicate consumption, ID reuse and stale target capability. Runtime transport and host assumptions remain visible. E20–E26. |
| **§§9–11,462–669: probabilistic and circuit applications** | Sample occurrence is not distribution equality. Shared recipes and independent redraws can have equal marginals with different joint behavior. Classical circuit descriptions, live quantum resources and measurement/reset have different contracts. | Preserve occurrence identity, independence/correlation and resource interpretation through elaboration. Keep exact matching, metric loss, probabilistic guarantees and coherent uncomputation distinct. Physical amplitude/storage and scheduling premises need their own realization evidence. Do not transfer a result between these interpretations from shared notation alone. |
| **Status across §§1/5/12,39,212–256,672–686** | The work is identified as language design, but present-tense compiler and benefit claims can blur derivations with implemented acceptance. | Add a compact status account: reference-calculus result, local proof, proposed language rule, checked/mechanized instance, implemented path and measured result. Bind the last categories to revisions and gate evidence. Retain design claims as such where evidence is absent. |

These are concrete review recommendations, not findings that the stated propositions are false. Most immediate additions would make assumptions, elaboration and implementation status assessable. A changed theorem or stronger general claim requires the successful experiment or counterexample that justifies it.

## Recommended manuscript changes and their order

**H1:** expand NFT with the finite elaboration/equality/demand fragment and its explicit status table. State the selected unique-label row/qualified scheme interfaces and preserve the distinctions among dimensional equations, value equality and live-instance use. Update DTS+DMM's pending-member discussion for the admitted generalized requirements and PHG's worked examples for the retained dependencies. Give the coexponential paper an explicit finite reconstruction/witness interface, demand and continuation example, and unsupported-boundary account. These design clarifications can be written as commitments before the new theorems exist. Mark theorem statements and implementation coverage accurately.

**H2:** connect NFT's local propositions to Baker-owned inference and revision-bound PSG evidence as the feature gates pass. DTS+DMM should document the implemented generalization and numeric/deferred contract. PHG and the coexponential paper should identify retained invocation/frame identities, multi-party dependencies and measured reuse behavior. The same source scheme can persist while selected representations and boundary evidence change, so cached type syntax alone cannot justify reuse.

Publish the actual combined results rather than inheriting a claim of global principality from a component algorithm.

**H3:** an admitted adapter correspondence could revise NFT's structural scope directly. It must define preserved observations, composition/coherence, variance and resource treatment before claiming a subtype order or replacement for algebraic subtyping. Current `1/v` does not already define a general `B/A` calculus. A complementary relationship is a valid result. Universal replacement is not required. The derivative transpose mentioned in NFT's applications is distinct from Atelier's proposed source-translation feature.

The site articles make this reconciliation concrete. *The Gift of Deferred Inference* separates source schemes, ranges and physical choices. The FPGA article supplies per-output state/input dependencies across a broader target remit. *Carrying Proofs into JavaScript* adds arithmetic, identity, suspension and recovery obligations. These inform H1 experiments and identify premises for proofs of the combined system. Exact article/platform bindings and implementation-status limits are in [chapter 2](02-js-numerics-and-interop.md).

## FFI and differential-compilation implications

Farscape's implemented separation between source numeric spelling and ABI descriptors supplies a useful worked case for all four papers. DTS+DMM can distinguish unchanged source schemes from changed representation/foreign premises. PHG can expose the proof and code dependencies that require different invalidation. NFT's representation proposition can state what preserves selected value equality and distinct live instances at the boundary. The coexponential account must additionally bind the declaration, message, endpoint and waiting invocation through the admitted exchange. Elicited foreign types are premises for this connection, not a derivation of the foreign algorithm's behavior. [Current and historical owner evidence](02-js-numerics-and-interop.md)

A meaningful revision would include a bound example that survives fresh-versus-reused compilation, invalidates a changed ABI or ownership premise, and preserves the admitted marshaling contract in its claimed native artifact. Equal foreign-call arguments must not merge effectful occurrences. Equal pointer bits must not merge successive resource lifetimes. This is where stable inference can reduce unnecessary graph work while still propagating changes that matter. Current Farscape status does not establish that reuse result already.

## What counts as significant?

**A new structural capability.** A principal measured-row scheme, a sound generalized qualified-member relation, a useful subtype fragment, or a checked higher-rank interface may admit programs the present account excludes. State exactly which restriction changes. The current rule is not a reason to reject the proposal, but the change cannot be described as merely a faster implementation.

**A stronger proof account.** Establishing that a class of adapters preserves the required observations and resources could connect NFT with structural compatibility. Establishing lawful transfers between constraint families could advance PHG's combined-analysis account. Neither follows from common notation or separate component proofs.

**A measured implementation result.** Better diagnostics or incremental latency can be valuable without a new type theorem. Report the actual workload and conditions. Mutable unification's speed in a teaching example is not a Clef result, and a source-invariant schedule change need not rewrite the language theory.

The specific “quieter graph” hypothesis belongs here: stable schemes and retained obligations might avoid repeated commitment/retraction and narrow invalidation. H1.7 must compare semantic changes and total edit-to-result cost with full recomputation, while changing hidden range, platform, ABI, equality and resource premises to test dependency completeness. A successful result could strengthen DTS+DMM's differential-compilation account and PHG's reuse discussion. Fewer updates caused by missed dependencies or weaker answers would instead falsify that improvement claim.

**An exposed overclaim.** A counterexample can justify narrowing a claim. For example, one satisfying specialization does not establish principal inference. A final numeric range does not justify every intermediate operation. A shared lazy result does not manufacture resource rights. An unverified suspicion is a research question, not a manuscript correction.

## Claims that must remain separate

The review distinguishes a valid typing derivation, principal inference, completeness relative to annotations, termination, sound approximation, behavioral preservation and performance. A result may establish one and leave the others open.

Tier 1 is broader than dimensional unification, but it remains tied to an admitted interpretation. DBC `decidable-by-construction.md:197–216,440–450` separates structural judgments from discovery/checking and preserves the premises of each procedure. NFT `negative-fractional-types-in-fidelity.md:182–194` retains value indices and permitted resource use. DTS+DMM `426–434` and `fixed-point-scaffolding.md:274–284` qualify parametricity by effects, partiality and demand.

Consequently, a row-parametricity statement must name the actual interpretation and forbidden observations. A type shape does not automatically supply a free theorem for every effectful or resource-sensitive NTU program. A heterogeneous measured union may be intentional data. Its admission is not the same as validating incompatible arithmetic.

## Documentation reconciliation to keep separate

The inquiry found older or inconsistent prose worth checking at its owning document:

- `clef-lang-site@15d381634f7a08c2a44884a0598d0e634083b313`, `hugo/content/docs/design/types/structural-polymorphism.md:15`, describes one unification machinery broadly. A common implementation can orchestrate several theories, but this wording supplies no single-algebra or composed-principality theorem.
- `arxiv-papers`, `research/grade-axis/02-annotation-disciplines-and-the-unification-substrate.md:19–37,79–109`, contains broader historical claims than the current DBC manuscript's scoped account. Do not reintroduce those claims while expanding the theory.
- `clef-lang-spec@a69ac8a91b49f97bd5a5e7bea2934246c2d54edd`, `spec/terms-and-definitions.md:100`, retains a source-seal definition in tension with current numeric/width prose. This is a narrow documentation issue, not evidence for a replacement type theory.
- At the same spec revision, `spec/synchronous-rpc-liveness.md:65–85,132–138` supports automatic admitted cases but also permits priority annotations and unresolved timeout supervision. Reconcile those modes with the selected no-escape language contract: a checked timeout/failure protocol can be useful, but unresolved supervision must not be labeled a deadlock-freedom or progress proof. The supported automatic guarantee is grounded in `arxiv-papers@d2bab3376032929dc7a4eca7e0bc807247a88c03`, `coexponential-exploration.md:280–308,665–676`. Its realization remains proposed at line 934. This is a concrete specification amendment owner, not a claim that all present paths already enforce the new policy.

These observations were recorded without changing the specifications or manuscripts. Reconcile them as explicit document corrections, not as substitute evidence for the research hypotheses.

## Recommended revision discipline

The compiler-verification direction also belongs in the wider manuscript account. Connect program-level judgments to actual artifact correspondence, then state the planned mechanized preservation and bootstrap obligations for a self-hosted compiler. Reusable Rocq/Coq libraries and cvc5 procedures have distinct roles. A tier label does not identify their trusted base. The current Composer proof-composition owner, not a historical pipeline sketch, governs that integration. [Ecosystem and positioning](07-explaining-clefs-position.md)

Record the selected architecture as the design direction now. At each successful horizon gate, attach the exact judgment, theorem or measured result to the relevant paragraph and promote its status accordingly. Retain counterexamples and unsupported cases. Name new source rules before implementation spreads to readers or backends. Label each commitment with its current evidentiary status.

Use the existing compiler owners to establish the result. No new proof should be created opportunistically during publication, passive Alex witnessing or target lowering. Conversely, those ownership constraints do not require preserving every current F#-derived source restriction.

**Document owner and growth reason:** this inquiry owns the manuscript impact assessment. It provides precise revision thresholds without becoming a second authority for the papers' claims.

# JavaScript, numerics and interop

A concrete programming contract gives the inference comparison its purpose. Beancounter's “JavaScript you can count on” chapter asks that amounts remain exact at the application's chosen resolution, collections preserve value semantics, calculations retain their dependencies, and displayed results remain attached to their meaning. JavaScript offers a substantial opportunity because these guarantees cross a host boundary and often depend on generated libraries. The same questions apply to native records, numerical kernels, device interfaces and shared application components. [J1]

**Recommendation:** CCS/Baker settles the source contract, representation and arithmetic construction choices with their proof premises. Composer realizes those settled choices through its JSIR or native path. Measured rows, qualified requirements, NFT uses and deferred numeric obligations form the selected source account. This chapter gives the concrete lowering decisions. The [strategy](04-horizons-and-experiments.md) owns delivery and gates. The proposed JSIR path still needs its implementation evidence.

The first shared implementation case should be a deferred measured computation with a one-shot completion right tracked separately beside its immutable record, outside the indexed data. Its record interface, arithmetic, state transitions and resource identity must agree.

NFT supplies the admitted indexed-use contract. Rows and qualified requirements supply interface abstraction. Numeric and platform procedures supply realization premises. Resource-bearing aggregates follow under an explicit admission rule. Together, these cases test the native design across its semantic boundaries.

## The strongest case for measured rows

A reusable operation often needs only part of a record. Consider a function that divides a record's distance by its duration. A candidate inferred contract can quantify over both the dimensions of those fields and the unmentioned remainder of the record:

```text
{ distance: float<L>; duration: float<T> | remainder } -> float<L/T>
```

This is illustrative type notation, not accepted Clef syntax. The useful property is the joint abstraction: callers can supply different measurement dimensions and additional metadata without inventing a common nominal record. A related record update can preserve the remainder rather than reconstructing every caller's fields.

That supports telemetry adapters, coordinate-bearing records, calibrated sensor readings and application components on native targets as well as JavaScript. The experiment must demonstrate this reuse. Count duplicated adapters, required annotations and retained constraints across several unrelated call sites. Also measure diagnostic quality and incremental rechecking. An attractive inferred signature alone does not establish a worthwhile implementation.

Select unique-label rows where projection, extension and update need explicit field presence and a remaining shape. An operation must retain the field's dimensional scheme. Extension requires absence. Replacement/update is explicit and must preserve the applicable resource/effect contract. This is a better default for Clef's native and JS records than scoped duplicate-label shadowing.

Optional fields and recursive shapes need admitted rules. Record rows, effect rows and member-overload constraints remain distinct judgments even if implementation machinery is shared.

Native realization adds another obligation. A row-polymorphic source function must eventually have a settled layout and calling convention, whether through specialization, admitted dictionary passing or another justified representation. These are candidate elaborations to compare, not reasons to move missing semantics into a backend. CCS/Baker currently owns settlement and publishes the facts Alex consumes. [N1]

## Where checked views and explicit boundaries belong

Some demand for rows is really demand for a smaller interface to a richer value. Use a checked view for that case, and a qualified member requirement when the requirement is an operation rather than a structural field. Algebraic subtyping is a strong alternative for union/intersection-heavy APIs, but making it the global inference regime is unnecessary for these immediate contracts. The recommendation is rows plus qualified requirements, with admitted views where a concrete interface requires them.

The distinction matters at results. Accepting a value with extra fields does not automatically promise to preserve and return those fields. A row-preserving transformation and a function accepting a smaller structural interface have different contracts. Compare them on the same programs, including mutation and higher-order use, before claiming one subsumes the other in the admitted fragment.

An explicit-boundary design is also a serious baseline. The present JavaScript profile maps options bags to generated nominal records, keeps `JsValue` and `JsRef` outside subtyping, and requires total narrowing before a dynamic value enters an ordinary declared type. That can localize substantial complexity while leaving the interior predictable. A closed generated adapter may be preferable when there is little demonstrated structural reuse. [N2]

Its cost is repeated shape declarations and adapters where generic operations would suffice. Add the selected structural abstraction inside the validated language boundary, and relax a particular boundary restriction only through an explicit source rule. Unknown inbound objects still require validation: structural inference cannot establish a future payload, and a field name does not establish the behavior of a getter or proxy. This preserves the useful open-world boundary while improving reuse inside it. [N2, J2]

## Value semantics must survive the inferred contract

Beancounter requires content equality, persistent map/set updates, defined key comparison and ordered traversal. These are observable behaviors. [J1]

The inspected Fickl source dispatches F# Map/Set operations to runtime libraries. Its maps and sets use comparer-directed trees. Updates construct collection values, and folds traverse left/key/right. The local Fable checkout contains the same persistent core. Fickl has additional changes, but this evidence does not attribute the invention of those collection semantics to Fickl. Nor does it show a global replacement of JavaScript's built-ins. [F1–F3]

Fickl's record support first checks constructor compatibility, then compares contents. Preserve nominal records' declared equality and keep the new structural domain explicit. For the selected structural fragment, infer qualified equality/comparison requirements over every field and the complete tail. Compare values at the same admitted instantiated row type, use a stable label order for derived comparison, and require comparison-zero to agree with equality. There is no implicit nominal-to-structural equality conversion.

This supplies a coherent map-key policy without silently changing the inspected runtime's nominal contract. [F4; structural policy is the recommendation]

Persistence likewise needs more than an immutable outer type. A retained scenario must continue to observe its earlier collection contents. Any mutable values reachable through that collection need their own semantics. Temporary mutable lookup tables can still be useful when their effects do not escape the permitted context. Ordered traversal does not establish transaction uniqueness or permit arbitrary reassociation of calculations. [J1]

## Precision is several obligations

Beancounter distinguishes integer minor-unit amounts, currency and exact rational rates. Its documented model deliberately has a finite monetary resolution. Sub-minor-unit accrual needs a richer amount model. Currency compatibility, scale, rounding schedule, intermediate capacity and representation are separate concerns. Treating them all as a choice of numeric width would obscure the actual contract. [J1, J3]

The numeric carrier alone is insufficient. Fickl routes fixed-width integer operations through BigInt machinery and then an unchecked width conversion. Its runtime separately provides checked conversion. Beancounter's refusal of overflow depends on the admitted money operation and its boundary checks. [F5]

A small discriminator makes the distinction clear: half-even rounding of two half-cent results separately gives zero cents after addition. Adding the exact halves before rounding gives one cent. Matching currencies, dimensions and final widths do not justify equating those programs. Similarly, allocating 10,000 cents three ways requires a conservation rule and a remainder policy, rather than three independent approximations. [J1, J3]

Native lowering faces the same issue. Checked range evidence, intended modular arithmetic, fixed-point scale changes and floating-point rounding impose different obligations. Current Clef specifications require intermediate capacity and source-to-operation correspondence, and distinguish an unresolved range from a known lack of coverage. A rival inference strategy should improve the production of such evidence without confusing it with structural type compatibility. [N3]

## Select numeric constructions by the source contract

The strategic JS path should compile settled native arithmetic through Composer's proposed JSIR backend. Keep Fickl/Fable behavior as a concrete application and regression reference for equality, persistence and checked monetary operations. Do not make Fable's host-oriented replacement choices the permanent definition of Clef's native numerics.

The following construction policy sets implementation targets for JSIR. CCS/Baker establishes eligibility and proof premises. Composer realizes the selected operations and helpers. The backend does not infer a missing range or silently weaken precision.

| Source contract | Preferred JS realization | Required eligibility and preservation |
|---|---|---|
| Exact integers within a justified domain | `Number` when every relevant intermediate is exactly representable | Prove the operation-specific range/definedness premises. Exclude accidental 32-bit coercions and preserve observable zero policy. |
| Exact integers beyond that domain | `BigInt` or another admitted exact integer construction | Bind operation semantics and boundary conversions. Do not introduce unchecked fixed-width wrapping merely because a runtime helper offers it. |
| Exact scaled quantities and rational rates | Exact integer-backed scale or numerator/denominator operations until the declared rounding point | Preserve dimension/currency, scale alignment, division preconditions, intermediate capacity and named rounding schedule. |
| Rounded real computation | Binary64 under its declared error/rounding contract. Use an admitted residual/expansion construction when the source contract calls for greater accuracy | Establish construction premises and error propagation. Do not silently rewrite an explicitly ordered rounded computation into a different one. |
| Partition-independent reduction | An admitted exact accumulator with exact merges and deterministic final rounding | Prove capacity, disjoint coverage and multiplicity. Preserve accumulator state through codecs and recovery. A fixed rounded tree provides a narrower guarantee. |
| Foreign or durable boundary | Generated validation and an explicit value-preserving codec | Bind actual values, representation, identity and protocol state. A convenient scalar/JSON encoding must not discard exact information. |

This is better for JavaScript because the compiler can deliver a richer numeric contract using a construction of supported operations. A native type need not collapse to one JavaScript primitive. Conversely, a precision contract that cannot be established under the selected capabilities should produce a located refusal or the explicitly permitted fallback. It should not quietly become ordinary `Number` arithmetic. [J1, J3, J5–J6, N3; construction choices are this guide's recommendation]

Start with exact measured integer/fixed-point calculations and named rounding, then one exact reduction across a suspension boundary. Those cases connect directly to Beancounter's integrity rules and expose both arithmetic and identity failures. Add compensated and broader real constructions after their operation correspondence and error premises are available. This gives JSIR a concrete precision-first delivery sequence.

## Source structure, numeric width and platform quotations

**The Gift of Deferred Inference** makes a stronger point than choosing a wider carrier. A dimensional source scheme can remain stable while justified ranges determine different representations for its uses. Its FPGA example gives a state counter in `[0,399999999]` a 29-bit unsigned representation. Other fields use 17 and 11 bits while the transition interface remains `State × Inputs → State × Outputs`. The widths settle before synthesis and remain fixed during operation.

The article reports integer HelloArty support, while real-valued selection and editor readouts remain its stated implementation horizon. This review has not independently qualified those implementation claims. [D1]

This is the useful sense of separating width from type arity: a field remains one source field even when its physical width changes. Type-constructor arity, function arity, record field count and tensor rank are distinct structural notions. The article does not define them as one quantity called arity. The normative width contract keeps source numeric identity at `int`/`float` and its dimension, and explicitly covers CPU, GPU/NPU and JSIR alongside FPGA. FPGA exposed the opportunity. It does not confine it. [D1, N5]

Candidate inference regimes must therefore preserve several related facts without collapsing them: the structural/dimensional scheme, contextual numeric domain, exactness or error requirement, intermediate capacity, selected representation, and storage/access realization. Two invocations can share a source scheme and have different proven ranges. An admitted shared implementation must cover both. A specialization can use its own premises. A 29-to-30-bit change must not silently change the source scheme, and an unresolved range must not default to a convenient host width. [D1, N3, N5]

Fidelity.Platform often supplies constraints through actual language quotations, as well as records and immutable aliases. Its canonical contract accepts these through typed PSG with declaration provenance. It follows supported declarations rather than executing arbitrary quotation programs. An inspected capability declaration uses `Expr<bool>` and `<@ true @>`. These are compiler inputs with a source identity, not merely passages quoted from a specification.

Source range, pointer width, register width and transaction width remain distinct. A platform change can invalidate representation eligibility without changing the source type. Platform owns the declarations. CCS checks and settles the resulting numeric, layout and access obligations. [P1–P2]

## State-machine reasoning applies across targets

Mealy/Moore reasoning describes a dependency in the computation: a Mealy output may depend on current state and input, while a Moore output depends on state. FPGA makes the physical consequences conspicuous, but the distinction is useful for software state transitions, reactive processing and actor/workflow realizations too. Preserve initial state, transition relations, output dependencies and the declared observation points. A rewrite between the two forms can introduce state or change when an output is observed. Matching record types alone does not prove equivalent behavior. The cross-target experiment must establish the chosen trace correspondence, with timing requirements stated where relevant. [D2; proposed experiment E21]

Width inference adds the numeric side of that transition contract. A counter's reachable range requires initialization, update and guard facts. Its final bound alone does not justify every intermediate operation. A physically sufficient bit width also does not establish DSP count, timing or area. The deferred-inference article illustrates this with a 17×29-bit multiply that does not directly fit one 18×27-bit DSP block. Numeric eligibility and physical mapping require their respective evidence. [D1]

## What “Carrying Proofs into JavaScript” adds

The requested JavaScript article is titled **Carrying Proofs into JavaScript**. Its proposed compiler mechanism derives numerical obligations from the computation, instantiates construction theorems, establishes their premises and preserves the result through lowering. That is a direct test of inference design: can a useful source expression obtain a justified numeric construction without requiring the author to handcraft its proof? The article explicitly distinguishes this direction from completed artifact-bound JSIR evidence. [J5]

For example, integer terms bounded by `B`, with count at most `N` and `N·B ≤ 2^53`, can support exact binary64 summation in any tree of disjoint partial sums, under the article's integer-operation and zero-handling premises. Every subtotal is bounded by the sum of absolute magnitudes. Arbitrary fractional inputs require a different construction: recovering a rounding residual with TwoSum does not give a two-component accumulator unlimited capacity. Fixed-point rescaling, error propagation, exact accumulation and deterministic final rounding each introduce their own conditions. This is richer than inferring a scalar width. [J5]

The same proof must survive an `await`, a message or a durable restart. A stale selection can receive a perfectly well-typed result. An exact sum can still count a retried contribution twice. The article requires input/job identity, disjoint partition coverage, accepted-contribution multiplicity, faithful encoding and a consistent recovery protocol. These are related to types but also involve effects, value identities, state transitions and host assumptions. They should inform the inference/evidence regime rather than being delegated to incidental runtime conventions. [J6]

The recommendation is to test which obligations can be derived structurally, which need admitted arithmetic or transition procedures, which require boundary checks, and which remain explicit host premises. Do not relabel all of them Tier 1 or mistake proof of a generated checker for proof about an unchecked incoming value. Likewise, order independence of a successful result does not establish delivery or termination. These distinctions apply across substrates. The JavaScript article supplies a particularly demanding realization. [J5–J6]

NFT sharpens this test. Preserving numeric range is weaker than preserving the selected equality of a reciprocal's value index, and preserving equal values is weaker than keeping distinct live instances distinct. A lossy conversion cannot justify exact indexed elimination merely because the final number fits. A retry cannot manufacture a second completion right. Conversely, a live resource token alone does not prove atomic durable acceptance or a remote effect protocol. The [NFT manuscript review](05-manuscript-implications.md) states the separate inference, representation and recovery obligations.

## Farscape: elicited foreign types and proof to the marshaled boundary

The FFI work supplies an existing connection to native lowering. Farscape elicits declarations and representation evidence. CCS/Baker settles their source conversions and obligations. Fidelity.PSG carries the resulting facts, which Alex consumes passively. Composer preserves their correspondence in lowering and artifacts. Bozzetto's local documentation changes redirect the standing work to the Farscape wiki. That migration is an observed uncommitted change, distinct from the indexed historical record. [B1, X1]

The source/representation separation is visible in implementation. Farscape's `clefSpelling` maps signed and unsigned integer families to source `int`, while `AbiRepr` separately retains family, bit width, provenance stratum and C spelling. Profiles distinguish `int`, `long` and pointer widths. Its layout probe uses the declaring header, include paths and defines to obtain Clang layout information. The inspected probe is a C translation unit. This evidence does not establish a general C++ object ABI. [X2]

This gives the inference comparison a concrete input: the source type and dimension, foreign declaration and declaring unit, selected ABI, measured layout and dynamic resource instance must remain distinguishable. A C `long` can expose the same source `int` under different ABI widths. A deferred value of `2^40` therefore needs different boundary coverage under LP64 and LLP64. Changing the profile must invalidate the affected proof and lowering facts while preserving the source type. This comparison is proposed work; cross-target acceptance remains to be established.

A physical width supplied by a descriptor is a boundary constraint, not permission to truncate silently. [N3, X2–X3]

The intended proof scope is the admitted marshaled values, storage/access and ownership contracts under explicit foreign hypotheses. It does not establish that an arbitrary C algorithm computes the intended answer. A return check cannot undo an unauthorized write already performed by foreign code. NFT can help express value matching and permitted uses, but applying its initial finite immutable interpretation to opaque `CHandle<T>` values requires an explicit equality, alias/lifetime and resource interpretation. Equal raw addresses, equal source types and equal live-instance identities are different claims. [X1; NFT assessment in chapter 5]

This is also a precise differential-compilation case. The current working agreements distinguish proof dependencies from code dependencies and forbid merging effectful foreign calls merely because arguments are equal. A reusable graph judgment may remain stable while its boundary evidence must change with a descriptor, layout, ownership policy or foreign behavioral hypothesis. “Differential” here includes incremental evidence reuse. A C-versus-Clef execution comparison is a separate control with its own observations. H1.7 measures the validity of reuse as well as the number of changed rows. [X1, B1]

Current evidence must remain scoped. The BoundaryConformance driver describes declaration generation and compiler/public-PSG checks. It explicitly does not execute C/native Clef, validate callback ABI execution or discharge releases. The separately versioned Definition of Done, with status dated October27, reports limited libc-shaped Linux x86-64 native evidence and marks reuse NR/unsettled. Neither is a new gate receipt from this review. Header extraction, native execution, boundary proofs and reuse acceptance are separate evidence categories. [X3–X4]

## Acceptance cases and the evidence each needs

| Case | Required observation and evidence |
|---|---|
| Measured projection and remainder-preserving update | Reuse across several record shapes and dimensions; explicit field, dimension and remainder derivations; settled native/JS realization. |
| Equal keys and persistent scenarios | Equal-content separate values behave as intended. Distinct nominal identities follow the declared rule. Updates preserve prior observations. Check comparer and library correspondence. |
| Rounding, allocation and capacity | Preserve rounding order and allocation conservation. Refuse incompatible currency and inadmissible capacity. Structural derivations do not replace arithmetic evidence. |
| Deferred mutable read | A guard before closure construction cannot justify a later read after mutation unless preservation is established. Retain demand and storage dependencies. |
| Resource-bearing field | Projection, extension and higher-order reuse must not duplicate or discard an ownership obligation merely because the record shape permits it. State the admitted resource fragment. |
| Foreign input and coherent display | Validate incoming shape/value constraints, retain failure paths and context identity, and preserve meaning through codec, library and emitted artifact. |
| Stable source scheme, varying numeric context | Retain the same scheme while proving each invocation's ranges, intermediate capacity and shared or specialized realization. Retain platform quotation provenance. |
| Stateful computation and recoverable reduction | Preserve declared transition/output observations. Accept each logical contribution with the required multiplicity and recover the same represented numeric state. |
| Elicited foreign contract and native boundary | Preserve declaration/translation-unit/ABI provenance, prove admitted conversion and access obligations, retain call/resource identity and state the foreign hypotheses. |

The last case must exceed a convenient oracle. The chapter-linked display check compares rendered amount magnitudes against a set of pushed figures. That is useful scoped evidence. It cannot alone establish correct sign, label, multiplicity or current selection. [J4]

Tier 1 is a useful organization for admitted structural inference, not an automatic proof of decidability, speed or trustworthiness. A procedure must identify its judgment, domain, premises, checking mechanism and unresolved outcomes. Range reasoning, dynamic validation and translation preservation retain their own evidence requirements. The normative conformance contract already permits different proof systems while requiring justified composition and invalidation. [N4]

## Recommendations across the horizons

**H1:** implement the bounded native scheme/NFT/deferred contract, unique-label measured rows and qualified requirements. Use the first JS exact-arithmetic case and Farscape boundary case to prove that those judgments reach a faithful realization. Include contextual ranges, platform changes and state/output dependencies. Measure inference ergonomics and valid differential reuse against the current baseline.

**H2:** integrate the selected contract into existing CCS/Baker owners as each feature gate passes. Expand admitted numeric constructions, resource aggregates and target/library support while preserving lazy-demand evidence and dependency-complete invalidation. The direction is selected. The gates determine supported coverage. [N1, N3–N4]

**H3:** investigate broader admitted-adapter calculi, dimensional/NFT relationships and multiple source languages only as named fragments. The [subtyping/NFT/Transpose chapter](03-subtyping-nft-and-transpose.md) develops those questions. Manuscript implications belong in [chapter 05](05-manuscript-implications.md). Provenance and review limits are collected in [chapter 06](06-evidence-and-review.md).

## Source registry and scope

Indexed evidence used schema → snapshot-pinned `find` → `pgq` → `sources`, with fresh/latest matching generation 71 snapshot `1eaf58131802b85f0789664c072e5cb5d6d8047423b77c2be4390d224fdc6311`. Unindexed repositories below were read directly in their primary checkouts. Source observations and normative claims are distinguished from execution evidence. No tests were run for this chapter.

- **N1:** FidelityFramework/Composer `74493a128a08a5333a9991a8e1dc147b036d4be4`, `docs/NTU_Architecture.md:8–57`.
- **N2:** FidelityFramework/clef-lang-spec `a69ac8a91b49f97bd5a5e7bea2934246c2d54edd`, `spec/javascript-boundary.md:47–89,101–133`.
- **N3:** Same spec revision, `spec/width-inference.md:30–52,91–148`.
- **N4:** Same spec revision, `spec/terms-and-definitions.md:98`; `spec/conformance.md:75–90`.
- **N5:** Same spec revision, `spec/width-inference.md:99–155`, especially the cross-target rows at lines 124–131.
- **D1:** FidelityFramework/clef-lang-site `15d381634f7a08c2a44884a0598d0e634083b313`, `hugo/content/blog/deferred-inference.md:36–44,64–96,132–140,160–198,202–278,300–315`.
- **D2:** Same site revision, `hugo/content/blog/fpga-and-hardware-inference.md:94–104,261–271`; per-output input/state dependency analysis and its broader application.
- **P1:** FidelityFramework/Fidelity.Platform `8452124a5af4fb0d5d289d6f16ab47d23a07ed10`, `docs/CANONICAL_PLATFORM_SPEC.md:9–11,51–71,80–86`.
- **P2:** Same Platform revision, `Environments/Linux/x86_64/Ariel/Capabilities.clef:4–5`.
- **B1:** FidelityFramework/Bozzetto `9e32da285c5a0f73312ea8d0f27deebbf4cdf482`, indexed historical `docs/ffi-correction-compendium.md:21–28,45–60,182–226`; `docs/development.md:123,137–139`. The observed local diff deletes the compendium and redirects standing FFI records to Farscape. It is not part of that indexed revision.
- **X1:** [Farscape FFI Working Agreements](https://forge.spkez.dev/FidelityFramework/Farscape/wiki/FFI-Working-Agreements), separately versioned page commit `053b1b2141b5a9fd243be3ad013551e765dcb460`, lines9–14,31–47.
- **X2:** FidelityFramework/Farscape `053206a98240190b43231f901f3e7f3747c4ec16`, `src/Farscape.Core/TypeMapper.fs:21–75,182–194,231–239`; `src/Farscape.Core/CppParser.fs:1362–1435,1504–1525`. Cite the mapping implementation. Its introductory unsigned-to-`uint` comment is stale.
- **X3:** Same Farscape revision, `tests/BoundaryConformance/README.md:20–62`.
- **X4:** [Farscape Definition of Done](https://forge.spkez.dev/FidelityFramework/Farscape/wiki/Definition-of-Done), page commit `f0625c8e69e7b51d379e175683647d058d57f48a`, lines19–29,37–64. Dated status and requirements, not independently rerun receipts.
- **J1:** beancounter.wiki `e8182de19b8f12797c63f23034c658f01e03abf5`, `22_javascript_substrate.md:7–9,23–51,55–88,104–149`.
- **J2:** FidelityFramework/clef-lang-site `15d381634f7a08c2a44884a0598d0e634083b313`, `hugo/content/docs/design/javascript-targeting/jsir-javascript-as-mlir-backend.md:91–99`.
- **J3:** Same wiki revision, `07_data_model.md:88–113`; `18_budgets_and_forecasting.md:19–24,54–77,829–840`.
- **J4:** beancounter `c5f4d2a4a22180830aa63d4f3b6963d210dc6961`, `src/beancounter-web/scripts/check-amounts.js:1–13,40–59,106–115`.
- **J5:** Same site revision as D1, `hugo/content/blog/carrying-proofs-into-javascript.md:16–56`.
- **J6:** Same article, 58–86,114–126,158–220; proposed preservation requirements and named host premises, not verified host implementations.
- **F1:** Fickl `2a25774b5926800ea718e49e785684c69b1f3c13`, `src/Fable.Transforms/Replacements.fs:2665–2704`.
- **F2:** Same Fickl revision, `src/fable-library-ts/Map.fs:142–154,440–449,734–747,844–862,936–954`; `src/fable-library-ts/Set.fs:148–171,309–318,750–763,881–884`.
- **F3:** Fable `3a21511f47ea7ef87672fc4d49abe3d6d2daf052`, `src/fable-library-ts/Map.fs:731–744,841–859`; `src/fable-library-ts/Set.fs:747–760,878–881`.
- **F4:** Fickl revision above, `src/fable-library-ts/Types.ts:157–195`.
- **F5:** Fickl revision above, `src/Fable.Transforms/Replacements.fs:325–330,592–615`; `src/fable-library-ts/BigInt.ts:133–143`.

Growth justification: this comparative inquiry chapter connects a concrete application remit to candidate inference experiments. Return to the [review index](README.md).

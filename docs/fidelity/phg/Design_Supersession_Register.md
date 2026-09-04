# Design Supersession Register

> Every document in the corpus touched by the settled position — the PSG as the
> sole, exhaustive compilation authority; no DCont, INet, or closure dialect
> above the witness boundary; hyperedges in the graph, not passes beside it —
> classified by what it currently says and what it needs. Inventoried
> 2026-09-04 across clef, Composer, clef-lang-spec, clef-lang-site, and the
> papers.
>
> The finding that matters: **the spec is internally inconsistent.** Its
> newer chapters (`program-hypergraph`, `conformance` §6) already state the
> settled position; three older normative chapters still bind implementations
> to the retired forms. Which chapters get rewritten is a decision about
> authority, and it is yours — but the spec's own newer text has already
> decided it.

## Category (c) — normative text binding the retired form  *(decision required)*

These are not documentation nits. Each is a SHALL that a conforming
implementation would have to violate to follow the design.

### c1 — `clef-lang-spec/spec/dcont-representation.md`

**What it binds.** §2 specifies a *continuation operation surface* —
`cont.new`, `cont.suspend`, `cont.resume`, `cont.alloc/store/load`,
`cont.is_done` — "the way a dialect specifies an abstraction," explicitly
following WAMI's DCont dialect (§References). §9.1: "A delimited continuation
SHALL be expressed by the target-neutral operation surface of §2 … which every
target lowering consumes." §9.5 makes the surface transportable and every
target "a different lowering pass over the same surface." §6 specifies a
`ContStateMachine` node whose state indices are "assigned by a coeffect …
computed during preprocessing" — i.e. in Composer, beside the graph.

**What supersedes it.** `Composer/docs/Delimited_Continuations_Architecture`
§3–§7: the suspension recipe in Baker (segments at `let!` cuts, live-across
sets as frame slots, delimiter as graph structure), fold-in settling state
count / frame layout / placement, five QF verification conditions, and the
witnessed form — "a discriminant, a byte frame with static `memref.view`s,
function values, and `scf.index_switch` … **No continuation dialect, no llvm
dialect, no new op.**" `Thin_Middle_End` §3: "The DCont dialect dissolved."
`program-hypergraph` §5.2: the emission traversal consumes node-local codata or
reified structure, never an operation surface.

**Recommendation.** Rewrite §2 and §9.1/§9.5 to specify the suspension recipe
and its witnessed form. Keep §4 (suspended state: index, in-flight value,
capture set, internal state — that *is* the frame), §7 (cooperative
scheduling), and §9.2–9.4/9.6 with their references repointed. A `cont.*`
vocabulary may legitimately exist **below** the boundary as transliteration
for a stack-switching target (`Thin_Middle_End` §4 names exactly that leg);
what changes is that the front end does not emit it. Verify §6's citations of
PSG chapter §12.5 and §14.3.3 during the rewrite.

### c2 — `backend-lowering-architecture.md` §4.2, §7.5–6; `closure-representation.md` §6.3; site `gaining-closure` §"The Witnessed Form"

**What they bind.** §7.5: "the conversion of a function address to and from
data SHALL be represented as `builtin.unrealized_conversion_cast` and resolved
per target." §7.6: "a target pathway SHALL resolve the `func_type ↔ index` and
`index → memref` closure casts … for the LLVM pathway this resolution SHALL run
after standard dialect conversions and before `--reconcile-unrealized-casts`"
— i.e. the `flat-closure-lowering` plugin is a conformance requirement.
`closure-representation` §6.3 normalizes the packed `(index, index)` pair.
`Gaining Closure` defends the casts as "honest markers of everything left
undecided."

**What supersedes it.** C-01 §14.3: the closure value is "two SSA values
traveling together: the function value and the environment buffer … passed
and returned as ordinary multiple values. **No packing, no casts, no new
dialect.**" `Thin_Middle_End` §3: "the anonymous cast resolved into a named
pair." `mlir-plugins/ROADMAP`: both plugins "interim."

**Recommendation.** §7.5 inverts: the middle end SHALL NOT emit
`unrealized_conversion_cast`; a closure value SHALL be carried as a
function-typed SSA value and a `memref` environment. §7.6 is deleted; §4.2
rewritten to the multi-value form; `closure-representation` §6.3 likewise.
Packing into words is a boundary event under C-01 §6.7 only. `Gaining
Closure` gets a dated addendum. This is `Closure_Retooling_Plan` step 7.

### c3 — `seq-representation.md` §5.2, §6.3–6.4

**What it binds.** §6.3 NORMATIVE: "All nested Sequential nodes MUST be
flattened before splitting at yield" — the `flattenSequentials` /
`splitAtYield` algorithm, which is the two-shape (`Sequential` |
`WhileBased`) recognizer in clef's `Core.fs`. §5.2 specifies MoveNext as an
unstructured CFG: `switch state: [0 → ^s0, 1 → ^s1]`, `br`, `cond_br` — the
`cf` vocabulary the witnessed region excludes.

**What supersedes it.** `Delimited_Continuations` §3–§7: `seq { }` "is the
degenerate case in which every resumption source is the caller's pull"; the
suspension recipe "generalizes the resumption edge and keeps the
representation." Segments at cuts replace pre/post-yield splitting; the
discriminant dispatch is `scf.index_switch`, not `cf.switch`.

**Recommendation.** §6 retired in favour of a pointer to the suspension
recipe with `yield` as the cut; §5.2 restated over `scf.index_switch`. §4
(layout: `{state, current, code_ptr, captures, internal_state}`) stands — it
is the frame, and `Delimited_Continuations` §7 says so.

### c4 — `native-type-mappings.md` §"Computation Expressions as Continuation Capture"

Routes sequential effects to "DCont regime; `ContStateMachine` on the PSG,
[DCont Representation] §6." Follows c1: the pointer moves to the suspension
recipe. The "Parallel pure → Inet regime" row is consistent with the PHG
paper §1.4 (nets as hyperedge structure) and stands.

## Category (b) — stale claims that read as current  *(edits)*

| Where | Claim | Edit |
|---|---|---|
| `Composer/src/MiddleEnd/Alex/Pipeline/MLIRNanopass.fs:1-18, 139-140` | "Future: MLIR → MLIR … → DCont/Inet dialects"; "DCont lowering … Inet lowering" as planned passes | Remove the roadmap; what the file *does* (declaration relocation) gets a one-line honest header. Whether that relocation is a witness concern or a serializer concern is a drift-gate question for `Closure_Retooling_Plan` §7, not settled here. |
| `Composer/docs/WebView_Desktop_Architecture.md:225-226` | table maps async → "DCont dialect", pure → "Inet dialect" | → suspension recipe / net hyperedges; cite `Delimited_Continuations` §7 |
| `Composer/docs/PRDs/C-04-CoreCollections.md` §15 "DCont/INet Dialect Integration" | code comments assigning ops to dialects | retitle "DCont/INet Regimes on the PSG"; same citation |
| `Composer/docs/QuantumCredential/Compilation/C-01-SCF-Parallel-Pattern.md:5, 25-26` | "Full Vision: Custom DCont/Inet dialects with purity-driven selection" | the vision line is superseded; the table's regime split stands as PSG structure |
| `Composer/docs/wasm-targeting/03_build_bundle_and_execution_models.md:25`; `javascript-targeting/README.md:33` | "Alex → WAMI dialects (SsaWasm/Wasm)"; "DCont-via-Coroutines vs DCont-Native" | Alex emits the witnessed vocabulary; a WAMI/stack-switching leg is a **backend** pathway below the boundary (`Thin_Middle_End` §4). Reword the pathway line; the pathway itself stands. |
| `clef/docs/fidelity/ccs-specification.md` §12.6 "Future Direction: DCont/Inet Dialects" | as titled | retitle and repoint |
| site `docs/internals/concepts/coeffects-and-codata.md:602-608` "WebAssembly via WAMI" | "The WAMI backend preserves delimited continuations (dcont) through every stage of compilation" — present tense, as ours | dated note: continuations are settled on the PSG; a stack-switching leg may consume them below the boundary |

## Category (d) — stale since Increment 1  *(edits; my work made these stale)*

| Where | Claim | Edit |
|---|---|---|
| `Composer/docs/PSG_Nanopass_Architecture.md:529-531` roadmap | "Mid-term: hyperedge promotion" | landed for obligations and residence (`Increment_1`); closures next (`Closure_Retooling_Plan`) |
| `Composer/docs/Coeffect_Analysis_Architecture.md` §"The Critical Distinction" | two classes: enrichment creates nodes; coeffect analysis computes metadata | add the third: **F-enrichment** creates hyperedges — changes neither node set nor metadata. `Obligation_Residency` §3's "from analysis to enrichment" is this crossing. |
| `Composer/docs/CCS_Architecture.md:191-198, 220-232` | coeffect table and layer table say CCS computes SSA, captures, lifetime, emission strategy, escape | **the design is right and the code lags** (`Witness_Boundary_Audit` §1: none of the 14 `TransferCoeffects` come from CCS). Add a status line pointing at the plan's *Draining Alex* inventory, and add what CCS *does* compute now: obligations, platform resolution, residence. |
| `clef-lang-spec/spec/program-hypergraph.md` §6 Domain Instances | rows for grade, co-location, mesh, wait-for, quire | add rows: **obligation hyperedges** (QF_LIA/QF_BV; owning treatment C-01 §14.5 / `Obligation_Residency`), **residence** (declared platform → value; BAREWire docs/11), **closure environment** (C-01 §14). Informative table, but the spec should locate what is built. |

## Category (a) — already record the supersession  *(no action)*

`Thin_Middle_End` §3; `Delimited_Continuations` §2 ("The Op Rendering, Two
Exhibits" — retired); `Single_Flattening` §4 (and §38/§61, which place net
vocabulary *below* the boundary for CGRA-class targets — correct);
`Negative_Fractional_Types` §5; PHG paper §1.4 ("dialect-level encodings of
either regime stand as prior art"); DTS/DMM §6.7. Spec:
`program-hypergraph.md` — **matches what Increment 1 built** ($(V, F, α, β)$,
enumerated sources, joint firing, transport with two carriers);
`conformance.md` §6 — the preservation obligation already requires that every
artifact fact "trace to a declared origin: the source program, a requirement
of this specification, or the platform declaration for the selected target,"
which is the `1024L` case stated as a conformance rule before the code caught
up. Site: `dcont-inet-duality:229-233`, `delimited-continuations:144`,
`the-continuation-preservation-paradox:96`,
`coroutine-versus-stack-switching:90-92` — each records that the dialect
framing was earlier and was elevated to the graph.

## Category (e) — external references  *(no action)*

Blog posts citing CMU's DCont dialect and Coll's Inet dialect as research
context (`abstract-machine-model-paradox`, `flight-qualified-bytecode`,
`doubling-down-dmm-dts`). Accurate as history.

## Order

c2 lands with `Closure_Retooling_Plan` step 7. c1, c3, c4 land together when
the suspension recipe is built — they are one rewrite in three chapters, and
writing them before the recipe exists would be the same error as the
`cont.*` surface was. (b) and (d) are independent of any code and can land
now.

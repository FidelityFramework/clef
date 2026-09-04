# Design Supersession Register

> Every document in the corpus touched by the settled position — the PSG as the
> sole, exhaustive compilation authority; no DCont, INet, or closure dialect
> above the witness boundary; hyperedges in the graph, not passes beside it;
> a closure as two SSA values, never a cast — classified by what it said and
> what was done. Inventoried 2026-09-04 across clef, Composer, clef-lang-spec,
> clef-lang-site, ship-of-theseus, and the papers; **executed 2026-09-04**.
>
> The register is enforced by [`drift-gate.sh`](./drift-gate.sh): the retired
> vocabulary below is a lint failure anywhere in the corpus unless the line
> marks it as superseded, the file is one of the superseding designs, or the
> file is on the *scheduled* list (code whose replacement is a
> `Closure_Retooling_Plan` deliverable, reported but not failing, removed from
> the list as each lands).

## The settled position, in one table

| Concern | Retired form | Settled form | Where settled |
|---|---|---|---|
| Delimited continuations | a `cont.*` / `dcont.*` op surface; a DCont dialect; `ContStateMachine` as a Composer coeffect | the suspension recipe: segments at cuts, a frame (environment node, state-machine slot class), a delimiter edge per cut; witnessed as a discriminant, byte frame, `scf.index_switch` | spec `dcont-representation.md` §2, §5, §6, §9; `Delimited_Continuations_Architecture.md` |
| Interaction nets | an Inet dialect | hyperedge rule structure over enumerated source sets; witnessed as data flow | `program-hypergraph.md`; `Single_Flattening_Design.md` §4 |
| Closures | `memref<2xindex>` index pair + `builtin.unrealized_conversion_cast`, resolved by the `resolve-closure-casts` plugin; a `code_ptr` word inside the environment | the pair `(fn, env)` — `func.constant` + `memref` — never packed, never cast, no function address stored as data; pathways consume it with standard lowerings | spec `closure-representation.md` §2.1, §6.3, §10.1; `backend-lowering-architecture.md` §2.2, §4, §7.1, §7.5; C-01 §14.3 |
| Lazy and seq | `{computed, value, code_ptr, …}` / `{state, current, code_ptr, …}` with the thunk / MoveNext address at slot `[2]` | `(thunk, {computed, value, captures})` and `(moveNext, {state, current, captures, internal})`; captures begin at `[2]` | spec `lazy-representation.md` §3, §4, §8, §11; `seq-representation.md` §4, §5, §8 |
| Seq state machine | `flattenSequentials` / `splitAtYield` two-shape recognizer; `cf.switch`/`br` MoveNext; `WhileBasedMoveNextInfo` | segments at `yield` by the suspension recipe; `scf.index_switch` | `seq-representation.md` §5.2, §6 |
| Witnessed vocabulary | `func, cf, scf, arith, memref, index, builtin` | `func, scf, arith, memref, index` — five, no other; `cf.*` is produced by the pathway's `scf` lowering; admission of a further dialect is a change to the table first | `backend-lowering-architecture.md` §2.1, §7.1 |
| Stack switching / WAMI | "Alex → WAMI dialects"; "DCont-via-Coroutines vs DCont-Native strategies" | two backend realizations of one witnessed form: the state machine as written, or a backend leg transliterating frame + discriminant into the proposal's `cont.*` instructions | `dcont-representation.md` §5.2; `wasm-targeting/README.md` Axis 2 |

## Category (c) — normative text that bound the retired form  *(rewritten)*

| Chapter | What it bound | Done |
|---|---|---|
| `dcont-representation.md` | §2 op surface; §9.1/§9.5 "SHALL be expressed by the target-neutral operation surface"; §6 `ContStateMachine` coeffect | full rewrite; §4 (suspended state) and §7 (cooperative scheduling) kept and repointed; WAMI moved to prior art in References |
| `backend-lowering-architecture.md` | §2.2 "no portable representation" for a function address; §4 deferred resolution; §7.1 dialect list with `cf`/`builtin`; §7.5 cast SHALL; §7.6 plugin SHALL | §2.1 table trimmed to five dialects with an admission rule; §2.2, §4 rewritten to the multi-value form; §7.5 inverted (SHALL NOT), §7.6 deleted, renumbered |
| `closure-representation.md` | §2.1 `code_ptr` at `[0]`; §6.1–6.3 struct-pointer convention and index-pair encoding; §9 layout in Alex | §2.1 pair form; §4, §5, §6, §8, §9, §10.1 repointed |
| `lazy-representation.md` | `code_ptr` at `[2]`; §4.2 and §8 casts; captures at `[3]` | pair form throughout; size formula and worked bytes recomputed; §7 marked interim |
| `seq-representation.md` | §4.1 `code_ptr`; §5.2 `cf` CFG; §6.3 flattening NORMATIVE; §7–8 recognizer data structures | §4 pair form; §5.2 `scf.index_switch`; §6–8 replaced by "Segments at Yield"; renumbered; mis-numbered §4 subsections fixed |
| `native-type-mappings.md` | DCont row → `ContStateMachine` | repointed to the recipe |
| `ntu-types.md` §8.1, `ffi-boundary.md` §3.2 | `NTUfnptr → index` via cast; extern symbol address as cast | function value is a `func` value; extern symbol is `func.constant` on the declaration |
| `program-hypergraph.md` §6 | no rows for what Increment 1 built | rows added: obligation residence, platform residence, closure/continuation environment |
| `seq-operations-representation.md` | wrapper layouts with `code_ptr` at `[2]`; `llvm.*` listings presented for the creation and invocation forms | pair form; `code_ptr` rows removed and reindexed; §5.1/§5.3 listings rewritten over `memref`/`func` (known-callee direct call; the function-value-parameter case named as the retooling plan's open placement decision); §6.1, §9.1, §10.3–4 repointed |
| `expressions.md` lazy note; `platform-bindings.md`, `incremental-computation.md` dialect lists | struct-pointer thunk convention; seven-dialect list with `cf`/`builtin` | pair form; five dialects |

## Category (b) — stale claims that read as current  *(edited)*

`MLIRNanopass.fs` header and `applyPasses` docblock; `WebView_Desktop_Architecture.md` regime table; `C-04-CoreCollections.md` §15; `QuantumCredential/…/C-01-SCF-Parallel-Pattern.md` (banner; "Custom Dialect Requirements" and Phases 3–5 replaced by retirement notes; "defers" table repointed; decision record kept as history); `wasm-targeting/README.md` Axis 2 rewritten and five further lines; `wasm-targeting/03` two paragraphs; `javascript-targeting/README.md`; clef `ccs-specification.md` §12.6 retitled "Suspension and Nets on the PSG"; `Partial_Application_Closure_Reification.md` pair line; `PRDs/C-07-SeqOperations.md` inventory line marked interim; ship-of-theseus `scaffold/qa-preparation.md` rehearsed answer re-voiced ("prior art I learned from, not a dependency" — **review the voice**); site `coeffects-and-codata.md` WAMI section, `gaining-closure.md` §"The Witnessed Form" and LLVM realization rewritten to the pair form, `dcont-inet-duality.md` and `delimited-continuations.md` supersession sentences marked; blog `abstract-machine-model-paradox.md` (dated 2025-09-05) given an editor's note and three "prior art" qualifiers rather than a rewrite — **review**.

## Category (d) — stale since Increment 1  *(edited)*

`PSG_Nanopass_Architecture.md` roadmap (hyperedges landed; closures next; suspension/nets mid-term); `Coeffect_Analysis_Architecture.md` (third class: hyperedge enrichment over $F$; yield-state row marked interim); `CCS_Architecture.md` (three rows added; honest status line on which coeffects CCS computes today; layer table).

## Sample applications are corpus

Sample applications that "express" a capability (Composer `samples/`, the FidelityHello set, HelloProof and the rest of ship-of-theseus) are swept by the gate on the same terms as the spec. A sample that teaches the retired shape — a cast-plugin closure path, a two-shape seq, a doc line promising a dialect — is revised, not preserved as an exhibit. Sample intermediates and expectations that pin the cast form are on the scheduled list and move with the witness.

## Waypoint — interaction-net annihilation

Held as a bearing while the resumption-edge class and the RPC wait-for edge are designed, not as work scheduled now. Annihilation is the one rewrite in the Baker inventory that *removes* structure, and the hypergraph's second invariant (monotone saturation) admits no deletion. So it must be grounded as a fold-in consequence: the active pair's hyperedge fires on its complete two-member source set, both agents move to *Latent* under the DTS/DMM three-state model, and the auxiliary ports are connected pairwise as new edges. Nothing is deleted; the graph is monotone in annotation and the reduced structure is the consequence. This is the same $|S_f| = 2$ pairing shape the η/ε twin and the synchronous-RPC wait-for edge use — one pairing mechanism, three instances — which is why the continuation design should be checked against it as it comes together. Lessons from the retired dialects are measured in this frame only.

## Category (a) — already record the supersession  *(allow-listed in the gate)*

`Thin_Middle_End_Design.md`, `Delimited_Continuations_Architecture.md`, `Single_Flattening_Design.md` — the superseding designs, which quote the retired vocabulary in order to retire it and define the one place it survives (below the boundary, as transliteration). `Witness_Boundary_Audit.md`, this register, and the plans beside it.

## Category (e) — external references  *(no action)*

Papers and posts citing CMU's and Coll's dialects as research context: PHG paper §1.4, `flight-qualified-bytecode`, `doubling-down-dmm-dts`. Accurate as history; the gate's marker rule ("prior art") admits them.

## The pointer crutch — `nativeptr`, `code_ptr`, `!fidelity.*`

Raised as the same drift seen from the language surface: `FSharp.NativeInterop`'s `nativeptr` was the early crutch that made three retired forms easy to write — the environment reached through a raw address (`ptr<Lazy<T>>` struct-pointer passing), the code reached as address-as-data (`code_ptr` in the environment), and by-reference captures typed `ptr<T>`. The spec already holds the position (`ffi-boundary.md` §1: interior Clef has no raw pointer type; `Ptr<'T, 'Region, 'Access>` is the interior handle, `CHandle<'T>` the boundary handle; commit 8768e536e strips the surface, `TNativePtr` compiler-internal). This changeset carries it through:

- **Spec**: by-reference captures are `memref<1xT>` views (closure-rep §2.2); thunks and `MoveNext` receive their environment (lazy §4, seq §5); `NTUfnptr` is a `func` value (`ntu-types` §8.1); extern symbols are `func.constant` (`ffi-boundary` §3.2); the `!fidelity.*` MLIR columns in `native-type-universe` and `native-type-mappings` — the residue of an abandoned custom type dialect — map to the standard forms the representation chapters fix (`memref<?xi8>` strings, `memref<Exi8>` records/unions/options, `index` links, `(fn, env)` closures, `(A) -> B` functions).
- **Design docs** (clef, Composer, site): buffer parameters are the bounded stack array `platform-bindings` §57 prescribes; `stackalloc<T> n`; `Ptr.ofAddress` for declared peripheral regions; `CHandle<'T>` in extern declarations; the feature audit's `NativePtr.*` rows marked stripped with their replacements; the "strings are fat pointers" claim corrected (a string *is* a `memref<?xi8>`); the `async.func`/`!fidelity.*` and "hypothetical seq dialect" sketches replaced by the witnessed form.
- **Bannered, reported-not-failing**: implementation PRDs (surface note); Farscape's generated-code sketches (move with the generator); dated blog posts (editor's note); the inherited F# compiler test corpus under `clef/tests/`; BAREWire's .NET-side docs (NativeInterop is legitimate there).
- **Found, not fixed here** (design decision needed): `map-representation.md` §"Empty" and `set-representation.md` §"Empty" represent the empty collection as a **null pointer** (`Map.empty = null : ptr<Map>`; `isEmpty` is a null check). That contradicts null-free by construction (closure-rep §10.4, expressions). The principled forms are a tag in the node (the DU chapter's shape) or a static sentinel node in `Flash`; either is a representation change to those two chapters. The `ptr<…>` notation in the list/map/set layout boxes denotes `NTUptr` links (→ `index`), not the stripped surface, and stands.

## Scheduled (code; reported, not failing)

| Site | Replacement | Plan step |
|---|---|---|
| `clef/src/Compiler/PSGSaturation/SemanticGraph/Core.fs` (SeqSaturation recognizer) | suspension recipe in Baker | Phase 3 |
| `Composer/src/MiddleEnd/PSGElaboration/YieldStateIndices.fs` | retired with the recognizer | Phase 3 |
| `Composer/src/MiddleEnd/PSGElaboration/` (`ClosureLayout`, closure-pair coeffects) | closure hyperedge in CCS | Closure_Retooling steps 1–3 |
| `Composer/src/MiddleEnd/Alex/` (cast sites, `memref<2xindex>`) | witness rewrite | steps 4–5 |
| `Composer/src/BackEnd/LLVM/Lowering.fs`, `mlir-plugins/` | plugin removal | step 5 |
| `Composer/tests/`, `Composer/samples/` expectations pinning the cast form | move with the witness | step 5 |
| `Composer/docs/PRDs/` (`code_ptr`, `nativeptr` rows only; bannered) | move with the code | steps 1–5 |
| `clef/src/Compiler/` (`nativeptr` only; `TNativePtr` internal) | confirm `NativePtr.*` intrinsic recognition is gone | — |
| `clef/tests/` (`nativeptr` only; inherited F# test corpus) | retire with those tests | — |
| `BAREWire/docs/`, site `blog/`, site `internals/farscape/` (`nativeptr` only) | legitimate / noted / moves with Farscape | — |

## Also rewritten (design docs and site, on the `code_ptr` sweep)

`Closure_Nanopass_Architecture.md` §3 (pair form; interim indices noted), `Alex_Architecture_Overview.md` lazy sketch, `Partial_Application_Closure_Reification.md` (two lines), `PH2-04-Bootstrap-Options.md` ISR wording, clef `Layout_As_Joint_Constraint.md` prefix shapes (`CodePtr` case removed); site `why-lazy-is-hard.md`, `seqing-simplicity.md`, `gaining-closure.md` diagrams and tables.

## Open

- `closure-representation.md` §2.1's consequence — no `code_ptr` word in any environment — was drawn from C-01 §14.3 (a closure value is two SSA values, no packing) and closure-rep §7 (a seq/lazy value is a flat closure first). It changes the lazy and seq layouts and their normative field indices. If you want the environment to carry a code component for memory-resident closures, that is `Closure_Retooling_Plan`'s open decision and the chapters revert on that point only.

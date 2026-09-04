# Clef PSG → PHG: The Program Hypergraph as the CCS Front End

## Context

Every design document in the corpus assumes a graph whose relations are first-class values. Clef's PSG has none.

- `program-hypergraph-paper.md` §2.1 defines $\mathrm{PHG} = (V, F, \alpha, \beta)$ and proves the PSG is the degenerate case where every $|S_f| = 1$.
- `dts-dmm-paper.md` §4.3 annotates *edges* with a per-target reachability bitvector; §4.4 puts transfer analysis "on the transfer edge"; §6.8 requires obligations established at design time and re-checked at the lowering seam **on one graph**, "without the potential loss of integrity that might surface when engaging a disconnected checker."
- `Obligation_Residency_Design.md` §3 requires obligation nodes with "dependency edges to the structures it constrains," and twin pairing as "a pairing hyperedge."
- `Delimited_Continuations_Architecture.md` §5: "every suspension point carries an **edge** to its delimiter by construction."
- `Single_Flattening_Design.md` §4: "Baker gains significant structure. The recipes carry the semantic inventory: closures, suspension, dual pairs, and **nets**."

Instead of $F$, the PSG has **four parallel ad-hoc encodings of relation**, none of which is a relation:

1. `NodeId` fields buried positionally inside `SemanticKind` payloads (58 cases)
2. `Children` / `Parent` lists on `SemanticNode`
3. Four hardcoded accessors unioned transiently inside `Reachability.computeReachable:282`
4. `EnrichmentId` — a shared metadata integer grouping nodes minted by one recipe firing: a source set with no index

Keeping (1)–(3) consistent costs **~316 lines of hand-maintained triplicate**: `Builder.extractImpliedChildren` (65), `Reachability.getSemanticReferences` (136), `FoldIn.updateKindRefs` (115) — three case-per-`SemanticKind` matches re-deriving the same relation in three directions. `Builder.fs:17-21` states the reason plainly: any NodeId in a `SemanticKind` "must be reachable via children for traversal algorithms to work."

Everything downstream follows from that single absence, and each consequence is independently on the record:

| Consequence | Evidence |
|---|---|
| Obligations cannot be graph citizens | HelloProof's `Prover.fsx` authored 18 obligations from the artifact — §6.8's "disconnected checker." Verdict went from false green to honest FAIL. |
| Memory layout cannot be cross-applied | `Description.clef` declares `consoleReadln`'s capacity; `PlatformPatterns.fs:305,313` still authors `1024L` |
| Delimited continuations are not elaborated | `SeqSaturation.fs` is a two-shape *recognizer*; the machine is built in Composer's `YieldStateIndices.fs` |
| Alex computes what it should observe | `LambdaWitness.fs:324,327` computes byte offsets with `// Approximate` comments; mints SSAs as `V (10000 + tempIdx)` at :617 |
| 4 of 13 Tier 2 families are blocked | Callsheet families 8–11, all on one enabling item: *"the closure reckoning: … `ClosureLayout`/`DULayout` heap sequences **into graph structure**"* |

**Intended outcome.** CCS produces a fully saturated PHG in which everything semantic is settled. Composer triggers CCS and consumes the result; Alex's sole remaining role is witnessing settled structure into flat MLIR generic ops from common dialects. The joint constraints of memory layout and the Tier 1/Tier 2 proofs are not built separately — they *fall out* of the structure, dispatched once at design time from the PHG and again after witnessing to re-check the MLIR, both to cvc5.

Reaching that state is substantial work in **both** directions: building $F$ in clef, and moving what Alex currently computes back into Baker and the graph. The second is not cleanup after the fact — it is the same work seen from the other end, and it is inventoried under *Draining Alex* below.

---

# Part I — The PHG writ large

## I.1 The structure

$$\mathrm{PHG} = (V, F, \alpha, \beta)$$

$V$ is the node set. $F$ is a set of hyperedges $f = (S_f, t_f, \lambda_f)$ with $S_f \subseteq V$ a **source set**, $t_f$ a target, $\lambda_f$ the annotation. $\alpha$ annotates nodes; $\beta$ annotates hyperedges. A binary edge is $|S_f| = 1$, so **every valid PSG is already a valid PHG** — the generalization is an embedding, not a replacement.

## I.2 The four integrity invariants

These are the load-bearing constraint, not quality goals. The graph's *construction* must be the proof structure the program is witnessed from.

**I1 — Enumerated source sets.** Every $S_f$ is finite and fixed at elaboration. This is what keeps obligations quantifier-free. DTS/DMM §3.2.1 and `Closure_Nanopass_Architecture.md:59-74` both name the case that matters: *"The flat closure is … the **finiteness lemma** of the memory discipline."* Because the capture set is enumerated, a closure's reachability frontier is exactly its field list, its extent a literal, its release a single site. A linked environment forfeits this — reachability becomes unbounded, obligations leave QF, and discharge becomes interactive proof. **Any hyperedge whose source set cannot be enumerated at elaboration is rejected by construction.**

**I2 — Monotone saturation.** Annotation only accrues, over $\{\mathrm{Fresh} < \mathrm{Elaborated} < \mathrm{Saturated}\}$. A hyperedge rule fires only when **all** $v \in S_f$ are Saturated (PHG §2.3), never on partial observation. Termination follows by the standard fixpoint argument over a finite lattice. Callsheet family 13 fixes the boundary: schema lemmas are **per recipe shape, never a per-program fixpoint** — the decidable-by-construction line.

**I3 — One structure, two readings.** The layout is the hyperedge's consequence on $\alpha$; the proof is its discharge over $F$. Deciding a placement and proving it sound are the same act at saturation. No fact that bears on observable behavior may be authored below the graph.

**I4 — The transport rule.** (PHG §2.4) A hyperedge participates in saturation and discharge and is **never** a query target for the emission traversal. Its consequence reaches Alex only as (a) saturated annotations on the nodes it governs, read as codata, or (b) a reified attribute set on emitted ops. *This is what makes the whole change tractable: adding $F$ does not perturb the emission walk at all.*

## I.3 The two dispatches

One hyperedge set, read twice, against the same anchor names:

1. **Design time, from the PHG.** Saturation closes $F$; each obligation hyperedge emits SMT-LIB2; cvc5 discharges. Continuous, in Lattice, as source is edited.
2. **Build time, from the witnessed MLIR.** Alex emits; the same obligations are re-derived from the artifact and re-dispatched to cvc5 to show the MLIR graph is valid.

Twin pairing is itself a hyperedge with $|S_f| = 2$ — one design-time provenance, one build-time — and it fires under I2 exactly when both are present. An unpaired *observable* obligation at the saturation boundary is a design-time error, structurally identical to an η site without its ε. **A leak is detected by the same mechanism that discharges the proof**, which is the whole point of I3.

## I.4 What Baker carries

`Single_Flattening_Design.md` §4 names the inventory: **closures, suspension, dual pairs, and nets.** All four are hyperedge families over enumerated source sets, and all four are the same mechanism:

| Family | $S_f$ | $\lambda_f$ carries | VCs |
|---|---|---|---|
| **Closures** | captured bindings ∪ {lambda} | C-01 §14 form (7 forms, selected by a condition decidable at saturation) | VC-EXT, VC-DIS, VC-REG, VC-REL, VC-APP |
| **Suspension** (DCont) | live-across set per segment ∪ {delimiter} | state count, frame layout by interference coloring, placement | VC-EXT, VC-STATE, VC-ACC, VC-DOM, VC-ONE |
| **Dual pairs** | {η site, ε site} | pairing | boundary saturation check |
| **Nets** (INet) | the $k$-ary active set | rewrite rule, grade/arity constraint | per-rule |

DCont and INet are the two halves of the duality (PHG §1.4): the delimited-continuation structure resides as a **saturated aggregate**, the interaction-net rule system as **hyperedge structure**. Both must be fully elaborated in the PHG — nothing about a computation expression, an `async`, or a net reduction may be synthesized in the middle end.

The witnessed form for all of them is already standard: C-01 §14.3 demonstrates every interior closure form in `func` + `memref` + `arith` over a 1-D i8 buffer, concluding *"the standard dialect already contains the elaborated form; nothing needs to be invented."* DCont §7 adds only `scf.index_switch` over a discriminant.

## I.5 Where memory layout and the proofs fall out

They are not separate work. Once $F$ exists with the lattice and the inventory families are elaborated:

- A **layout** is a hyperedge annotation projected onto $\alpha$ (I4a) — offsets on the nodes.
- A **proof** is the same hyperedge discharged over $F$ (I3).
- A **platform declaration** cross-applied with the code regions it governs is a hyperedge whose source set spans the declaration node and the governed sites — the generalization of `PlatformPinResolution`, which already does exactly this at $|S_f| = 1$ for FPGA pins, under the banner *"Two observers, one truth, two residuals"* (`Coeffects.fs:230`).

`layout_user_strings` is the canonical instance: $S_f$ = five string-literal nodes, $t_f$ = the rodata space, $\lambda_f$ = consecutive placement from a symbolic base — which *is* the layout and *is* the proposition (pairwise disjointness over ten pairs, exact span 31). Arity 5, irreducible: a clique of pairwise constraints does not entail the span.

---

# Part II — Verified state of the code

Measured, not inferred.

| Element | Present | Evidence |
|---|---|---|
| $V$ | yes | `SemanticGraph.Nodes: Map<NodeId, SemanticNode>` |
| $\alpha$ | partial | `Type`, `ArenaAffinity`, `LayoutHint`, `Metadata`; $\delta$/$\kappa$ ride inside `NativeType` |
| $F$, $\beta$ | **no** | no edge type, no `EdgeKind`, no `EdgeId` anywhere in `src/` |
| Saturation lattice | **no** | "lattice" appears **zero** times in the repository |
| Fixpoint saturation | **no** | only iterate-to-convergence in the compiler is `Monomorphization.fs:233` (`rounds < 8`) |
| Three-state node model | **no** | only `IsReachable: bool` |
| Per-target reachability bitvector | **no** | single boolean, on the node, not the edge |
| Obligation node/edge kind | **no** | absent from `SemanticKind` and from `src/Compiler/Baker/` |

**Saturation is a misnomer today.** The word is overloaded four ways; only `Applications.fs:269` uses it in the standard PLT sense. `BakerSaturation` is a *one-shot* fan-out/fold-in over a hardcoded decomposition table (`shouldDecomposeIntrinsic`, `BakerSaturation.fs:69-137`), run exactly once. **A saturation opportunity introduced by a recipe is never revisited** — so recipes must emit fully-primitive structure in a single firing. That constraint is survivable for collection HOFs and fatal for DCont/INet, which need multi-round elaboration.

**Edge labels already exist and are thrown away.** `Traversal.RegionKind` (`Traversal.fs:16-33`) names exactly what an edge label carries — `GuardRegion`, `BodyRegion`, `ThenRegion`, `ElseRegion`, `MatchCaseRegion of index`, `LambdaBodyRegion` — but is passed to a callback and discarded. It is never stored.

**The reachability paradox is a symptom.** `FoldIn.fs:245-253` documents removing mid-pipeline validation because two competing definitions of "reachable" disagreed (151 vs 30 nodes). The resolution — "trust recipe creation, validate once at end" — is precisely what a real lattice formulation replaces.

**Closures are half-settled.** Captures *are* computed in CCS (`Applications.computeCaptures:561`, ordering fixed alphabetically by `Set.toList`), per `Closure_Nanopass_Architecture.md:23`: "Capture analysis is NOT a Composer nanopass." But `ClosureLayout` is built in **Composer** (`SSAAssignment.fs:202-320`), and `LambdaWitness.fs` then:

- computes byte offsets itself (`:548`, `:632`), with two `// Approximate` comments on load-bearing prefix offsets (`:324`, `:327`)
- re-derives the extraction SSA schedule (`:328-362`), duplicating `captureExtractionWorkSSACount`
- mints SSAs at emission: `V (10000 + tempIdx)` (`:617`)
- snapshots the accumulator because it distrusts the coeffect's SSAs (`:295-307`)
- repurposes ~7 vestigial `ClosureLayout` fields as scratch SSAs
- never calls `pFlatClosure`, which is dead on this path

`Partial_Application_Closure_Reification.md` §4.2 names this class by name: *"violates photographer principle."*

**The witness boundary is half-held, and the graph is why.** The doctrine is unambiguous — `CCS_Architecture.md:204-205`: *"The Zipper traversal in Alex is **purely navigational** … **It does not compute, infer, or decide.**"* Against that:

- **None of the 14 `TransferCoeffects` fields come from CCS.** All are computed in `Composer/src/MiddleEnd/PSGElaboration/*`. What Alex receives *from Clef* is `SemanticGraph` + `SemanticNode` and nothing else — contradicting `CCS_Architecture.md:191-198`, whose table claims CCS computes SSA, captures, lifetime, and emission strategy.
- **`LayoutHint`, `ArenaAffinity`, and `SRTPResolution` have zero references in Alex.** The three channels the PSG carries for exactly this purpose are ignored.
- **Three mutually inconsistent size models run in the same compilation.** `mlirTypeSize` (`Dialects/Core/Types.fs:59`, memref = 40, arch-blind), `mlirTypeSizeForArch` (`TypeMapping.fs:55`, 5 × word), and `computeSize` (`TypeSizing.fs:27`, memref = 32, **dead code with zero callers**). Record layouts use the first; closure layouts use the second.
- **A live layout bug follows directly.** `TypeMapping.fs:387` synthesizes DU payload size as `casePayloadTypes |> List.choose id |> List.tryHead` — *first* case, not largest — under-sizing any union whose first payload case is not its biggest. Its own comment admits the cause: "proper size comparison would need layout info." `:244` in the same file uses `max` for `Result`, so the two paths disagree.
- **The dialect bound is exceeded.** Beyond the five documented (`func, memref, arith, scf, index`): `builtin.unrealized_conversion_cast` (6 sites — `Thin_Middle_End_Design.md:32` claims this "resolved into the named materialize and scatter pair"; it did not), CIRCT `hw`/`comb`/`seq` emitted *at* the witness rather than below it, `smt`, and raw `aie`/`aiex` text via `MLIROp.RawMLIR` bypassing the typed op representation entirely.
- **"Flat generic ops" is true of neither half today.** The op stream is nested (`FuncDef` carries a body list; `TransferTypes.fs:423` needs a recursive `countOperations`), and the serializer emits custom assembly form, not generic form.

**The mechanical cause is named in Composer's own roadmap.** `PSG_Nanopass_Architecture.md:425-536` already describes the PSG→PHG evolution and hyperedge promotion — and places it at "Mid-term." Layout sits in Alex because *the graph does not yet carry it.* This plan is that roadmap entry.

**The model citizen exists.** `Traversal/XDCTransfer.fs` is 72 lines, pure `PlatformPinMapping → string`, with the posture in its header: *"The coeffect IS the pre-computed data. This transfer is serialization."* Every transfer should look like this one.

**Dead weight** *(removed, `65fa9407d`)*. `src/Compiler/TypedTree/` was 32,290 lines of inherited F# compiler machinery (`TcGlobals`, `TypeProviders`, `QuotationPickler`, `tainted.fs`) across 38 `fsproj` entries, whose only two consumers — `Driver/XmlDocFileWriter.fs`, `Utilities/TypeHashing.fs` — were themselves referenced by nothing. The PSG path never touched it.

**One dead field.** Nothing in clef ever reads `graph.SeqSaturation.Value`; the consumer is out of tree.

---

# Part III — The pathway

## Track A — cut the F# TypedTree  *(LANDED)*

Removed `src/Compiler/TypedTree/` (21 files, 32,290 lines) and its two dead
consumers, `Driver/XmlDocFileWriter.{fs,fsi}` and `Utilities/TypeHashing.fs`.
Committed as `65fa9407d`.

The matching removal of the 22 `<Compile Include>` entries from
`Clef.Compiler.Service.fsproj` is a separate change and must land with it —
without it Composer's build fails `FS0225` on the deleted sources.

## Phase 0 — The embedding ($|S_f| = 1$, behavior-identical)  *(WRITTEN, UNVERIFIED)*

Introduce $F$ and $\beta$ to `SemanticGraph` carrying *only* degenerate hyperedges derived from the four existing encodings. `RegionKind` becomes the seed of the edge-label vocabulary; the four `Reachability` accessors become edge kinds (`TypeRef`, `IntrinsicImpl`, `SymbolRef`, `Semantic`); `EnrichmentId` becomes a provenance edge.

Collapse the ~316-line triplicate: `extractImpliedChildren`, `getSemanticReferences`, and `updateKindRefs` all become projections of one edge table.

**Files:** `PSGSaturation/SemanticGraph/Types.fs` (add `Hyperedge`, `EdgeKind`, `SemanticGraph.Edges`), `Core.fs` (edge constructors + query API — note it currently has *no* `children`/`parent`/`neighbors` function at all), `Reachability.fs`, `Builder.fs`, `Nanopass/FoldIn.fs`.

*Status: written and compiling; `phase0-embedding.patch` in this folder, with the three touched files archived beside it. The edge vocabulary, the unified `kindEdges` table, and the Builder/Reachability projections are done — 212 lines of triplicate down to 31. `FoldIn.updateKindRefs` is NOT yet converted. Unverified: see the gate below.*

**Gate — this is the phase's whole value:** reachability computed over $F$ must equal today's result node-for-node on every sample; every existing gate unchanged. PHG §2.4 guarantees backward compatibility, so this is *provable*, not hoped for.

## Phase 1 — The saturation lattice

Add per-node $\{\mathrm{Fresh} < \mathrm{Elaborated} < \mathrm{Saturated}\}$ and the three-state Live/Latent/Fresh model (DTS/DMM §4.2), replacing `IsReachable: bool`. Move reachability to a per-target bitvector on the *edge* (§4.3). Replace the one-shot Pass 3/4 with a monotone driver that iterates fan-out/fold-in until no rule fires.

This is what lets a recipe emit structure that is *itself* further elaborated — the precondition for DCont and INet — and it retires the `FoldIn.fs:245` paradox.

**Constraint (callsheet family 13):** the fixpoint is over recipe *shapes*, never a per-program fixpoint. Keep the DBC boundary explicit in the driver.

## Phase 2 — Arity > 1: flat closures

The first genuine hyperedge family, chosen because it is the finiteness lemma everything else rests on.

- Closure hyperedge: $S_f$ = captured bindings ∪ {lambda}, $\lambda_f$ = the C-01 §14 form.
- Move `ClosureLayout` construction out of Composer's `SSAAssignment.fs` into CCS as the hyperedge's $\lambda_f$, with byte offsets settled there — deleting the `// Approximate` computations, the `V (10000 + …)` minting, and the accumulator snapshot from `LambdaWitness.fs`.

  **The design for this is [Layout_As_Joint_Constraint.md](./Layout_As_Joint_Constraint.md)** — the layout hyperedge, the single `placeSlots` function replacing five disagreeing size computations, the seven VCs, the projection onto $\alpha$, and the structural consequence that placement moves from type-check time to saturation. Read it before starting Phase 2; it covers records, DUs, options, tuples, lazy and seq frames, not only closures.
- Emit VC-EXT / VC-DIS / VC-REG / VC-REL / VC-APP as obligation hyperedges discharged at saturation, per C-01 §14.4: *"The discharge point is fixed: at saturation, over the PSG, before witnessing."*
- Drop the ~7 vestigial fields; route construction through `pFlatClosure`.

**This single phase unblocks callsheet families 8, 9, 10 and 11** — every one whose enabling work is "`ClosureLayout`/`DULayout` heap sequences into graph structure."

**Known open gap to schedule here, not defer:** `Partial_Application_Closure_Reification.md` — an escaping partial application has no saturation site today (`makeScaledAdder` fails). Its Option A/C is the PHG-native answer.

## Phase 3 — The rest of the inventory

**Suspension (DCont).** Fan-out splits a computation-expression region at `let!` cuts into segments; per-segment live-across sets become frame slots; fold-in settles state count, frame layout (interference coloring over segment liveness), and placement. Every suspension carries an edge to its delimiter, so nesting is static — no prompt tag, no dynamic search. Generalize `SeqSaturation`'s two-shape recognizer into the real elaborator, and retire `YieldStateIndices.fs`. Covers `seq`, `async`, actor `receive`, and any CE, over one resumption-edge class (I/O completion, mailbox, interrupt, DMA).

**Dual pairs.** η/ε pairing hyperedge; boundary saturation check shared with obligation twin-pairing.

**Nets (INet).** The interaction-net rule system as hyperedge structure — the $k$-ary generalization of the binary active pair, where $k$ is set by the domain's algebra.

**Blocker to settle before this phase starts.** `Alex/Pipeline/MLIRNanopass.fs:1-18` is an MLIR→MLIR transformation pass **already running post-witness in the middle end**, and its roadmap states the intent to add *"DCont lowering (sequential/effectful patterns → stack-based async)"* and *"Inet lowering (parallel/pure patterns → graph reduction)"* **there**. That is the opposite of this plan and of the stated requirement that both be fully elaborated in the PHG. It collides with `Thin_Middle_End_Design.md:22` and `:30`, and with `Single_Flattening_Design.md:38` and `:52` ("The count is one"). Two live documents plan opposite futures for the same file; the plan takes the graph side, and `MLIRNanopass.fs`'s roadmap should be retired in writing before Phase 3 code begins.

## Phase 4 — Cross-apply, and the two dispatches

Thin by design: the structure is already there.

- Generalize `PlatformPinResolution`'s four hardcoded `extract*` into a type-name table, reading `PlatformDescription` records structurally from the graph (the mechanism `CANONICAL_PLATFORM_SPEC.md:83-87` already fixes).
- Cross-apply declarations with governed sites as hyperedges; obligations cite the declaration by name.
- Wire dispatch 1 (design time, from $F$) and dispatch 2 (build time, from the witnessed MLIR), sharing anchor names so twin pairing fires.

Retires HelloProof's `read_bound`/`read_copy_bound` leaks, deletes `pSysReadline`'s `1024L`, and unblocks BAREWire steps 10 and 13.

## Draining Alex — the through-line, not a phase

This is not deferred work at the end; it is what each phase above *is*, seen from the other side. Every hyperedge family that lands in the graph removes a corresponding computation from Alex. The target end state: Alex holds nothing but transcription, and `XDCTransfer.fs` is what every transfer looks like.

**The doctrinal contradiction gets resolved in the graph's favor.** `NativeTypes.fs:655-656` says *"CCS preserves type identity; **Alex resolves to concrete size**"*; `CCS_Architecture.md:205` says Alex *"does not compute, infer, or decide."* These are irreconcilable as written. The plan takes the second: layout is settled in the PHG, and those `NativeTypes.fs` comments are corrected as Phase 2 lands.

The inventory to move, with its destination:

| Currently in Alex | Moves to | Lands in |
|---|---|---|
| Closure byte offsets, extraction schedule (`LambdaWitness`, `ClosurePatterns` — computed twice, independently) | closure hyperedge $\lambda_f$ | Phase 2 |
| `ClosureLayout` construction (`SSAAssignment.fs:202-320`) | Baker recipe | Phase 2 |
| Record field offsets (`RecordPatterns.fs:28`), option repr (`OptionWitness.fs:38`), DU layout incl. the `tryHead` bug (`TypeMapping.fs:368-396`), tuple/lazy/seq offsets (`TypeMapping.fs:422-470`) | layout hyperedges; one size model replaces three | Phase 2 |
| Seq/async state machine (`YieldStateIndices.fs`) | suspension recipe | Phase 3 |
| DCont + INet lowering (planned for `MLIRNanopass.fs`) | Baker recipes — **never built in the middle end** | Phase 3 |
| `1024L` readln buffer + unconditional `-1` newline trim (`PlatformPatterns.fs:305,313,326`) | platform-declaration cross-apply | Phase 4 |
| SysV struct-classification ABI (`PlatformPatterns.fs:422-430`, duplicated `:693`) | target coeffect on the graph | Phase 4 |
| Escape-kind defaulting (`EscapeAnalysis.fs:291` → `StackScoped` when absent) | required annotation; absence becomes a diagnostic | Phase 5 |
| `Kind.ToString().StartsWith("Lambda")` and name/string dispatch (`VarRefWitness:68`, `BindingWitness:41`, `LambdaWitness:172,464`, `MatchWitness:85`, `TypeMapping:286`) | coeffect reads — `VarRefWitness:82-84` already shows the right form ten lines below the wrong one | Phases 2–5 |
| Witness-minted SSAs `V (10000 + tempIdx)` (`LambdaWitness:617`, `ClosurePatterns:103`) | pre-assignment | Phase 5 |
| Synthesized structure with no PSG counterpart: AIE module string template (`KernelModuleWitness:262-371`), Mealy machine (`HardwareModulePatterns:112-520`), `_as_closure` thunks (`ClosurePatterns:140-177`), `@main` wrapper (`LambdaWitness:184-188`) | Baker recipes, so it is marked, visible to Lattice, and reachable by the "pierce the veil" debugging `PSG_Enrichment_Architecture.md:91-131` describes | Phase 5 |

**SSA pre-assignment moves too.** DTS/DMM §4.1 lists it in the coeffect table as a PSG-resident fact ("SSA identifier for the node's result"), and the witness-side minting and accumulator-snapshotting above are the symptoms of it living in the wrong place. `SSAAssignment.fs` is 1,844 lines — the largest single item, and the last to move.

Delete on the way through: `TypeSizing.fs` (dead, zero callers, third size model) and the dead `CFOp`/`VectorOp` unions that fall through to `sprintf "// TODO: Serialize %A"`.

---

# Verification

Every phase carries the same three gates, run before and after:

1. **`RoundTrip` native gate** — `dotnet <Composer>/src/bin/Debug/net10.0/Composer.dll compile samples/RoundTrip/RoundTrip.fidproj`, run, `diff` against `samples/RoundTrip/expected.txt`. Must stay byte-identical. *(Confirmed passing today.)*
2. **BAREWire .NET gate** — `dotnet run --project tests/BAREWire.Tests.fsproj`; 300/300 with cvc5 genuinely dispatched (the `"cvc5-unavailable"` fallback fails the assertions). *(Confirmed passing today.)*
3. **HelloProof differential** — `HelloProof/run.sh`; obligation count and anchor identity unchanged except where a phase is *specified* to change them (Phase 2 adds families 8–11; Phase 4 retires the read-pair leaks).

**Not a gate: the Composer 24-sample regression suite.** `Composer/tests/regression/Runner.fsx`
is not currently usable as a pass/fail gate — not all samples run, and the full
language surface is not expressed, so failures there are expected and carry no
signal. Its `runProcess` also reads `StandardOutput.ReadToEnd()` synchronously
before `WaitForExit`, so a child that fills the stdout pipe wedges the harness
and the 30s timeout never fires (stderr is handled async; stdout is not). Use
targeted per-sample compiles instead, and compare verdict *sets* rather than
counts if the suite is ever used at all.

**Phase 0's three deltas, for whoever verifies it.** Unifying the two projections
necessarily differs from at least one of them, since they disagreed. The
differences are:

| Delta | Reaches | Assessment |
|---|---|---|
| Lambda parameters added to the reference projection | `computeReachable` (returns a `Set`); `DepthAnalysis` (a max-fold) | order-immune; Composer's `foldPostOrderGraph`/`foldPreOrderGraph` re-exports are dead and never called |
| `RecordExpr` source order swapped | same two | order-immune |
| **`InterpolatedString` ExprParts now enter `Children`** | SSA assignment → MLIR → output | **the one that can move output** |

The third is a latent bug fix, not a regression: the structural projection
treated `InterpolatedString` as a leaf, so interpolation sub-expressions never
became children and survived only because the *other* projection caught them.
Five samples use `$"..."` — 02, 03, 04, 10_Records, 11_Closures — so compile
those individually before and after and diff the MLIR. That is the whole
verification Phase 0 needs; a suite run is not required and is not available.

Phase 0 adds a fourth, and it is the one that makes the embedding safe: **reachability over $F$ must equal reachability over the legacy accessors, node-for-node, on every sample.** Assert it in-tree and keep it until Phase 1 replaces the definition.

**A standing regression gate for the Alex drain**, checkable in CI and monotone by construction: no `sizeOf`/`mlirTypeSize*` call, no mutable byte-offset accumulator, and no `V (10000 + …)` may appear in `Alex/Witnesses/` or `Alex/Patterns/`. Seed it as a warning listing today's sites; each phase removes rows; it becomes an error when the list empties. The count of size models must go 3 → 1.

Two independent correctness checks fall out of Phase 2 and are worth asserting as their own tests: a DU whose first payload case is not its largest must round-trip (today `TypeMapping.fs:387` under-sizes it), and a record and a closure containing the same field types must agree on that field's size (today they use different size models).

## Open items

- **Tier 1 boundary.** The callsheet names an FPGA width/interval "Tier 1/2 seam" but does not enumerate Tier 1 families the way it does Tier 2's thirteen. Worth pinning before Phase 4 wires dispatch.
- **`MLIRNanopass.fs` roadmap** must be retired in writing before Phase 3 — see the blocker note there.
- **`SeqSaturation` consumer.** Nothing in clef reads it; confirm the out-of-tree consumer before Phase 3 replaces the type.
- **The `Thin_Middle_End_Design.md` §5 vocabulary is asserted but never enumerated**, so "additions to that vocabulary are additions to this document first" is unenforceable — and has not held (`hw`, `comb`, `seq`, `smt`, `aie`, `builtin`, `ffi.`). Enumerate it as part of Phase 0 so the drain has a fixed target.
- Three architecture docs are cited by code but absent: `docs/PSG_Elaboration_Fold_Architecture.md`, `docs/Coeffect_Analysis_Architecture.md` (clef-side), and the "Serena memory" references in `Recipe.fs:8`, `FanOut.fs:14`, `FoldIn.fs:11`.

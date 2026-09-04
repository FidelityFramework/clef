# The Flat Closure in the PSG — Retooling Plan

> Increment 2. The flat closure moves from an MLIR plugin below the boundary
> into PSG elaboration and saturation, so Alex witnesses `func`/`memref`/`arith`
> and stock `mlir-opt` lowers it. This is the microcosm of the whole program:
> one representation, retooled from "settled below the graph and re-derived at
> lowering" to "settled in the graph and witnessed out."
>
> The plan is written to be **structurally incapable of drift**: every step
> cites the design section that decides it; every step lands through fan-out /
> fold-in with ingredients and recipes and nothing else; every step has a gate
> that exists; and the invariants are grep-checkable in CI, not held in memory.

## 0. The design that decides this

| Decision | Cited by |
|---|---|
| Flat closure is the finiteness lemma; enumerated capture set = the hyperedge's source set | `Closure_Nanopass_Architecture` §4; spec `closure-representation` §11; DTS/DMM §3.2.1 |
| The environment node is the general object: closure env, DCont frame, actor cell share one fold-in rule | C-01 §14.1 |
| Seven forms, selected by a condition decidable at saturation; forms 1–2 materialize nothing | C-01 §14.2 |
| Every interior form is `func` + `memref` + `arith`; the closure value is **two SSA values, no packing, no casts** | C-01 §14.3 |
| VC-EXT / VC-DIS / VC-REG / VC-REL / VC-APP discharged at saturation, over the PSG, before witnessing | C-01 §14.4 |
| Layout is settled before emission; the witness reads it, never computes it | spec §9; `Closure_Nanopass_Architecture` §5 |
| Placement by the four-point lifetime lattice: stack / region / static / heap; no heap on a heapless target is a compile error | spec §3.3, §10.8 |
| Nested named functions pass captures as parameters — no struct | spec §8, §10.11–12 |
| Packing into words is a boundary event only, under the §6.7 contract | C-01 §14.2 "Fence packing is not a form"; §6.7 |
| The plugins are "interim… superseded when per-obligation correspondence lands" | `Thin_Middle_End` §3; `mlir-plugins/ROADMAP.md` |
| Hyperedges: `(S_f, t_f, λ_f)`, fire when all sources are elaborated; consequence reaches emission as α or as a reified attribute, never by querying F | PHG paper §2.1–2.4 |
| The witnessed vocabulary is fixed and additions go through the document first | `Thin_Middle_End` §22, §5 |

Two documents currently **normalize the form being retired** and must follow
the code, not lead it: spec `closure-representation` §6.3 and spec
`backend-lowering-architecture` §4.2 and §7.5–6 (which *require* the
`unrealized_conversion_cast` deferral and a per-target resolution plugin).
`Gaining Closure` §"The Witnessed Form" defends the casts as honest markers.
C-01 §14.3 is the later design and supersedes all three; the spec edits are a
step of this plan, not a prerequisite.

## 1. What works and what does not — the FidelityHelloWorld set

Measured 2026-09-04 against the rebuilt compiler, each sample compiled
individually through the CLI and run against the manifest's expected output.
**17 of 24 pass end to end.**

| # | sample | PRD | compile | run | what fails |
|---|---|---|---|---|---|
| 01 | HelloWorldDirect | F-01 | OK | OK | |
| 02 | HelloWorldSaturated | F-02 | OK | OK | |
| 03 | HelloWorldHalfCurried | F-03 | OK | OK | |
| 04 | HelloWorldFullCurried | F-04 | OK | OK | |
| 05 | AddNumbers | F-05 | OK | OK | |
| 06 | AddNumbersInteractive | F-06 | OK | **mismatch** | both stdin lines fold into operand 1 — `readln` framing, a platform question (`Surface_Gaps` §Deferred), not this plan |
| 07 | BitsTest | F-07 | OK | OK | |
| 08 | Option | F-08 | OK | OK | |
| 09 | Result | F-09 | OK | OK | |
| 10 | Records | F-10 | OK | OK | |
| 10a | ImperativeControl | — | OK | OK | |
| 11 | Closures | C-01 | OK | **mismatch** | `Hello, !` for `Hello, Alice!`; `add10 5: 5` for `15` — **every capture reads back empty or zero** |
| 12 | HigherOrderFunctions | C-02 | OK | **SIGSEGV** | same capture failure, then a segfault mid-line |
| 13 | Recursion | C-03 | **FAIL** | — | `mlir-opt`: `region entry argument '%arg0' is already in use` — an SSA collision in `sumTo` |
| 14 | Lazy | C-05 | **FAIL** | — | `pBuildLazyForce: Expected at least 5 SSAs, got 3`; 45 `AX2001 arguments not yet witnessed` |
| 15 | SimpleSeq | C-06 | **FAIL** | — | `FS0001` on `while n <= max do` inside `seq { }` (three sites) |
| 16 | SeqOperations | C-07 | **FAIL** | — | `Unhandled intrinsic 'SeqEnumerator.moveNext'` |
| 17 | ExternCall | — | OK | OK | |
| 18 | Generalization | — | OK | OK | |
| 19 | ModuleValues | — | OK | OK | |
| 20 | ArraySurface | — | OK | OK | |
| 21 | RecordsAndTags | — | OK | OK | |
| 22 | UnionPayloads | — | OK | OK | |
| 23 | RecordSurface | — | OK | OK | |

**Five of the seven failures are the closure family.** Spec
`closure-representation` §7 defines the lazy value and the sequence expression
as *the flat closure extended with slot classes* — memoization slots
(`computed`, `value`) and state-machine slots (`state`, `current`, internal
state) — inheriting every property of the base representation. So 11, 12, 14,
15 and 16 fail for one reason with five faces: the closure representation is
settled below the graph, and what is settled there is wrong. Retooling the
closure is the gate for all five. 13 is an SSA-assignment collision in the same
"computed at emission" class at a different site; 06 is out of scope.

`13a_SimpleCollections` / `13a_BAREWireCollections` exist on disk (C-04) but are
not in the manifest and were not measured; the List surface is
`Surface_Gaps` §Deferred.

## 2. The microcosm, measured — sample 11 today

Compiled fresh with the rebuilt compiler, `07_output.mlir`:

| | count |
|---|---|
| `builtin.unrealized_conversion_cast` | **28** |
| `memref<2xindex>` (the packed pair) | 72 |
| `func.call_indirect` | 15 |

Every one of the 28 casts is a fact settled below the graph — "what a function
value is as data, what a buffer is as data" — that the `flat-closure-lowering`
plugin resolves after standard lowering. Remove the plugin today and the build
fails at `--reconcile-unrealized-casts`. And the values it produces are wrong.

The path that produces this, per the witness-boundary audit: `ClosureLayout`
built in Composer's `SSAAssignment.fs:202-320` with ~7 vestigial fields
repurposed as scratch; byte offsets computed in `LambdaWitness.fs` with two
`// Approximate` comments, and computed **a second time, independently** in
`ClosurePatterns.fs` on the extraction side; SSAs minted at emission
(`V (10000 + tempIdx)`); `pFlatClosure` dead on the live path.

## 3. The target form

C-01 §14.3, primitive by primitive:

```mlir
// construction, in the parent — a form-3 (stack flat) closure over one i32
%env = memref.alloca() : memref<4xi8>                    ; extent literal (VC-EXT)
%c0  = arith.constant 0 : index                          ; offset literal (VC-DIS)
%f0  = memref.view %env[%c0][] : memref<4xi8> to memref<1xi32>
memref.store %n, %f0[%c0] : memref<1xi32>
%fn  = func.constant @makeAdder_lambda : (memref<4xi8>, i32) -> i32
; the closure value is (%fn, %env): two SSA values. Nothing is packed.

// invocation
%r = func.call_indirect %fn(%env, %x) : (memref<4xi8>, i32) -> i32

// the body — receives the environment; captures are views at literal offsets
func.func private @makeAdder_lambda(%env: memref<4xi8>, %x: i32) -> i32 {
  %c0 = arith.constant 0 : index
  %v  = memref.view %env[%c0][] : memref<4xi8> to memref<1xi32>
  %n  = memref.load %v[%c0] : memref<1xi32>
  ...
```

No cast anywhere. `--convert-func-to-llvm` lowers `func.constant` and
`call_indirect`; `--finalize-memref-to-llvm` lowers the views. Stock passes.

**The one open design decision, named.** Two SSA values cover binding, passing,
returning, and HOF arguments — every case in sample 11. They do not by
themselves cover a closure **stored as data**: captured by another closure, or
carried as a DU payload (spec §8.1 calls that an escape point). A `memref`
cannot hold a function-typed element, and function→data with no cast has no
standard form. §14.2 is where this resolves: form 2 *Unmaterialized* when the
callee is statically known at every site (a lambda literal captured by a
lambda — the outer environment stores the inner *environment*, and the inner
code is re-materialized by symbol); a materialized function field only when the
callee is genuinely unknown (a closure *parameter* captured by a lambda). The
second case is the `makeScaledAdder` / PAP territory `Partial_Application_
Closure_Reification` records as an open gap. **Step 6 below writes that
decision down before any code touches it.** Nothing in steps 1–5 depends on it.

## 4. The mechanism — and only this mechanism

The closure becomes a Baker recipe; the pass is fan-out → fold-in; the witness
reads. This is C-01 §14.7's "recipe migration", and it reuses what Increment 1
built.

**Ingredients** (`Baker/Ingredients/Closures.fs`, new):
the environment node; capture nodes carrying mode (`ByValue`/`ByRef` from
`CaptureInfo.IsMutable`); the code reference; the escape-class edge; the
release-site edge. These are C-01 §14.1's five structures as node/edge
constructors. Plus the closure hyperedge:

```
f_closure = (S_f = captured bindings ∪ {lambda},  t_f = environment node,  λ_f = ClosureForm)
```

**Recipes** (`Baker/Recipes/ClosureRecipes.fs`, new):
- *fan-out* — for each capturing `Lambda`: mint the five structures and the
  hyperedge. For a nested named function (spec §8.3: enclosing function present
  and parent is a `Binding`): mint nothing; captures become leading parameters.
- *fold-in* — select the form (§14.2) from modes, escape class, and sizes;
  compute the layout with `placeSlots` (`Layout_As_Joint_Constraint` §2.3 —
  the one placement function, taking `PlatformContext`); emit VC-EXT/DIS/REG/
  REL/APP as obligation hyperedges through `Baker/Ingredients/Obligations`;
  project the layout onto α (`LayoutHint` on the environment node,
  `SlotPlacement` on each capture).

**Pass** (`Nanopass/ClosureElaboration.fs`, new): discovers capturing lambdas,
applies the recipes, folds. Same shape as `ObligationElaboration`.

**Witness** (`LambdaWitness.fs`, rewritten to the ~20-line thin observer the
Alex architecture mandates): reads the form and the placements; emits the §14.3
table row for row. `ClosurePatterns.fs` becomes the ~50-line composition of
`memref.alloca` / `memref.view` / `memref.store` / `func.constant` /
`func.call_indirect` over settled literals. Zero `sizeOf`. Zero offset
arithmetic. Zero minted SSAs.

**Escape classification** moves to CCS with this step, because fold-in reads it.
`EscapeAnalysis.fs`'s classification is the spec §3.3 lattice; it becomes a
saturated annotation the recipe consumes, not a Composer coeffect the witness
defaults when absent.

## 5. What is removed

| Removed | Why | Cited |
|---|---|---|
| `flat-closure-lowering` from `BackEnd/LLVM/Lowering.fs` pipeline (`resolve-closure-casts`) | nothing left to resolve | §14.3 |
| `MemRefOp.IndexToMemRef`/`MemRefToIndex`, `FuncOp.IndexToFunc`/`FuncToIndex` and their `unrealized_conversion_cast` serialization | the cast constructors | `Thin_Middle_End` §3 |
| `ClosureLayout` (`Coeffects.fs:72-133`) and `buildClosureLayout` (`SSAAssignment.fs:202-320`) | layout is the hyperedge's λ_f, settled in CCS | spec §9 |
| offset computation in `LambdaWitness.fs:317-327, 546-632` and `ClosurePatterns.fs:226-268` | the witness reads | `Closure_Nanopass` §5 |
| `V (10000 + tempIdx)` minting (`LambdaWitness:617`, `ClosurePatterns:103`) | SSAs are pre-assigned | Learning to Walk |
| `pFlatClosure`, `pNamedFunctionAsClosure` thunk synthesis | dead / synthesized below the graph | audit §4g |
| the packed `memref<2xindex>` pair everywhere it is constructed or read | replaced by multi-value | §14.3 |

`reconcile-ffi-externs` stays for now: it is the `ffi.` fence, and the fence
becomes a boundary hyperedge under §6.7 — a later increment.

## 6. Steps, gated

Each step lands only when its gate is green. RoundTrip and the HelloProof
harness run at every step and must not move.

1. **Measure** (§1 table). Gate: per-sample compile/run verdicts recorded;
   this is the baseline every later step is diffed against.
2. **`placeSlots` in CCS** (from `Layout_As_Joint_Constraint` §2.3). Gate:
   reproduces today's x86_64 offsets for every record and closure in samples
   10, 11, 21, 23; the DU `tryHead` divergence is the one expected difference.
3. **Closure ingredients + recipes + pass**, fan-out only — the five structures
   and the hyperedge in the graph, nothing consumed yet. Gate: `05_psg2.json`
   shows the environment nodes and closure hyperedges for sample 11 (four
   arity ≥ 2 edges: `makeGreeter`, `makeAdder`, `makeRangeChecker`,
   `makeFormatter`); every existing gate unchanged.
4. **Fold-in**: form selection, layout onto α, VCs as obligations. Gate:
   `06a` gains the closure families (callsheet 8, 9, 11); `cvc5` unsat on all;
   HelloProof unchanged (it has no capturing lambda that materializes).
5. **The witness reads; the casts go; the plugin goes.** `LambdaWitness` /
   `ClosurePatterns` rewritten; cast constructors deleted; `Lowering.fs`
   pipeline loses `resolve-closure-casts`. Gate: sample 11 **prints its
   expected output** (C-01 §8.2, the first time); `grep -c
   unrealized_conversion_cast 07_output.mlir` = **0** on every sample that
   compiles; `Lowering.fs` has no `--load-pass-plugin` for closures.
6. **The stored-closure decision.** A design note (`Closure_As_Data.md`)
   deciding §14.2 form selection for a closure captured by a closure and for
   DU payloads, citing spec §8.1 and `Partial_Application_Closure_Reification`
   Option A. Then `makeScaledAdder` returns to sample 11 and prints. Gate:
   sample 11's TODO is gone and it passes; sample 12 passes.
7. **Spec follows.** `closure-representation` §6.3 and
   `backend-lowering-architecture` §4.2/§7.5–6 rewritten to the multi-value
   form; `Gaining Closure` §"The Witnessed Form" updated; `mlir-plugins`
   README/ROADMAP mark `flat-closure-lowering` retired.
8. **Supersede the DCont/INet dialect claims** that still read as live:
   `MLIRNanopass.fs:5,15-16,139-140`, `WebView_Desktop_Architecture.md:225-226`,
   `C-04-CoreCollections.md` §15, clef `ccs-specification.md` §12.6. Each
   becomes a pointer to `Delimited_Continuations_Architecture` §7 (the witnessed
   form is a discriminant + frame + `scf.index_switch`). `Single_Flattening`
   §38/§61 stay: they already place net vocabulary below the boundary, for
   CGRA-class targets only.

## 7. The drift gates — checked in CI, not remembered

These are the structural guarantees. Each is a grep or an assertion; each is
seeded green (or seeded with today's known violations as a warning list that
must only shrink) and becomes an error when its list empties.

| Gate | Rule | Enforces |
|---|---|---|
| **Dialect register** | every op prefix in `07_output.mlir` ∈ {`func`, `memref`, `arith`, `scf`, `index`} ∪ the admitted list in `Thin_Middle_End` §5; anything else fails | `Thin_Middle_End` §22, §5. **Admitting `affine` (or any dialect) = a row in the register, a design citation, and the sample that needs it.** Step-wise by construction. |
| **No deferred casts** | `unrealized_conversion_cast` count in witnessed MLIR = 0 | §14.3 |
| **No plugins** | `Lowering.fs` contains no `--load-pass-plugin` for closure resolution | `Thin_Middle_End` §3 |
| **Witnesses read** | no `sizeOf`, `mlirTypeSize*`, mutable byte-offset accumulator, or `V (10000 +` in `Alex/Witnesses/` or `Alex/Patterns/` | spec §9; audit §4d/4f |
| **No F in the witness** | no reference to `graph.Edges` / `SemanticGraph.edges*` under `Alex/` | PHG §2.4 (I4) |
| **I1 — enumerated sources** | in-tree assertion at fold-in: every hyperedge has ≥1 source, every source ∈ V, every closure hyperedge's sources = exactly the lambda's `CaptureInfo` list | finiteness lemma |
| **No name dispatch** | no `Kind.ToString().StartsWith` in `Alex/` | `CCS_Architecture` §225 |
| **Layer firewall** | `Elements/` stay `module internal`; no `open Alex.Witnesses` inside `Witnesses/` | `Alex_Architecture_Overview` §Enforcement |

The dialect register is the one you asked for: the original five were a
forcing function against sprawl, and the register keeps the forcing function
while making admission a formal, visible act rather than a silent `open`.

The register has two halves, and the FPGA and GPU legs are the precedent for
the second. *Above* the boundary, the witnessed vocabulary — where `affine`,
`async`, and the parallelism/threading dialects will be admitted as the PSG
comes to express them. *Below* the boundary, per `Thin_Middle_End` §4, a
dialect is justified exactly when it "expresses the target upward": CIRCT on
the FPGA leg, MLIR-AIE on the NPU leg. The audit's finding that `hw`/`comb`/
`seq` are emitted *at* the witness rather than below it is the marshaling still
owed at that demarcation; the register records which half each dialect lives
in, so the demarcation is checkable too.

## 8. What this does not do

- The FFI fence (`reconcile-ffi-externs`, the `ffi.` namespace, callback tiers
  A/B/C). That is the §6.7 boundary hyperedge — its own increment, after this
  one, because it packs closures into words *at the fence* and needs the
  interior form settled first. Its two acceptance programs already exist:
  **HelloWayland** (the listener shape — registration, invocations, and release
  as one lifetime claim; Tier B) and **WrenHello** (the WREN stack's WebView in
  a native application — the host-operation surface, the script-message
  channel, the length-carried-string rule as a Platform obligation). GTK is set
  aside as a direct dependency; D-01 follows WrenHello's shape, not the reverse.
- Lazy / seq / DCont frames. They are instances of the same environment node
  (§14.1) and extend the flat closure with slot classes (spec §7). This plan
  lands the base representation; they follow as recipes over it.
- Affine, threading, process management. The register is where they enter.

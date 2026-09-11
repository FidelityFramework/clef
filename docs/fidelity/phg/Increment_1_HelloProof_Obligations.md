# Increment 1 — DMM Layout Invariants from the Cross-Compiled Platform, as Hyperedges

> The first concrete step of the PHG in clef. This is BAREWire Readiness Audit
> steps 10 and 13: *"the platform description as a coeffect of the program
> semantic graph … obligations stated against the declaration in both
> dispatches … replacing the `1024L` literals in `pSysReadline`."* HelloProof is
> the acceptance program.

## The three layers, one structure

| Layer | What it supplies | Where it is |
|---|---|---|
| **DMM** (DTS/DMM §2.5, §3) | Memory spaces as an *enumeration sort* in the same decidable constraint system as physical units. Placement is a dimensional constraint. | The type system; `NTUMemorySpace`, `ArenaAffinity` already exist in clef |
| **BAREWire** (docs/11) | The vocabulary: `MemorySpace {Capacity; Alignment; Access; …}`, `BufferSchema {Capacity; Framing; Space; …}`. The declared authority on layout. | `BAREWire/src/Platform/Description.fs`, compiled as Clef |
| **Cross-compilation** | `Fidelity.Platform/Environments/Linux/x86_64/Description.clef` declares `text`, `rodata`, `data`, `bss`, `stack`, `arena`, `heap`, `consoleReadln`, `consoleWrite` in that vocabulary — and compiles *with* the program. | Already `RecordExpr` nodes in HelloProof's PSG. Unread. |

The hypergraph is what joins the declaration to the values that live in it. A
string literal *resides in* `rodata`; that residence is a relation, not
containment, so it is an edge in $F$. The layout obligation over all literals
is a joint claim over the literals *and* the space they share, so its source
set includes the declaration node. The obligation *cites* the declaration.

## What was cobbled

`Composer/.../ProofObligations.fs` observes the finished graph and invents a
layout with no declared home: five storages, consecutive, span 31 — bounded
by nothing. `pSysReadline` authors `1024L` twice. `read_bound` and
`read_copy_bound` therefore exist only build-time, re-derived from the
artifact — two of HelloProof's five recorded leaks (`EXTRACTION.md` §3, the
"witness residency" pair).

## The increment

**Resolution.** At saturation, find the `PlatformDescription` root and its
`MemorySpace` / `BufferSchema` records structurally — by type name and field
name, exactly as `PlatformPinResolution` reads pins (the mechanism constraint,
`CANONICAL_PLATFORM_SPEC.md` §"The mechanism constraint"). Reads all nodes,
reachable or not: declarations are cited through $F$, never emitted.

**Residence edges.** For each reachable string literal $\ell$: an edge
$(\{\mathrm{rodata}\}, \ell, \mathrm{Resides})$ — the declared space constrains
the value. For the `readln` site $r$: $(\{\mathrm{consoleReadln}\}, r,
\mathrm{Resides})$.

**Obligation nodes and edges.** Each obligation is a node in $V$ (identity,
provenance, source position, the thing Lattice shows) and a hyperedge in $F$
(the joint source set). Both readings in the corpus — "obligation node with
dependency edges" (C-01 §14.5) and "obligations as hyperedges" (PHG §6.4) —
are the same structure.

| Obligation | $S_f$ | $\lambda_f$ | Cites |
|---|---|---|---|
| `storage_<s>`, `view_<s>`, `sentinel_<s>` | $\{\ell\}$ | as today | — |
| `layout_user_strings` | $L \cup \{\mathrm{rodata}\}$ | consecutive, disjoint, span $= \sum(n_i{+}1)$, **and span $\le$ `rodata.Capacity`** | `cpu-linux-x86_64:rodata` |
| `concat_<s>` | $\{c, a, b\}$ | as today | — |
| `input_bound_consolereadln` | $\{r, \mathrm{consoleReadln}\}$ | count $=$ declared capacity $\le$ allocation | `cpu-linux-x86_64:consoleReadln` |
| `input_copy_bound_consolereadln` | $\{r, \mathrm{consoleReadln}\}$ | $\forall r' \in [1, \mathrm{cap}]: r'{-}1 \le \mathrm{cap}{-}1$ | `cpu-linux-x86_64:consoleReadln` |
| `capacity_consolereadln` | $\{\mathrm{consoleReadln}, \mathrm{arena}\}$ | buffer capacity $\le$ space capacity | both |

The last three are BAREWire's own `Obligations.ofDescription` vocabulary
(`Platform/Obligations.fs`), now stated by the compiler over the program's
actual `readln` site rather than by the library over the description alone.

**The annotation (I4).** The `readln` site's node carries the declared
capacity as a saturated annotation — the hyperedge's consequence on $\alpha$.
`pSysReadline` reads it. The `1024L` literals are deleted.

**Discharge.** Design-time: read $F$, render SMT-LIB, dispatch to cvc5;
`06a`/`06b` become projections of the graph. Build-time: `SMTTransfer` reads
the same records from the graph. `ProofObligations.analyze` is deleted.

**Where it fires.** After final reachability, over the saturated graph
(Pass 5). Under Phase 1's lattice it becomes a rule that fires when its
sources are Saturated.

## Substrate

Phase 0's $F$ (applied). Adds `EdgeClass.Obligation`, `EdgeRole.Resides` /
`Constrains`, `SemanticKind.Obligation`, `Recipe.NewHyperedges`, and edge
accumulation in `FoldIn`. `Obligation`/`ObligationBody` types move to clef so
both dispatches share one definition.

## Not in this increment

- The general escape-class → memory-space assignment (DMM §3.2.1). Only the
  spaces HelloProof exercises: `rodata` for literals, `arena` for the readln
  buffer.
- Fanning out the string storage cell into the graph (`LiteralPatterns` →
  Baker). The obligations cite the literal; the next increment makes them cite
  the storage and view nodes the recipe fans out.
- The lattice. Pass 5 is a fixed position.

## Status — 2026-09-04: built and verified

Measured against a fresh HelloProof compile with the rebuilt clef + Composer.

| Check | Result |
|---|---|
| `05_psg2.json` | 25,793 nodes; **23 obligation nodes**, all `IsReachable = false`, all `Elaboration.Kind = "Obligation"`; **29 hyperedges** — 23 `Obligation/Constrains`, 6 `Reference/Resides` (5 literals → `rodata`, the readln site → `consoleReadln`) |
| Arity | 21 × 1, 4 × 2, 3 × 3, **1 × 6** — the six is `layout_user_strings` over five literals plus the `rodata` declaration |
| `06a` | **23** obligations (19 + the four `consoleReadln` families). `layout_user_strings` cites `cpu-linux-x86_64:rodata` and bounds the 31-byte span against its 4096-byte capacity; the readln four cite `cpu-linux-x86_64:consoleReadln` |
| `06b` | `cvc5` → **23 × unsat** |
| `09_obligations.mlir` | 38 `smt.declare_fun` (23 anchors + 15 symbolic constants); anchor identity preserved by construction — both dispatches render one list |
| `PlatformPatterns.fs` | no `1024`; `pSysReadline` reads `Buffer.Capacity`/`Buffer.TrimDelimiter` from the site's annotation and fails loudly without it. The `arith.constant 1024` in `07_output.mlir` now originates in `Description.clef` |
| `ProofObligations.analyze` | gone from the build (file left on disk: it carries uncommitted edits, deletion is the owner's) |
| `TypeSizing.fs` | deleted — dead, zero callers, the third inconsistent size model |
| RoundTrip | transcript byte-identical |
| The program | `Enter your name: Hello, World!` |

I under-counted in the plan: the readln cross-apply yields four obligations
(`capacity_positive`, `capacity`, `input_bound`, `input_copy_bound`), not two.
The four are BAREWire's own `Obligations.ofDescription` vocabulary, now stated
by the compiler over the program's actual site.

### HelloProof's harness — PASS

`run.sh` compiles with a **pinned** Composer (`tools/composer/Composer`,
`9a1a60b`), so its first run consumed a 19-obligation ledger and Pass 5 never
entered. Against a fresh compile with the rebuilt compiler, and with one change
to `Prover.fsx` (uncommitted, in ship-of-theseus, +33/-1), the harness reports:

```
obligation identity (design-time SMT-LIB ≡ SMT-dialect export): PRESERVED
ARTIFACT CROSS-CHECK — 23 obligations — all OK
  input_bound_consolerea...  OK  readln @read count 1024 into memref.alloc(1024) at 07:107
  input_copy_bound_conso...  OK  readln trimmed copy (arith.subi) at 07:110 over read count 1024
UNVERIFIED BEHAVIOR + LAYOUT CHECK (1): rodata_map  layout  (linker placement, lawful)
ROCQ CODA: targets/rocq/MemoryMap.v: CHECKED
PASS: every obligation proven at both stages, cross-checked in the artifact;
      no unverified observable behavior
```

Before: `FAIL: 2 observable behaviors are unverified` — `read_bound` and
`read_copy_bound`, the "witness residency" pair of `EXTRACTION.md` §3.

The `Prover.fsx` change is the destination `EXTRACTION.md` §2 already named for
those rows: the artifact-side extraction of the readln facts stays (it is the
clerk), the two rows are a leak only while the ledger lacks
`input_bound_consolereadln` / `input_copy_bound_consolereadln` — the same gate
the twelve string twins use — and cross-check rules for the four declared-buffer
kinds reconcile the artifact's `read` count and allocation against the capacity
the ledger cites. Nothing in the harness authors an obligation any more.

The pinned binary was not replaced; re-snapshotting `tools/composer/Composer`
is the owner's act.

## Design decisions taken

- **`SMTTransfer` keeps its shape.** It is a *transfer* — "the coeffect IS the
  pre-computed data; this transfer is serialization" — BAREWire 11's third
  observer as a pure function, parallel to `XDCTransfer`. What changed is its
  **input**: the graph's obligation records, not an `ObligationSet` computed
  beside the graph. Its header now says so.
- **Recipes in Baker, orchestration in Nanopass.** `Baker/Ingredients/Obligations.fs`
  (the `Enrichment` type, node/edge primitives, naming discipline),
  `Baker/Recipes/ObligationRecipes.fs` (the four families),
  `Nanopass/ObligationElaboration.fs` (subject discovery, apply, fold).
  `PlatformResolution.fs` stays in `SemanticGraph/`: it is a projection of the
  graph, the codata the recipes observe.
- **Obligation nodes are unreachable by design** (I4). Reachability is
  containment; obligations are cited through $F$. `markUnreachable` leaves them
  out of the emission set, which is correct.
- **Functional throughout.** The slug uniquifier is a fold over a `Map`;
  `elaborate` is `SemanticGraph -> Enrichment`; `foldIn` is
  `Enrichment -> SemanticGraph -> SemanticGraph`. No accumulator by reference.
- **The ledger description changed** from "coeffect" to "graph citizens". The
  word was wrong.

## Also landed — the two findings from the handoff

**The reified attribute (PHG §2.4b).** Every obligation hyperedge is projected
onto its source nodes at saturation as `Obligation.Anchors` (form a, derived
from $F$ in the pass — no recipe annotates by hand, so a node constrained by
several obligations carries all of them). `LiteralWitness` reads it as codata
and `GlobalString` reifies it (form b):

```
memref.global "private" constant @str_4116459851 : memref<6xi8> = dense<[...]>
    {clef.obligations = ["storage_hello", "view_hello", "sentinel_hello", "layout_user_strings"]}
```

The artifact now carries the correspondence explicitly. The five-way joint claim
sits on all five globals; a literal that is a `concat2` operand also carries
that site's anchor, because it is in the hyperedge's source set. The extern
boundary's strings (`dlopen` path, `dlsym` symbol) carry none — they are
synthesized below the graph, a recorded gap at the FFI fence
(`Witness_Boundary_Audit` §4g; C-01 §6.7). The `concat2` site's own
alloc/memcpy chain does not yet carry its anchor; that is `StringPatterns`'
work and the harness already records its artifact extraction as pending.

**`cf` / `vector` removed.** `Thin_Middle_End_Design` §22 fixes the witnessed
vocabulary at `func, memref, arith, scf, index`. `cf` is unstructured control
flow — what `scf` lowers *to* below the boundary — and `Delimited_Continuations`
§7 chooses `scf.index_switch` for the discriminant. `CFElements`,
`VectorElements`, the `CFOp`/`VectorOp` unions and the one dead `pSwitch`
pattern (no callers) are gone. Not a side quest: the design decided it.

## Next, in order

1. **Storage-cell fan-out.** `LiteralPatterns` still synthesizes the `n+1`
   storage with the sentinel below the graph. The obligation recipe should fan
   out the storage and view nodes and cite *them* — "the recipe that fans out a
   string global fans out its obligations in the same firing", in full.
2. **The `concat2` chain carries its anchor** (`StringPatterns`), and the
   harness's "artifact extraction pending (concat chain)" row closes.
3. **Extern-boundary strings** become graph citizens under the C-01 §6.7
   boundary contract, so `dlopen`/`dlsym` globals cite something.

# PSG → PHG

Working folder for the Program Hypergraph transition: turning Clef's PSG into a
$\mathrm{PHG} = (V, F, \alpha, \beta)$ that is the CCS front end, and from which
memory layout and the Tier 1/Tier 2 proofs fall out as one structure rather than
two.

| File | What it is |
|---|---|
| [Dimensional_Handoff.md](./Dimensional_Handoff.md) | **Start here for the dimensional range wave.** The reading order and authority, the placement rule, the working model, the state, the gates with exact commands, what is next, what is owed, the code map, the as-built template. Written for an agent with no prior context. |
| [Opus_Extension_Sweep.md](./Opus_Extension_Sweep.md) | A mechanical brief for a limited agent: rename the compiler sources `.fs` to `.clef`, rewrite the project files, re-run every gate. Gated on the owner naming the build mechanism that admits the extension (stock `fsc` refuses it, FS0226). |
| [PSG_to_PHG_Plan.md](./PSG_to_PHG_Plan.md) | The plan. The PHG writ large, the four integrity invariants, the two dispatches, the verified state of the code, Track A + Phases 0–5, the *Draining Alex* inventory, verification. |
| [Increment_1_HelloProof_Obligations.md](./Increment_1_HelloProof_Obligations.md) | The first built increment: DMM layout invariants from the cross-compiled platform, as hyperedges. What it required, what was cobbled, what was built, measured results, decisions, next steps. |
| [Closure_Retooling_Plan.md](./Closure_Retooling_Plan.md) | Increment 2, the microcosm: the flat closure moves from an MLIR plugin into PSG elaboration and saturation. The measured 24-sample baseline (17 pass; 5 of 7 failures are the closure family), the target form (C-01 §14.3, no casts, no plugin), the one open design decision, eight gated steps, and the CI drift gates including the dialect register. |
| [Design_Supersession_Register.md](./Design_Supersession_Register.md) | Every document touched by the settled position, classified: normative spec text still binding the retired forms (a decision about authority), stale claims, stale-since-Increment-1, already-superseded, external. |
| [Layout_As_Joint_Constraint.md](./Layout_As_Joint_Constraint.md) | The Phase 2 design: bringing layout up out of Alex into the PSG as joint constraints. The layout hyperedge, `placeSlots`, the seven VCs, projection onto $\alpha$, and why placement must move from type-check time to saturation. |

Companion outside this folder: **`Composer/docs/Witness_Boundary_Audit.md`** —
the measured state of the Alex witness boundary. The plan's *Draining Alex*
table is derived from its Section 4, and the layout design replaces what its
Sections 4b and 4d document.

## Status

- **Track A** — landed (`65fa9407d`). The matching `fsproj` entry removal must
  land with it.
- **Phase 0** — landed with Increment 1: `Hyperedge`/`EdgeClass`/`EdgeRole`, `kindEdges`, `SemanticGraph.Edges`; `NodeBuilder` and `Reachability` project the one table. `FoldIn.updateKindRefs` not yet converted.
- **Increment 1** ([Increment_1_HelloProof_Obligations.md](./Increment_1_HelloProof_Obligations.md)) — **built and verified**: obligations are graph citizens minted by Baker recipes; the cross-compiled platform description is cross-applied to the values in it; 23 obligations, 23 × `unsat`, `pSysReadline` reads the declaration. **HelloProof's harness: PASS** — the two recorded readln leaks are retired (its `Prover.fsx` re-pointed at the graph-born pair, uncommitted in ship-of-theseus). Every string global carries `{clef.obligations = [...]}` — the transport rule's second carrier. Dead `cf`/`vector` vocabulary removed from Alex.
- **Phase 2 / Increment 2** — planned ([Closure_Retooling_Plan.md](./Closure_Retooling_Plan.md)); baseline measured; implementation not started.
- Phases 1, 3, 4, 5 — not started.

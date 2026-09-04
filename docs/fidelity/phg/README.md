# PSG → PHG

Working folder for the Program Hypergraph transition: turning Clef's PSG into a
$\mathrm{PHG} = (V, F, \alpha, \beta)$ that is the CCS front end, and from which
memory layout and the Tier 1/Tier 2 proofs fall out as one structure rather than
two.

| File | What it is |
|---|---|
| [PSG_to_PHG_Plan.md](./PSG_to_PHG_Plan.md) | The plan. The PHG writ large, the four integrity invariants, the two dispatches, the verified state of the code, Track A + Phases 0–5, the *Draining Alex* inventory, verification. |
| [Increment_1_HelloProof_Obligations.md](./Increment_1_HelloProof_Obligations.md) | The first built increment: DMM layout invariants from the cross-compiled platform, as hyperedges. What it required, what was cobbled, what was built, measured results, decisions, next steps. |
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
- **Phase 2 design** — written. Implementation not started.
- Phases 1, 3, 4, 5 — not started.

# PSG → PHG

Working folder for the Program Hypergraph transition: turning Clef's PSG into a
$\mathrm{PHG} = (V, F, \alpha, \beta)$ that is the CCS front end, and from which
memory layout and the Tier 1/Tier 2 proofs fall out as one structure rather than
two.

| File | What it is |
|---|---|
| [PSG_to_PHG_Plan.md](./PSG_to_PHG_Plan.md) | The plan. The PHG writ large, the four integrity invariants, the two dispatches, the verified state of the code, Track A + Phases 0–5, the *Draining Alex* inventory, verification. |
| [Layout_As_Joint_Constraint.md](./Layout_As_Joint_Constraint.md) | The Phase 2 design: bringing layout up out of Alex into the PSG as joint constraints. The layout hyperedge, `placeSlots`, the seven VCs, projection onto $\alpha$, and why placement must move from type-check time to saturation. |
| `phase0-embedding.patch` | Phase 0 as written: the edge vocabulary, the unified `kindEdges` table, and the two projections. Compiles; unverified. **Predates the `Builder.fs` → `NodeBuilder.fs` rename — adjust that path when applying.** |

Companion outside this folder: **`Composer/docs/Witness_Boundary_Audit.md`** —
the measured state of the Alex witness boundary. The plan's *Draining Alex*
table is derived from its Section 4, and the layout design replaces what its
Sections 4b and 4d document.

## Status

- **Track A** — landed (`65fa9407d`). The matching `fsproj` entry removal must
  land with it.
- **Phase 0** — written, compiles, unverified. `updateKindRefs` not yet converted.
- **Phase 2 design** — written. Implementation not started.
- Phases 1, 3, 4, 5 — not started.

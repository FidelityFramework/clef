# Required compiler architecture

These are owner requirements for all work in this repository.

- CCS/Baker owns source semantics, elaboration, saturation, numeric selection,
  declaration/ABI settlement and proof premises in the PSG. Preserve nanopass
  ingredients/recipes, joint constraints, scope and the intermediate rewrite record.
- Publish settled facts for passive Alex Huet Element/Pattern/Witness composition.
  Do not move analysis, inference or semantic repair into Alex or an MLIR pass.
- A graph leaves CCS in one place and one form: a revision of `Fidelity.PSG`,
  assembled in `src/Compiler/PSGSaturation/Publication`. No reader of a
  revision references this assembly or calls a function in it. Publication
  copies rows that Baker wrote. A computation performed at publication is debt
  owed to a Baker recipe. Moving it there from a reader does not settle it.
- All custom MLIR plugins and their compatibility dependencies are retired.
  Do not restore deleted plugin repositories or preserve a plugin to keep a gate
  passing. Target-specific lowering belongs to Composer's backend.
- Failures must surface and be repaired at the owning source contract. Do not
  substitute convenient widths, partial premises or weaker tests for proof.
- Preserve Clef's native dimensional type universe and lazy-default semantics.
  .NET is the compiler/tooling host, not the language's semantic model.
- Use .NET tooling; do not introduce or run Python automation.
- Keep temporary test fixtures and gate scratch under `artifacts/scratch/` in
  this primary checkout.
- Record exact evidence and failures. Focused passing checks do not establish
  complete F/C acceptance.

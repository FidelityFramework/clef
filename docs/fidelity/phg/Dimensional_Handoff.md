# Dimensional range wave: handoff

> For an agent, from any vendor, with no prior context. Read this first, then the documents in the order §1 gives. Nothing in this folder assumes a conversation you were part of. The owner is Houston Haynes; the owner rules, reviews and commits; you build, gate and record.

## 0. What this work is

Clef's numeric types are becoming one integer kind and one real kind whose width and representation are selected from the value's analysed range and the platform's declared representations, never from a width-named spelling (`int32`, `uint64`, `byte`). The compiler service (CCS, the `clef` repo) computes every fact about a program at saturation and carries it on the Program Semantic Graph; the code generator (Composer, its `Alex` middle end) reads the graph and writes MLIR and computes nothing. The wave runs as gated changesets, CS-9 through CS-13, each recorded as an "as built" section in the design of record.

## 1. Read in this order (authority runs top to bottom)

| Document | What it settles |
|---|---|
| `clef-lang-spec/spec/width-inference.md`, `numeric-selection.md`, `ntu-types.md`, `platform-bindings.md`, `ffi-boundary.md`, `error-handling.md` | The normative language: range-driven width, selection over declared representations, boundaries as declarations, the CCS diagnostic code table |
| `Dimensional_Range_Design.md` | The design of record for hardening steps 3, 7 and 8. Its first section, **"Where code lives"**, is the placement rule and the record of its violation. §0 the closed decisions; §1 the range; §3 selection; §4 boundaries; §7 the codes; §8 what is deleted and what moves; §9 the corpus migration; §12 the changesets and their gates. Then the rulings sections and every as-built, newest last |
| `Dimensional_Steps_1_2_Sequence.md` | The status ledger: one paragraph per changeset, gates and counts, in order. The last paragraph is the current state |
| `Dimensional_Vetting_Plan.md` | The harness (`vet.sh`), the vetting rows (W, M, UoM, NS) and their `expect.toml` files under `Composer/samples/dimensional/`, the hardening steps |
| `Layout_As_Joint_Constraint.md`, `Closure_Retooling_Plan.md` | Layout as a saturation fact; the flat closure's target form |
| `Composer/docs/CCS_Architecture.md` | The CCS/Composer division, the coeffect table with its 2026-09-05 status |
| `Horizon_Requirements.md` | The constraints the papers fix (C3: width is a function of the range, never stored or fabricated) |

Where a document disagrees with a later one, the later one was written to correct it and says so. Where the spec disagrees with the design of record, §10 of the design lists the corrected passages. The owner's rulings, quoted in the rulings sections, outrank both.

## 2. The one rule

A fact about the program is computed in CCS, once, at saturation, and carried on the graph. Composer reads. There is no third place, and there is no "interim" place. The full table and the checks are in `Dimensional_Range_Design.md`, "Where code lives"; the short form:

- Program facts (ranges, selections, layouts, escapes, placements, call-site resolutions, pins, partial applications, meets, declaration roots): `clef/src/Compiler/PSGSaturation/SemanticGraph/`, run from `NativeService.buildResult`, written to the graph (`SemanticGraph.Codata`, `Layouts`, `FieldRanges`, `ElementRanges`, `Escaping`, the node's `ValueRange`).
- Graph rewrites (a Baker recipe, chain flattening): `clef/src/Compiler/Nanopass/` or a saturation pass. Never after the graph leaves CCS.
- What a node becomes in MLIR, and the names of the values emitted: `Composer/src/MiddleEnd/Alex/`. A value is named by `Alex/Traversal/Values.fs` from its node, `V (node, k)`. No pass numbers values, no witness holds a counter, no table of emission costs exists.
- The platform's declarations: the description (`Fidelity.Platform`, BAREWire's vocabulary), read into `PlatformContext` and the graph by `PlatformResolution.fs` and `PlatformDeclaration.fs`. Never a table in a compiler.

If a witness needs a fact the graph does not carry, it stops with a message naming the fact. You then add the fact to CCS. You do not add a pass to Composer.

## 3. How the work is done

- **The owner rules.** A decision about architecture, a boundary, a default, a diagnostic's severity, or the scope of a sweep is the owner's. Put the question with a recommendation and stop. The rulings sections show the form: the question, the facts from the record, the recommendation, and the owner's answer.
- **Changesets are gated slices.** Build both compilers, run every gate in §5 on the final binary, and record the results from the transcripts you ran, never from a file you assume unchanged. A prior implementer recorded a stale file as identical and was rejected for it.
- **Every changeset writes its as-built** at the end of `Dimensional_Range_Design.md` and one paragraph in the ledger: what landed by file, the gates with their counts, **Decisions, for the owner**, and **Owed**. The docs are the source of truth and change in the same changeset as the code.
- **The owner commits.** Never commit, push or tag. Leave the working tree ready and propose exactly one commit line, `type(scope): what`, no body.
- **Never restore what the owner removed.** Composer's `src/MiddleEnd/PSGElaboration/` is gone and stays gone.
- **Nothing is defaulted and nothing is fabricated.** An unobservable range is CCS8011, never a guessed width (§1.3, C3). A boundary is a declaration read from the description, never a number in code.
- **Prose register.** Plain sentences, one idea each; no em dashes; state facts and consequences; the cited documents belong and are not re-litigated.

## 4. State on 2026-09-05

Built and gated: CS-9 (operator kinds and library schemes), CS-10 (the range pass in CCS, the fabric leg reads the node), CS-11 (the CPU leg: declared range sources, selection, settled layouts, the escaping boundary at the word, meets, truncation at refined reads), CS-12 step 1a (one structural reader for wire fields, peripheral registers and binding descriptors, the errno bound from the contract, the vocabulary's own field ranges), the Farscape leg (extern signatures spell `int`; every extern carries its `Expr<FunctionDescriptor>`; C structs are layout modules with `StructDescriptor`s), CS-12 step 5a (width-named spellings and suffixes are an interim alias of the bare kind, CCS8019 at each site, the spelling's representation an interim declared boundary), and the PSGElaboration lift (every program fact Composer used to compute is a CCS pass writing `Codata`; values named at emission). Ruling 3 is built: one-step backward refinement through `-` and `+`, and predicate atoms carried to call sites.

Counts on RoundTrip at this state: 56 CCS8011 (information on cores until promotion: `readUInt`'s unguarded `shift` carried through the type-level tuple join, Validator's accumulations, the arithmetic cycles), 19 CCS8012 (the correlated `offset + n` shape under `count <= length - offset`, a warning the interval domain cannot discharge, plus `Fmt.ofInt64`), 468 CCS8019 (the spelled-site inventory: 339 spellings, 129 suffixes). RoundTrip's binary hash is `ebbaab77ae6a5a59…` after ruling 3; the transcript is the gate, and the hash is re-baselined at the owner's word.

**Step 5a, judged after the fact (2026-09-05).** Kept whole. The alias (`Types.sameCarrierIdentity`), the declaration a spelling denotes (`RangeSources.declarationOfKind`), the reads through it (`selectNode`, `selectedWidth`, `boundByCarrier`, `Placement.carrierSlot`, Composer's `mapNativeTypeForTarget`), CCS8019 once per site with suffixes treated as spellings, and CCS8012/CCS8014 at spelled sites follow ruling 5 and hold on every gate. Two hazards it carries, both already owed: `NTUKind.isInteger` includes `usize` and `diff`, so pointer-width spellings unify with `int` ahead of step 5's handles, and a pointer-width value met with a word integer reaches Composer's `index` mapping untested (a loud stop, not a silent result); and `mapNTUKindToMLIRType`'s graph-less arm still maps a spelled literal at the spelling's own bits, which the promotion step deletes with the spellings.

## 5. Gates, exact commands, expected results

Run all of them on the final binaries. Paths are this machine's.

| Gate | Command | Expected |
|---|---|---|
| CCS build | `dotnet build /home/hhh/repos/clef/src/Compiler/Clef.Compiler.Service.fsproj` | clean |
| Composer build | `dotnet build /home/hhh/repos/Composer/src/Composer.fsproj` | clean |
| RoundTrip | `cd /home/hhh/repos/BAREWire/samples/RoundTrip && /home/hhh/repos/Composer/src/bin/Debug/net10.0/Composer compile RoundTrip.fidproj 2>&1 \| tee compile.txt; ./targets/roundtrip \| diff expected.txt -` | compile exit 0; run exit 0; no diff; `grep -c CCS8011 compile.txt` at the ledger's count or lower, never higher without a ruling |
| HelloArty | `cd /home/hhh/repos/HelloArty/src/FPGA && Composer compile HelloArty.fidproj -k` | exit 0; `Verified: 25 HDL ports match 25 constraints`; 0 CCS8011; `07_output.mlir` holds `Counter: i30`, `StepTick: i19`, `Phase: i10`, `PeriodMs: i12` |
| HelloProof | `cd /home/hhh/repos/ship-of-theseus/HelloProof/sample && Composer compile HelloWorld.fidproj -k && echo Houston \| ./targets/helloworld; cvc5 --lang=smt2 targets/intermediates/06b_obligations.smt2 \| sort \| uniq -c` | prints `Enter your name: Hello, Houston!`; `23 unsat` |
| BAREWire tests | `cd /home/hhh/repos/BAREWire && dotnet run --project tests/BAREWire.Tests.fsproj` | `309 passed, 0 failed` |
| Harness | `cd /home/hhh/repos/Composer/samples/dimensional && ./vet.sh --through 3` | exit 0; `30 of 49 rows match today; 23 of 23 judged rows`; every judged row identical to the previous run unless the changeset says which row moves and why |
| Placement | `test ! -d /home/hhh/repos/Composer/src/MiddleEnd/PSGElaboration; grep -rn "PSGElaboration" /home/hhh/repos/Composer/src --include=*.fs; grep -rn "V (" /home/hhh/repos/Composer/src --include=*.fs \| grep -v Traversal/Values.fs` | the folder is absent; no references; the only `V (` outside `Values.fs` is the pattern match in `Serialize.fs` |

MLIR text is not a byte-identity gate: value names carry the node id. Compare shapes (signatures, struct types, widths) when a change should leave them alone; the layouts of BAREWire's wire records are the standing example.

## 6. Next, in order

1. **Step 5: access kind and region are checked (the M rows).** Settled, not open; every sentence here has a source, and an agent does not re-open any of it.
   - *What `Ptr` is.* `clef-lang-spec/spec/access-kinds.md` and `memory-regions.md` define `Ptr<'T, 'Region, 'Access>`, a one-word typed handle to a cell. Its region is one of `Stack`, `Arena`, `Peripheral`, `Sram`, `Flash` (memory-regions.md, "Region Types"); its access kind one of `ReadOnly`, `WriteOnly`, `ReadWrite` (access-kinds.md, "Access Kind Types"). It carries no extent. It is not the fat pointer: `TypeLayout.FatPointer` (address and length, two words; the five-word view on the CPU leg) is what an array, a string or an arena is, and needs nothing from this step.
   - *The rule.* `Dimensional_Vetting_Plan.md` §5, step 5, under decision D2 (§6): region and access are enumeration-sort components of type identity, compared by equality, never entering the measure unifier; there is no subtyping on either; a `ReadWrite` handle where `ReadOnly` is required passes only through `Ptr.asReadOnly` (`Ptr.asWriteOnly` for `WriteOnly`), coercions that are nodes in the graph, not rules in the checker; `NTUQualifiers` join type identity under the same rule.
   - *The diagnostics.* A write through `ReadOnly` is CCS8020 at the assignment site; a read through `WriteOnly` is CCS8021 at the dereference site; an access mismatch without the coercion is CCS8022; a region mismatch is CCS8100 (`error-handling.md`, as amended 2026-09-04).
   - *The gates.* The five M leaves under `Composer/samples/dimensional/`, each a reject and an accept program, `pending = "step 5"`, judged by `vet.sh --through 5`: M-1 no write through `ReadOnly` (CCS8020); M-2 no read through `WriteOnly` (CCS8021); M-3 access is identity, coercion only through `Ptr.asReadOnly` (CCS8022); M-4 region is invariant (CCS8100); M-5 every dimensional component is identity, unit, region and access, on `array<int, 4, Stack>` against `Sram` (CCS8100). Today every M leaf stops at CCS8706, `The type 'Stack' is not defined`, because `Ptr` and its region and access types are not type constructors CCS knows (`mkTypeConRefWithMeasures` has no caller; the samples call `Ptr.read` and `Ptr.write` on a bare `nativeint`), and `NTUQualifiers` are still excluded from identity (`NativeTypes.fs`, `Unify.fs`; the L-6 row of the vetting plan). Building the constructors, the identity rule and the four diagnostics is the step.
   - *Why it comes before CS-12's deletion.* CS-12 deletes `nativeint` with the width spellings (`Dimensional_Range_Design.md` §2). Every site that holds an address as a `nativeint` needs a typed handle to move to: `Ptr`, `Mmio` or `CHandle` (§2; `ffi-boundary.md` §1 for `CHandle`, the opaque non-null handle a C binding hands back). The ten `Fidelity.Platform` files that still spell `NativePtr.*` at 448 sites are replaced by `CHandle` and `Mmio` (the CS-11 note, "Found on the way").
   - *What `Mmio` is, and is not.* An MMIO register is a boundary row of §4.1: a value meeting the register's declared width. Its reader is built (step 1a): it reads the BAREWire Hardware `PeripheralDescriptor` and `StructDescriptor` a description carries. The `Mmio` handle type the spec names (`platform-bindings.md`, among the argument types a binding may take; the `Mmio.read` and `Mmio.store` intrinsics CCS recognises by module pattern) is unbuilt and waits on this step: "a register read through a handle is still the stop it is; only the descriptor is read" (the 1a as-built; the vetting plan: "the `Mmio` row waits on step 5"). W-5's leaf writes `Mmio.store reg8 300`. No new language surface is proposed for MMIO in this wave, and none is needed by any gate.
2. **Ruling 5, the sweep.** Hand-written sources only: `BAREWire/src`, CCS and its samples, the leaf's own files (`Fidelity.Platform/CPU/Linux/x86_64/*.clef`). Farscape bindings are regenerated by Farscape's own leg, never text-swept; generated outputs no gate compiles are deleted with their pilots kept. Each spelled use becomes `int` plus a declaration where a boundary genuinely exists and nothing where the range suffices. The sweep also bounds the source items ruling 3 left: a guard on `Decoder.readUInt`'s `shift`, declared maxima on `Validator`'s accumulations, and the `offset + n` returns of `writeBytesRaw` and `readBytesRaw`, each of which is a CCS8012 warning today.
3. **Ruling 5, the deletion.** CCS8706 for a spelling, CCS8018 for a suffix; CCS8019 and Composer's `Output.interimWarnings` deleted with the alias; `W-1/reject` turns green; the drift rows become failures.
4. **Ruling 6, promotion.** CCS8011 an error on every substrate once RoundTrip, HelloProof and every harness leaf carry none; `RangeAnalysis.heldWidthOf`'s interim word and `registerWidth` fallback deleted; `W-4/reject` judged. Projects outside the gates that still carry spellings fail loudly by design until regenerated.
5. **CS-13**, the reals: the interval domain, the selection objective, per-coefficient selection.

## 7. Owed, consolidated

From the as-builts, still open: a per-construction tuple fact on the graph (the type-level `int * int` join carries one unobservable position to every tuple of the type; owed since CS-10); a relational step for the `offset + n` shape, only if the owner rules one as a §1.2a change; the union residence criterion (`Placement.unionResidence` holds the leg's `result` rule; a structural criterion belongs with the union's layout hyperedge); the freestanding leg's syscall emission (`ResolvedBinding.Syscall` names the operation, the number is the description's, no asm is emitted); `mapNTUKindToMLIRType`'s graph-less spelled arm (dies at promotion); pointer-width spellings aliasing `int` ahead of step 5; CCS8014 at interior spelled values (reported at bindings and parameters only); `Fmt.ofInt64`'s CCS8012 (BAREWire's to bound in the sweep); `sqrt`, `atan2` and the transcendentals typed but unwitnessed (CS-9); the `for i in a .. b` defect a CS-10 probe found; Farscape's validation at the regeneration horizon (its maturation plan §9); the flat-closure target form of `Closure_Retooling_Plan.md`.

## 8. Code map

| Concern | CCS (`clef/src/Compiler/`) | Composer (`Composer/src/MiddleEnd/`) |
|---|---|---|
| The range of every integer node, `FieldRanges`, `ElementRanges`, CCS8011/8012/8014/8016, selection | `PSGSaturation/SemanticGraph/RangeAnalysis.fs`; sources and declarations in `NativeTypedTree/Expressions/Intrinsics.fs` (`RangeSources`) | reads: `Alex/CodeGeneration/TypeMapping.fs` (`nodeWidth`, `elementWidth`, `settledLayout`), `Alex/XParsec/PSGCombinators.fs` (`narrowType`, `adaptOperand`) |
| Settled layouts (records, unions, tuples, options, Results, closures), union residence | `PSGSaturation/SemanticGraph/Placement.fs` | reads through `TypeMapping.settledStruct`, `RecordPatterns`, `MemoryPatterns`, `LambdaWitness` |
| The platform's declaration: widths, representations, contracts, endpoints, wire fields, peripheral registers, binding descriptors | `PSGSaturation/SemanticGraph/PlatformResolution.fs`, `PlatformDeclaration.fs`; `PlatformContext` in `NativeTypedTree/NativeTypes.fs` | `MLIRGeneration.architectureOf` reads the ISA and the two widths into `Architecture` |
| Meets (width adaptations at consumers), return meets | `SemanticGraph/Meets.fs` → `Codata.Meets`, `Codata.ReturnMeets` | `TransferTypes.meetFor`, `PSGCombinators.meetOp`/`adaptOperand`, `BindingWitness`, `LambdaWitness` |
| Curried chains flattened, partial and saturated applications | `SemanticGraph/Curry.fs` → `Codata.Curry` | `ApplicationWitness`, `BindingWitness`, `VarRefWitness`, `NanopassArchitecture` |
| Escape of allocating sites | `SemanticGraph/Escape.fs` → `Codata.Escapes` | `TransferTypes.escapeOf`; `MemoryPatterns.pAllocValue`, `LambdaWitness` |
| Platform call sites, runtime mode, linked libraries; pins | `SemanticGraph/PlatformBindings.fs` → `Codata.Bindings`, `Codata.Pins` | `PlatformPatterns`, `MLIRNanopass`, `XDCTransfer`, `HardwareModuleWitness` |
| Declaration roots' lambdas | `SemanticGraph/Roots.fs` → `Codata.DeclarationRootLambdas` | `LambdaWitness`, `NanopassArchitecture` |
| Value names | none | `Alex/Traversal/Values.fs` |
| Diagnostic codes and severities | `NativeTypedTree/Expressions/Types.fs` (`DiagnosticCodes`), the spec's `error-handling.md` table | `CLI/Output.fs` (`interimWarnings`, the `--warnaserror` switch) |

## 9. The as-built template

```
## <Changeset>, as built (<date>)

<One paragraph: who built it, how it was gated, what it delivers.>

**What landed, by file.** <CCS files, then Composer, then other repos; each with what changed and the section or ruling it follows.>

**Gates.** <Each gate of §5 with the observed result and counts, from this run's transcripts.>

**Decisions, for the owner.** <Numbered; each a question with the facts and a recommendation.>

**Owed.** <What this changeset leaves open, and to which step.>
```

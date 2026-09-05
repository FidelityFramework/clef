# Dimensional Vetting Plan

> How the Clef Compiler Service comes to check dimensional types fully: what the design requires, what the
> checker does today (measured, with citations), the program set that decides the gap, and the hardening
> steps in order. Design of record, 2026-09-04. Companion to [PSG_to_PHG_Plan.md](PSG_to_PHG_Plan.md) and the
> [Design_Supersession_Register](Design_Supersession_Register.md). The user's diagnosis that opened this work:
> "the dimensional types are not really type-checking correctly, or at least not fully." The finding that
> confirms it: units of measure are parsed and then discarded, which the user has ruled vestigial. Units are
> integral to the Native Type Universe; their dropping is a course correction, not a feature request.

## 0. The position

Dimensions are part of type identity and are never erased by the checker. CCS infers them, checks them,
and resolves the platform-dependent ones against the platform description at saturation, per
program-graph section; the resolved values ride on the PSG as annotations, Alex reads them, and they are
dropped only at native emission, where they become debug metadata and never touch the instruction stream
(DTS/DMM §1.1, §2.3). This is the same rule that settled closures, obligations and layout: the graph
decides, the witness observes. One text in the corpus still says otherwise and is corrected as part of
this plan (step 6): `ntu-types.md` §1 ("type WIDTH is an erased assumption"; "resolved by Alex via
`PlatformContext`"), §1.1, §3.2, §3.3, §7.1 and §9.2 place resolution below the witness boundary, against
that chapter's own §2.1 and §5.1. `ntu-dimensional-architecture.md` §4.3 and §5.2 and the
`NativeTypes.fs:69-72` comment already state the rule (both corrected 2026-09-04); the plan's earlier
citation of them as inverting the design is withdrawn, while `NativeTypes.fs:658` and `:663` ("Alex
resolves to concrete size via platform quotations") still invert it. The platform description is always
present (there is no target-free compilation), so cross-apply at saturation is always available;
`PlatformContext.resolveWidth` already lives in CCS (`NativeTypes.fs:443-448`), and the layout literals
depend on it.

## 1. The dimension families and their normative sources

| Family | What it is | Algebra | Normative source |
|---|---|---|---|
| **Units of measure** | the physical dimension of a numeric value, `float<m s^-1>` | finitely generated free abelian group: addition requires equal dimensions, multiplication adds exponent vectors, division subtracts; inference is HM extended with dimension variables, complete, principal, decidable | DTS/DMM paper §2.1–2.2 and Appendix C (the annotated `computeForce`); spec `units-of-measure.md` (relations, normalisation, constraint solving, generalisation); the chapter's erasure passages (line 12, §Measure Parameter Erasure) describe F#'s early erasure and are superseded by DTS/DMM §2.3 |
| **Width** | the bit width of an integer or the representation of a real | lattice family, not a group: a bounded interval domain, meet-directed, propagated through the PSG dataflow to a least fixed point and never unified; the width is derived from the analysed range and selected from the representations the platform declares; there is no width-named type, no seal and no conversion (D10, `Dimensional_Range_Design.md` §0) | `width-inference.md` §1, §3, §5, §10; `numeric-selection.md` §2; GA-02 §2, §7.1 |
| **Memory space and access kind** | where a value resides and how it may be accessed, `Ptr<'T, 'Region, 'Access>`, `NTUMemorySpace`, `NTUAccessPattern` | an enumeration sort in the SMT sense, not a group: solved by equality unification over a finite domain in the same inference pass; every component is invariant and there is no subtyping (D2); a `ReadWrite` handle where `ReadOnly` is required passes only through the explicit coercion `Ptr.asReadOnly`, a node in the graph, never a checker rule | DTS/DMM §2.5; `arxiv-papers/research/grade-axis/01` §7 (identity check); `access-kinds.md` §Access Kind Coercion and §Diagnostics (`CCS8020`–`CCS8022`); `memory-regions.md`; `platform-bindings.md` §Program-Lifetime Spaces. `ntu-dimensional-architecture.md` §7.2's "covariant access" is an open question superseded by D2 |
| **Representation** | which concrete numeric format realises a dimensioned range on a target (IEEE, posit, fixed-point) | a deterministic function of the dimensional range and the target's covering set (the argmin with coverage and ulp floor) | DTS/DMM §2.6; `width-inference.md` §4; `numeric-selection.md`; `grade-discipline.md` |
| **Alignment, tensor shape** | design only | | `ntu-dimensional-architecture.md` §2.4–2.5 |

Grade (the parity component of Clifford grade, valued in Z2) is a further generator the PHG paper carries;
it is out of this plan's first increment. When it enters, parity joins the measure algebra as a Z2 generator (the group is no longer free, DTS/DMM §2.1; the solver moves from Hermite to Smith normal form with the same signature), blade support enters as a lattice coeffect beside the range and never through the unifier, and the signature enters as a universe parameter of the algebra declaration (`Horizon_Requirements.md` C1, C2).

## 2. What CCS does today (measured)

Every row is a primary-source reading of `clef/src/Compiler/NativeTypedTree` as of 2026-09-04.

| Concern | Today | Where |
|---|---|---|
| Measured literal `1.0<m>` | the measure is discarded: "For now, just use the base type; measure annotation is tracked separately" (it is not tracked anywhere) | `Expressions/Literals.fs:42-46`; `:78` (`constToLiteral innerConst`) |
| Measured type syntax `float<m>` | `SynType.MeasurePower` resolves to the base type; the measure is dropped | `Expressions/Types.fs:948-950` |
| Representability of a measured numeric | the numeric constructors are built with `ParamKinds = []`: `float`, `int`, `posit32` have no slot in which a measure could sit, so `float<m>` and `float<s>` are the same `TApp(floatTyCon, [])` | `NativeTypes.fs:764-766` (`mkNTUTypeConRef`), `Types` module `:1378-1405` |
| Measure representation | `Measure = MVar \| MCon \| MProd \| MInv` exists (no exponent normalisation, no `MOne` in the DU though the unifier matches `MOne`) | `NativeTypes.fs:994-998` |
| Measure unification | never binds a variable ("we'd need a proper measure representation ... for now mark as used"), never unifies a bound variable, compares products structurally (so `m s` and `s m` differ), and every other mismatch falls to `\| _ -> ()`: it succeeds | `Unify.fs:251-286` |
| `HasMeasure` constraint | a no-op (`ignore ...; Ok ()`) | `Unify.fs:379-382` |
| Arithmetic operators | `'T -> 'T -> 'T` with a fresh unconstrained type variable: no numeric constraint (`true + true` types), and equal operand types, which is the wrong shape for measures (`float<m> * float<s>` must be `float<m s>`, never `'T -> 'T -> 'T`) | `Expressions/Intrinsics.fs:817-822`; comparison `:823-827` |
| Named widths | distinct type constructors (`int`, `int32`, `int64`, `nativeint` ...), so mixed named widths are rejected by name equality in `unify`; unsuffixed literals are `Register` width; no range analysis exists anywhere | `Types` module; `Literals.fs:63-74`; `Unify.fs:86-92` |
| Width resolution | `PlatformContext.resolveWidth` resolves `Pointer`/`Register` for layout, inside CCS; the file comment says the opposite | `NativeTypes.fs:443-461` vs `:69-70` |
| Memory space and access qualifiers | `NTUQualifiers` exist but are explicitly excluded from type identity ("types with different placement qualifiers unify as the same type") | `NativeTypes.fs:248`; `Unify.fs:86-88` |
| `Ptr<'T, 'region, 'access>` | region and access are measure parameters (`mkTypeConRefWithMeasures`), so they pass through the never-failing measure unifier | `NativeTypes.fs:725, 760` |
| Access-kind diagnostics | none are emitted anywhere; the collections chapters' VC-RO cites `CCS8020`, which the checker does not know | grep of `NativeTypedTree/`, `PSGSaturation/`: only `FS8000`, `FS8010-8013`, `FS8500` |
| Diagnostic series | the code's codes are `FS8xxx` (`FS8000_TypeMismatch` ...); the spec's are `CCS8xxx` (`access-kinds.md` §Diagnostics); clef's former `ccs-specification.md` Appendix D (retired 2026-09-04) listed `FS8xxx` | `Expressions/Types.fs:39-45`; `NativeService.fs:1878` |
| Verdict mechanism | `composer compile` prints CCS diagnostics to stderr as `location: error CODE: message` and exits 1 on errors | `Composer/src/CLI/Output.fs:84-120`, `Program.fs:67-71` |

Summary: the width family is checked by name and resolved in the right place; units of measure are not
checked at all and cannot be represented; memory space and access kind are not checked at all; the diagnostic
vocabulary is on the wrong series. That is the gap, and it is structural (representation and operator
types), not a missing branch.

## 3. The vetting rules and the program set

Each rule has a minimal program that must be rejected and one that must be accepted. The set lives at
`Composer/samples/dimensional/<rule>/{reject,accept}/` (a `.clef` file, a `.fidproj` cloned from
`BAREWire/samples/RoundTrip/RoundTrip.fidproj`, and an `expect.toml` naming the verdict, the diagnostic code family and the range).
The verdict table is rule → expected → actual; a rule is green when both programs report as expected.

| Rule | Statement | Reject | Accept | Code | Today |
|---|---|---|---|---|---|
| UoM-1 | addition and subtraction require equal dimensions | `1.0<m> + 1.0<s>` | `1.0<m> + 2.0<m>` | `CCS8040` (measure mismatch) | accepted (measure dropped) |
| UoM-2 | multiplication adds exponent vectors | `let x : float<m> = 2.0<m> * 3.0<s>` | `let a : float<m s> = 2.0<m> * 3.0<s>` | `CCS8040` | reject not detected; accept mis-typed |
| UoM-3 | division subtracts exponent vectors | `let v : float<m> = 6.0<m> / 2.0<s>` | `let v : float<m/s> = 6.0<m> / 2.0<s>` | `CCS8040` | as above |
| UoM-4 | an unannotated numeric literal is dimensionless (`float = float<1>`, `units-of-measure.md` §Measures; the paper's Appendix A step 1, which gives a bare literal a fresh dimension variable, is superseded by its Appendix C, which annotates the constant); a dimensionless factor scales without changing dimension | `let x : float<s> = 2.0 * 3.0<m>` | `let x : float<m> = 2.0 * 3.0<m>` | `CCS8040` | as above |
| UoM-5 | measures normalise as an abelian group | `let x : float<m> = 1.0<m s> / 1.0<m>` | `let x : float<s> = 1.0<m s> / 1.0<m>`; `let y : float<m s> = 1.0<s m>` | `CCS8040` | structural compare only |
| UoM-6 | comparison requires equal dimensions: comparison is typed at one measured type on both sides (`IComparable<float<'u>>`), so `<` on `float<m>` and `float<s>` fails measure unification | `if 1.0<m> < 1.0<s> then ...` | `if 1.0<m> < 2.0<m> then ...` | `CCS8040` | accepted |
| UoM-7 | annotation and inference agree at calls | `let f (x: float<m>) = x` then `f 1.0<s>` | `f 1.0<m>` | `CCS8040` | accepted |
| UoM-8 | generalisation: a dimension-polymorphic function is used at two dimensions | (none) | `let scale f v = f * v` used at `(float, float<m>)` and `(float<s>, float<m>)`, inferred `float<'u> -> float<'v> -> float<'u 'v>` | | measure variables never bound |
| UoM-9 | the paper's example infers its result without a return annotation | `let computeForce (m1: float<kg>) (m2: float<kg>) (r: float<m>) = let g = 6.674e-11<m^3 kg^-1 s^-2> in g * m1 * m2 / (r * r)` applied as `computeForce 1.0<m> 1.0<kg> 1.0<m>` | the same definition, inferred `float<kg> -> float<kg> -> float<m> -> float<kg m / s^2>`, applied as `computeForce 1.0<kg> 1.0<kg> 1.0<m>` (Appendix C; Appendix A as written, with a bare `g`, generalises to `float<'a> -> float<'b> -> float<'c> -> float<'a 'b / 'c^2>` under UoM-4 and accepts a `float<m>` mass) | `CCS8040` | not inferable |
| W-1 | there is no width-named type and no width suffix: one integer kind `int`, one real kind `float`, each with a dimension; the width is the analysed range's (D10) | `let f (x: int32) (y: int64) = x + y` | `let f (x: int) (y: int) = x + y`; `let a = 1 + 1` | `CCS8706` ×2 (the suffix case `1L` is `CCS8018`) | rejected today, as CCS8706 since CS-8 |
| W-2 | operands of `-`, `*`, `/`, `%` are numeric; operands of `+` are both numeric or both string (D5), never `bool` | `true + true`; `true - true` | `1 + 2`; `"a" + "b"` | `CCS8000` | accepted |
| W-3 | a boundary width comes from the platform description, resolved in CCS at saturation, never in the witness | (differential: `type Pair = { Addr: Ptr<int, Stack, ReadOnly>; Tag: int }` with `Tag`'s range `[1, 1]`, compiled under x86_64 Linux and the Cortex-M33 leaf: `Addr` 8 then 4 bytes, `Tag` 1 byte on both; `expect.toml` names both layouts) | | layouts | needs step 5's `Ptr` and CS-12 |
| W-4 | no silent default: an integer whose range is unobservable is a diagnostic; a bounded one is not; a bare real lowers to `f64`; a dimensioned real with an unobservable range is a diagnostic at the dimensioning seam naming the bare source | `let rec run n = run (n + 1)` | `let f (n: int) = if n < 1000 then n + 1 else 0` | `CCS8011` | accept compiles; reject accepted (no range pass) |
| NS-1 | dimensioning seam (reals): a bare real with an unobservable range lowers to IEEE `f64` without error and still carries range propagation; an unbounded bare real flowing into a dimensioned context fires at the dimensioning boundary and names the bare source (`numeric-selection.md` §6, §6.1, §13.7–13.8) | `let y (bareInput: float) (oneNewton: float<N>) : float<N> = bareInput * oneNewton` with `bareInput` unbounded | `let y (bareInput: float) = bareInput * 2.0` | numeric-selection family code (peer of the width codes, §11), allocated with the D3 table; gated by step 8 | nothing exists; the real interval domain "does not yet exist in the integer twin" (§3.1) |
| NS-2 | coverage-empty: no offered representation covers the dimensional range | `astronomicalDistance<m>` with range `[1e-11, 1e72]` on a posit-only target | the same on a target offering `f64` | numeric-selection family, Warning promoted under `--warnaserror`; selection falls to the argmin over the full offered set with the uncovered range recorded (§2.1, §13.2 as amended) | nothing exists |
| NS-3 | tier disagreement: an observed dataflow range not contained in the binding claim (`R₁ ⊄ R_binding`) is a diagnostic, never a change to the binding range (§3.4 item 3, §13.5) | a `Fidelity.Physics` range narrower than a literal the dataflow proves | contained | numeric-selection family, Warning promoted under `--warnaserror` (§13.5 as amended) | nothing exists |
| NS-4 | a covering-but-suboptimal seal compiles and is witnessed with the representation the open argmin would have chosen (§13.9) | (none) | a `float64` seal on a near-unity range on a posit target: accept with the design-time witness | numeric-selection family, Info | nothing exists |
| W-5 | a boundary's declared representation must cover the analysed range; intended loss is written as arithmetic (`%`, `clamp`) and never as a conversion | `Ptr.write reg8 300` with `reg8 : Ptr<int, Peripheral, WriteOnly>` an 8-bit register the Contracts leaf declares (range `[300, 300]`) | `Ptr.write reg8 (v % 256)`; `Ptr.write reg8 (clamp 0 255 v)` | `CCS8012` (Warning, promoted under `--warnaserror`) | needs step 5's `Ptr` and CS-12 |
| W-6 | width is propagated, never unified: a non-`inline` function is one body whose parameter range is the join over its call sites; a call site carries its own range only under explicit `inline` | (none) | `let g x y = x + y` used at `g 1 2` and `g 100000 200000` in one program: one body at the joined range `[2, 300000]` | accept, one emitted body | accept compiles today |
| M-1 | no write through a `ReadOnly` handle | `let w (p: Ptr<int, Flash, ReadOnly>) = Ptr.write p 0` | `let w (p: Ptr<int, Stack, ReadWrite>) = Ptr.write p 1` | `CCS8020` | `Ptr<'T, 'Region, 'Access>` is not a type constructor CCS knows: `mkTypeConRefWithMeasures` (`NativeTypes.fs:762`) has no caller, `Ptr` appears only in a comment (`:727`), and the samples call `Ptr.read`/`Ptr.write` on a bare `nativeint` (`stm32l5-blinky/STM32L5.fs:92-94`), so there is no access component to check |
| M-2 | no read through a `WriteOnly` handle | `let r (q: Ptr<int, Peripheral, WriteOnly>) = Ptr.read q` | `let r (q: Ptr<int, Peripheral, ReadWrite>) = Ptr.read q` | `CCS8021` | as M-1: no `Ptr` type constructor exists in CCS |
| M-3 | access is part of identity, no subtyping: a `ReadWrite` handle where `ReadOnly` is required passes only through the explicit coercion `Ptr.asReadOnly` (`Ptr.asWriteOnly` for `WriteOnly`), a node in the graph rather than a rule in the checker | `let ro : Ptr<int, Stack, ReadOnly> = rw` with `rw : Ptr<int, Stack, ReadWrite>`; `let rw2 : Ptr<int, Stack, ReadWrite> = ro` | `let ro : Ptr<int, Stack, ReadOnly> = Ptr.asReadOnly rw` | `CCS8022` | as M-1; `ntu-dimensional-architecture.md` §7.2 (Prospective) still says "covariant", superseded by D2 |
| M-4 | region is invariant: an enumeration sort unified by equality (DTS/DMM §2.5) | `let f (p: Ptr<int, Peripheral, ReadWrite>) = Ptr.read p` then `f stackPtr` with `stackPtr : Ptr<int, Stack, ReadWrite>` | `f gpioReg` with `gpioReg : Ptr<int, Peripheral, ReadWrite>` | `CCS8100` (region mismatch; `error-handling.md` §Diagnostics as amended 2026-09-04) | accepted |
| M-5 | every dimensional component is part of identity (D2): unit, region, access | `let f (b: array<int, 4, Stack>) = b` applied to `s : array<int, 4, Sram>` | same region | region code as M-4 | `NTUQualifiers` are excluded from identity (`NativeTypes.fs:248`, `Unify.fs:86-88`); no surface form carries a memory space on a numeric (`ntu-dimensional-architecture.md` §2.2 is marked Design), so the numeric-carried row joins the set when §2.2 leaves Design |

The W rows follow D1 as closed by D10 (`Dimensional_Range_Design.md` §0): one width regime, the range
a coeffect propagated by interval arithmetic and composed with declared claims by precedence; no
written width, no seal, no conversion. The NS rows are the real-valued family of `numeric-selection.md`,
gated by step 8. The design for steps 1 and 2 is `Dimensional_Step1_2_Design.md`; for steps 3, 7 and 8
it is `Dimensional_Range_Design.md`, the one statement; the ranged-type position is
`Types_As_Ranges_Position.md`; the requirements the horizons impose are `Horizon_Requirements.md`.

## 4. The harness

- `Composer/samples/dimensional/vet.sh` compiles every `<rule>/<verdict>/*.fidproj` with
  `composer compile <fidproj>` (intermediates on request, `--intermediates`, since keeping them costs
  about a minute per leaf and changes no verdict), records the exit code and the stderr diagnostics, matches the
  `expect.toml` (`verdict = "reject" | "accept"`, `code = "CCS8040"`, optional `range = "L:C-L:C"`), and
  prints the rule table with a final count. It never calls `tests/regression/Runner.fsx`.
- A rejected program is green only if the expected code appears; an accepted program is green only if the
  exit code is 0 and no error is printed. Warnings are reported, not judged, until the representation rules
  land.
- The RoundTrip native gate (`BAREWire/samples/RoundTrip`, diffed against its `expected.txt`) and the HelloProof baseline (23 obligations, 29 hyperedges, 23 unsat) run
  alongside; the drift gate runs after every step.

## 5. Hardening steps, in order, each gated by the table

0. **Remove C leakage** (the object lesson: `a-lesson-in-memory-safety.md`). Every path where a numeric
   representation is decided by a type name at one end and reinterpreted silently at the other, or where a
   conversion is inserted by a party other than the source, is removed or replaced by a diagnostic. The
   inventory, measured 2026-09-04:

   | # | Where | What it does | Class | Disposition |
   |---|---|---|---|---|
   | L-1 | `Literals.fs:63-64` (`constToLiteral`), `:36-51` (`typeOfConst`) | an unsuffixed integer literal is minted at `Resolved Register`, i.e. sealed to the platform word | C's `int` = whatever the register holds | with step 7: a literal is bare with a point range and takes a seal only from context |
   | L-2 | `Literals.fs:42-46` | the measure on a literal is discarded | implicit measured-to-dimensionless conversion | step 1 |
   | L-3 | `Literals.fs:49-51` | `UserNum "I"` (bigint) and any unknown suffix become `intType` "for now" | fabricated representation, silent | done 2026-09-04: `CCS8018` unsupported literal suffix (`Literals.fs` `checkConst`, `Types.fs` `DiagnosticCodes`) |
   | L-4 | `Intrinsics.fs:953-976` | every conversion intrinsic is typed `'a -> Target` from a fresh type variable | the polymorphic `'T -> Target` coercion `width-inference.md` §7.3 forbids; `int x` accepts a string, a bool, a char | step 3: each conversion intrinsic is typed with a numeric constraint on its source and names its target seal, removing the `'a -> Target` shape (§7.3); step 7: the coverage check of the target against the source's analysed range and the stated-discipline requirement (§7.1–7.2), which need the range coeffect |
   | L-5 | `SRTPResolution.fs:290-410` | a `ConversionCategory` and an MLIR op name are computed and discarded (`_category`, `_mlirOp`); int-to-int is always `Widening`; int-to-int always `extsi` ("for narrowing should be trunci"); unknown falls to `fidelity.convert`; header cites `spec/drafts/NTU_Conversion_Model.md`, which does not exist (retired by `width-inference.md` §9) | dead code shaped like a decision; a dangling citation | done 2026-09-04: category, op-name and citation deleted; only the witness naming remains |
   | L-6 | `Unify.fs:86-88` | placement qualifiers excluded from identity | implicit conversion between memory spaces | step 5 (D2, M-5) |
   | L-7 | `Composer/.../Alex/Patterns/ApplicationPatterns.fs:183-233` (FPGA leg) | the witness widens both operands to the max width with `pExtSI` regardless of the source's signedness, and truncates the result; HelloArty's `07_output.mlir:116` shows `arith.extsi %periodMs : i13 to i30` | the FreeBSD class: the party that widens is not the party that knows the sign | not live today only because of L-7b; the two are removed together in step 7: width from the range per `width-inference.md` §3, extension op from the range's signedness (`extui` for a non-negative range), both settled in the graph |
| L-7b | `Composer/.../PSGElaboration/IntervalAnalysis.fs:88-113` (`minSignedBits`, `bitsFromInterval`) | every interval gets a sign bit, non-negative ones included (`[0, 4000]` becomes 13 bits, not 12); `IsSigned` is recorded false but the bit is spent | the spec formula (§3: unsigned `ceil(log2(b+1))`) is not what runs; the spec's own example table (31/21/10/13) and HelloArty's README carry the +1 figures, while the two site posts claim 29/11 | step 7; and a spec rough edge to report: `width-inference.md` §3's table contradicts its formula |
| L-8 | `ApplicationPatterns.fs:236-249` (CPU leg) | shift amounts "typed `int` by the front end" are truncated or zero-extended to the operand width by the witness | conversion inserted below the graph; the comment admits the front end typed it wrong | step 3: the front end types the amount; no witness cast |
   | L-9 | `ApplicationPatterns.fs:449-490` (`pTypeConversion`) | int-to-int truncation with no range check; float-to-int with no rounding or saturation discipline; int-to-float always `sitofp` even for unsigned sources; the result type resolved by `mapNativeTypeWithGraphForArch` in Alex | Alex deciding; `width-inference.md` §7.2 requires a stated discipline | step 3: the conversion node carries source seal, target seal, discipline and fidelity; Alex transcribes |
   | L-10 | `Alex/XParsec/PSGCombinators.fs:104,120` | CPU leg defaults an unresolved width to the platform word; FPGA leg throws `FPGA0001` | silent default on one leg, a thrown string on the other | step 7 (W-4) |
| L-11 | `NativeService.fs` `parseString` (clef); `Core/CompilationOrchestrator.fs` `requireCleanDiagnostics` (Composer) | the parser reported through the thread-installed logger, which the parse function never installed, so every parse error went to the discarding default logger; the checker then received a damaged tree and the failure surfaced as "No declaration roots found in PSG" or a witness error with no code | the FreeBSD class in the front end: a failure decided by the wrong party and reported by none | done 2026-09-04: the capturing logger and the Parse phase are installed for the parse, every error-severity diagnostic is rendered with its range, Composer prints them and stops with "Compilation failed with N parse error(s)"; the parser family's CCS codes land with the step-4 table |
| L-12 | `NativeTypes.fs` `NativeLiteral.BigInt`; `MatchRecipes.fs`; Composer `SSAAssignment.fs` | a `BigInt` literal case with no producer, mapped to `int64` "for now" in two places | fabricated representation | done 2026-09-04: case and both arms removed, Composer's arm with them |
| L-13 | `Project/ProjectChecker.fs` `buildPlatformContext` | the width dimensions are derived from one `WordSize` (`Some 64` or `Some 32`) and otherwise fall back to the x86_64 defaults; the platform description declares no dimension by name and no representation | silent default of a platform fact | done 2026-09-04 (CS-7b, D8): the descriptor's `TargetCore` declares `Widths` by name and `Representations` with capability, exact range and boundary (BAREWire `Platform/Description.fs`, the Contracts twin); `PlatformResolution` reads them structurally and `PlatformDeclaration.fill` writes `PlatformContext.Dimensions`/`Representations` once, at the saturation entry; `word_size`, `PointerAlign`, `defaultLinux_x86_64` and `fromPlatformPath` are deleted (a leftover `word_size` key is CCS8205 information); an undeclared dimension is CCS8203 and an unoffered representation CCS8204 at the first reachable site; Composer's `platformWordBits`/`platformWordType` read the context's `Register` and fail with CCS8203's text when absent. Residual for L-10: Alex's `platformWordWidth arch` table in TypeMapping/SSAAssignment is checked against the declaration at `MLIRGeneration.generate` and stops the build on disagreement; it is retired with step 7. Review fixes: the declaration's own defects are CCS8206 (unreadable element), CCS8207 (tag outside its vocabulary, no bits, duplicate name, Register disagreeing with `WordSizeBits`) and CCS8208 (a second description of one form among the binding's sources) at the declaring node, before any site; a dimension-named seal resolves by (family, bits), never by a synthesised name; the reader follows a quotation and reads only the binding's own sources |
| L-14 | `Expressions/Types.fs` `resolveSynType` | a type name that resolves to nothing became `TError`, and `Unify.fs` unifies an error type with anything, so an unknown type in an annotation was silently accepted and surfaced, if at all, as a witness error below the graph (`Expr<...>` on every quoted descriptor; `array<byte, 'n, Stack>` on the M rows) | silent failure in the front end | done 2026-09-04 (CS-8): CCS8706 at the annotation, the one report of that failure; the M rows' first printed error is now that located diagnostic |

   Items marked "now" have no dependence on the rewrite and were removed first (L-3, L-5, L-11, L-12 on
   2026-09-04, each gated by a Composer build and a byte-identical RoundTrip); the rest are removed by
   the step that replaces the path, so no conversion is ever re-implemented in its current shape.

1. **Measures are representable and survive.** Give the NTU numeric kinds a measure component (the
   design's "type variables carry an associated dimension variable"): a normalised exponent map over the
   declared base measures plus measure variables, carried on the numeric type, not as a positional `TApp`
   argument; `Literals.fs` keeps the measure of a measured literal; `Types.fs` resolves `MeasurePower` and
   `App` measure syntax into it; `[<Measure>] type` definitions and abbreviations enter the environment
   (`units-of-measure.md` §Measure Definitions). Gate: UoM programs parse to distinct types.
2. **Measure unification is the abelian-group algorithm.** Replace `unifyMeasure` with unification over
   exponent vectors with measure variables (Kennedy's algorithm: normalise, eliminate, bind), failing with
   `CCS8040` and presenting measures in the spec's normalised form; `HasMeasure` removed (under D4 no
   source form produces it; the fact it would carry is `TNum` equality, decided in one place); generalisation of
   unbound measure variables at `let` (§Generalization of Measure Variables). Gate: UoM-1, -5, -6, -7, -8.
3. **Operators and the kind functions.** Specified by `Dimensional_Range_Design.md` §1.2, §5 and §12
   (CS-9): a numeric constraint on every operator, `+` as kind dispatch (D5), unit equation and range
   image as separate obligations (`Horizon_Requirements.md` C5), the width conversion intrinsics deleted
   and `float`, `floor`, `ceiling`, `round`, `truncate` typed as kind functions with range images, shift
   amounts typed by the front end (L-8). Gate: W-2, UoM-2, -3, -4, -9.
4. **Diagnostics on the `CCS8xxx` series.** Rename the `DiagnosticCodes` module's values and clef's
   the retired Appendix D's occupants to the spec's series in `error-handling.md` and clef's `DiagnosticCodes`; add `CCS8040` (measure mismatch), `CCS8020-8022`
   (access), `CCS8003` (region). Gate: every rule's expected code exists in `DiagnosticCodes`.
5. **Access kind and region are checked.** Region and access measures unify under the rule of D2
   (region and access are enumeration-sort components, not measures: they compare by identity under D2, never enter the measure unifier, and a `ReadWrite` handle where `ReadOnly` is required passes only through `Ptr.asReadOnly`); writes through `ReadOnly` and reads through `WriteOnly` are
   diagnosed at the assignment and dereference sites; `NTUQualifiers` join type identity with the same
   rule. This is also what makes the collections chapters' VC-RO real. Gate: M-1 to M-5.
6. **Resolution stays in CCS, and the texts say so.** Rewrite `ntu-dimensional-architecture.md` §4.3 and
   §5.2 to "CCS resolves per section at saturation; Alex reads"; delete the `NativeTypes.fs:69-70` comment;
   confirm `TypeMapping.fs` in Composer reads `LayoutHint`/resolved widths rather than resolving. Gate: the layout differential is observed at step 7, when W-3 compiles (its accept program puts a bare literal into a sealed field, which needs the seal rule);
   the drift gate learns "resolved by Alex".
7. **The range, from the literal to the boundary.** Specified by `Dimensional_Range_Design.md` §0–§5,
   §8, §9 and §12 (CS-10, CS-11, CS-12): the range pass in CCS writing range and width coeffects; one
   integer kind and one real kind, the width-named types and suffixes deleted (D10) and the corpus
   migrated; coverage at declared boundaries (CCS8012 warning under `--warnaserror`, CCS8014, CCS8016);
   L-1, L-4, L-7, L-7b, L-8, L-9, L-10 retired; the drift gate's scheduled `TyCon` and spelling rows
   turned to failures. Gate: W-1, W-3, W-4, W-5, W-6; HelloArty's MLIR at the note's §8.2 figures.
8. **Representation selection.** Specified by `Dimensional_Range_Design.md` §3.2, §3.3 and §6 (CS-13):
   the argmin over the platform's declared real representations covering the range, the real interval
   domain of `numeric-selection.md` §9.1, per-coefficient selection, the coverage warning promoted by
   `--warnaserror`, the boundary-representation witness (CCS8014). Gate: NS-1 to NS-4 and the
   `numeric-selection.md` programs.

Steps 1–5 are the increment agreed on 2026-09-04; they precede every fan-out (closure retooling, suspension
recipe, sentinel collections, the Lattice server).

## 6. Decisions

Decided 2026-09-04, all five by the user (D1 re-derived from the design corpus and then confirmed).

- **D1, one width regime, not two (confirmed).** Sources: `width-inference.md` §1, §5, §6, §8,
  §10; `numeric-selection.md` §3 (tiers), §3.4 (precedence override), §6 (unobservable ranges), §6.1
  (the bare/dimensioned seam); the site posts *The Gift of Deferred Inference* and *FPGA and Hardware
  Inference*; HelloArty (`Behavior.clef:55-58` declares `Counter: int` and receives 31 bits by the spec's table (`width-inference.md` §3) and HelloArty's README, 29 by the spec's formula and the site posts, the discrepancy L-7b records;
  `docs/AutomaticPipelineInference.md` places the analysis in CCS and limits it to structurally certain
  facts). What they say: the type of a number is its kind (integer or real) and its dimension. Width and
  representation are not part of the type; they are coeffects derived from the analysed range per target at
  saturation, and a declared machine model is the established pattern for how a declaration meets an
  inference: the analysis runs regardless, validates the declaration, and a mismatch is a diagnostic. A
  written concrete width (`int32`, `uint8`, `float32`; the `posit<n, es>` form is the Level-3 escape hatch
  whose syntax is not yet specified, `numeric-selection.md` §8.1) is therefore a Tier-3 **seal**: a fixed
  representation `r` whose dynamic range `dynrange(r)` is read as the highest-precedence range claim `R₃`
  (`numeric-selection.md` §3.4 item 1), which turns the selector into a checker (the §2.1 coverage check on
  the singleton `{r}`, §5). The seal is not itself a range type: the value's type stays kind plus dimension
  (D4); the range, its width, its representation and the seal are coeffects beside the type
  (`width-inference.md` §5), never components of identity (D2), and never unified. `nativeint` is a seal
  whose width the platform description supplies. `int` is not a seal: it is the bare integer kind, the type of an unsuffixed
  literal (`expressions.md` §Constant Expressions, `86 // int/int32`), whose CPU realisation rounds to the
  native word (`width-inference.md` §8) and whose FPGA realisation is the inferred width. The two-regime
  reading in `native-type-universe.md` §2.3 (`int` = platform word; `int` and `nativeint` are synonyms) and
  `ntu-types.md` §2.2, §3.1, §6.1, §6.2 (`let x: int64 = 42 // Error: int ≠ int64`) is the text D1 retires,
  rewritten at step 6. Ada and VHDL are the precedent the site names (`dimensional-type-safety.md`
  §Historical Foundations; `doubling-down-dmm-dts.md`: derived types and physical types), and only for the
  pattern: a declaration is validated against an analysed fact and a mismatch is a diagnostic. They are not
  the precedent for where the range lives: Ada puts the range on the subtype, Clef infers it as a coeffect
  on the PSG (`width-inference.md` §1 lineage, §5) and keeps it out of type identity. The further Ada facts
  (`'Size` clauses, GNAT dimension aspects) are language facts not anchored in the corpus. Consequences: (1) two different seals
  meeting is an explicit-conversion site, so W-1 stands for seal against seal; (2) a bare operand meeting a
  sealed one is the §3.4 precedence composition: the seal's `dynrange(r)` is the binding range `R₃`, the
  bare operand's analysed range `R₁` (a point range for a literal) becomes the containment obligation
  `R₁ ⊆ R₃`, and a violated containment is the coverage diagnostic; this is monotone override, "not a
  lattice meet" (§3.4), and coincides with the grade-axis note's ordering check only in its verdict; so
  `1 + 1L` is accepted; (3) an unobservable range is an error for any integer and for a dimensioned real, and
  lowers to IEEE `f64` for a bare real, exactly as the two chapters state, and the seal at a boundary is
  supplied by the platform description (its word and pointer widths, `PlatformContext.Dimensions`) or by
  the `Fixed` widths the binding generator emits for C ABI types from `PlatformABI`
  (`ntu-dimensional-architecture.md` §2.1), or a range is supplied as the FPGA binding does; the platform
  supplies a seal only where its ABI governs the site (an exported parameter or return, an FFI or syscall
  argument, a pointer), and `int` itself carries no seal anywhere: it is the bare integer kind, so an
  exported `int` parameter on a CPU target is sealed by the calling convention's register width, while an
  internal `int` with no bound is W-4's diagnostic; the developer writes a seal by hand only there. No
  silent default at any point; (4) the CPU leg rounds a bare width up to the native size for arithmetic and
  never narrows below the range (`width-inference.md` §8); (5) the range that propagates from a sealed site
  is the binding range (`dynrange(r)` when no tighter source bounds the value); arithmetic on sealed
  operands yields a result whose range is the interval image, and re-sealing that result
  (`let z : int64 = x + 1L`) is a `width-inference.md` §7.2 site that must be covered or state a wrap or
  saturation discipline (W-4's wrap rule). Settled with the owner (2026-09-04): what an operation does at a representation's boundary is a declared fact of the target, carried by the platform description beside its representation set (wrap on a two's-complement ALU, saturate on a posit unit or a saturating DSP block, exact on fabric where the width came from the range); the language never discerns it from a cold start. The range coeffect is the analyzer: when the interval image of a sealed operation stays inside the seal's dynamic range nothing can wrap and nothing is said; when the range proves the boundary reachable, `CCS8015` fires as a warning promoted to an error under `--warnaserror`, naming the two knobs (bound the range, widen the seal) and the third, an explicitly saturating or wrapping operation written by the developer. The compiler selects nothing. Phase: `numeric-selection.md` §9 item 1 and
  `fixed-point-scaffolding.md` §4 say range analysis and selection run "during elaboration";
  `ntu-dimensional-architecture.md` §4.3 places platform-width resolution at Saturation. This plan runs
  range propagation in Elaboration where no platform fact is needed and closes it, with selection, at
  Saturation, because cross-application supplies the use-site and platform seals the addendum requires;
  the two chapters are reworded at step 6 and the drift register records it (R-12). The earlier
  recommendation to soften §10.1 is withdrawn; §10.1 stands as written. The interim
  `Composer/src/MiddleEnd/PSGElaboration/IntervalAnalysis.fs` reads no declared width, checks no seal, and
  records nothing for an unbounded value; the failure is raised later by the witness
  (`Alex/XParsec/PSGCombinators.fs:120`, `failwithf "error FPGA0001"`, FPGA only, CPU falls back to the
  platform word at `:104`), which is Alex deciding, in a non-CCS series, and its suggested fix `int<32>`
  puts a width in the slot D4 gives to the measure. The analysis moves to CCS as the range coeffect
  (step 7) and gains the seal check and the unbounded diagnostic there. The seal form is the named
  representation type in type position (`int32`, `uint8`, `float32`, `Posit32`; `numeric-selection.md` §5 as
  amended 2026-09-04) and the angle brackets stay the measure slot (`Posit32<newtons>`); only the
  rounding-or-saturation discipline of a lossy explicit conversion remains open (§14.1).
- **D1 addendum, the governing tension (stated by the user 2026-09-04).** Two commitments pull against
  each other and the design holds both: **no implicit conversions**, and **defer inference for as long as
  practical**, because cross-application in the hypergraph gathers more degrees of information than the
  tree ever could. They reconcile in one sentence: deferral is what removes conversions; it never
  introduces one. A representation is selected once, at saturation, after every source has been read
  (dataflow, library, platform, seals at every use site); a bare operand meeting a covering seal is that
  selection closing on the seal, not a conversion, because the bare value never held another
  representation. Where the gathered claims disagree (two seals on one value, a seal that does not cover
  the range, a range no source bounds), the diagnostic fires and names the sites; nothing is coerced. The
  object lesson is the FreeBSD `copy_from_kernel` bug in the site post *A Lesson in Memory Safety*
  (`clef-lang-site/hugo/content/blog/a-lesson-in-memory-safety.md:35-39`, `:65`, `:79`): a correct bound
  check defeated by the signed-to-unsigned reinterpretation C inserts at the `memcpy` boundary, with the
  representation decided by the type names at each end; in the discipline here signedness is derived from
  the range and there is no signed form of the length to smuggle. Any surviving implicit numeric
  conversion in CCS is C leakage and is removed as hardening step 0 (§5).
- **D2, dimensional identity (decided: exact match).** Two dimensional types are the same when every
  component matches: unit (compared in the spec's normalised form), region (the memory space of a
  `Ptr<'T, 'Region, 'Access>` or `array<'T, n, Region>` handle, an enumeration sort unified by equality per
  DTS/DMM §2.5), and access kind. There is no subtyping on any component: a `ReadWrite` handle where a
  `ReadOnly` one is required passes only through the explicit coercion `Ptr.asReadOnly` (`Ptr.asWriteOnly`
  for `WriteOnly`), a node in the graph rather than a rule in the checker; the word "narrowing" is not used
  here, being the spec's term for eliminating a foreign value at the JavaScript boundary. A seal is not a
  component of identity: under D1 it is the highest-precedence range claim on a value, propagated and never
  unified, so two seals meeting on one value is an explicit-conversion site (W-1) and a bare operand
  adopting a seal is not a mismatch. `ntu-dimensional-architecture.md` §7.2's "covariant access" is
  rewritten with step 6.
- **D3, diagnostic series (decided: CCS).** Every `FS`-prefixed code is retired, including the lexer and
  parser codes inherited from FCS (the spec's own `warning FS0058` example in `lexical-filtering.md`
  §Offside moves with them); a mapping table lands with hardening step 4 and clef's Appendix D moves with
  it. The table allocates inside the ranges `error-handling.md` §Error Codes fixes (CCS8000–8099 type
  system including access kinds; CCS8100–8199 memory management; CCS8200–8299 platform bindings;
  CCS8300–8399 effect system; CCS8400–8499 code generation) and never reassigns a code the spec has bound:
  `CCS8010` (null not permitted), `CCS8020`–`CCS8022` (access kinds), `CCS8030`–`CCS8033` (platform
  intrinsics), `CCS8040`–`CCS8104` (null-freedom). The measure family takes `CCS8040`–`CCS8050`, width and
  seals `CCS8011`–`CCS8018`, region mismatch `CCS8100` (the first code of the memory block, freed by removing the null codes from `error-handling.md`); the full list is in the step 1–2 design
  note, §(f).
- **D4, where the measure lives (decided: on the numeric type).** The measure is a component of the
  numeric type node, beside the range and representation annotations that accrue to it, as Ada's dimension
  aspect and VHDL's range constraint sit on the type rather than as a parameter. `float<newtons>` is
  Kennedy's surface syntax for that component, not a type-constructor application; `float` keeps arity 0,
  and bare `float` is the component at the dimensionless measure `1` (`float = float<1>`,
  `units-of-measure.md` §Measures), so a dimensionless operand unifies with `float<1>` and no special case
  exists. Measure-sorted parameters on non-numeric constructors (`Vector<[<Measure>] 'U>`,
  `Arena<[<Measure>] 'lifetime>`) remain and unify through the same measure unifier. The range is
  recorded beside the dimension on the same node (`numeric-selection.md` §13.10) and is not a second
  component of identity: dimension is unified (group family, Tier 1), the range is propagated (a coeffect,
  Tier 2 content), and the two meet only at the dimensioning seam (§6.1), where the dimension is the
  promise that a range exists and the obligation crystallises.
- **D6, ranged types (settled by the corpus, 2026-09-04; the horizon requirements find no choice on where the range lives, `Horizon_Requirements.md` C3).** The
  continuum the site names (point, range, distribution) is real and the corpus places the numeric type on
  it three times: a point is an interval of width zero (`width-inference.md` §2: a literal is `[a, a]`) and
  a posterior of variance zero (site only); a ranged value is one whose interval has positive width and
  whose representation the argmin chooses; the distribution end is designed only to the Gaussian case
  (`research/geometric-interchange/03`) and is the next stretch of the grade-axis work. What the corpus
  designs is that the range is a coeffect beside the dimension, propagated and never unified, and never a
  component of type identity (DTS/DMM §1.3, §2.6; `width-inference.md` §5; `numeric-selection.md` §13.10);
  "types as ranges" is therefore realised as the annotation on the numeric node, not as a new type
  constructor, and no surface form for a ranged integer or real is admitted (`RangeInt` on the site and the
  "ranged real" of `numeric-selection.md` §8 item 1 are not specified), so no vet program reaches for one.
  A written width is a representation read as a range claim (D1). The seven items the corpus designs
  completely but no spec chapter yet admits are listed in the ranged-type note beside the step 1–2 design
  note. The corpus leaves no choice open on where the range lives. The seal form and the phase wording are
  resolved (R-11, R-12); per-instantiation analysis with joined emission is recorded at W-6; the one
  residual is whether a coefficient's range is a marginal box or a projection of a joint manifold range
  (`research/fabric-inference/07`), which the spec answers "the coefficient's own analysed range" today and
  the research leaves as horizon-three work.
- **D7, implementation decisions for steps 1–2 (reframed 2026-09-04 after the owner asked to zoom out;
  pending the owner's word).** The changeset sequence (`Dimensional_Steps_1_2_Sequence.md`) found three
  places the design note leaves open for implementation. (U-1) Width before step 7: nothing in CS-1 to
  CS-8 redesigns width. It stays where it is today, in the numeric carrier and compared by name, until
  step 7's range coeffect exists to replace it; the plan already calls that "right result, wrong
  mechanism" for W-1, and every W row is gated at step 7. The sequence's phrase "an interim third
  component on `TNum` that the unifier compares" describes the same code and is withdrawn as a
  description, because it reads as putting width back into the type. (U-2) The stores: measure and
  carrier variables live in the store the type variables already use, kind-checked, with `resolve` the
  only read; a second, persistent store beside the existing mutable union-find would be two mechanisms
  for one fact, against one-place pull. The mutable union-find is retired once, by the PHG saturation
  lattice (PSG_to_PHG_Plan.md Phase 1), not here. `solveDim` itself stays pure over the values it is
  given (design note §b.2). (U-3) UoM-5 and UoM-8 turn on `*` and `/`, whose schemes the spec's operator
  table fixes; they are pulled forward into step 2's changeset CS-6 so step 2's gate stays as written.
  Corrected 2026-09-04: the schemes quantify over a carrier variable (`κ<'u> -> κ<'v> -> κ<'u 'v>`,
  design note §a.2, §c), and without it `let scale f v = f * v` cannot be typed for UoM-8, so CS-6
  carries the carrier variable too (`CarrierRef = Carrier of the interim per-width constructor |
  CVar`, `TypeParamKind.Carrier`, unified and generalised like a measure variable); the per-width
  constructor stays the carrier's value until step 7 (U-1). This is the design's own element
  arriving one changeset earlier than the sequence placed it, not a new decision.
- **D8, representations are declared by the platform description (decided 2026-09-04; lands at
  CS-7).** The language carries only a representation name (`int32`, `float64`, `Posit32`); the set
  of representations a target offers, each with its capability, dynamic range and boundary
  semantics, is declared by the platform description (`platform-bindings.md` descriptor
  requirements; `numeric-selection.md` §7, §9 item 6), and a seal spelling resolves against that
  declaration at saturation. The design note's §e.1 closed union of representation families
  (`FixedInt`, `PlatformInt`, `Ieee`, `Posit`, `FixedPoint`) is therefore not the end form: it is
  the vocabulary a declaration may use, and adding a family is a declaration, not a language
  change. This is the same move made for width dimensions (§7.1 of the architecture chapter).
  Addendum (the user, 2026-09-04): the descriptor is authored as a quotation, `<@ { ... } @>`, and stays
  so; the quotation is the type-carrying form over sources that are stringly typed or untyped. The
  compiler never evaluates it: the reader follows into the quotation node and reads the typed record
  inside structurally, by type name and field name, as it does a plain record. The spec's quotation
  sketches in `platform-bindings.md` are the design; the canonical Fidelity.Platform note's "not a
  quoted Expr" sentence is the drift to correct.
- **D9, quotations are intrinsic (the user, 2026-09-04; built in CS-8).** "I don't want to just make a
  Fidelity.Quotations as a reflex if it makes more sense to have it become intrinsic ... Since we're
  basically guaranteed to encounter it at every project I can't imagine it *not* be intrinsic"; the
  precedent is Alloy folded into the intrinsics and IcedTasks becoming Frosty, the default continuation
  model. So: `Expr<'T>` is a type constructor the compiler provides (`Types.exprTyCon`, resolvable in
  type position, the bare `Expr` denoting `Expr<_>`); `<@ e @>` and `<@@ e @@>` elaborate into the graph
  as a `Quote` node the compiler reads as data and never evaluates; a binding holding a quotation is a
  declaration, in no module-init or definition list, never entered by reachability from its module,
  and never witnessed; a reference to a quotation from executed code is CCS8066, a splice CCS8065; a
  reference from inside another quotation is structure and is legal. Quotation processing is the
  compiler's own: the structural reader for declarations (PlatformResolution today; binding and
  peripheral descriptors and predicates on the same reader) and, at step 8, the closed-form evaluator
  for range laws (`numeric-selection.md` §4). No quotations library, no `ReflectedDefinition`, no
  runtime tree. The inherited F# text of `expressions.md` "Quoted Expressions" and
  `type-definitions.md` "Conversion to Quotation Values" is rewritten to this; the two x86_64 leaf
  files that opened the F# quotations namespace no longer do.
- **D10, one integer kind, one real kind; the range selects the width (the user, 2026-09-04; the
  statement is `Dimensional_Range_Design.md`, which closes steps 3, 7 and 8 together).** "There is no
  int16, no int32 and no int64. There is just int with a specified width selection and the range
  determines which one is used." The value is a range until it is used and the range is known at the
  use, on every substrate: the FPGA rule is the general rule and the CPU differs only in selecting from
  the platform's declared set. No width-named type, no width suffix, no seal, no conversion syntax, no
  discipline syntax; intended loss is arithmetic (`%`, `clamp`, the rounding functions, `float`); a
  width is declared only by the platform description and by boundary declarations, and a value meeting
  a boundary is checked for coverage (CCS8012, warning under `--warnaserror`), never converted. D1's
  "a written width is a Tier-3 seal" and D7's "seal column" are retired by this decision; the per-width
  carriers are deleted. The rulings are quoted in the note's §0, and the note's §0.1 is the list of what
  is closed. Re-opening any item on that list is drift.
- **D5, `+` on strings (decided: concatenates).** `+` dispatches on the kind of its operands: on numerics it
  is the unit-unified add with a range obligation; on strings it is the concat recipe with an extent
  obligation. No proof complication follows, because each dispatch emits its own obligation family.

## 7. Corpus rough edges surfaced by verification, and their resolution

Resolved from the design on 2026-09-04 (the owner's rule: a table is not right because it exists; what
aligns with the design is kept, what does not is corrected). Spec edits are in `clef-lang-spec`; paper
items are reported, never edited.

| # | Where | Finding | Resolution |
|---|---|---|---|
| R-1 | `width-inference.md` §3 | the example table (31/21/10/13) carried the implementation's sign bit; the formula gives 30/20/9/12 | table corrected to the formula; a sentence added: a non-negative range spends no sign bit, extension follows the range's signedness, an implementation that adds a sign bit to every range does not conform (L-7b is that defect) |
| R-2 | `error-handling.md` | null codes `CCS8100`–`CCS8104` inside the memory block | removed; null-freedom has one diagnostic, `CCS8010`; `CCS8100` is region mismatch; the exception-style warning moves to the effect block as `CCS8300`; a sentence states the warning-plus-flag rule |
| R-3 | `ntu-types.md` §1, §1.1, §3, §4.1, §6, §7.1, §9 | width as identity, `int ≠ int64` by name, resolution and erasure attributed to Alex | chapter rewritten to the seal model: identity is kind and dimension; seals are coeffects, never unified; CCS resolves at saturation; Alex reads; nothing erased by the checker |
| R-4 | `native-type-universe.md` §2.3 | `int` = platform word; `int` and `nativeint` synonyms | rewritten: `int` is the bare integer kind, width from the range, word-sealed only at an ABI site; `nativeint` is the pointer seal; they coincide at the ABI and nowhere else |
| R-5 | `dts-dmm-paper.md` Appendix A step 1 vs Appendix C and §2.6 | a bare literal given a fresh dimension variable | paper: the design is Appendix C and the spec's dimensionless-literal rule; Appendix A step 1 is the rough edge, for the next publication cycle |
| R-6 | `ntu-dimensional-architecture.md` §7.2 | "covariant access" left open | answered: exact identity on every component, access invariant, coercion only through `Ptr.asReadOnly` |
| R-7 | clef `docs/fidelity/ccs-specification.md`, `native-type-universe.md`, `NTU_Type_System.md`, `From_FSharp_to_Clef.md` | FS codes, `!`/`:=` pointer forms, "regions form a subtyping hierarchy", a null-assignment error; three parallel copies of spec chapters | narrative doc corrected; the three parallel documents retired on the owner's word (2026-09-04), references redirected to `clef-lang-spec/spec` and `Baker_Saturation_Architecture.md` |
| R-8 | `units-of-measure.md` line 12, §Measure Parameter Erasure | F#'s erasure text | rewritten: the checker never erases; measures ride the graph and drop at native emission |
| R-9 | `decidable-by-construction.md` §2.2 | Z^7 as the dimension space | paper: base measures are declared, not fixed at seven (DBC §4.1's own currency example); for the amendment schedule |
| R-10 | `research/grade-axis/00` | two `../spec/` drafts cited that exist nowhere | research folder: reported |
| R-11 | `numeric-selection.md` §5, §8, §14.1; `width-inference.md` §7 | seal syntax open | resolved: the seal is the named representation type in type position; the angle brackets stay the measure slot; the parameterised posit form is a synthesis configuration, never a seal; the compiler never selects a discipline: a conversion whose analysed range is covered is lossless and admitted bare; one that would lose information must carry the developer's stated discipline (`width-inference.md` §7) or is rejected; only the spelling of that statement is open, and the owner (2026-09-04) will not pre-decide it |
| R-12 | `numeric-selection.md` §9 item 1; `fixed-point-scaffolding.md` §4 | "during elaboration" versus Saturation | spec reworded: propagation in Elaboration where no platform fact is needed, closed with selection at Saturation; paper: reported |
| R-13 | `dts-dmm-paper.md` §2.6 vs `numeric-selection.md` §2.1, §13.2 | warning in the paper, hard error in the spec | the owner's rule: always a warning with `--warnaserror` to make it an error, as the FPGA timing budget does; spec amended, the paper was right |
| R-14 | `fixed-point-scaffolding.md` §4 | sign-extends an unsigned value; elaborator versus lowering | paper: reported; the same defect as L-7b |
| R-15 | `numeric-selection.md` §3.4 vs §5 | two severities for one condition | one severity now: warning promoted under the flag |

- **R-16 (`platform-predicates.md` §5.2, resolved 2026-09-04 with D9).** The draft's "dynamic CPU
  detection" sketched a predicate quotation holding a run-time call, with "Alex may generate runtime
  check or use compile-time target selection". Alex decides nothing (`CCS_Architecture.md`), a
  predicate is a declared fact read structurally (D8), and a quotation is never evaluated (D9). The
  section now says: a predicate's quotation holds a literal; a capability known only at run time is an
  ordinary function the program calls, on which the compiler makes no selection; a non-literal predicate
  body is a defect of the declaration (CCS8206).

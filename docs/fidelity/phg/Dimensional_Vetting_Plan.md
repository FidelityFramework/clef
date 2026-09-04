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
| **Width** | the analysed range `[a, b]` of an integer, its minimal width and signedness (`width-inference.md` §3); reals carry a representation, not a width (§4) | lattice family, not a group: a bounded interval domain over Z, meet-directed, propagated through the PSG dataflow to a least fixed point and never unified; the width is derived from the analysed range; a written width (`int32`, `uint8`, `nativeint`) is a Tier-3 seal checked for coverage; `Resolved Pointer/Register` seals take their value from `PlatformContext.Dimensions` per section at saturation (D1) | `width-inference.md` §1–§3, §5, §10; `numeric-selection.md` §3, §5; `arxiv-papers/research/grade-axis/02` §2 (Width row), §7.1; `ntu-dimensional-architecture.md` §2.1, §4.3. `ntu-types.md` §3.1, §6.1–§6.2 (width as type identity, `int ≠ int64` by name) is the text D1 supersedes |
| **Memory space and access kind** | where a value resides and how it may be accessed, `Ptr<'T, 'Region, 'Access>`, `NTUMemorySpace`, `NTUAccessPattern` | an enumeration sort in the SMT sense, not a group: solved by equality unification over a finite domain in the same inference pass; every component is invariant and there is no subtyping (D2); a `ReadWrite` handle where `ReadOnly` is required passes only through the explicit coercion `Ptr.asReadOnly`, a node in the graph, never a checker rule | DTS/DMM §2.5; `arxiv-papers/research/grade-axis/01` §7 (identity check); `access-kinds.md` §Access Kind Coercion and §Diagnostics (`CCS8020`–`CCS8022`); `memory-regions.md`; `platform-bindings.md` §Program-Lifetime Spaces. `ntu-dimensional-architecture.md` §7.2's "covariant access" is an open question superseded by D2 |
| **Representation** | which concrete numeric format realises a dimensioned range on a target (IEEE, posit, fixed-point) | a deterministic function of the dimensional range and the target's covering set (the argmin with coverage and ulp floor) | DTS/DMM §2.6; `width-inference.md` §4; `numeric-selection.md`; `grade-discipline.md` |
| **Alignment, tensor shape** | design only | | `ntu-dimensional-architecture.md` §2.4–2.5 |

Grade (the parity component of Clifford grade, valued in Z2) is a further generator the PHG paper carries;
it is out of this plan's first increment; when it enters, the group is no longer free (Z^n ⊕ Z2, DTS/DMM §2.1) and the solver moves from Hermite to Smith normal form, with the same signature.

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
| Diagnostic series | the code's codes are `FS8xxx` (`FS8000_TypeMismatch` ...); the spec's are `CCS8xxx` (`access-kinds.md` §Diagnostics); clef's `ccs-specification.md` Appendix D still lists `FS8xxx` | `Expressions/Types.fs:39-45`; `NativeService.fs:1878` |
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
| W-1 | two different seals meeting is an explicit-conversion site; a bare operand (an unsuffixed literal, whose type `int` is the bare integer kind, D1) adopts a covering seal | `int32 x + int64 y`; `nativeint p + int32 x` | `1 + 1L` (bare literal, point range `[1, 1]`, covered by the seal); `1L + 2L`; `int64 x + 1L` | `CCS8013` (seal mismatch; `CCS8010` is the spec's null-keyword error) | `1 + 1L` rejected by name, which `ntu-types.md` §6.2 (`let x: int64 = 42 // Error: int ≠ int64`) prescribes and D1 overrides, a spec tension for step 6; seal pairs rejected by name (right result, wrong mechanism) |
| W-2 | operands of `-`, `*`, `/`, `%` are numeric; operands of `+` are both numeric or both string (D5), never `bool` | `true + true`; `true - true` | `1 + 2`; `"a" + "b"` | `CCS8000` | accepted |
| W-3 | a seal at a platform boundary comes from the platform description (word and pointer widths from `PlatformContext.Dimensions`) or from the `Fixed` seals the binding generator emits for C ABI types from `PlatformABI` (`ntu-dimensional-architecture.md` §2.1), resolved in CCS at saturation, never in the witness | (differential: `type Pair = { Addr: nativeint; Tag: int32 }` compiled under x86_64 Linux and the Cortex-M33 descriptor of `platform-bindings.md`, `Dimensions = [(Pointer, 32); (Register, 32)]`; `expect.toml` names both layouts) | | | resolved in CCS (`NativeTypes.fs:443-448`; the header comment at `:69-72` now agrees); still contradicted by `NativeTypes.fs:658`, `:663` and `ntu-types.md` §1, §1.1, §3.2, §3.3, §7.1, §9.2 |
| W-4 | no silent default: an integer whose range is unobservable and that carries no seal from any source (dataflow, library, platform, developer) is a diagnostic. Arithmetic on a sealed operand keeps the seal's wrapping semantics (`native-type-universe.md` §2.3, `width-inference.md` §8), so a sealed result is covered by construction | `let rec run n = run (n + 1)` (no modulus, comparison or seal: unobservable on every target) | `let f (n: int32) = n + 1` (the sum wraps in the seal) | `CCS8011` (range unobservable) | no diagnostic in CCS; Alex throws `FPGA0001` on the FPGA leg (`PSGCombinators.fs:120`), CPU leg falls back to the platform word (`:104`) |
| NS-1 | dimensioning seam (reals): a bare real with an unobservable range lowers to IEEE `f64` without error and still carries range propagation; an unbounded bare real flowing into a dimensioned context fires at the dimensioning boundary and names the bare source (`numeric-selection.md` §6, §6.1, §13.7–13.8) | `let y (bareInput: float) (oneNewton: float<N>) : float<N> = bareInput * oneNewton` with `bareInput` unbounded | `let y (bareInput: float) = bareInput * 2.0` | numeric-selection family code (peer of the width codes, §11), allocated with the D3 table; gated by step 8 | nothing exists; the real interval domain "does not yet exist in the integer twin" (§3.1) |
| NS-2 | coverage-empty: no offered representation covers the dimensional range | `astronomicalDistance<m>` with range `[1e-11, 1e72]` on a posit-only target | the same on a target offering `f64` | numeric-selection family, error (§2.1, §13.2) | nothing exists |
| NS-3 | tier disagreement: an observed dataflow range not contained in the binding claim (`R₁ ⊄ R_binding`) is a diagnostic, never a change to the binding range (§3.4 item 3, §13.5) | a `Fidelity.Physics` range narrower than a literal the dataflow proves | contained | numeric-selection family | nothing exists |
| NS-4 | a covering-but-suboptimal seal compiles and is witnessed with the representation the open argmin would have chosen (§13.9) | (none) | a `float64` seal on a near-unity range on a posit target: accept with the design-time witness | numeric-selection family, Info | nothing exists |
| W-5 | a seal must cover the analysed range (a bare range meeting a seal is the `width-inference.md` §7.2 conversion check on a singleton candidate set, `numeric-selection.md` §2.1) | `let x : uint8 = 300`; `let c (counter: uint32) : int8 = counter % 1000` (range `[0, 999]`) | `let x (counter: uint32) : uint8 = counter % 256` (range `[0, 255]`); `let y : int8 = -128` | `CCS8012` (seal does not cover range; the spec states the non-covering case with two severities, §3.4 item 3 "a diagnostic" and §5 "the §2.1 hard error", and the plan takes the error reading, §13.2) | no range analysis in CCS |
| W-6 | width is propagated, never unified (`width-inference.md` §2, §5; `arxiv-papers/research/grade-axis/02` §2, §7.1): the range coeffect of a generalised function is analysed per instantiation (DTS/DMM §2.6: a call-site instantiation with its argument ranges yields the result range, which propagates onward); a non-`inline` function is emitted as one body whose width is the join over its instantiations (only carrier instantiations split bodies, design note §d.3); per-call-site bodies arise only under explicit `inline` | (none) | `let g x y = x + y` used at `g 1L 2L` and `g 1 2` in one program: the first instantiation is sealed `int64` with the seal-bound image as its result range, the second is bare with range `[3, 3]`, both accepted, one body | | second use rejected by name (`Bindings.fs:397` disables generalisation, so `'T` binds to `int64` at the first use); `ntu-types.md` §6.1 prescribes that rejection, a spec tension for step 6 |
| M-1 | no write through a `ReadOnly` handle | `let w (p: Ptr<byte, Flash, ReadOnly>) = Ptr.write p 0uy` | `let w (p: Ptr<int, Stack, ReadWrite>) = Ptr.write p 1` | `CCS8020` | `Ptr<'T, 'Region, 'Access>` is not a type constructor CCS knows: `mkTypeConRefWithMeasures` (`NativeTypes.fs:762`) has no caller, `Ptr` appears only in a comment (`:727`), and the samples call `Ptr.read`/`Ptr.write` on a bare `nativeint` (`stm32l5-blinky/STM32L5.fs:92-94`), so there is no access component to check |
| M-2 | no read through a `WriteOnly` handle | `let r (q: Ptr<uint32, Peripheral, WriteOnly>) = Ptr.read q` | `let r (q: Ptr<uint32, Peripheral, ReadWrite>) = Ptr.read q` | `CCS8021` | as M-1: no `Ptr` type constructor exists in CCS |
| M-3 | access is part of identity, no subtyping: a `ReadWrite` handle where `ReadOnly` is required passes only through the explicit coercion `Ptr.asReadOnly` (`Ptr.asWriteOnly` for `WriteOnly`), a node in the graph rather than a rule in the checker | `let ro : Ptr<int, Stack, ReadOnly> = rw` with `rw : Ptr<int, Stack, ReadWrite>`; `let rw2 : Ptr<int, Stack, ReadWrite> = ro` | `let ro : Ptr<int, Stack, ReadOnly> = Ptr.asReadOnly rw` | `CCS8022` | as M-1; `ntu-dimensional-architecture.md` §7.2 (Prospective) still says "covariant", superseded by D2 |
| M-4 | region is invariant: an enumeration sort unified by equality (DTS/DMM §2.5) | `let f (p: Ptr<int, Peripheral, ReadWrite>) = Ptr.read p` then `f stackPtr` with `stackPtr : Ptr<int, Stack, ReadWrite>` | `f gpioReg` with `gpioReg : Ptr<int, Peripheral, ReadWrite>` | `CCS8110` (region mismatch, proposed in the spec's memory block; the spec assigns no number, and its own table spends `CCS8040`–`CCS8104` on null-freedom inside the block it reserves for memory; clef's Appendix D `FS8003` is on the wrong series) | accepted |
| M-5 | every dimensional component is part of identity (D2): unit, region, access | `let f (b: array<int, 4, Stack>) = b` applied to `s : array<int, 4, Sram>` | same region | region code as M-4 | `NTUQualifiers` are excluded from identity (`NativeTypes.fs:248`, `Unify.fs:86-88`); no surface form carries a memory space on a numeric (`ntu-dimensional-architecture.md` §2.2 is marked Design), so the numeric-carried row joins the set when §2.2 leaves Design |

The W rows follow decision D1 (one width regime; a written width is a seal; the range is a coeffect
propagated by interval arithmetic, `width-inference.md` §2, §5, and composed with claims by precedence,
`numeric-selection.md` §3.4; the grade-axis note's lattice-family placement of width is directional and
agrees in verdict). The NS rows are the real-valued family of `numeric-selection.md`, gated by step 8; explicit
conversion (`width-inference.md` §7) is gated by step 7 (L-4, L-9). The design for steps 1 and 2 is
`Dimensional_Step1_2_Design.md`; the ranged-type position is `Types_As_Ranges_Position.md`.

## 4. The harness

- `Composer/samples/dimensional/vet.sh` compiles every `<rule>/<verdict>/*.fidproj` with
  `composer compile <fidproj> -k`, records the exit code and the stderr diagnostics, matches the
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
   | L-3 | `Literals.fs:49-51` | `UserNum "I"` (bigint) and any unknown suffix become `intType` "for now" | fabricated representation, silent | now: `CCS80xx` unsupported literal suffix |
   | L-4 | `Intrinsics.fs:953-976` | every conversion intrinsic is typed `'a -> Target` from a fresh type variable | the polymorphic `'T -> Target` coercion `width-inference.md` §7.3 forbids; `int x` accepts a string, a bool, a char | step 3: each conversion intrinsic is typed with a numeric constraint on its source and names its target seal, removing the `'a -> Target` shape (§7.3); step 7: the coverage check of the target against the source's analysed range and the stated-discipline requirement (§7.1–7.2), which need the range coeffect |
   | L-5 | `SRTPResolution.fs:290-410` | a `ConversionCategory` and an MLIR op name are computed and discarded (`_category`, `_mlirOp`); int-to-int is always `Widening`; int-to-int always `extsi` ("for narrowing should be trunci"); unknown falls to `fidelity.convert`; header cites `spec/drafts/NTU_Conversion_Model.md`, which does not exist (retired by `width-inference.md` §9) | dead code shaped like a decision; a dangling citation | now: delete the category, op-name and citation; keep only the witness naming |
   | L-6 | `Unify.fs:86-88` | placement qualifiers excluded from identity | implicit conversion between memory spaces | step 5 (D2, M-5) |
   | L-7 | `Composer/.../Alex/Patterns/ApplicationPatterns.fs:183-233` (FPGA leg) | the witness widens both operands to the max width with `pExtSI` regardless of the source's signedness, and truncates the result; HelloArty's `07_output.mlir:116` shows `arith.extsi %periodMs : i13 to i30` | the FreeBSD class: the party that widens is not the party that knows the sign | not live today only because of L-7b; the two are removed together in step 7: width from the range per `width-inference.md` §3, extension op from the range's signedness (`extui` for a non-negative range), both settled in the graph |
| L-7b | `Composer/.../PSGElaboration/IntervalAnalysis.fs:88-113` (`minSignedBits`, `bitsFromInterval`) | every interval gets a sign bit, non-negative ones included (`[0, 4000]` becomes 13 bits, not 12); `IsSigned` is recorded false but the bit is spent | the spec formula (§3: unsigned `ceil(log2(b+1))`) is not what runs; the spec's own example table (31/21/10/13) and HelloArty's README carry the +1 figures, while the two site posts claim 29/11 | step 7; and a spec rough edge to report: `width-inference.md` §3's table contradicts its formula |
| L-8 | `ApplicationPatterns.fs:236-249` (CPU leg) | shift amounts "typed `int` by the front end" are truncated or zero-extended to the operand width by the witness | conversion inserted below the graph; the comment admits the front end typed it wrong | step 3: the front end types the amount; no witness cast |
   | L-9 | `ApplicationPatterns.fs:449-490` (`pTypeConversion`) | int-to-int truncation with no range check; float-to-int with no rounding or saturation discipline; int-to-float always `sitofp` even for unsigned sources; the result type resolved by `mapNativeTypeWithGraphForArch` in Alex | Alex deciding; `width-inference.md` §7.2 requires a stated discipline | step 3: the conversion node carries source seal, target seal, discipline and fidelity; Alex transcribes |
   | L-10 | `Alex/XParsec/PSGCombinators.fs:104,120` | CPU leg defaults an unresolved width to the platform word; FPGA leg throws `FPGA0001` | silent default on one leg, a thrown string on the other | step 7 (W-4) |

   Items marked "now" have no dependence on the rewrite and are removed first; the rest are removed by
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
3. **Operator types carry dimensions.** `op_Addition`/`op_Subtraction`/comparison: `num<'u> -> num<'u> -> _`;
   `op_Multiply`: `num<'u> -> num<'v> -> num<'u 'v>`; `op_Division`: `num<'u 'v^-1>`; a numeric constraint on
   `'T` for all of them (W-2); dimensionless literals scale (UoM-4). Gate: UoM-2, -3, -4, -9, W-2.
4. **Diagnostics on the `CCS8xxx` series.** Rename the `DiagnosticCodes` module's values and clef's
   `ccs-specification.md` Appendix D to the spec's series; add `CCS8040` (measure mismatch), `CCS8020-8022`
   (access), `CCS8003` (region). Gate: every rule's expected code exists in `DiagnosticCodes`.
5. **Access kind and region are checked.** Region and access measures unify under the rule of D2
   (access covariant, region invariant); writes through `ReadOnly` and reads through `WriteOnly` are
   diagnosed at the assignment and dereference sites; `NTUQualifiers` join type identity with the same
   rule. This is also what makes the collections chapters' VC-RO real. Gate: M-1 to M-5.
6. **Resolution stays in CCS, and the texts say so.** Rewrite `ntu-dimensional-architecture.md` §4.3 and
   §5.2 to "CCS resolves per section at saturation; Alex reads"; delete the `NativeTypes.fs:69-70` comment;
   confirm `TypeMapping.fs` in Composer reads `LayoutHint`/resolved widths rather than resolving. Gate: W-3;
   the drift gate learns "resolved by Alex".
7. **Width inference as a coeffect** (after D1): interval analysis over the PSG placing the analysed range
   and minimal width as annotations; overflow and narrowing diagnosed; the FPGA leg narrows registers from
   the annotation. Gate: W-1, W-4, W-5, W-6, and `width-inference.md` §10 items 1, 2, 4, 5, 7, plus
   accept programs for the three seeding rules of §2 (a literal is a point interval; a comparison bounds
   the branch; a counter `mod N` has range `[0, N-1]`) with their expected widths under the §3 formula; the
   seal check and the conversion coverage of §7.1–7.2 (L-4, L-9) land here. §10 item 3 and the real cases
   of item 6 belong to step 8.
8. **Representation selection** (after D4): the covering-set argmin over the platform's declared
   representations, placed as an annotation; coverage-empty and a non-covering seal as errors (`numeric-selection.md` §2.1, §5, §13.2), reported with the paper's diagnostic text (DTS/DMM §2.6, whose "Warning" severity the spec supersedes), the design-time warning reserved for the covering-but-suboptimal seal (§13.9), and the prerequisite real interval domain of §9.1 (outward rounding, sign-split reciprocal, format-boundary widening). Gate: the
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
  saturation discipline (W-4's wrap rule). Phase: `numeric-selection.md` §9 item 1 and
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
  (step 7) and gains the seal check and the unbounded diagnostic there; seal syntax is open
  (`numeric-selection.md` §14.1) and must not collide with the measure slot.
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
  seals `CCS8011`–`CCS8018`, region mismatch `CCS8110` (proposed); the full list is in the step 1–2 design
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
- **D6, ranged types (recommended from the corpus sweep of 2026-09-04; pending the user's word).** The
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
  note. The corpus leaves no choice open on where the range lives; the open choices are the seal form, the
  phase wording (R-12), and per-instantiation analysis with joined emission (W-6).
- **D5, `+` on strings (decided: concatenates).** `+` dispatches on the kind of its operands: on numerics it
  is the unit-unified add with a range obligation; on strings it is the concat recipe with an extent
  obligation. No proof complication follows, because each dispatch emits its own obligation family.

## 7. Corpus rough edges surfaced by verification (for the owner to rule on; nothing edited)

| # | Where | What | Bearing |
|---|---|---|---|
| R-1 | `width-inference.md` §3 | the formula gives 29 bits for HelloArty's counter; the chapter's own example table says 31 (copied from the implementation, which adds a sign bit to every range, L-7b) | W-4, step 7 |
| R-2 | `error-handling.md` §Error Codes vs §Diagnostics | CCS8100–8199 is reserved for memory management while CCS8100–8104 are spent on null-freedom inside it | D3 |
| R-3 | `ntu-types.md` §1, §1.1, §3.2, §3.3, §6.1, §6.2, §7.1, §9.2 | width as type identity, `int ≠ int64` by name, "resolved by Alex", "erased before code generation" | D1, §0, step 6 |
| R-4 | `native-type-universe.md` §2.3 | `int` = platform word; `int` and `nativeint` are synonyms | D1 |
| R-5 | `dts-dmm-paper.md` Appendix A vs Appendix C and §2.6 | Appendix A gives the bare literal `g` a fresh dimension variable; Appendix C annotates it and §2.6 says constraints alone do not determine magnitudes | UoM-4, UoM-9 |
| R-6 | `ntu-dimensional-architecture.md` §7.2 | "covariant access" left as an open question | D2, M-3 |
| R-7 | clef `docs` Appendix D | `FS8003` region mismatch on the wrong series; "regions form a subtyping hierarchy for assignment" | D2, D3, M-4 |
| R-8 | `units-of-measure.md` line 12, §Measure Parameter Erasure | F#'s erasure text survives in a chapter whose framework never erases (DTS/DMM §2.3) | §0, step 6 |
| R-9 | `decidable-by-construction.md` §2.2 | Z^7 as the dimension space, where base measures are declared and not fixed at seven (DBC §4.1's currency example) | step 1 |
| R-10 | `arxiv-papers/research/grade-axis/00` | cites `../spec/draft-grade-discipline-chapter.md` and `../spec/clef-spec-amendment-schedule.md`, which exist nowhere under the repos | grade increment |
| R-11 | `numeric-selection.md` §14 item 1; `width-inference.md` §7 | seal syntax and explicit-conversion syntax are open; the angle brackets are the measure slot, so a seal form cannot use them | step 3, step 7 |
| R-12 | `numeric-selection.md` §9 item 1; `fixed-point-scaffolding.md` §4 vs `ntu-dimensional-architecture.md` §4.3 | "during elaboration" versus "at saturation" for range analysis and selection; Elaboration and Saturation are reserved phase terms and the lowercase uses read as the phase | D1 phase note |
| R-13 | `dts-dmm-paper.md` §2.6 line 176 vs `numeric-selection.md` §2.1, §13.2 | an uncovered range is a Warning in the paper and a hard error in the spec | step 8, W-5 |
| R-14 | `fixed-point-scaffolding.md` §4 (Appendix C) | sign-extends a `[0, 1023]` value the same listing and `width-inference.md` §3 treat as unsigned; line 59 says the elaborator fixes the representation, line 61 says lowering reads the coeffect | L-7, step 7 |
| R-15 | `numeric-selection.md` §3.4 item 3 vs §5 | the non-covering case is "a diagnostic" in one place and "the §2.1 hard error" in the other | W-5 |

# Dimensional Vetting Plan

> How the Clef Compiler Service comes to check dimensional types fully: what the design requires, what the
> checker does today (measured, with citations), the program set that decides the gap, and the hardening
> steps in order. Design of record, 2026-09-04. Companion to [PSG_to_PHG_Plan.md](PSG_to_PHG_Plan.md) and the
> [Design_Supersession_Register](Design_Supersession_Register.md). The user's diagnosis that opened this work:
> "the dimensional types are not really type-checking correctly, or at least not fully." The finding that
> confirms it: units of measure are parsed and then discarded, which the user has ruled vestigial. Units are
> integral to the Native Type Universe; their dropping is a course correction, not a feature request.

## 0. The position

Dimensions are part of type identity and never erase. CCS infers them, checks them, and resolves the
platform-dependent ones against the platform description at saturation, per program-graph section; the
resolved values ride on the PSG as annotations, and Alex reads them. This is the same rule that settled
closures, obligations and layout: the graph decides, the witness observes. Two texts in the corpus say
otherwise and are corrected as part of this plan. The dimensional-architecture chapter's resolution flow
(`ntu-dimensional-architecture.md` §4.3, "PlatformContext → Alex (per section) → MLIR emission with concrete
widths") and its §5.2 ("Alex resolves dimensional types to concrete values") place resolution below the
witness boundary; and `NativeTypes.fs:69-70` calls width "erased metadata resolved by Alex via platform
quotations". Both invert the design. The platform description is always present (there is no target-free
compilation), so cross-apply at saturation is always available; `PlatformContext.resolveWidth` already lives
in CCS (`NativeTypes.fs:443`), and the layout literals depend on it.

## 1. The dimension families and their normative sources

| Family | What it is | Algebra | Normative source |
|---|---|---|---|
| **Units of measure** | the physical dimension of a numeric value, `float<m s^-1>` | finitely generated free abelian group: addition requires equal dimensions, multiplication adds exponent vectors, division subtracts; inference is HM extended with dimension variables, complete, principal, decidable | DTS/DMM paper §2.1–2.2 and Appendix A (the `computeForce` example); spec `units-of-measure.md` (relations, normalisation, constraint solving, generalisation) |
| **Width** | the bit width of an integer or real, `NTUWidth = Fixed n \| Resolved Pointer/Register` | named widths are distinct types; `Resolved` widths are resolved per section from `PlatformContext.Dimensions`; mixing a `Pointer`-width and a `Fixed 32` integer without explicit conversion is an error | `ntu-types.md`, `ntu-dimensional-architecture.md` §2.1, §5.1; `width-inference.md` adds a range-derived regime (§2–§3, §10.1: "derived from the value's analyzed range, not from a target type name"), see decision D1 |
| **Memory space and access kind** | where a value resides and how it may be accessed, `Ptr<'T, 'Region, 'Access>`, `NTUMemorySpace`, `NTUAccessPattern` | an enumeration sort in the SMT sense, not a group; access is covariant (a `ReadWrite` value may be passed where `ReadOnly` is expected, never the reverse); region is invariant | DTS/DMM §2.5; `ntu-dimensional-architecture.md` §2.2–2.3, §7.2; `access-kinds.md` (diagnostics `CCS8020`, `CCS8021`, `CCS8022`); `memory-regions.md`; platform description as declared authority (`platform-bindings.md` §Program-Lifetime Spaces) |
| **Representation** | which concrete numeric format realises a dimensioned range on a target (IEEE, posit, fixed-point) | a deterministic function of the dimensional range and the target's covering set (the argmin with coverage and ulp floor) | DTS/DMM §2.6; `width-inference.md` §4; `numeric-selection.md`; `grade-discipline.md` |
| **Alignment, tensor shape** | design only | | `ntu-dimensional-architecture.md` §2.4–2.5 |

Grade (the parity component of Clifford grade, valued in Z2) is a further generator the PHG paper carries;
it is out of this plan's first increment and enters through the same measure algebra when it does.

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
| UoM-1 | addition and subtraction require equal dimensions | `1.0<m> + 1.0<s>` | `1.0<m> + 2.0<m>` | `CCS8100` (measure mismatch) | accepted (measure dropped) |
| UoM-2 | multiplication adds exponent vectors | `let x : float<m> = 2.0<m> * 3.0<s>` | `let a : float<m s> = 2.0<m> * 3.0<s>` | `CCS8100` | reject not detected; accept mis-typed |
| UoM-3 | division subtracts exponent vectors | `let v : float<m> = 6.0<m> / 2.0<s>` | `let v : float<m/s> = 6.0<m> / 2.0<s>` | `CCS8100` | as above |
| UoM-4 | a dimensionless factor scales without changing dimension | `let x : float<s> = 2.0 * 3.0<m>` | `let x : float<m> = 2.0 * 3.0<m>` | `CCS8100` | as above |
| UoM-5 | measures normalise as an abelian group | `let x : float<m> = 1.0<m s> / 1.0<m>` | `let x : float<s> = 1.0<m s> / 1.0<m>`; `let y : float<m s> = 1.0<s m>` | `CCS8100` | structural compare only |
| UoM-6 | comparison requires equal dimensions | `if 1.0<m> < 1.0<s> then ...` | `if 1.0<m> < 2.0<m> then ...` | `CCS8100` | accepted |
| UoM-7 | annotation and inference agree at calls | `let f (x: float<m>) = x` then `f 1.0<s>` | `f 1.0<m>` | `CCS8100` | accepted |
| UoM-8 | generalisation: a dimension-polymorphic function is used at two dimensions | (none) | `let scale f v = f * v` used at `(float, float<m>)` and `(float<s>, float<m>)`, inferred `float<'u> -> float<'v> -> float<'u 'v>` | | measure variables never bound |
| UoM-9 | the paper's example infers without annotation | `computeForce` with a `float<m>` where a mass is expected | Appendix A as written, result `float<kg m s^-2>` | `CCS8100` | not inferable |
| W-1 | mixed named widths need explicit conversion | `1 + 1L`; `nativeint 1 + 1` (Pointer vs Register, `ntu-dimensional` §5.1) | `1L + 2L`; `int64 x + 1L` | `CCS8000` (type mismatch) | rejected by name |
| W-2 | arithmetic operands are numeric | `true + true` | `1 + 2` | `CCS8000` | accepted |
| W-3 | a `Resolved` width resolves per section from the platform description, never in the witness | (a program compiled for two platform contexts yields layouts with the declared widths) | | | resolved in CCS; contradicted by comment |
| W-4 | no silent default width for an unanalysable range | per `width-inference.md` §6, §10.5 | | | no range analysis exists; see D1 |
| M-1 | no write through a `ReadOnly` handle | `let p : Ptr<int, Stack, ReadOnly> = ... in p := 1` | `let p : Ptr<int, Stack, ReadWrite> = ... in p := 1` | `CCS8020` | accepted |
| M-2 | no read through a `WriteOnly` handle | `let v = !q` with `q : Ptr<uint32, Peripheral, WriteOnly>` | read through `ReadWrite` | `CCS8021` | accepted |
| M-3 | access is covariant | `ReadOnly` passed where `ReadWrite` expected | `ReadWrite` passed where `ReadOnly` expected | `CCS8022` | both accepted |
| M-4 | region is invariant | `Ptr<int, Stack, _>` passed where `Ptr<int, Peripheral, _>` expected | matching regions | `CCS8003` (region mismatch; clef Appendix D numbers it in the wrong series) | accepted |
| M-5 | qualifiers are part of identity once the subtyping rule is decided | `NTUint(Fixed 32, Global)` where `Stack` expected (GPU sections) | same space | `CCS8022` | erased from identity; see D2 |

Rules W-4 and the representation-selection family (posit coverage warnings, `width-inference.md` §7
conversions) join the set once decisions D1 and D4 are taken; their programs are written then.

## 4. The harness

- `Composer/samples/dimensional/vet.sh` compiles every `<rule>/<verdict>/*.fidproj` with
  `composer compile <fidproj> -k`, records the exit code and the stderr diagnostics, matches the
  `expect.toml` (`verdict = "reject" | "accept"`, `code = "CCS8100"`, optional `range = "L:C-L:C"`), and
  prints the rule table with a final count. It never calls `tests/regression/Runner.fsx`.
- A rejected program is green only if the expected code appears; an accepted program is green only if the
  exit code is 0 and no error is printed. Warnings are reported, not judged, until the representation rules
  land.
- The RoundTrip native gate (`BAREWire/samples/RoundTrip`, diffed against its `expected.txt`) and the HelloProof baseline (23 obligations, 29 hyperedges, 23 unsat) run
  alongside; the drift gate runs after every step.

## 5. Hardening steps, in order, each gated by the table

1. **Measures are representable and survive.** Give the NTU numeric kinds a measure component (the
   design's "type variables carry an associated dimension variable"): a normalised exponent map over the
   declared base measures plus measure variables, carried on the numeric type, not as a positional `TApp`
   argument; `Literals.fs` keeps the measure of a measured literal; `Types.fs` resolves `MeasurePower` and
   `App` measure syntax into it; `[<Measure>] type` definitions and abbreviations enter the environment
   (`units-of-measure.md` §Measure Definitions). Gate: UoM programs parse to distinct types.
2. **Measure unification is the abelian-group algorithm.** Replace `unifyMeasure` with unification over
   exponent vectors with measure variables (Kennedy's algorithm: normalise, eliminate, bind), failing with
   `CCS8100` and presenting measures in the spec's normalised form; `HasMeasure` enforced; generalisation of
   unbound measure variables at `let` (§Generalization of Measure Variables). Gate: UoM-1, -5, -6, -7, -8.
3. **Operator types carry dimensions.** `op_Addition`/`op_Subtraction`/comparison: `num<'u> -> num<'u> -> _`;
   `op_Multiply`: `num<'u> -> num<'v> -> num<'u 'v>`; `op_Division`: `num<'u 'v^-1>`; a numeric constraint on
   `'T` for all of them (W-2); dimensionless literals scale (UoM-4). Gate: UoM-2, -3, -4, -9, W-2.
4. **Diagnostics on the `CCS8xxx` series.** Rename the `DiagnosticCodes` module's values and clef's
   `ccs-specification.md` Appendix D to the spec's series; add `CCS8100` (measure mismatch), `CCS8020-8022`
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
   the annotation. Gate: W-4 and the `width-inference.md` normative list.
8. **Representation selection** (after D4): the covering-set argmin over the platform's declared
   representations, placed as an annotation; posit coverage warnings as in DTS/DMM §2.6. Gate: the
   `numeric-selection.md` programs.

Steps 1–5 are the increment agreed on 2026-09-04; they precede every fan-out (closure retooling, suspension
recipe, sentinel collections, the Lattice server).

## 6. Decisions

Decided 2026-09-04 (D2–D5 by the user; D1 re-derived from the design corpus and pending the user's word).

- **D1, one width regime, not two (re-derived; pending).** Sources: `width-inference.md` §1, §5, §6, §8,
  §10; `numeric-selection.md` §3 (tiers), §3.4 (precedence override), §6 (unobservable ranges), §6.1
  (the bare/dimensioned seam); the site posts *The Gift of Deferred Inference* and *FPGA and Hardware
  Inference*; HelloArty (`Behavior.clef:55-58` declares `Counter: int` and receives 29 bits;
  `docs/AutomaticPipelineInference.md` places the analysis in CCS and limits it to structurally certain
  facts). What they say: the type of a number is its kind (integer or real) and its dimension. Width and
  representation are not part of the type; they are coeffects derived from the analysed range per target at
  saturation, and a declared machine model is the established pattern for how a declaration meets an
  inference: the analysis runs regardless, validates the declaration, and a mismatch is a diagnostic. A
  written concrete width (`int32`, `uint8`, `float32`, `posit<32,2>`) is therefore a Tier-3 **seal**: the
  highest-precedence range claim, which turns the selector into a checker (the analysed range must be
  covered by the seal, else a coverage diagnostic). `nativeint` is a seal whose width the platform
  description supplies. Ada is the precedent: range and precision belong to the type declaration, a
  representation clause (`'Size`) is validated against them, and dimensions are an aspect of the numeric
  type; VHDL puts range and width on the subtype the same way. Consequences: (1) two different seals
  meeting is an explicit-conversion site, so W-1 stands for seal against seal; (2) a bare operand meeting a
  sealed one adopts the seal when its range is covered, so `1 + 1L` is accepted (the literal is bare with a
  point range); (3) an unobservable range is an error for any integer and for a dimensioned real, and
  lowers to IEEE `f64` for a bare real, exactly as the two chapters state, which on the CPU leg means every
  boundary integer (FFI, parse, syscall) carries a seal; (4) the CPU leg rounds a bare width up to the
  native size for arithmetic and never narrows below the range (`width-inference.md` §8). The earlier
  recommendation to soften §10.1 is withdrawn; §10.1 stands as written. The interim
  `Composer/src/MiddleEnd/PSGElaboration/IntervalAnalysis.fs` reads no declared width, checks no seal, and
  records nothing for an unbounded value; the failure is raised later by the witness
  (`Alex/XParsec/PSGCombinators.fs:120`, `failwithf "error FPGA0001"`, FPGA only, CPU falls back to the
  platform word at `:104`), which is Alex deciding, in a non-CCS series, and its suggested fix `int<32>`
  puts a width in the slot D4 gives to the measure. The analysis moves to CCS as the range coeffect
  (step 7) and gains the seal check and the unbounded diagnostic there; seal syntax is open
  (`numeric-selection.md` §14.1) and must not collide with the measure slot.
- **D2, dimensional identity (decided: exact match).** Two dimensional types are the same when every
  component matches: unit, memory space, region, access, and seal where present. There is no subtyping on
  any component. A read-write pointer where a read-only one is required is an explicit narrowing, which is
  a node in the graph rather than a rule in the checker.
- **D3, diagnostic series (decided: CCS).** Every `FS`-prefixed code is retired, including the lexer and
  parser codes inherited from FCS; a mapping table lands with hardening step 4 and clef's Appendix D moves
  with it.
- **D4, where the measure lives (decided: on the numeric type).** The measure is a component of the
  numeric type node, beside the range and representation annotations that accrue to it, as Ada's dimension
  aspect and VHDL's range constraint sit on the type rather than as a parameter. `float<newtons>` is
  Kennedy's surface syntax for that component, not a type-constructor application; `float` keeps arity 0.
- **D5, `+` on strings (decided: concatenates).** `+` dispatches on the kind of its operands: on numerics it
  is the unit-unified add with a range obligation; on strings it is the concat recipe with an extent
  obligation. No proof complication follows, because each dispatch emits its own obligation family.

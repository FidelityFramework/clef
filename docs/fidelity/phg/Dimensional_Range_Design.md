# One discipline: the range, from the literal to the boundary

> Design note for hardening steps 3, 7 and 8 of `Dimensional_Vetting_Plan.md`, written as one
> statement on 2026-09-04 at the owner's instruction ("Please write them as one design note and
> ensure they are unified. We keep relitigating this. That is drift."). It supersedes the step-3
> preview and the width sections of `Dimensional_Step1_2_Design.md` ((e), (h) 14–16, (i) 4–6), the
> per-step text of plan §5 steps 3, 7 and 8, and every spec passage §10 below lists. Authority order:
> the white papers, then the spec, then the docs; the owner's rulings quoted in §0 are the position
> where the spec drafts disagreed with them, and those drafts are corrected here, not argued with.

## 0. The underscore

**There is one integer kind, `int`, and one real kind, `float`, each with a dimension. A value is a
range until it is used. The platform declares the selection of widths and representations it has,
and the analysed range picks from that selection. Nothing else decides a width.**

The owner's words, 2026-09-04:

- "One of the things I can't stop thinking about is that the value *can* be a range until it's
  used, and then the range will be known. This is the FPGA case. I don't understand why that
  doesn't apply to all cases."
- "I don't think there's any place for an int8 - there is only int that happens to be 8 wide. Do
  you understand? There is no int16, no int32 and no int64. There is just int with a specified width
  selection and the range determines which one is used. Is that so difficult to understand? This
  is number theory, yet?"
- On stating an intended loss: "I would say per-seal, but would strongly advise updating Platform"
  — read with the second ruling, the per-seal spelling has no seal to attach to, and what survives
  of it is the platform's declaration of what each of its representations does at its boundary
  (§4.3, §7).
- Earlier, in force: no silent defaults ("the platform information for the target should either
  provide it or it should [provide] a range that is supplied as with FPGA"); no implicit
  conversion (the FreeBSD lesson, `a-lesson-in-memory-safety.md`); the compiler never selects a
  wrap or saturate discipline; a coverage finding is a warning promoted by `--warnaserror`; the
  platform declares, the language carries only names (D8); quotations are intrinsic (D9).

The FPGA case is the general case. On fabric an interior value's width is synthesised from its
range and nothing is selected; on a CPU the same range selects from the finite set the platform
declares. The input is the same, the range; the check at a boundary is the same, coverage; only the
codomain differs. `width-inference.md` §1 already says it: "representation follows from analyzed
range, precision loss is explicit and tracked, and an unanalyzable range is a reported error, never
a silent default"; §3: "A value uses exactly the bits its range requires — no more"; §10 item 1:
"Integer representation width SHALL be derived from the value's analyzed range, not from a target
type name." The only thing the corpus had beside this was a second mechanism, the written width as
a "Tier-3 seal" (`numeric-selection.md` §3.3, §5; `ntu-types.md` as rewritten in CS-7), and that
second mechanism is what kept the question open. It is retired.

### 0.1 Closed. Not to be re-opened by any later step, note, review or changeset.

1. **No width-named type exists in the language.** `int8`, `int16`, `int32`, `int64`, `uint8`,
   `uint16`, `uint32`, `uint64`, `byte`, `sbyte`, `uint`, `nativeint`, `unativeint`, `float32`,
   `single`, `double`, `float64`, `Posit8`…`Posit64` are not types and not spellings. A program
   that writes one is CCS8706 (the type is not defined) once the migration of §9 has run.
2. **No width-bearing literal suffix exists.** `1L`, `1u`, `1uy`, `1s`, `1n`, `1.0f` are CCS8018.
   A literal is `int` or `float` at the dimensionless measure `1`, with the point range `[v, v]`.
3. **No seal, no conversion syntax, no discipline syntax.** There is nothing to write a width or a
   representation into and nothing to convert between. The "explicit conversion" of
   `width-inference.md` §7, the "Tier-3 seal" of `numeric-selection.md` §3.3 and §5, the "conversion
   and seal form" of `rounding.md` §6 and the `int32`-style spellings in `ntu-types.md` are retired
   together (§10). The critical-path gap those chapters named is closed by having no syntax.
4. **Intended loss is arithmetic.** Reduction modulo `2^n` is `x % 2^n` (or `x &&& mask`) and has
   range `[0, 2^n − 1]`; saturation is `clamp lo hi x`, i.e. `min hi (max lo x)`, and has range
   `[lo, hi]`; a real becomes an integer through `floor`, `ceiling`, `round` or `truncate`, each with
   its range image; an integer becomes a real through `float`, exactly where the selected real
   representation holds the range. Every one of these is a function with a range, and the width
   follows from the range as it does everywhere. No operation is a representation change.
5. **A width appears in exactly two places, and both are declarations the compiler reads:** the
   platform description (widths by name, representations with family, bits, range, capability and
   boundary semantics: CS-7b, D8) and a boundary declaration (a wire-schema field, an MMIO register
   width, a C ABI parameter in a binding descriptor, an endpoint contract). A value meeting a
   declared boundary is checked for coverage of its range, never converted.
6. **The compiler never selects a wrap or saturate discipline and never inserts a conversion.** A
   range that a boundary does not cover is CCS8012, a warning promoted by `--warnaserror`, whose
   remedies are to bound the range at its source or to change the declaration. Arithmetic on
   analysed ranges never overflows: the result's range is computed and its representation selected
   to cover it.
7. **Width and representation are coeffects beside the type**, derived from the range and read by
   every later pass (D1, `width-inference.md` §5, GA-02 §2 lattice row). They never enter
   unification (§1.2 below; `Dimensional_Step1_2_Design.md` e.6 stands).
8. **The platform declares; the language carries names only** (D8). A representation's boundary
   semantics are a fact about hardware the compiler reads to realise `%` and `clamp` cheaply and to
   witness, never to decide a program's meaning.

### 0.2 Open, and only these (the spec's own genuinely-open items, unchanged)

`ulp_min(r)` per family (`numeric-selection.md` §14.9, `rounding.md` §11.2); the `Fidelity.Physics`
binding contract (§14.2); profiling-evidence provenance (§14.4); tier-disagreement tolerance for
reals (§14.3); `R_eff = ∅` versus `R_cov = ∅` precedence (§14.8); cascade rounding (`rounding.md`
§11.4); the quire conversion mode (§11.5); type-directed posit synthesis (§14.7). None of them is a
question about whether a width is a type.

## 1. The value as a range

### 1.1 Seeding

- A literal is a point: `124` has range `[124, 124]` (`width-inference.md` §2). Its type is `int`
  at measure `1`; a measured literal `1.0<m>` is `float` at `m`. No literal carries a width; plan
  row L-1 (a bare literal minted at `Resolved Register`) is retired with the spellings.
- A comparison bounds the branch it guards: `if n < 1000 then … n …` gives `n` the range
  `[lo(n), 999]` inside the branch (§2, "Comparisons seed ranges").
- `x % k` has range `[0, k − 1]` for a non-negative `x` and `k > 0`; `clamp lo hi x` has `[lo, hi]`;
  `abs x` is non-negative; a DU tag has `[0, cases − 1]`; a boolean is `[0, 1]`
  (seeded by `RangeAnalysis.fs` in CCS since CS-10; Composer's `IntervalAnalysis.fs` is deleted).
- An input arrives through a declaration and carries the declared range: a platform endpoint's
  contract, a wire-schema field, an MMIO register's width, an exported entry point's argument at the
  platform's Register or Pointer width, a C ABI parameter at the width its binding descriptor
  declares. There is no input whose range is unknown by construction; there are only inputs whose
  declaration is missing, and that is CCS8203 or CCS8012 at the declaration site, never a guess.

### 1.2 Propagation, and why it is not unification

Ranges propagate forward along dataflow to a least fixed point: interval arithmetic through the
operators, joins at merges and at the parameters of a function called from several sites, widening
for loops. They are the lattice family (GA-02 §2, §7.1: "support is propagated, never unified;
parity and dimension are unified, never propagated"). Dimensions are the group family and are
unified (`solveDim`, CS-2). One operator node carries both obligations, the unit equation and the
range image; they share operands and no variables and are discharged separately, QF_LIA for the
range containment and the unit equation, QF_BV only for a fixed-width fact once a representation is
selected (`Horizon_Requirements.md` C5; `grade-discipline.md` §4.1). The range never enters the
unifier: it has no inverses, its principal object is a least fixed point, and a claim about it is
checked by containment, never solved by an equation (`Dimensional_Step1_2_Design.md` e.6, which
stands).

A non-`inline` function has one body; each parameter's range is the join over its call sites, the
whole-program least fixed point available because saturation runs over the program hypergraph after
every use is elaborated. A call site carries its own range only under explicit `inline`, by
expansion (`inline` is semantic, never a width-solving device). Generalisation quantifies measure
and carrier variables (CS-6) and never ranges: a range is per instantiation and joined.

### 1.2a Precision (the owner, 2026-09-05: the earlier analysis "was to simply show the
possibility. This is a good opportunity for refinement and recalibration")

The pass is a new analysis, not a port. Its precision comes from: per-node ranges, so a variable
read under a comparison guard carries the refined range on that branch (§1.1's comparison rule)
instead of a seeded guess; a widening operator whose thresholds are the declared representations'
boundaries of the sign-selected family, then the program's own settled constants (`c − 1`, `c`
above a rising endpoint; `c`, `c + 1` below a falling one, for every point range the program
holds), then the infinity (the CS-10 review: without the constants a counter that carries its own
value on one branch, `if not advance then state.Phase else (state.Phase + 1) % cycleSteps`, widens
past its modulus and no guard can bring it back, and the spec's `[0, N − 1]` for a free-running
counter is unreachable; ratified 2026-09-05 as the owner's "refinement and recalibration"),
followed by a bounded narrowing pass that recovers the precision widening gave up
(standard descending iteration; sound because it only tightens a post-fixpoint); arithmetic that
saturates to "unbounded" rather than wrapping an endpoint; parameters joined over every call site
and record fields ranged per field; and the §3 formula for the width, which spends no sign bit on a
non-negative range. Any later refinement (a relational domain, congruences for `%` and shifts) is a
change to this section first.

### 1.3 The unobservable range

A loop or recursion the program never bounds has no range: `let rec run n = run (n + 1)`. That is
CCS8011, an error, on every substrate, and the remedy is to bound it: a comparison that terminates
it, a modulus, an `abs`, a `clamp`. Nothing is defaulted to the platform word. A bare `float`
with an unobservable range selects IEEE `f64`, the no-bet representation, without a diagnostic, and
keeps propagating (`numeric-selection.md` §6, §13.7); a dimensioned real with an unobservable range
is CCS8011 at the dimensioning seam, naming the bare source (§6.1, §13.8).

## 2. The kinds

| Kind | Spelling | Dimension | Signedness | What selects its representation |
|---|---|---|---|---|
| integer | `int` | `int<m>`, Kennedy's slot, ASCII (C8.1) | a fact of the range: non-negative ranges spend no sign bit (`width-inference.md` §3) | the smallest offered integer representation covering the range, §3.1 |
| real | `float` | `float<m>` | — | the argmin of `numeric-selection.md` §2 over the offered real representations covering the range, §3.2 |

The angle-bracket slot is the measure slot and nothing else is ever written there (C8.1); the
carrier keeps arity 0 and the measure is a component of the numeric type node (D4). `int<1>` and
`float<1>` are the bare kinds. `TNum(carrier, dim)` with `Carrier = Int | Real` is the type form
the CS-1 note (a.2) named and D7 deferred; D7's per-width carriers are deleted, not collapsed into a
seal column (§8.1).

Signedness is not a kind. `uint` had been "`int` with the range claim `[0, ∞)`"; a claim of that
shape is a fact the range already carries, so `uint` goes with the widths. `nativeint` had been
"the platform's pointer seal"; an address is not an integer the program does arithmetic on
(`ffi-boundary.md` §1: `nativeint`-as-pointer is not denotable; addresses live in `Ptr`, `Mmio`
and `CHandle`), and an integer at the platform's Pointer width is `int` at a boundary the
description declares (§4.1). Both spellings go.

## 3. Selection: the platform's declared set, the range's choice

### 3.1 Integers

The platform description declares its representations (CS-7b): for each, a family (`int`, `uint`,
`ieee`, `posit`, `fixed`), its bits, its exact dynamic range, its capability (native, emulated,
unavailable) and its boundary semantics (wrap, saturate, exact). For an integer value with range
`[a, b]` the compiler selects the offered representation of the integer family with the fewest
bits whose range covers `[a, b]`, choosing the signed family only when `a < 0`. That is
`width-inference.md` §8's "rounded up to the nearest native integer size" stated as selection over
a declared set, and it is the same `R_cov` filter §3.2 uses. On fabric there is no core and no set:
the width is exactly `width([a, b])` by the §3 formula, a non-negative range spending no sign bit,
and the extension an operand needs when it meets a wider one is `extui` or `extsi` by the sign of
its range, never by a type name. The result is the width coeffect on the node, read by Alex; it is
never stored as a fact independent of the range it was derived from (C3).

A range that sits away from zero has a cheaper realisation than two's complement: stored as
`value − lo`, it needs `⌈log2(hi − lo + 1)⌉` bits (`[1000, 1023]` is five bits, not ten). That is a
representation, an offset encoding the fabric may declare, and its choice belongs to step 8's
selection (§3.2, CS-13), not to the range fact; recorded here (the owner, 2026-09-05) so the
opportunity is not lost.

### 3.2 Reals

For a real with range `[a, b]` on a target offering `R(T)`, the representation is the argmin of
worst-case ULP-floored error over `R_cov(T, [a, b])`, the offered representations whose dynamic
range covers `[a, b]` (`numeric-selection.md` §2, §2.1, §2.2; DTS/DMM §2.6). Performance is a
capability filter on the candidate set, never a score term (§7). If `R_cov` is empty, that is the
coverage warning, promoted by `--warnaserror`, and selection falls to the argmin over the full
offered set with the uncovered range recorded (§2.1, §13.2). The real interval domain is a new
abstract domain (outward rounding, sign-split reciprocal, transcendentals, widening with the
declared formats' range boundaries as thresholds, §9.1); it rides the same traversal and carriage
as the integer one and reuses none of its transfer functions.

### 3.3 Aggregates

Each coefficient of an aggregate, each field of a record, each element type of an array, selects
independently from its own range (`grade-discipline.md` §5.2; C4). A record's layout is the
consequence of its fields' selections, settled in the graph, and Composer's three size models
collapse to a read of the selected representations (§8.3). A byte buffer is `array<int>` whose
element range is the buffer's declared cell range, `[0, 255]` for a platform buffer schema over
octets; the width of the cell is that range's.

## 4. Boundaries

### 4.1 What a boundary is

A boundary is any place a value meets a representation that a declaration, not the range, fixed:

| Boundary | Where the width is declared | Read by |
|---|---|---|
| platform endpoint and its contract (a syscall's arguments, a console buffer) | `Description.clef` / `Platform.clef`, BAREWire vocabulary | PlatformResolution |
| exported entry point, ABI-governed parameter | the description's `Register` and `Pointer` widths | PlatformDeclaration |
| wire-schema field | the BAREWire schema (`Field { Width = … }`) | the schema reader |
| MMIO register | the register's declared width on the `Mmio` handle (Contracts leaf) | the peripheral reader |
| C ABI parameter or return | the binding descriptor Farscape emits (`Expr<FunctionDescriptor>`), a quotation | the binding reader |
| JavaScript number | the JSIR profile's documented realisation (`width-inference.md` §8) | the pathway |

### 4.2 The check

At a boundary with declared range `D` and a value with analysed range `R`: `R ⊆ D` is the
obligation. Covered, the value takes the boundary's representation, the transfer is exact, and
nothing is written in source. Not covered, CCS8012, a warning promoted by `--warnaserror`, naming
`R`, `D`, the declaration and the two remedies: bound the value (a `%`, a `clamp`, a guard) or
change the declaration. A boundary whose declared representation the platform does not offer is
CCS8204 (CS-7b). A covering boundary whose representation is wider than the range needs is
information, CCS8014, the design-time witness of `numeric-selection.md` §13.9 with the seal word
removed. An analysed range not contained in a higher-provenance claim (a library law's range, a
declaration) is CCS8016, a warning promoted by the flag: the claim binds and the disagreement is
witnessed (§3.4 item 3; NS-3).

### 4.3 Boundary semantics are the platform's, and are read, never chosen

The description declares for each representation what its hardware does when a result would leave
its range: wrap on a two's-complement unit, saturate on a saturating DSP block or posit unit, exact
on fabric. Under §0.1 item 6 no program ever depends on that fact for its meaning: a covered range
never leaves its representation. The compiler reads it for two things only: to realise `x % 2^n`
as the free truncation a wrap-native representation performs, or `clamp` as the saturating
instruction a saturating unit has, when the selected representation is that one; and to witness the
build-time twin of the design-time obligation. This is what "updating Platform" comes to: the
declaration CS-7b built is the whole of it, and a representation may declare several boundary
disciplines with their capabilities (wrap native, saturate emulated) so that a `clamp` on such a
target is realised where it is native and emulated where it is not, with the capability gate of
`numeric-selection.md` §7 reporting emulation under the `allow-emulated-warn` policy. The language
still carries no name for any of it.

### 4.4 The three provenances, without a type in any of them

`numeric-selection.md` §3's tiers are provenances of one range input: dataflow (Tier 1), a library
law evaluated at compile time from its quotation (Tier 2, §4; D9), and a declaration (Tier 3). The
third tier had been read as a type written in source; it is the boundary declaration of §4.1 and,
where the compiler cannot infer a property of input data, the one supplied hypothesis in one
construct that C7.5 admits, which is a number about data, not a type about a value. Composition is
unchanged: the highest provenance binds, the lower claims are containment obligations, disagreement
is witnessed, never merged (§3.4).

## 5. Intended loss is arithmetic

| Intent | Written as | Range image | Realised as |
|---|---|---|---|
| reduce modulo `2^n` | `x % 2^n`, `x &&& (2^n − 1)` | `[0, 2^n − 1]` | truncation, free on a wrap-native representation of `n` bits; a `rem` otherwise |
| saturate to `[lo, hi]` | `clamp lo hi x` (`min hi (max lo x)`) | `[lo, hi]` | compare-and-select; a saturating instruction where the unit declares one |
| real to integer | `floor`, `ceiling`, `round`, `truncate` | the image interval, integer-valued | the rounding op of the selected real representation |
| integer to real | `float x` | `[a, b]` as reals | exact where the selected real holds `[a, b]` exactly; else CCS8012 at the boundary of that representation |
| change nothing | (nothing) | — | — |

The "fidelity" of `width-inference.md` §7 item 1 recorded a loss a representation change caused;
with no representation change there is nothing to record beside what the graph already carries, the
range into and out of each of these functions, which Lattice shows on hover. The requirement that a
lossy step be explicit is kept in its only remaining form: the developer wrote the `%` or the
`clamp`.

## 6. Reals, rounding and the quire

Everything in §1, §3.2 and §4 applies. What `rounding.md` adds stands: a sound interval enclosure
carries its directed rounding as representation identity (§3.1) and an ordinary value carries
rounding as a coeffect (§3.2); a quire rounds once (§4); a boundary between two real representations
of different families, a posit value meeting an IEEE parameter in a C ABI, rounds by the mode the
boundary's declared representation offers and the platform's declared boundary discipline, never by
a source-level conversion (§4.3 above replaces `rounding.md` §6). `rounding.md` §5's saturate-versus-
wrap axis is the platform's declaration of §4.3, not a conversion attribute.

## 7. Diagnostics

| Code | Severity | Meaning under this note |
|---|---|---|
| CCS8000 | Error | an operator's operand is not of a numeric kind (`+` dispatches on kind: numeric add or string concat, D5) |
| CCS8001 | Error | the kind of an operator's operands cannot be determined at a non-generalisable binding |
| CCS8011 | Error | an integer or dimensioned real whose range is unobservable; at the dimensioning seam for a bare real that flows into a dimension |
| CCS8012 | Warning, `--warnaserror` | a value's analysed range is not covered by the boundary's declared representation |
| CCS8013 | retired | "two seals meet": there are no seals |
| CCS8014 | Info | a declared boundary representation wider than the range requires |
| CCS8015 | retired | "sealed arithmetic may wrap": arithmetic on analysed ranges never overflows |
| CCS8016 | Warning, `--warnaserror` | an analysed range exceeds a higher-provenance claim |
| CCS8017 | retired | "a conversion cannot hold the range": there are no conversions |
| CCS8018 | Error | a literal suffix: every width suffix, `I`, and any suffix the language does not have |
| CCS8040–8050 | Error | measures (CS-2 to CS-6, unchanged) |
| CCS8203/8204 | Error | a width dimension or representation the description does not declare or offer (CS-7b, unchanged) |
| CCS8706 | Error | a type name that is not defined, which after §9 is what `int32` is |

## 8. What is deleted and what moves

### 8.1 Deleted from CCS

The per-width type constructors `int8TyCon` … `uint64TyCon`, `float32TyCon`, `posit8TyCon` …
`posit64TyCon`, `nintTyCon`, `unintTyCon`, `uintTyCon`; the width column of `Types.numericSpellings`
and every spelling but `int` and `float`; `NTUWidth.Fixed`; the `SealRepresentation` type and
`representationOfCarrier`; `NativeLiteral`'s `NTUKind` field (a literal carries its value and its
kind, `Int` or `Real`); the `SynConst` arms for width-suffixed constants, which become CCS8018; the
width conversion intrinsics (`int8` … `uint64`, `nativeint`, `float32`), leaving `float`, `floor`,
`ceiling`, `round`, `truncate` and `char`; the name comparison of carriers in `Unify.fs`; the
`Fixed` seal Farscape's output relied on. `Carrier` becomes `Int | Real`. The drift gate's scheduled
`TyCon` rows become failures when this lands.

### 8.2 Moved into CCS

`Composer/src/MiddleEnd/PSGElaboration/IntervalAnalysis.fs` in substance: the range pass runs at
saturation in CCS over the whole graph (seeding §1.1, propagation §1.2, widening §1.3, joins at
function parameters), and writes the range and the selected width or representation as coeffects
on the node. Its `minSignedBits` spends a sign bit on every range (plan L-7b); the spec's §3 formula
is what runs, and HelloArty's `07_output.mlir` changes on purpose (the figures computed by the
CS-10 pass from the current source, correcting the spec table's older cadence quoted here before):
`Counter` `[0, 799999999]` 30 bits, `StepTick` `[0, 390624]` 19 bits, `Phase` `[0, 1023]` 10 bits,
`PeriodMs` `[500, 4000]` 12 bits, and every `arith.extsi` of a non-negative value becoming an
`arith.extui`. HelloArty's README table (31/21/10/13) is corrected with it.

### 8.3 Deleted from Composer

`ApplicationPatterns.fs` L-7 (widening both operands with `pExtSI` and truncating the result: the
extension op is read from the node's range sign), L-8 (shift amounts cast by the witness: typed by
the front end), L-9 (`pTypeConversion`: no conversions exist); `PSGCombinators.fs` L-10 (the
platform-word default and the `FPGA0001` throw: the node carries its width); the three size models
(`mlirTypeSize`, `mlirTypeSizeForArch`, `TypeSizing.computeSize`) reduced to one read of the selected
representation; `TypeMapping.fs` and `SSAAssignment.fs` keying widths on `NTUKind` widths or on the
architecture table (`platformWordWidth arch`, checked at `MLIRGeneration.generate` since CS-7b,
retired here). The FPGA leg keeps `IntervalAnalysis.fs` only as long as CS-10 has not landed; then
it reads the node.

**What CS-11 deleted of this list (2026-09-05).** L-10: the architecture table
`platformWordWidth arch` and the agreement check at `MLIRGeneration.generate` are gone;
`Architecture` carries the declared `Register` and `Pointer` widths read once from the CCS context
(`PlatformConfig.resolveOSArch`), and every site reads `declaredWordWidth` or
`declaredPointerBytes`. The three size models are one: `mlirTypeSizeWith` over the declared Pointer
width (`mlirTypeSize arch` reads it through the architecture), `mlirTypeSizeForArch` deleted,
`TypeSizing` already gone; the serializer takes the declared pointer width and sizes no struct by a
silent word. Deleted with them: the `X86_64`-defaulting `mapNativeType` and `mapNativeTypeWithGraph`
and the string-based type helpers, all without a caller. Still standing, owed to the node-reading
CPU leg (the CS-11 as-built below): L-7's CPU branch of `pBinaryArithOp` and `pComparisonOp`, L-8's
shift-amount cast, L-9's `pTypeConversion`, and `TypeMapping`'s mapping of the bare kind to the
declared word on CPU (`mapNTUKindToMLIRType`, `mapNativeTypeForArch`), which reads the declaration
now and the node's selection later.

**SSA is a nanopass derivation (the owner, 2026-09-05: "No minting. No push style application.
This is nanopass." "NO POOLS." "NO POOL MANAGEMENT." "THIS IS ARCHITECTURE.").** `SSAAssignment`
runs once over the finished graph, after every range and selection is settled, and derives each
node's SSAs exactly from its structure, as its own header states: "SSA count is a deterministic
function of instance structure ... no generation during emission". A string literal derives its
three values; a meet that adapts an operand to another width derives one more, from the same
settled facts; nothing is allocated, budgeted, pooled or counted at witness time, and no witness
constructs a name. Composer's witnesses read the derivation and transcribe. The three files that
still minted names by arithmetic (`LambdaWitness.fs`'s extraction schedule, `ClosurePatterns.fs`,
`HardwareModulePatterns.fs`'s forward references) are corrected in CS-11, not scheduled; the
first attempt at CS-11, which added a counter, was stopped for it. The drift gate's row for a
constructed name outside `SSAAssignment.fs` is a lint behind the code, not the enforcement: the
enforcement is that the code shows one pattern.

### 8.4 The FPGA's own design-time integrity tooling, preserved

The owner, 2026-09-05: "while I want width inference to be available to any target, there's
*still* FPGA specific tooling I want to see preserved in a way that supports design-time integrity
for that platform target." Width inference is general (§0); two things stay the fabric's own, and
this note keeps them:

- **Machine-type inference.** A `[<HardwareModule>]` design (`Design { InitialState; Step; Clock }`)
  is read as a Mealy machine: the state register, the step function's combinational body, the
  registered outputs; today synthesised by Composer's `HardwareModulePatterns`, later a Baker recipe
  under the PHG plan's drain, unchanged in meaning by any step of this note.
- **The temporal budget** (`DepthAnalysis`, CCS0100, a warning promoted by `--warnaserror`). The
  chain of combinational operations between register boundaries is weighed and compared with the
  budget one clock period allows: `threshold = ⌊period_ns / ns_per_weight_unit⌋`, the period from
  the clock the design runs at, the nanoseconds per weight unit a fabric calibration against
  Vivado's post-route slack. "This would get caught in Vivado synthesis, so we set a warning"; the
  diagnostic names the chain and offers both remedies, restructure the computation to shorten the
  chain, or step the clock down so more compute fits the window, and the budget relaxes with the
  chosen clock (the Arty A7 has four; HelloArty runs at 25 MHz against the leaf's 100).

Two refinements the range annotation makes possible, recorded for the FPGA leg after CS-10:

1. **Weights that read the width.** An adder's carry chain is deeper at 30 bits than at 10; a
   multiplier's more so. The weight table (`DepthAnalysis.arithmeticWeight`: multiply, divide and
   modulus 2, everything else 1, unitless) can read `ValueRange.width` of the operation's result
   node and weigh by width, recalibrated against the same Vivado ground truth; the estimate then
   tightens as the widths do.
2. **The clock as a declared fact.** The leaf declares its clocks (`Clocks = [ sysClk ]` on the
   Arty; the board has four) and the design selects one (`Clock = Endpoints.clock`). The project
   file's `clock_mhz` override is today a free number; under D8 it becomes a selection among the
   declared clocks, or an explicitly declared derived clock, so that the budget is always computed
   against a clock the description knows and the "step down" remedy names the declared alternatives.
   With CS-12 (boundaries are declarations) or as its own small changeset.

## 9. The migration

The spellings are everywhere Clef source was written in F#'s vocabulary. Measured 2026-09-04,
excluding a worktree copy under `Fidelity.Platform/.claude`:

| Where | Files | Mentions | What they are |
|---|---|---|---|
| `BAREWire/src` | 25 | 420 | encoding cursors and wire fields: `uint32`, `byte`, `uint64` |
| `Fidelity.Platform` (leaves and Bindings) | ~45 | ~1,600 | mostly Farscape-generated C ABI declarations under `Bindings/` (`uint32`, `byte`, `uint`); the leaves' own logic is a minority |
| `Composer/samples` | 27 | 131 | regression and dimensional samples |
| harness leaves W-1, W-3, W-4, W-5, W-6, M-1 to M-5 | 10 | — | rewritten with this note (§11) |
| spec chapters | — | — | §10 |
| blog posts | dated | — | allowed by the drift gate as history |

Farscape's output is the largest item and the most mechanical: a C parameter of `uint32_t` is a
boundary fact the descriptor quotation carries, and the Clef signature beside it says `int`; the
generator changes once and the bindings are regenerated. The BAREWire encoders write wire fields
whose widths the schema declares and whose values are `int` with ranges; each `uint32` in a cursor
becomes an `int` whose range the schema field gives it. The sweep is a corpus job for the lean
fleet shape (one implementer per repository with the gates in its brief, one light reviewer, fixes
by hand), and the drift gate's scheduled rows are its inventory until each repository is clean.

## 10. Spec passages this note corrects (done 2026-09-04)

| Chapter | Passage | Correction |
|---|---|---|
| `ntu-types.md` | the whole chapter as rewritten in CS-7 (seal model, `Fixed n` widths, `int32` spellings, CCS8013) | rewritten to the one-kind model: §2 kinds, §3 identity and coeffects, §4 source mapping (`int`, `float`, handles), §6 no conversion, §8 MLIR mapping from the node's width |
| `width-inference.md` | §7 "Explicit Conversion", its "Not yet specified" note; §10 items 6–7 | §7 becomes "Intended Loss Is Arithmetic" (§5 above); items 6–7 restated; the open item closed |
| `numeric-selection.md` | §3 table row "3 — Direct … a seal form"; §3.3; §5 "Sealing and Reverse Selection"; §13.9; §14.1 | Tier 3 is the boundary declaration; §5 becomes "Boundaries and Reverse Selection"; §13.9 names the boundary; §14.1 closed |
| `rounding.md` | §5 last sentence, §6, §10.1–10.2, §11.1, §11.3 | §6 becomes "No Conversion Form"; the saturate/wrap axis is the platform's declaration; §11.1 and §11.3 closed |
| `native-type-universe.md` | §2.3 table and decisions 3–4, alignment table, overflow table, `Checked`; §2.4 table, `float32`/`single`/`double` | one integer kind, one real kind; overflow does not occur on analysed ranges; alignment follows the selected representation |
| `units-of-measure.md` | the constant grammar's `byte<…>` … `uint64<…>` rows | `int<measure-literal>` and `float<measure-literal>` |
| `ntu-dimensional-architecture.md` | §2.1 (`Fixed` as "a developer's seal", Farscape emitting Fixed-width NTU types), §7.1, §7.2 | `NTUWidth` is the selected width coeffect; Farscape emits descriptor widths; §7.1/§7.2 repointed |
| `error-handling.md` | the CCS8011–8018 row | the §7 table above |
| `numeric-selection.md` | §9.1 "the integer interval domain is `int64`-only (a min/max pair with two's-complement bit-counting transfer functions)" and "the widening introduces no thresholds of its own" | corrected 2026-09-05: the integer domain is the five-case lattice of `ValueRange` (empty, bounded, two half-lines, unbounded) with exact `bigint` transfer saturating to an infinity; the widening's thresholds are the declared boundaries, then the program's settled constants, then the infinity (§1.2a) |

## 11. The vetting rows, restated

| Rule | Statement | Reject | Accept | Code |
|---|---|---|---|---|
| W-1 | there is no width-named type and no width suffix | `let f (x: int32) (y: int64) = x + y` | `let f (x: int) (y: int) = x + y`; `let a = 1 + 1` | CCS8706 ×2 (the suffix case `1L` is CCS8018, exercised by L-3's probe) |
| W-2 | operands of `-`, `*`, `/`, `%` are numeric; `+` is both numeric or both string | `true + true`; `true - true` | `1 + 2`; `"a" + "b"` | CCS8000 |
| W-3 | a boundary width comes from the platform description, resolved in CCS at saturation, never in the witness | (differential) | `type Pair = { Addr: Ptr<int, Stack, ReadOnly>; Tag: int }` with `Tag`'s range `[1, 1]`, compiled under x86_64 and Cortex-M33: `Addr` 8 then 4 bytes, `Tag` 1 byte on both | layouts in `expect.toml` |
| W-4 | no silent default: an unobservable integer range is a diagnostic; a bounded one is not | `let rec run n = run (n + 1)` | `let f (n: int) = if n < 1000 then n + 1 else 0` | CCS8011 |
| W-5 | a boundary's declared representation must cover the analysed range; intended loss is written as arithmetic | `Mmio.store reg8 300` (an 8-bit register declared in the Contracts leaf; range `[300, 300]`) | `Mmio.store reg8 (v % 256)`; `Mmio.store reg8 (clamp 0 255 v)` | CCS8012, Warning, `--warnaserror` |
| W-6 | width is propagated, never unified: one body, the parameter range the join over call sites | (none) | `let g x y = x + y` at `g 1 2` and `g 100000 200000`: one body at the joined range `[2, 300000]` | accept, one emitted body |
| M-1…M-5 | unchanged in substance; their handles are `Ptr<int, …>` and their literals bare | | | |
| NS-1…NS-4 | unchanged; NS-4's "seal" is a declared boundary representation | | | |

## 12. The changesets, in order, each gated by the table

| CS | Delivers | Gate |
|---|---|---|
| CS-9 | step 3: the numeric constraint on every operator (W-2, CCS8000 for `1 + "a"`), `+` as kind dispatch, unary negation and plus witnessed in Composer, `abs`/`sign`/`min`/`max`/`clamp`/`sqrt`/`atan2` as library schemes with Baker recipes, shift amounts typed by the front end (L-8), every conversion typed with a numeric source (`κ<'u> -> Target<'u>`, CCS8002; the width-named conversions are typed here like the rest and deleted in CS-11) and `float`/`floor`/`ceiling`/`round`/`truncate` typed as kind functions (built 2026-09-04, below) | W-2 both, W-7, W-8 both; UoM-2/3/4/9 stay green; RoundTrip; HelloProof |
| CS-10 | step 7, first half: the range pass in CCS (§1) writing range and width coeffects; Composer's FPGA leg reads the node (L-7, L-7b retired), HelloArty's MLIR changes as §8.2 states and its README with it | W-4 both; W-6; HelloArty `07_output.mlir` at the §8.2 figures; RoundTrip |
| CS-11 | step 7, second half, the CPU leg (order corrected 2026-09-05: the deletion of the spellings cannot precede the CPU leg reading the node, since BAREWire's wire structs and FFI calls carry their widths in those spellings until the migration; so the CPU leg comes first): the range's declared sources (§1.1's last bullet: intrinsic result ranges as the compiler's own facts, the platform's declared representation range of a width-named carrier as an interim boundary, array element and tuple position ranges on the graph), the CPU leg selecting the smallest declared integer representation covering each node's range (§3.1) with extension and truncation at meets as the fabric leg does, one size model reading the node, the L-9 and L-10 sites deleted, and CCS8011 promoted to an error on CPU once RoundTrip, HelloProof and the harness carry none | W-4/reject once promoted; RoundTrip transcript identical with the hash re-baselined (narrower interior widths change the binary); HelloArty MLIR byte-identical; HelloProof |
| CS-12 | one kind (§2, §8.1): the width-named types and suffixes deleted, CCS8706/CCS8018 for the spellings and suffixes, the corpus migration (§9) by the lean fleet with each width-named use becoming `int` plus a declaration where a boundary genuinely exists (a wire-schema field, a C ABI parameter, an MMIO register) and nothing where the range suffices; `int` of a `char` kept as a kind function (code point, `[0, 1114111]`) in the one spelling table and the interim `retypeCharConversion` deleted (decided 2026-09-05 under the owner's ratification); the harness leaves of §11 (W-1, W-3, W-5 with step 5's `Ptr`); the drift gate's `TyCon` and spelling rows turned to failures | W-1, W-3, W-5; every leaf compiles; BAREWire 309; RoundTrip transcript identical (hash re-baselined again, BAREWire's own source migrates) |
| CS-13 | step 8: the real interval domain (§3.2), the selection objective with its filters, per-coefficient selection, the boundary-representation witness | NS-1 to NS-4; `numeric-selection.md`'s programs |

Step 5 (access and region, M rows) sits between CS-11 and CS-12 in the plan's order and is unchanged by
this note except that its handles carry `int`. The order from CS-10 on is therefore CS-11 (CPU leg and
boundaries), step 5, CS-12 (one kind and the migration), CS-13 (reals).

Tied off means: 46 of 46 judged through step 8, RoundTrip's transcript byte-identical, HelloArty's
MLIR at the §8.2 figures and unchanged thereafter, HelloProof's 23 obligations unchanged or joined
by width obligations, and the drift gate with no scheduled row left for a width spelling.

## CS-9 as built (2026-09-04)

Delivered in four slices, each built inside Composer and gated before the next; every gate below was re-run on the final binary.

**Slice 1, `+` on strings and the kind mismatch (c.3, D5).** `NativeTypedTree/Unify.fs`: a new `UnificationError.OperandKindMismatch(op, lhs, rhs, range)` and `checkOperandKinds`, run by `unify` on the raw sides before `applySubst`: a variable carrying `OperandOf` that is already bound to one kind and meets the other (numeric against string, either way round) is that operator's failure, surfaced as CCS8000 with the text `The operands of '+' must both be numeric or both string; got int and string` (`operatorSpelling` renders `op_Addition` as `+`; the kind that met the bound variable is rendered first, which for a direct `a + b` is source order because constraints are discharged newest-first). Two numeric carriers (`1.0 + 2`) stay the carrier equation's CCS8003 and `bool` stays `fireOperandDispatch`'s CCS8000. `NativeTypedTree/NativeService.fs`: `dispatchStringAddition`, at the store boundary after `Monomorphization.run` (so a generalised `x + y` used at strings is rewritten in its string clone): every `Application` of the `op_Addition` intrinsic whose resolved type is string has its function node carry `Intrinsic { Module = String; Operation = "concat2" }`, the intrinsic Alex witnesses atomically. The unifier fires the dispatch but has no node; the resolved map is the one place both operand kinds are final, which is why the rewrite lives there and not in Composer.

**Slice 2, the library schemes and their recipes ((c) table, §5).** `Expressions/Intrinsics.fs`: `librarySchemeType` states each scheme once, instantiated with fresh carrier and measure variables per use: `abs` `κ<'u> -> κ<'u>`; `sign` `κ<'u> -> int<1>`; `min`, `max` `κ<'u> -> κ<'u> -> κ<'u>`; `clamp lo hi x`; `sqrt` `ρ<'u^2> -> ρ<'u>` (`Dimension.pow 2`, so `sqrt 1.0<m>` is CCS8041 through `solveDim`); `atan2` `ρ<'u> -> ρ<'u> -> ρ<1>`; `floor`, `ceiling`, `round`, `truncate` `ρ<'u> -> int<'u>`; `ρ` is the float carrier (D10). `tryResolveLibraryScheme` wraps them as `IntrinsicModule.Math` intrinsics, and `resolveMathOp` resolves `Math.abs`, `Math.sqrt`, `Math.atan2`, `Math.floor`, `Math.ceiling`, `Math.round` to the same schemes (one definition, two spellings; the transcendentals and `Math.min`/`Math.max`/`Math.pow` keep their float typing). `min` and `max` left `tryResolveOperator`. `Expressions/Identity.fs`, `resolveIdentifierCore` step 2e: the schemes resolve only after binding lookup fails, so a user's `abs` wins (probe `abs_user`). `Baker/Recipes/NumericRecipes.fs` (new; registered in `Clef.Compiler.Service.fsproj` after `OptionRecipes.fs`, in `BakerSaturation.shouldDecomposeIntrinsic` and the `IntrinsicModule.Math` arm of `applyIntrinsicRecipe`): `abs x = if x < 0 then -x else x`; `sign` as nested conditionals to `1`, `-1`, `0`; `min`/`max` compare-and-select; `clamp lo hi x = min hi (max lo x)`; `floor`/`ceiling` through `truncate` and `float`; `round` half away from zero. `Baker/Ingredients/Primitives.fs` gains `sub`, `neg`, `ge`, `le`, `numLit`, `floatLit`, `toFloat` and `truncate`; `numLit`/`floatLit` type the literal at the operand's carrier and dimension, and a carrier with no literal form (a posit) fails the recipe loudly. `tryDecompose` leaves an application alone when an operand is not a numeric type with a resolved carrier, because saturation runs inside `buildResult` before diagnostics surface: `abs true` is then the CCS8000 already minted, not a Baker exception. A value used in the guard and both branches (`truncate x` in `floor`) is one node, witnessed at its first visit, the guard; a value used only inside the branches (the `0.5` of `round`) is one node per branch.

**Slice 3, conversions and shifts (L-4, L-8).** `Expressions/Intrinsics.fs`, `tryResolveConversion`: every numeric spelling is `κ<'u> -> Target<'u>`, `κ` fresh and carrying `OperandOf(name)`, the dimension preserved (`float 3<m>` is `float<m>`, probe `float_measure`); `char` keeps its polymorphic source. `Expressions/Types.fs`, `DiagnosticCodes.CCS8002_ConversionSourceNotNumeric`; `Unify.fs`, `isConversionSource` reads the one spelling table so the `NotNumeric` failure at a conversion position formats as `The source of 'int' must be numeric; got string` and `NativeService.errorsToDiagnostics` codes it CCS8002. Shifts are `κ<'u> -> int<1> -> κ<'u>`, bitwise and/or/xor `κ<'u> -> κ<'u> -> κ<'u>`, complement `κ<'u> -> κ<'u>`. Composer's cast of a shift amount to the operand's width (`ApplicationPatterns.pBinaryArithOp`) is unchanged and is retired at CS-10 when widths come from the node.

**Slice 4, the atomic witnesses (Composer).** `Alex/XParsec/PSGCombinators.fs`, `classifyAtomicOp`: `op_UnaryNegation -> UnaryArith "neg"`, `op_UnaryPlus -> UnaryArith "plus"`. `Alex/Patterns/ApplicationPatterns.fs`: `pUnaryNegate` (an integer operand: `arith.subi` of a zero constant of the operand's type and the operand; a float operand: `arith.negf`), `pUnaryPlus` (forwards the operand's SSA, no op), `pTruncate`/`pTruncateIntrinsic` (`Math.truncate` as `arith.fptosi` to the type the node carries), wired in `pUnaryArithIntrinsic` and `Witnesses/ArithIntrinsicWitness.fs`. `Dialects/Core/Types.fs` and `Serialize.fs` gain `ArithOp.NegF`; `Elements/ArithElements.fs` gains `pNegF`. Nothing else in Composer; TypeMapping and IntervalAnalysis untouched.

**Found on the way, fixed in CCS.** `Expressions/Patterns.fs`, the `SynArgPats.Pats` arm of a union-case pattern: the constructor's result type is now unified with the scrutinee's (`Some b` against `int option` ties the instance's payload variable to `int`). Before, a `Some b` payload was typed only by its uses: `match (o: string option) with Some b -> b + 1` compiled through the checker and failed at `mlir-opt`, and `float b` on a pattern variable left its carrier open (BAREWire `Manifest.fs:33`, unreachable). Now `b` has the payload's type, and the `string option` case is CCS8003 at the checker.

**Decisions, for the owner.** (1) `ValueRange` endpoints are `bigint` (the reason above: CCS8012
needs the bounded range a product leaves 64 bits with). (2) A width-named element carrier's range
is its declared range regardless of the stores (buffers are filled by endpoints the pass does not
see), and an array handed to a boundary call takes an unbounded store. (3) The candidate rule joins
every value call's arguments into every unifiable escaping lambda; a partial application makes the
open parameters candidates; a non-lambda function value poisons the value calls it may reach.
(4) `Architecture` carries the declared widths as `Result`s rather than a module-level setting, so
that no mutable and no default exists; a core's leg refuses to start on a description declaring no
`Register` or `Pointer` (`MLIRGeneration.generate`, `CCS8203` in the message, before any witness
runs), and the fabric leg derives no byte layout (no DU, no closure) and reads neither. (5) The CPU
leg is owed whole, for the three decisions below; `platformWordWidth` is gone but
`mapNTUKindToMLIRType` still maps the bare kind to the declared word on CPU, and
`RangeAnalysis.selectedWidthOf` returns `None` for an unobservable range rather than a widest
(C3; the eventual leg stops naming the node). (6) CCS8011 stays Info on CPU: the residual is 117
on RoundTrip. (7) For the owner to rule: a length is the Pointer maximum, so `3 * n` on x86_64 is
CCS8012 (RoundTrip's `Validator.validate`); the alternative is an exact length where the array
traces to a literal (`RangeSources.intrinsic`'s `length` row through the element stores), which
would close that warning without a source change.

**Gates (the owner's session, on the final binary).** Composer build clean. RoundTrip
(`rt-cs11-final.*`): compile 0, run 0, transcript identical to `expected.txt`, hash
`aefcc865bd4817195ea61b0a676ba6cb00d403b1539ad9062d950a66986d83c9` unchanged (the CPU leg does not
read the annotation; `07_output.mlir` byte-identical to the pre-changeset capture
`cs11/roundtrip-before.mlir`); 117 CCS8011 information lines (from 320) and 1 CCS8012 warning
(`Validator.validate`, `3 * n` with `n = Array.length fields` in `[0, 2^63 − 1]`, range
`[0, 27670116110564327421]`, `uint64` selected; a finding the design intends, and a failure under
`--warnaserror` until the source bounds `n` or the owner rules on a literal array's length, below).
Harness `vet.sh --through 3` (`vet-cs11-final.txt`): exit 0, every row identical to
`vet-cs10-final.txt` (W-4/reject unchanged, CCS8011 not promoted). HelloArty
(`helloarty-cs11-fix2.txt`): exit 0, 0 CCS8011, `07_output.mlir` written by that compile (13:39:14)
and byte-identical to CS-10; the implementer's run had failed (`declares no width dimension
'Pointer'`) and its as-built had recorded a stale file as identical. HelloProof (`hp-cs11-final.*`):
compile 0 with 0 CCS8011 (was 2: `write`'s result is tabled), run prints
`Enter your name: Hello, Houston!`, 23 obligations, PASS, verdict lines identical to CS-10. Drift
gate clean. SSA: no `V (` or `SSA.V` outside `SSAAssignment.fs`; no counter, pool, budget or spare
vocabulary; no `platformWordWidth`, `mlirTypeSizeForArch` or `TypeSizing` reader.

**Review, and the fixes applied by hand (2026-09-05).** The reviewer rejected the implementer's
tree: (1) HelloArty failed (`declares no width dimension 'Pointer'`): `SSAAssignment` derived a
core's byte layouts (`buildDULayout`, `buildClosureLayout`) on the fabric leg, sized before this
changeset by the silent `X86_64` fallback the deleted table hid; fixed by deriving neither on the
FPGA target (`SSAContext.TargetPlatform`), and by `MLIRGeneration.generate` refusing a core's leg
on a description that declares no `Register` or `Pointer` (`generateCore` is the former body).
(2) A non-lambda function value made value calls unsound (valcall `[0, 1]` for `103`); fixed by
`poisoningOf`/`poisonReaches` above. (3) An array producer the store fold did not see took other
arrays' elements (arrmap2 `[1, 3]` for `1000000`); fixed by the closed element rule above. (4) The
carrier meet on a widened half-line was narrower than the carrier's set (carrierloop); fixed by the
source-only, whole-range rule above. Must-fixes: `selectedWidthOf` no longer fabricates a widest
width for an unobservable range; `coverageDiagnostics` reports through a `List.choose` with no
placeholder representation; the as-built's gate paragraph is rewritten from the owner's session's
transcripts and the section re-titled to its scope. Notes kept as owed: `resolveOSArch`'s `X86_64`
ISA fallback; Composer's pre-existing layout computations (`maxPayloadBytes`, the field-count
estimate, the SysV byval thresholds, the 64-bit array length) owed to the node-reading leg; the
per-part (a)–(e) inventory not measured separately.

**Owed.** `sqrt`, `atan2` and the transcendentals type-check and have no recipe and no witness: a reachable use stops Composer with `[ERROR] No witness handled node N — Kind: Application (...). Type: TNum (Carrier { Name = "float" ...` (loud, never a wrong result); their implementation is library-backed, the platform's libm on the x86_64 leaf. Composer's shift-amount cast stays until CS-10. The `char` conversion admission is CS-11's to close. The width-named conversion spellings are typed here like the rest and deleted in CS-11.

**Owner pass (2026-09-05), after review.** The reviewer's one must-fix is applied: the older
CCS8000 arm (`Unify.formatError`, `NotNumeric`) now renders the operator's source spelling, so
`true + true` reports `'+'` and not `'op_Addition'`. The hazard the reviewer found on the way is
closed in Composer: a compile without `-k` wrote `output.mlir` and `output.ll` at fixed names under
the shared temp directory, so two concurrent compiles could link each other's IR without a word;
every backend now writes under a per-process directory (`Core.Utilities.IntermediateWriter.scratchPath`,
`composer-<pid>`), verified by two simultaneous compiles returning their own results. Re-gated on the
final binary: build; RoundTrip transcript identical at `e10c2ce1…`; harness `--through 3` 30 of 49,
23 of 23 judged, rows identical to the implementer's; HelloArty unchanged; HelloProof 23, PASS;
drift gate clean. Two items are the owner's: the interim admission of `char` at a conversion's
source (`Applications.retypeCharConversion`, forced by BAREWire's `int (Text.charAt …)` at
`Description.fs:364` and the x86_64 leaf's `Parse.clef`), to be ratified as a conversion source in
the one spelling table or reversed by migrating those sites to a code-point function at CS-11; and
the plan's W-2, W-7 and W-8 rows, which the owner's assistant wrote before the handoff. Pre-existing
and recorded: `true - true` reports CCS8000 twice and `1 + true` reports a CCS8000 beside a CCS8003
at the same range; both collapse when operand positions are carried through the store.

## CS-10 as built (2026-09-05)

Delivered in five slices, each built inside Composer and gated before the next; every gate below was re-run on the final binary.

**Slice 1, the annotation (§0.1 item 7, Horizon C3).** `NativeTypedTree/NativeTypes.fs`, beside `NTUWidth`: `ValueRange` with the cases `Empty` (the join of no values: a record field nothing reachable constructs, width one), `Bounded (lo, hi)` (the one form with a width), `Above lo` and `Below hi` (the half-lines a widening leaves; unobservable if they survive the narrowing) and `Unbounded`; the module `ValueRange` with `join`, `meet`, `contains`, the interval arithmetic (`add`, `sub`, `neg`, `mul`, `div`, `rem`, `shl`, `shr`, `band`, `bor`, `bnot`, each exact in `bigint` and saturating an endpoint that leaves int64 to its infinity, never wrapping), `width` (the §3 formula: a non-negative range spends no sign bit, minimum one bit; `Empty` is one bit; a half-line and `Unbounded` have none), `isNonNegative`, `isObservable`, `render`, and `widen`. `PSGSaturation/SemanticGraph/Types.fs`: `SemanticNode.ValueRange: ValueRange option` (`None`: not a numeric node or not analysed; `Some r`: the range, the width derived on read and never stored), defaulted in `NodeBuilder.Create` and in the seventeen full constructions; `SemanticGraph.FieldRanges: Lazy<Map<string, Map<string, ValueRange>>>` (record type name, field name, the join over every reachable construction), defaulted in every graph construction. `Infrastructure/PhaseTypes.fs`, `PhaseEmitter.fs`, `NativeService.fs`: the range is written as `valueRange` on every node of the phase JSON (`05_psg2.json`, the final graph; `01_psg0.json` precedes the pass). `Expressions/Types.fs`: `DiagnosticCodes.CCS8011_UnobservableRange`.

**Slice 2, the pass (§1; width-inference.md §2, §3, §6).** New `PSGSaturation/SemanticGraph/RangeAnalysis.fs`, registered after `PlatformDeclaration.fs`, run in `NativeService.buildResult` after `PlatformDeclaration.fill` and before `PlatformDeclaration.check` on every substrate over reachable nodes only. The transfer rules, as implemented: an `Int` or `UInt` literal is its point, a `Bool` `[0, 1]`, a `Char` its code point; every boolean-typed node is at most `[0, 1]` and every char-typed node at most `[0, 0x10FFFF]` by its type; `DUGetTag` is `[0, cases − 1]` and a `UnionCase` or `DUConstruct` its tag; a comparison, `not`, `&&`, `||` is `[0, 1]`; `+ − * / %`, unary negation, `&&& ||| ^^^ ~~~`, `<<<` and `>>>` by the interval rules of slice 1 (division or modulus by a range containing zero has no image; `x % k` for a bounded positive `k` is `[0, k.hi − 1]` for a non-negative `x`, clipped to `x.hi`, and `[−(k.hi − 1), k.hi − 1]` otherwise, the sign following the dividend); `truncate`, `floor`, `ceiling`, `round` and every other integer-valued intrinsic (a length, a read, a conversion from a real) are unobservable here, the real domain being CS-13's; `IfThenElse`, `Match` and `CaseElimination` are the join of their branches; `Sequential` its last value; `Binding` its value, a mutable binding the join of its value and every `Set` to it; a `VarRef` its binding's; a Lambda parameter the join of the argument at every reachable call of its function (curried calls flattened), and a parameter no reachable call supplies (a declaration root's, an entry the platform calls) is unobservable here and takes the declared boundary range at CS-12; an `Application` of a user function is its body's range; `FieldGet` reads the record type's per-field join over every reachable `RecordExpr` (`FieldRanges` in the making); `TupleGet` reads element `i` of the `TupleExpr` constructions the tuple expression traces to, joined; a `[<HardwareModule>]` design's `InitialState` and the returned state (both `RecordExpr`s of the state type) feed the state type's `FieldRanges`, which the Step function's state parameter reads through `FieldGet`, and the Step function's inputs record is seeded from its declaration, a boolean pin `[0, 1]` (an integer pin has no declared range until CS-12). A counted `for` is the checker's `while` over a mutable cell, so the loop variable's cell is `[start, finish + 1]` and every read inside the body `[start, finish]` through the guard.

Comparison refinement (width-inference.md §2) is on use edges: for an `if` whose guard is `x < K`, `x <= K`, `x > K`, `x >= K`, `x = K` (either operand order, `K` any range, through `not`, `&&`, `||`, a boolean binding's definition and Baker's conditional forms of `&&`/`||`), every read of `x` by a node exclusive to the then-subtree, and the `if`'s own read of its then-branch, carries `x`'s range met with the bound (`< K`: `hi ≤ K.hi − 1`; `<= K`: `hi ≤ K.hi`; `> K`: `lo ≥ K.lo + 1`; `>= K`: `lo ≥ K.lo`; `= K`: `K`), and the else-subtree the complement; a `while` body likewise under its guard. "Read of `x`" is a reference to a compared binding or the compared node itself (Baker's recipes share one node between a guard and a branch, `min hi (max lo x)`), which is why the refinement lives on the consumer's edge and not on the node: a shared node has one range, its reads under different guards do not. A mutable binding's bound holds until the first assignment to it in tree order and, for a loop nested in the guarded subtree, is dead from that loop's first read of any mutable the loop assigns, since the loop's iterations never re-check the guard; a reference to such a mutable reads its definition unrefined on its own edge (the CS-10 review's `if n < 100 then while c < 5 do (read n; n <- n + 50; ...)`, whose inner read is now `[0, +∞)`); and never inside a nested lambda. This replaces IntervalAnalysis's "widen the narrower non-constant operand to the other's maximum" heuristic.

The fixpoint: a pure fold over an immutable `Map<NodeId, ValueRange>` in node order (Gauss–Seidel), each node the join of what it has and its transfer, to a post-fixpoint. The widening: after eight rounds an endpoint that still moves goes to the nearest threshold beyond it, the thresholds being the boundaries of the declared integer representations of the family the range's sign selects (`uint` for a non-negative range when the platform declares one, else `int`; `PlatformContext.Representations`) and, for either family, the program's settled constants (`c − 1` and `c` above, `c` and `c + 1` below, for every point range the analysis has found), then past the last threshold to its infinity; on fabric, which declares no representations, the constants and then the infinity. The constants are what let a free-running counter stop at its modulus when nothing but the modulus bounds it: `nextPhase = if not advancePhase then state.Phase else (state.Phase + 1) % cycleSteps` carries its own value forward on one branch, so a widening that overshoots the modulus is kept by the identity and no guard can narrow it back; with `cycleSteps − 1 = 1023` a threshold, the ascent stops at `[0, 1023]` exactly. Widening is per endpoint, so a counter whose ceiling is a comparison keeps its floor. After the ascent settles, up to eight rounds of narrowing recompute every node from its transfer and take the result only where it tightens (a monotone transfer applied at a post-fixpoint stays above the least fixpoint; §1.2a), which is what turns `StepTick`'s widened `[0, +inf)` into `[0, 390624]` through `nextStepTick < threshold`. An ascent past 8192 rounds is a stop naming the defect.

**Slice 3, CCS8011 (§1.3, §7).** `RangeAnalysis.diagnostics`: for every reachable integer node whose final range has no width (`Above`, `Below`, `Unbounded`), once per enclosing binding (a binding is its own; a parameter's is its function's) at the first such node in node order, `The range of '<spelling>' in '<function>' cannot be observed; bound it with a comparison, a modulus or a clamp`, the spelling being the reference, the field access (`state.Counter`), the operator result or the binding; a reference whose own binding is unobservable is that binding's finding, not a second one. Severity Error on fabric (`PlatformContext.substrateKind ctx = FPGA`: the width has no other source, and this replaces every Composer-side `FPGA0001` and the `IntWidth 0` stop with a located CCS diagnostic), Info on every other substrate in this changeset, because the CPU leg reads the carrier's width until CS-12 supplies the declared boundary ranges and CS-11 migrates the sources; the staging is a decision. `Reachability = Reachable`, so Composer prints them as information and never demotes them. Bare reals get no CCS8011 (numeric-selection.md §6: a bare float of unobservable range selects `f64`); the seam rule for dimensioned reals is CS-13's. Unreachable code is not analysed, so W-4/reject's `let rec run n = run (n + 1)`, which nothing calls, reports nothing and its row stays at the baseline.

**Slice 4, the FPGA leg reads the node (§8.2, §8.3; plan L-7, L-7b).** Deleted: `Composer/src/MiddleEnd/PSGElaboration/IntervalAnalysis.fs` and its fsproj entry, `TransferCoeffects.WidthInference` (`TransferTypes.fs`) and its computation (`MLIRGeneration.fs`), `clampZeroWidths` (`Dialects/Core/Types.fs`, the IntWidth 0 → 1 fallback). `Alex/XParsec/PSGCombinators.fs`: `nodeRange`, `extensionOp` (the `extui`/`extsi` of a value by the sign of its node's range), and `narrowType coeffects graph nodeId ty`, type-directed: `TInt (IntWidth 0)` is the width of the node's range; a struct's sentinel fields are the widths of the record type's `FieldRanges` by the node's native type, nested records, options and tuples included (a tuple's elements through the `TupleExpr` the expression traces to); a node with no range or an unobservable one is a stop naming it, defence in depth only. Every caller passes the graph (`ControlFlowWitness`, `MatchWitness`, `HardwareModuleWitness`, `LambdaWitness`, `RecordWitness`, `ApplicationWitness`, `VarRefWitness`, `DUPatterns` for a payload-less DU's zero aggregate, and the two module-value slot sites in `BindingWitness` and `VarRefWitness`). `Alex/Patterns/ApplicationPatterns.fs`, `pBinaryArithOp` on fabric: the operation runs at the width of the join of the operand and result ranges (never narrower than an operand's physical width), each operand extended to it by the sign of its own range, the result truncated to its own range's width only where that is narrower (a modulus, a quotient, a mask), and a division, modulus or right shift in its unsigned form (`comb.divu`, the new `comb.modu`, `comb.shru`) when the join is non-negative; `pComparisonOp`: both operands extended to the join's width by their own sign, the predicate signed only when the join has a negative value. `Alex/Patterns/ControlFlowPatterns.fs`: a mux operand narrower than the result is extended by its range's sign, one wider (a reference refined below its binding's width) truncated. `Alex/Patterns/RecordPatterns.fs`, `pBuildRecord`: `hw.struct_create` at the record type's settled field widths, a narrower field value extended by its sign (the CPU layout's spare per-field SSA); a wider one is a stop. `Alex/Elements/CombElements.fs`, `Dialects/Core/Types.fs`, `Serialize.fs`: `CombModU`. The CPU leg (`TypeMapping` for CPU, `SSAAssignment`) is untouched.

Found on the way, in Composer's FPGA leg, and closed because gate 4 required HelloArty to compile: a module-level value was realised as a program-lifetime `memref.global` slot on every target (`ModuleValues.isSlotBinding`), which an `hw` design cannot hold and whose initialisers the walk emitted at module scope, so the platform's clock-endpoint record (`Description = Some …`, a payload DU) was witnessed and stopped; the old `IntWidth 0` stop came first and masked it. `Alex/Traversal/TransferTypes.fs`, `ModuleValues.isSlotBinding platform graph node`: nothing is a slot on FPGA; a module-level value is a constant expression witnessed inside each `hw.module` that reads it, which the walk's per-module visited set already does. `Alex/Traversal/NanopassArchitecture.fs`: module-init bindings are not walked as roots on FPGA; the design's metadata chain is consumed structurally by `HardwareModuleWitness` as before.

**Slice 5, HelloArty, the harness, docs.** HelloArty compiles end to end (`Composer compile HelloArty.fidproj -k`, exit 0, Verilog and XDC generated, 25 ports verified) with no CCS8011; its `07_output.mlir` has the state struct at `Counter: i30, StepTick: i19, Phase: i10, PeriodMs: i12` (was `i31, i20, i11, i13`), from the ranges the pass wrote: `Counter` `[0, 799999999]` (`nextCounter = (state.Counter + 1) % maxTicks`, `maxTicks = 4000 * 100000 * 2 = 800000000`; `⌈log2(800000000)⌉ = 30`), `StepTick` `[0, 390624]` (`resetStepTick = if advancePhase then 0 else nextStepTick`, the else-read of `nextStepTick` refined by `< threshold` with `threshold = (periodMs * 100000) / 1024` in `[48828, 390625]`; `⌈log2(390625)⌉ = 19`), `Phase` `[0, 1023]` (`(state.Phase + 1) % 1024`; 10 bits), `PeriodMs` `[500, 4000]` (the join of `4000 / 8`, `4000 / 4`, `4000 / 2`, `4000` and the latched initial `4000`; `⌈log2(4001)⌉ = 12`); `ticksPerStep` is `in i12, out i19` and `periodFromButtons` `in i12, out i12`. Every extension is `arith.extui` (131; `arith.extsi` 0, was 120): every extended value in the design is non-negative. Every `arith.trunci` (32) is to its result's range width, never below it (`pwmSubCycle` i30 to i8, `(state.Phase + 1) % 1024` i11 to i10, `ticksPerStep`'s quotient i29 to i19, a refined `ph0` read i10 to i8). Divisions and moduli are `comb.divu`/`comb.modu` except the four signed `comb.divs` of the Hermite terms (one per LED, join `[-129541, 195075]`) and four `comb.icmp slt` of `pwmSubCycle < smoothN` (`smooth` in `[-506, 762]`), whose join `[-129541, 195075]` is signed; comparisons of non-negative operands are `comb.icmp uge`/`ult`. No `memref` op remains in the design (was 201, the module-value slots). HelloArty's `README.md`: the width table at the four figures with their ranges, the paragraph below it stating the branch rule (no "seeding", no "protected constants"), the sentence that a non-negative range spends no sign bit, and the wave-chase phase counter corrected to `0..1023` (its `cycleSteps` is `4 * 256`). `width-inference.md` §3's table at the same four rows, so the table and the formula agree (L-7b). §8.2 above corrected to the computed figures.

**Decisions, for the owner.** (1) `ValueRange` has five cases, not two: the standard widening moves one endpoint at a time, so the working lattice needs the half-lines `Above` and `Below` (a two-case type cannot express `[0, +inf)` and every widened loop would be unobservable, including `StepTick`), and the join over zero constructions needs `Empty` (a record field nothing reachable constructs, `ArtyReport.PeriodMs` in HelloArty's `voption` payload, is one bit, the minimum wire, not a fabricated value and not an error). Only `Bounded` and `Empty` have a width; the annotation is `Some` for every reachable integer, boolean and char. (2) The node field is `ValueRange`, not `Range`: `SemanticNode.Range` is the source range and is read everywhere. (3) The widening's thresholds include the program's settled constants beside the declared representations (the reason above; the design's "a free-running counter mod N has range [0, N−1]" is otherwise unreachable for a counter that carries its own value on one branch), followed by the bounded narrowing the owner's §1.2a names. (4) Refinement is on use edges, forced by Baker's shared nodes (the `abs` and `clamp` recipes); a shared node's own annotation stays its binding's, its reads under a guard are refined. (5) The counted `for` is the checker's `while` over a mutable cell; the cell's range is one past `finish`, the body's reads are `[start, finish]`, and no `ForLoop` rule is separate. (6) On fabric, an unsigned integer literal above int64's maximum is `Above Int64.MaxValue` and so unobservable; such a literal is CCS8018 in any case. (7) A `TupleGet` on fabric narrows only through a `TupleExpr` the expression traces to by references, bindings and blocks; a tuple element that reaches Composer through a branch join is a stop, owed. (8) The FPGA module-value model above, a Composer change outside the slice list, taken because the gate required it and the alternative was a silent default.

**Gates.** Composer build clean (`cs10-build-final.txt`). RoundTrip (`rt-cs10-final.*`): compile 0, run 0, transcript identical to `expected.txt`, hash `e10c2ce1cb87076328f8151c47b36e2d7dbe69632581c66c081e67a52386116d` unchanged (the CPU leg does not read the annotation). Harness `vet.sh --through 3` (`vet-cs10.txt`): exit 0, every row identical to `vet-cs9-final.txt` (30 of 49, 23 of 23 judged; W-4/accept and W-6/accept ok). HelloArty as above (`helloarty-cs10-final.txt`). HelloProof (`hp-cs10-*.txt`): compile 0, run prints `Hello, Houston!`, 23 obligations PASS. Drift gate clean (`driftgate-cs10.txt`). The unbounded copy of HelloArty (`nextCounter = state.Counter + 1`): exactly one `error CCS8011: The range of 'state.Counter' in 'step' cannot be observed`, no Composer stop; `let rec run n = run (n + 1)` called from `main` on x86_64: one `info CCS8011: The range of 'n' in 'run'`.

**CCS8011 inventory.** Information on CPU until CS-12; the count is the migration inventory. RoundTrip: 310 lines (0 tagged unreachable), by binding: intrinsic results (`length` 52, `write`, `toUInt32`, `+`/`-`/`*` on them), parameters no reachable call bounds (`v`, `value`, `upto`, `i`, `n`, `w`, `va`, `vb`), `Abi.alignUp`, `writeMessage`, `writeHello`, and 35 tuple elements of `readHello`/`tryReadHello`/`tryDecodeStream`/`main` (`__tuple_N.ItemK`) whose sources are those. HelloProof: 2 (`the result of 'write'` in `write` and `writeln`). Harness leaves: M-3/accept 2 and M-3/reject 2 (`coerce`), W-1/reject 1 (`x` in `f`), W-7/accept 2 (`write`), W-8/accept 4 (`fl`, `ce`, `ro`, `truncate`: the rounding intrinsics, CS-13's); every other leaf 0. HelloArty: 0.

**Owed.** The CPU leg still reads the carrier's width (`TypeMapping` for CPU, `SSAAssignment`): CCS8011 is information there until CS-12 supplies the declared boundary ranges (an entry point's argument, an FFI parameter, a wire-schema field, an MMIO register: every parameter no reachable call supplies, every intrinsic result, every array element and every `DUEliminate` payload is unobservable in this changeset) and CS-11 migrates the sources. The real domain (CS-13): a rounding of a real is unobservable, and a bare real has no range. Tuple elements on fabric beyond a traceable `TupleExpr`. A `for … in a .. b` loop is checked as a `ForEach` whose loop variable does not resolve (`VarRef ("i", None)`) and has no `Set` witness on CPU, a pre-existing defect found by the for-loop probe and not this changeset's. The `sqrt`, `atan2` and transcendental owings of CS-9 stand.

**Owner pass (2026-09-05), after review.** The reviewer's five must-fixes are applied: the
mutable refinement's loop rule and reference-edge rule above (`RangeAnalysis.refineEdges`,
`assignedWithin`); the constant widening thresholds ratified and written into §1.2a; the operation
range read by Composer from CCS (`RangeAnalysis.operationRange` for an arithmetic op, the join of
its operands and result; `RangeAnalysis.operandRange` for a comparison, its operands alone) so
that no witness computes a range, `pBinaryArithOp` and `pComparisonOp` now reading it and an
unranged operand a stop, never an empty default; a `FieldGet` on a record type nothing reachable
constructs and nothing declares is unobservable (CCS8011), not a one-bit fabrication, while
`Empty` remains the `FieldRanges` entry of a field nothing reads; `x <<< n` with `n ≥ 63` is the
half-line by the sign of `x`, never empty. Also applied: `HardwareModuleWitness` no longer takes a
per-field `max` of the parameter and returned state widths, a disagreement being a stop. Stated
for the record: the pass stops with an internal failure past 8192 ascent rounds, a defect stop
with no CCS code, since termination is otherwise guaranteed per endpoint; a comparison of a
non-reference expression (`state.Counter`, an arithmetic node) refines only reads of that exact
node, so a second identical `state.Counter` under the guard is not refined (sound, a precision
limit); the narrowing runs eight rounds after widening. Re-gated on the final binary: build;
RoundTrip transcript identical at `e10c2ce1…` with 319 CCS8011 information lines (the nine beyond
the implementer's 310 are field reads of record types nothing constructs, now honest); harness
`--through 3` rows identical to CS-9; HelloArty compiles with 0 CCS8011 and its `07_output.mlir`
byte-identical to the reviewed copy (`Counter: i30, StepTick: i19, Phase: i10, PeriodMs: i12`, 131
`extui`, 0 `extsi`); the same design at 100 MHz reports CCS0100 (depth 10 against 6) with both
remedies, so D11's temporal budget stands; HelloProof 23, PASS; drift gate clean; the unbounded
HelloArty copy gives exactly one CCS8011 error naming `state.Counter`; `x <<< 63` is `[0, +∞)` and
CCS8011 information. HelloArty's `Behavior.clef` comments now say 256 levels and 1024 phase steps.

## CS-11 slice 0 as built (2026-09-05): SSA is a nanopass derivation

**Why first.** The first CS-11 attempt minted MLIR-level values in Alex (`freshTemp`, a counter from
1,000,000) for the CPU meets, extending a counter (`MLIRTempCounter`) and three minting sites that
had survived from before the plan, hidden by two blanket drift-gate rows that exempted the whole
middle end. The owner stopped the attempt: SSA assignment is the nanopass at the end of graph
building, principal and principled, and one file (`SSAAssignment.fs`) is where an SSA fault from
`mlir-opt` is located. The attempt's edits were saved as patches and both `src/` trees reset to
CS-10 before the cut.

**Landed (Composer 9d2feb6, clef fc4128c66).** Every value a witness emits is read from
`SSAAssignment.fs`: the callee prologue (`ClosureLayout.CaptureExtractionSSAs`,
`EnvReconstructionSSAs`), the base-pointer extraction a slot holding a memref value needs
(`CaptureSlot.ExtractsBasePointer`, derived from the capture's type; the witness checks the
accumulator's type against it and stops on disagreement), the zero a unit-typed function returns
(`UnitReturns`, the first value of the body's scope), and the whole Mealy machine body
(`HardwareModuleLayout`: power-on reset, reset constants, registers, input packs, state, instance,
step result, output flatten in `outputExtractions` order, next fields), with `PlatformPinResolution`
moved before `SSAAssignment` in the pipeline so the derivation reads reset and pin facts. Gone:
`MLIRTempCounter`, `freshTemp`, `V (10000 + …)`, the LambdaWitness extraction schedule
(`V (n + workIdx + k)`), both `ssaCounter` builders in `HardwareModulePatterns` and their
forward-reference arithmetic (which counted an input pack for any multi-pin field while emitting one
only for tuple fields). The dead `MemRef` intrinsic family (nothing produced it after the NativePtr
strip) and the `NativePtr` wording are removed on both sides; the `"Ptr" | "nativeptr"` name arms
and `extractPtrElementType` with them. The `SSAAssignment.fs` header, `Architecture_Canonical.md`
and `Closure_Nanopass_Architecture.md` now state the design (a post-saturation coeffect nanopass,
read as codata, scheduled into CCS) instead of "an MLIR/LLVM concern" and "the zipper carries SSA
counters". The drift gate's blanket rows are narrowed to the six closure-retooling patterns; the SSA
row (`V (a + b)`, the counter names) is live with `SSAAssignment.fs` its one allowed file.

**The thunk builder (this changeset, uncommitted).** `pNamedFunctionAsClosure` synthesised a
forwarding function `f_as_closure` with no graph node when a named function was used as a value,
deduplicated through accumulator state (`EmittedThunks`), driven by Composer's own
`ValuePositionAnalysis`. It is replaced by a Baker recipe (`BakerSaturation.fs`, `FunctionValue`,
beside the zero-capture lambda marking): a capture-free named function in value position fans out
to an eta-expanded Lambda whose body is the flat direct call over the definition's arity (then one
application per remaining currying level, as the binding eta-expansion applies a returned closure),
marked `RequiresClosurePair`, with the enclosing function's name recorded; fold-in wires it in and
the closure path witnesses it like any written lambda. A field of a `[<HardwareModule>]` binding's
Design record is a declaration read structurally and is not elaborated. Deleted in Composer:
`ValuePositionAnalysis.fs`, the `ValuePosition` coeffect, the 7-SSA VarRef cost, the thunk pattern,
`EmittedThunks`. Consequence to close in Baker: one lambda per use site (sample 12 carries 14 where
6 thunks were deduplicated by name); the principled dedup is a fan-out memo per definition and type.

**Gates.** Composer build clean. RoundTrip: compile 0, run 0, transcript identical to
`expected.txt`; the binary hash moves from `e10c2ce1…` to `aefcc865…` (the thunk became a lambda)
and is re-baselined; diagnostics identical to CS-10 plus one CCS8011 information line for the
synthesised `_eta1` parameter of `tryReadHello` (320 lines). Harness `--through 3` rows identical
to CS-10. HelloArty `07_output.mlir` byte-identical to CS-10, SSA numbers included. HelloProof 23,
PASS. Drift gate clean. Samples 11 and 12 (an oracle for the surface, not a gate) produce run output
identical to a CS-10 reference binary built from HEAD in the scratchpad; 12's segfault and 14's
failure are pre-existing on that binary. No `V (…)` outside `SSAAssignment.fs`.

**Found on the way, not this changeset.** Ten `Fidelity.Platform` files (WebSocket, libc, pthread
bindings) still spell `NativePtr.*` 448 times and cannot compile under current CCS; the design's
`CHandle` and `Mmio` replace them (ffi-boundary §1). The CS-11 workflow brief describes a working
tree that no longer exists and is rewritten before it resumes with slices 1-4.

## CS-11 slices 1, 2(a) and the L-10 half of 2(b), as built (2026-09-05)

Slices 1 and 2(a) landed in CCS; the L-10 half of slice 2(b) landed in Composer; the node-reading
CPU leg (the rest of 2(b), 2(c)) is not landed and is written up below with the decisions it needs,
so the §12 CS-11 row stays open; slice 3 leaves CCS8011 at Info on CPU (the residual is not zero).
The implementer's tree was reviewed and rejected on four blockers and four must-fixes (the
"Review" paragraph below), which the owner's session fixed by hand; every gate below was then
re-run on the final binary from the owner's session's transcripts.

Slices 1 and 2(a) landed in CCS; the L-10 half of slice 2(b) landed in Composer; the node-reading
CPU leg (the rest of 2(b), 2(c)) is not landed and is written up below with the decisions it needs;
slice 3 leaves CCS8011 at Info on CPU (the residual is not zero). Every gate below was re-run on
the final binary.

**Slice 1(a), the intrinsic table.** `NativeTypedTree/Expressions/Intrinsics.fs`, one module
`RangeSources` at the end of the file, read by `RangeAnalysis` and nothing else. `intrinsic ctx
info args` gives `Fact r`, `ElementOf i` or `Untabled`: the comparisons and `not`/`&&`/`||`
`[0, 1]`; the `Operators` by the interval rules (moved here from `RangeAnalysis.applicationRange`);
`Array.length`, `String.length`, `List.length`, `Seq.length` `[0, 2^(Pointer − 1) − 1]` from
`PlatformContext.Dimensions "Pointer"` (`lengthRange`; Unbounded on a context declaring no Pointer);
`String.indexOf` `[−1, 2^(Pointer − 1) − 1]`; `Array.get` the element range of its array argument
(`ElementOf 0`); `Sys.read` and `Sys.write` `[−4095, hi]` with `hi` the buffer argument's length
range, a string literal's byte length exactly and the platform's length range otherwise (the errno
convention the x86_64 description's `readBound` and `writeBound` contracts state in prose, cited in
the table's comment; a later changeset moves the number into the contract); a `Convert` intrinsic
the meet of its argument's range with the target representation's declared range where that covers
it (exact) and the declared range otherwise (the wrap's image, interim until CS-12 deletes the
spellings and the conversions), a conversion to the bare kind the identity, so `int` of a `char` is
`[0, 1114111]` by the char node's own range; `sign` `[−1, 1]`, `abs`, `min`, `max`, `clamp` their
images (new `ValueRange.abs`, `minOf`, `maxOf`); the `DateTime` component extractors the ranges
their definitions state (`hour` `[0, 23]`, `minute`/`second` `[0, 59]`, `millisecond` `[0, 999]`);
`Math.*`, the rounding intrinsics and every parse stay untabled (CS-13; an input's range is a
declaration, CS-12). `calls info` says what a higher-order intrinsic supplies to the function it is
handed: `Array.init n f` calls `f` at `[0, n − 1]` (`Seed.IndexBelow 0`); `List.*`/`Seq.*`/`Option.*`
hand a value the pass does not model (`Seed.Unknown`, named in the CCS8011 text).

**Slice 1(b), the interim carrier rule.** `RangeSources.declaredRangeOfKind ctx kind`: an integer
kind with `NTUWidth.Fixed bits` takes the declared range of the representation its spelling names
(`Types.numericSpellings`, the representation column, through `PlatformContext.tryRepresentationOfSeal`),
or on a context declaring none the two's-complement or unsigned range of its bits
(`ValueRange.twosComplement`, `unsignedOf`); a `Resolved Pointer` kind likewise through its dimension;
the bare kind (`Resolved Register`) never. `RangeAnalysis.boundByCarrier` applies it to a source
node only (`isSource`: a parameter nothing supplies, a field read, an element read, an unresolved
reference, an intrinsic's or a boundary call's or a poisoned value call's result) whose transfer is
unobservable, and gives the whole declared range, the carrier's physical set, never the meet with a
half-line (the review's carrierloop probe: a wrapping carrier does not respect a half-line, and the
meet `[0, 2^31 − 1]` excluded the negative half the wrap visits). An arithmetic cycle the program
never bounds stays unobservable, CCS8011 on every substrate (§1.3), whatever its carrier; a bounded
transfer is kept. This rule is deleted in CS-12 with the spellings.

**Slice 1(c), element ranges.** `PSGSaturation/SemanticGraph/Types.fs`,
`SemanticGraph.ElementRanges: Lazy<Map<string, ValueRange>>` keyed by the element type's rendered
form (`formatType` after `applySubst`), defaulted at every graph construction (`Core.fs`,
`NodeBuilder.fs`, `NativeService.fs`, `FoldIn.fs`, `ProjectChecker.fs`), written by
`RangeAnalysis.run`. `Program.ElementStores` collects every store: an `ArrayExpr`'s elements (a
comprehension's `Yield` values), an `IndexSet` and an `Array.set` into an array, `Array.create`'s
seed, `Array.init`'s function result (a lambda in place, a named lambda's body, or every candidate's
body through a value); `Program.ElementSeeds` the constant seeds: `Array.zeroCreate`'s zero, and an
unbounded store for an array handed to a boundary call (a `Sys` intrinsic, or a call through a
binding carrying `FidelityExtern.Library`), since a platform endpoint or a C call writes where the
pass sees no store. `elementRange`: a width-named element carrier is its declared range regardless
of the stores (the byte view of a buffer is `[0, 255]`; sound because such buffers are filled by
endpoints); otherwise the join of the stores and seeds; a type nothing reachable stores into is
Unbounded. Reads: `IndexGet` on an array, `Array.get`. Coarseness, stated: one range per element
type over the whole program, so two `int array`s with different contents share a range, and an
array of records is read through `FieldRanges` as before. The rule is closed (the review's arrmap2 probe): an intrinsic that produces an array from
anything but a same-element operation on an array (`RangeSources.sameElements`: `sub`, `copy`,
`append`, `filter`, `rev`, the sorts, `take`, `skip`, `truncate`, `concat`, `distinct` and the
non-producing operations) builds elements the fold does not see (`Seq.toArray`, `List.toArray`,
`String.toBytes`, any future producer), and its result's element type takes an unbounded seed;
`Array.init`, `map`, `mapi`, `collect` and `choose` store their function value's bodies
(`RangeSources.elementsFromFunction`, `functionArgument`), unbounded through a poisoned value. A
user function's array comes from the literals, stores and intrinsics inside it, which the fold sees.

**Slice 1(d), tuple positions.** `RangeAnalysis.tupleElement` follows `IfThenElse`, `Match`,
`CaseElimination`, `Sequential`, `Binding` (a mutable one's assignments joined), `VarRef`,
`PatternBinding` (a parameter's supplies), `TypeAnnotation`, an application's callee body (a named
lambda's, or every candidate's through a value) and an element read of an array of tuples
(`IndexGet`, `Array.get`, through `ElementStores`); `TupleGet` reads it. The public
`RangeAnalysis.tupleElementRange graph nodeId index` is the settled-annotation read of the same
trace for a witness.

**Slice 1(e), calls through function values.** `escapingOf`: a Lambda anywhere but the value of
a binding (Baker's eta-expanded lambda for a named function in value position among them), a
function binding referenced anywhere but a callee position, and a named lambda applied to fewer
arguments than it has parameters (the open parameters escape, `Candidate.Offset`) are candidates,
each with the reason it escapes (`passed as a value`, `stored as a value`, `bound as a value`,
`returned as a value`, `partially applied`). `poisoningOf` (the review's valcall probes): a
function value that is no lambda, in value position, poisons every value call it may reach: an
intrinsic named as a value, a partial application whose root is an intrinsic or a non-lambda
binding, a reference to an extern or platform binding of function type. `resolveCallee`: a
`VarRef` to a lambda binding or a Lambda in place is `Direct`; an intrinsic is `Intrinsic`; anything
else (a parameter, a non-lambda binding, a field, a tuple element, an element) is
`Value (candidates, poisoned)`, reaching every candidate with at least as many open parameters as
arguments whose parameter types may unify with the argument types (`mayUnify`: a type variable with
anything, an integer never with a real, functions and applied constructors structurally, an
unknown shape not excluded), and `poisoned` when a poisoning value's domains unify likewise
(`poisonReaches`); a named lambda applied to more arguments than it has parameters hands the
surplus to the value its body returns, a call through a value. Every reaching call joins its
arguments into the candidate's open parameters (`CallArguments`); a call through a value has the
join of every candidate's body, or is unobservable when poisoned (`applicationRange`,
`tupleElement`, and the element stores of `Array.init`/`map`/`mapi`/`collect`/`choose` through a
poisoned function value, which seed the element type unbounded). Coarseness, stated: two functions
of the same shape share their arguments wherever either is called through a value (the fnvalue
probe: `k`'s parameter takes `3` from `h 3` beside `[0, 3]` from `Array.init 4 k`), and one
poisoning value of a shape makes every value call of that shape unobservable (valcall: `g sq` and
`g ((+) 100)` are both unobservable once `(+) 100` exists). A parameter nothing supplies keeps
CCS8011, whose text now names the reason: `: its function is passed as a value and no call through
a value reaches it`, `: its function is handed to 'List.map', which supplies values the pass does
not model`, `: its function is a declaration root and the parameter's range is the declared
boundary's (CS-12)`, or `: no reachable call supplies it`.

**Exact endpoints.** `NativeTypedTree/NativeTypes.fs`, `ValueRange`: `Bounded`, `Above`, `Below`
carry `bigint`; the arithmetic is exact and nothing saturates (a half-line arises only from the
widening); `shl` follows a shift amount up to 4096 exactly and reads a larger one as the half-line
by the operand's sign; `Threshold` and `widen` carry `bigint`, so the declared `uint64` range is a
real threshold. Consequence: `x * y` with `x`, `y` about `2^40` is a bounded range no declared
representation covers, CCS8012, where before it saturated to a half-line and was CCS8011. Composer
reads only `ValueRange.width`, `render`, `isNonNegative`, unchanged.

**Slice 2(a), selection.** `RangeAnalysis`: `selectRange ctx range` picks the offered integer
representation of the family the sign selects (`uint` for a non-negative range where the context
offers one) with the fewest bits whose declared range covers the range, else the widest of the
family with `Covered = false`; `selectNode` gives a width-named carrier its own representation;
public `selectedRepresentation graph nodeId : NumericRepresentation option`, `selectedWidthOf graph
range : int option` (fabric: `ValueRange.width`; a core: the selected bits, or the widest declared
for an uncovered or unobservable range, emission only while CCS8011 is information) and
`selectedWidth graph nodeId : int option` (a width-named carrier at its representation's bits, or
its spelling's bits where the context offers none). Derived on read from `graph.Platform` and the
node's range, never stored (C3). `coverageDiagnostics`: CCS8012, Warning, `Reachability =
Reachable`, once per enclosing binding, for a bare-kind integer whose bounded range no declared
representation covers, naming the range and the widest representation
(`Expressions/Types.fs`, `DiagnosticCodes.CCS8012_RangeNotCovered`); promoted under `--warnaserror`
by Composer's existing elevation (the overflow probe: warning, and exit 1 under the flag). Nothing
changes on fabric.

**Slice 2(b), L-10 only.** Composer `Alex/Dialects/Core/Types.fs`: the architecture table
`platformWordWidth arch` is deleted; `Architecture` is now `{ Isa; Register: Result<int, string>;
Pointer: Result<int, string> }`, the instruction set (`Isa`, for the OS and syscall selection) beside
the two width dimensions the platform description declares, read once from the CCS context at
`PSGElaboration/PlatformConfig.resolveOSArch` (`PlatformContext.tryWidth`, CCS8203's text where a
dimension is not declared); `declaredWordWidth arch` and `declaredPointerBytes arch` read them and
fail with that text where a site on an undeclared substrate reads them. One size model:
`mlirTypeSizeWith pointer ty` sizes every pointer-sized type (an index, a five-word memref
descriptor, a two-word closure pair) by the declared Pointer width and `mlirTypeSize arch ty` reads
it through the architecture; `TypeMapping.mlirTypeSizeForArch` is deleted and its call sites
(`TypeMapping`, `SSAAssignment`, `ClosurePatterns`, `LambdaWitness`, `MemoryPatterns`) read
`mlirTypeSize arch`; the arch-less `mlirTypeSize` sites (`RecordPatterns.structFieldByteOffset`,
`MemoryPatterns.pRecordStruct`, `pTupleStruct`, `extractMemRefShape`, `OptionWitness`,
`MemRefPatterns.pBuildAddressOf`, `PlatformPatterns`' byval sizing) take the architecture from the
parser state or witness context; `Serialize.typeToString` and every serializer above it take the
declared pointer width as their first argument (`moduleToString arch.Pointer …` at
`MLIRGeneration`, `MLIRTransfer`, `MLIRNanopass`; the obligations module passes an `Error`, since it
carries no pointer-sized type), so a struct serialized as `memref<Nxi8>` is sized by the
declaration and never by a silent eight. Deleted with the table: the agreement check at
`MLIRGeneration.generate`, the `X86_64`-defaulting `mapNativeType` and `mapNativeTypeWithGraph`
and the string-based helpers (`nativeTypeToMLIR`, `mapTypeApp`, `getReturnType`, `getParamTypes`,
`isPrimitive`, `isInteger`, `isFloat`, `isIndex`, `integerBitWidth`; no caller), the
`TypeSizing` comment in the project file (the file itself was already gone). `TypeMapping`'s
`let wordSize = match arch with X86_64 | ARM64 | RISCV64 -> 8 | _ -> 4` reads
`declaredPointerBytes arch`. The `X86_64` fallback of `resolveOSArch` for an unrecognised platform
id stands (it selects an ISA, not a width) and is noted as owed.

**Not landed: the node-reading CPU leg (2(b) narrowing, 2(c) meets), by decision.** The surface
is every place a value meets a slot, and each is a derivation SSAAssignment must hold before a
witness can read it: binary and comparison operands (`ApplicationPatterns`, the CS-10 logic on
CPU), the `scf.if` result and match arms (`ControlFlowPatterns`), a call's arguments against the
parameter nodes and a return against the caller's node (`ApplicationWitness`, `LambdaWitness`),
a mutable cell's stores and loads (`BindingWitness`, `MutableAssignmentWitness`, `VarRefWitness`),
record fields and tuples (`RecordPatterns`, `TupleExpr`), array elements at every allocation and
access site (`MemoryPatterns`, `ArrayExpr`, `IndexSet`), DU payloads (`DUPatterns`), closure
environments and the closure calling convention (`ClosurePatterns`, `SSAAssignment.mapCaptureType`),
yields, interpolated strings, the syscall ABI (`PlatformPatterns`), and every C ABI call. Three of
these need a decision the design does not yet state, and were not decided here: (i) the closure
calling convention: a lambda called through a value has parameters whose width the call site cannot
know (any candidate), so the closure ABI must be a declared boundary (the platform word) while a
direct call meets the parameter node's width; (ii) record layouts: CCS computes
`TypeLayout.Inline (size, align)` before the range pass, so a field selected narrower than its
carrier leaves the CCS size as padding unless the layout is recomputed from `FieldRanges` after
saturation (a CCS change to `TypeConRef.Layout`, which every type carries); (iii) a refined read
of a wide cell (`VarRef` under a guard) either truncates at the read or keeps the cell's physical
width with the consumer adapting from the physical type, and the CS-10 fabric rule (an operation
never narrower than an operand's physical width) means slots must narrow for anything to narrow.
Landing a partial set of meets produces an MLIR verifier failure at best and a wrong binary at
worst (a closure ABI mismatch is not caught by the verifier), and RoundTrip's gate is a byte-identical
transcript, so the leg is owed whole, after (i)–(iii) are ratified, with the derivation table (per
consumer kind: the operand position, the expected width's source, the SSA the meet takes) written
into SSAAssignment first. Consequently pBinaryArithOp's CPU branch, the L-8 shift-amount cast and
L-9 `pTypeConversion` stand as they were, and the RoundTrip hash does not move in this changeset.

**Gates.** Composer build clean. RoundTrip (`rt-cs11.*`): compile 0, run 0, transcript identical
to `expected.txt`, hash `aefcc865bd4817195ea61b0a676ba6cb00d403b1539ad9062d950a66986d83c9` unchanged
(the CPU leg does not read the annotation; `07_output.mlir` byte-identical to the pre-changeset
capture `cs11/roundtrip-before.mlir`); 117 CCS8011 information lines (from 320) and 1 CCS8012
warning (`Validator.validate`, `3 * n` with `n = Array.length fields` in `[0, 2^63 − 1]`, range
`[0, 27670116110564327421]`, `uint64` selected; a finding the design intends, and a failure under
`--warnaserror` until the source bounds `n`). Harness `vet.sh --through 3` (`vet-cs11.txt`): exit
0, every row identical to `vet-cs10-final.txt` (W-4/reject unchanged, CCS8011 not promoted).
HelloArty (`cs11/helloarty-cs11.txt`): exit 0, 0 CCS8011, `07_output.mlir` byte-identical to CS-10.
HelloProof (`cs11/hp-cs11.*`): compile 0 with 0 CCS8011 (was 2: `write`'s result is tabled), run
prints `Enter your name: Hello, Houston!`, 23 obligations, PASS, anchors unchanged. Drift gate
clean. SSA: no `V (` or `SSA.V` outside `SSAAssignment.fs`; no counter, pool, budget or spare
vocabulary in the diff (one pre-existing comment in `RecordPatterns` reworded).

**Inventory (gate 7).** RoundTrip 320 → 117 CCS8011 (all Info); HelloProof 2 → 0; W-1/reject
1 → 0 (its `int32`/`int64` parameters take their declared ranges); M-3 2 + 2 unchanged (`coerce`, a
`Ptr` payload); W-7 2 → 0; W-8 4 unchanged (the rounding intrinsics, CS-13). Per part on
RoundTrip, cumulative in the order (a)–(e): see the report. The residual on RoundTrip by category,
one example each: 51 bindings or parameters that are cursors no comparison bounds
(`offset` in `Encoder.writeU8`: guarded by `Cursor.fits data offset 1`, a predicate whose bound
`count <= Array.length data - offset` is relational and not inlined, §1.2a's owed refinement, or a
source change in the CS-12 sweep; `pos` in `Fmt.digitsOf`, a digit-extraction loop bounded by the
magnitude of `v`, which needs a comparison on `pos`), 18 arithmetic on such an operand
(`the result of '-'` in `digitsOf`), 20 results of user functions whose bodies are those
(`writeUInt …` in `writeData`), 20 tuple elements whose sources are those (`__tuple_1959.Item2` in
`readInt`, the returned offset), 8 record fields of types whose constructions the pass does not see
(`bf.Position` in `Validator.validate`, `w.Bits` in `Check.checkWidth`: records of the platform
description, declared boundaries at CS-12), 0 parameters of escaping functions and 0 untabled
intrinsic results. The two W-8 lines are the rounding intrinsics (CS-13); M-3's `coerce` is a `Ptr`
payload read (step 5).

**Probes (gate 8), under `probe/cs11/` and the review's `probe/cs11r/`, on the final tree.**
(a) `lenloop`: `n = Array.length arr` `[0, 9223372036854775807]`, the loop cell `i`
`[0, 9223372036854775807]`; (b) `bytebuf`: `buf.[1]` for `buf: byte array` `[0, 255]`;
(c) `conv`: `uint32 x` with `x` `[0, 10]` gives `[0, 10]`, with an unobservable argument
(`truncate 3.7`) `[0, 4294967295]`; (d) `tupleif`: `let a, b = if c then (1, 2) else (3, 400)`
gives `a` `[1, 3]`, `b` `[2, 400]`; (e) `fnvalue`: `let g h = h 3 in g f` gives `f`'s `x` `[3, 3]`
through the eta-expanded lambda's `_eta0`, `Array.init 4 k` gives `k`'s `m` `[0, 3]` (joined with
the `3` every candidate of `h 3` receives), `r = g f` `[0, 6]`; (f) `overflow`: `x * y` with both
about `2^40` (built by arithmetic, since the lexer still limits a literal to 32-bit signed, CCS1147,
pre-existing) gives `warning CCS8012: The range [1208925819615728686333952, …] … the widest,
'uint64' (64 bits, …), is selected` and `error CCS8012`, exit 1, under `--warnaserror`; (g) not
applicable, the CPU leg is not landed (the counter probe's `i` is `[0, 10]`); (h) `recfree`:
`let rec run n = run (n + 1)` called from `main` gives one `info CCS8011: The range of 'n' in
'run' cannot be observed`. The review's: `valcall` and `valcall2` (`g sq` beside `g ((+) 100)` or
`g abs`): every value call through `g` is unobservable, CCS8011 on `h`, `g …` and the sum (was
`[0, 1]` for `103`); `arrmap2` (`Seq.toArray` of a comprehension): `b.[0]` unobservable, CCS8011
(was `[1, 3]` for `1000000`); `carrierloop` (a wrapping `int32` counter with no bound): `i`
unobservable, CCS8011 (was `[0, 2147483647]`); the probe itself is rejected by the checker with
CCS8003 (`int32 + int`), as the review noted, so the mechanism shows on the pass's annotations.

**Decisions, for the owner.** (1) `ValueRange` endpoints are `bigint` (the reason above: CCS8012
needs the bounded range a product leaves 64 bits with). (2) A width-named element carrier's range
is its declared range regardless of the stores (buffers are filled by endpoints the pass does not
see), and an array handed to a boundary call takes an unbounded store. (3) The candidate rule joins
every value call's arguments into every unifiable escaping lambda; a partial application makes the
open parameters candidates. (4) `Architecture` carries the declared widths as `Result`s rather than
a module-level setting, so that no mutable and no default exists and an FPGA description, which
declares neither, fails only at a site that reads one. (5) The CPU leg is owed whole, for the three
decisions above; `platformWordWidth` is gone but `mapNTUKindToMLIRType` still maps the bare kind to
the declared word on CPU. (6) CCS8011 stays Info on CPU: the residual is 117 on RoundTrip.

**Owed.** The node-reading CPU leg and its meets (2(b), 2(c)) with the SSAAssignment derivation
table, after decisions (i)–(iii); the L-8 shift-amount cast and L-9 `pTypeConversion` with it; the
per-node coverage witness at boundaries (CS-12's declarations); `resolveOSArch`'s `X86_64` fallback
for an unrecognised platform id (an ISA default, to become a diagnostic); Composer's witnesses for
`Array.init` and `List.length` on CPU (`No witness handled node`, pre-existing, met by the probes);
the lexer's 32-bit literal limit (CCS1147) against D10; the relational refinement of §1.2a
(`count <= length - offset`) or the CS-12 source sweep for BAREWire's cursors; the platform
description's records as declared boundaries (CS-12).

<!--
Provenance: derived on 2026-09-04 from the corpus in the owner's authority order (arXiv papers in
markdown, then the spec, then site docs and blog; grade-axis and coexponential research notes as
directional guidance) by a read-only extraction, adversarial verification and two-angle design pass.
Status: design, presented for the owner's review before any code. Nothing here has been built or
verified against a build. Code line numbers measure the gap only; the code is never the authority.

Reconciliation with Dimensional_Vetting_Plan.md (the plan wins where they differ):
- (e.3) "the seals meet under one rule" is the precedence composition of numeric-selection.md §3.4
  (the seal's dynamic range is the binding claim; the bare operand's analysed range becomes the
  containment obligation), "not a lattice meet"; the table's verdicts stand, the mechanism is override.
- (e.3, g W-6) the range coeffect of a generalised function is analysed per instantiation (DTS/DMM
  §2.6) and the non-inline body is emitted once at the join; plan W-6 as amended.
- (e.5, g W-4) the dimensioned-real seam is the plan's NS-1 row, gated by step 8, with a code in the
  numeric-selection family rather than CCS8011; the integer half stays W-4.
- (0.4) range propagation runs in Elaboration where no platform fact is needed and closes, with
  selection, at Saturation; plan D1 phase note and rough edge R-12.
- (f) codes are provisional until the D3 mapping table lands; the plan's D3 states the allocation rule.
  Region mismatch is CCS8100 (the null codes are gone from error-handling.md). Every coverage finding
  (CCS8012, CCS8016, coverage-empty) is a Warning promoted to an Error under --warnaserror, the owner's
  rule of 2026-09-04; unobservable-range findings (CCS8011, CCS8047) stay Errors.
- The seal form is resolved (numeric-selection.md §5 as amended): the named representation type in type
  position; only the lossy-conversion discipline syntax is open. Open items i.1 and i.6 are closed.
- Horizon_Requirements.md adds: per-coefficient selection for aggregates; a range containment over Z is
  a QF_LIA obligation and QF_BV carries fixed-width facts; region and access are an enumeration-sort
  family discharged in QF_UF, a third family beside group and lattice; a hyperedge may span families and
  is projected per family before discharge.
-->
# Design note: units of measure in the PHG and Kennedy unification in CCS

Synthesis of Design A and Design B under the verification verdicts. Hardening steps 1 and 2 of `/home/hhh/repos/clef/docs/fidelity/phg/Dimensional_Vetting_Plan.md` §5, with the width discipline stated far enough that steps 1 and 2 cannot foreclose step 7. Read-only. Nothing verified against a build.

Conventions. "Plan" is `/home/hhh/repos/clef/docs/fidelity/phg/Dimensional_Vetting_Plan.md`. "PHG plan" is `/home/hhh/repos/clef/docs/fidelity/phg/PSG_to_PHG_Plan.md`. "Paper" is `/home/hhh/repos/arxiv-papers/dts-dmm-paper.md`. "DBC" is `/home/hhh/repos/arxiv-papers/decidable-by-construction.md`. "NFT" is `/home/hhh/repos/arxiv-papers/negative-fractional-types-in-fidelity.md`. "GA-01" and "GA-02" are `/home/hhh/repos/arxiv-papers/research/grade-axis/01-…` and `02-…`. Spec chapters live under `/home/hhh/repos/clef-lang-spec/spec/`. Code line numbers measure the gap only.

Governing invariants, PHG plan §I.2 lines 50-56. I1: "Every $S_f$ is finite and fixed at elaboration. This is what keeps obligations quantifier-free." I2: "Annotation only accrues, over $\{\mathrm{Fresh} < \mathrm{Elaborated} < \mathrm{Saturated}\}$. A hyperedge rule fires only when **all** $v \in S_f$ are Saturated". I3: "Deciding a placement and proving it sound are the same act at saturation." I4: "Its consequence reaches Alex only as (a) saturated annotations on the nodes it governs, read as codata, or (b) a reified attribute set on emitted ops."

Diagnostic numbering. The verification verdicts on UoM-1 through UoM-7, UoM-9, W-1, D3 and M-4 found that the Plan's `CCS8100`, `CCS8010` and `CCS8003` collide with codes the spec has bound. The renumbered set is in section (f) and the Plan amendment in section (j). Where a verdict named a replacement, `CCS8040` for measure mismatch and `CCS8013` for seal mismatch, that number is used. Every other new code is an unallocated number inside the spec's own blocks, `error-handling.md` §Error Codes lines 189-190: "| CCS8000-CCS8099 | Type system (null-freedom, [access kinds](access-kinds.md)) |\n| CCS8100-CCS8199 | Memory management (regions, lifetimes) |".

---

## 0. The PHG derivation

**0.1 The dimension is a group-axis component of α on a numeric node.** `/home/hhh/repos/arxiv-papers/program-hypergraph-paper.md` §2.1 line 78: "each carrying a type annotation $\tau(v)$, a dimension annotation $\delta(v) \in \mathbb{Z}^n$, and a coeffect annotation $\kappa(v)$"; line 80: "$\alpha : V \to \mathrm{Ann}_V$ is the vertex annotation function assigning dimensional, coeffect, and lifetime properties to each node." Its algebra is the group family. GA-02 §2 line 21: "| Dimension | Free abelian group $\mathbb{Z}^7$ | Yes | Unitary (Hermite) | QF_LIA |". So $\delta(v) \in \mathbb{Z}^{B} \oplus \mathbb{Z}^{M}$, $B$ the declared base measures and $M$ the live measure variables. It sits on the numeric type inside α. D4 as amended in (j).

**0.2 A dimensional equation is a hyperedge over an enumerated source set discharged in QF_LIA.** Paper §2.2 line 78: "Addition of `a + b` generates $d(a) = d(b)$. Multiplication of `a * b` generates $d(\text{result}) = d(a) + d(b)$." The source set is the operand pair, fixed at elaboration, I1. It fires only when both sources are elaborated. `program-hypergraph.md` §3 line 41: "The inference rule for a hyperedge SHALL fire only when every node in $S_f$ is elaborated. A partial firing over a subset of sources SHALL NOT occur". Discharge family: `grade-discipline.md` §4.1 line 204: "The group family (dimensional exponents, parity) discharges in QF_LIA." Emission never reads the hyperedge. `program-hypergraph.md` §5 line 54: "The emission traversal SHALL NOT query the hyperedge set."

**0.3 Width is a lattice-axis coeffect propagated along edges, never unified.** GA-02 §2 line 24: "| Width | Bounded interval domain over $\mathbb{Z}$ | No | Meet-directed | QF_BV |"; §7.1 line 87: "support is propagated, never unified; parity and dimension are unified, never propagated; principality means most general unifier on the group axes and least fixed point on the lattice axes, each in its native sense." D1, Plan §6 line 178-179: "the type of a number is its kind (integer or real) and its dimension. Width and representation are not part of the type".

**0.4 Phases.** Paper §4.1 line 370: "**Elaboration.** Raw parsed syntax is enriched with type and dimensional information through inference."; line 372: "A saturated node has a complete, stable set of annotations: its type, dimension, memory placement, lifetime, and target-specific resolution are all determined." Dimensions need no platform, so their equations close during Elaboration. The residual check "no unresolved, ungeneralised measure variable" is asserted at Saturation. Width needs the platform and is Saturation work. `ntu-dimensional-architecture.md` §4.3 lines 310-312: "Resolution happens in CCS, at saturation, against the platform description of each section … Nothing below the witness boundary resolves a dimension". Monotonicity holds because a substitution binds a fresh variable and never retracts, I2.

---

## CS-1 as built (2026-09-04), and the four places the code departs from the letter of this note

`src/Compiler/NativeTypedTree/DimensionAlgebra.fs`, module `Clef.Compiler.NativeTypedTree.DimensionAlgebra`, compiled before `NativeTypes.fs` with no dependency on it. Departures, each sanctioned as the design of record: (1) `Dimension` is a public record; F# cannot forbid a record expression without hiding the fields, so `Dimension.mk` is the one constructor by contract and, in the codebase, in fact. (2) There is no `MeasureStore` type: per plan D7 (U-2) the solver is pure over a caller-supplied lookup and a threaded `MeasureSupply` value, and returns the bindings to make; the store is the existing union-find, whose only writer for measure cells is `solveDim`'s returned bindings (I2, never rebind), which is what keeps `resolve`'s fixpoint acyclic. (3) `renderVar` is exposed beside `render` because CCS8041 names a variable; it is the label `render` uses, so there is still one formatter; anonymous variables render as `'_n`. (4) `BaseMeasure.Module` is `string list`, the same type as `ModulePath`, which is declared later in `NativeTypes.fs`. Two rules the code fixes that (a.4) left implicit: "alphabetical" is ordinal and case-sensitive, as F# orders measures; a dimension whose numerator is empty renders as `1 / s^2`. `MeasureVar` identity is the `Id` alone, by custom equality and ordering, so a renamed survivor of generalisation stays the same variable. Exponents are `int`; the CS-2 syntax translator bounds the written power (a CCS8048-class diagnostic for an unrepresentable one) so the group arithmetic never overflows.

## CS-2 as built (2026-09-04)

`src/Compiler/NativeTypedTree/MeasureEnvironment.fs` (the declaration table, a sibling of the algebra, before `NativeTypes.fs`, no syntax and no type DU) and the translator section at the end of `Expressions/Types.fs`. Rules the code fixes that (a.3) and (a.4) left implicit: (1) a declaration group is ordered before any body is translated, by the bare names each body references (`measureReferences`, the registrant's syntax-aware listing passed into `MeasureEnv.registerGroup`), so a member is registered before every sibling that names it and a sibling that redeclares an outer name shadows it before any body can bind to the outer one; a reference that returns to a member still being ordered is CCS8043 with the chain. (2) A body whose expansion is not ground is CCS8049: a measure variable there is a parameter the declaration does not declare. (3) The translator lives in `Types.fs` because a name found as a type is CCS8045; registration takes it as a parameter, so there is still one translator. (4) The entry forms are `MeasureSyntax.Measure` (a literal's annotation), `Type` (an argument read in the measure sort) and `Applied` (a constructor with its argument list); `1.0<'u>` is CCS8044 in the `Measure` form, `_` mints a fresh variable. (5) The written exponent is bounded at 32767 and every translation step is checked, so the algebra's `int` arithmetic cannot overflow during translation; bounding the solver's bindings is CS-4's. (6) The failure value `MeasureFailure` is a DU; `describeMeasureFailure` beside `DiagnosticCodes` is the one projection to code, message and range. (7) Registration returns the first failure; per-declaration reporting is the declaration arm's (CS-4).

## CS-4 as built (2026-09-04)

Fifteen clef files and two Composer files; the emitted RoundTrip binary is bit-identical before and after every slice. Departures from the letter, each sanctioned: (1) `TNum of carrier: TypeConRef * dim: Dimension`, the carrier being the existing numeric type constructor with its width still inside and still compared by name (plan D7); `Carrier = Int | Real`, `CarrierRef` and `TypeParamKind.Carrier` arrive with the step-3 operator schemes. (2) Measure variables bind in the existing union-find as kind-checked cells; the bridge from the algebra's value-typed `MeasureVar` to its cell is a private id-keyed index inside `UnionFind.fs`, mutable within the one store's own regime and retired with it by the PHG saturation lattice; `lookupMeasure` and `resolveDim` are the only reads, `bindMeasures` the only writer, called only with `solveDim`'s bindings and failing on rebind (I2). Redesigning `MeasureVar` to carry the cell was rejected because it would couple the pure algebra module to the store. (3) CCS8041 prints the equation as `'v^k = residual^-1'`, which is true as written, rather than (f)'s `'v^k = residual'`; divisibility is unaffected and the rendering is the one renderer's. (4) A `[<Measure>] type` declaration produces no PSG node; a declaration group registers through `registerGroup`, and per-declaration reporting is a retry that sets aside the failing declaration, reports it at its own range, and registers the rest. (5) A named variable `'u` is one variable within one annotation; sharing across a binding's annotations and generalising are CS-6 (b.4). (6) `TVar ~ TNum` binds the variable to the whole `TNum`. (7) The unifier bounds the resolved sides of every equation and every binding it applies (the CS-2 obligation), surfacing `CCS8048`. (8) Types leaving the store are not yet resolved through the measure cells, so a variable bound to `1` still prints as `'_n`; that is CS-8's saturation residual check. (9) `measureExponentBound` moved to `DimensionAlgebra.fs`, one place, because `Unify.fs` precedes `Types.fs` in compile order. Harness after CS-4: 16 of 45 rows match; UoM-2, -3, -4, -9 rejects and NS-1/reject are green by the interim `'T -> 'T -> 'T` operator type and will move again at step 3; NS-2/reject and NS-3/reject were rejected only by the arity accident this changeset removed and are step-8-pending.

## CS-5 as built (2026-09-04)

`Types.numericSpellings` in `NativeTypes.fs`: one row per spelling with its carrier and its conversion operation; the type-position resolver, the SRTP conversion set and target table, the conversion intrinsics and the parse/format dispatch read it. The four tables it replaced disagreed in three places (`sbyte` absent from the resolver; `uint` and `float64` absent from the SRTP set), reconciled by the one table; the RoundTrip binary is unchanged. The per-width carriers the table points at are the D7 interim: at step 7 the carrier column collapses to `Int | Real`, a seal column takes the width, and the nineteen per-width constructors are deleted. `float64` is admitted as a type spelling (the explicit IEEE-64 seal, numeric-selection.md readouts) and aliases `float` until step 7 separates the bare kind from the seal; NS-4/accept turned green on that admission, not on step 8's mechanism.

## CS-6 as built (2026-09-04)

Thirteen clef files, two Composer files, one new harness leaf (UoM-10); the RoundTrip binary unchanged. What landed: `CarrierRef = Carrier of TypeConRef | CVar of TypeParam` with `TypeParamKind.Carrier`, a carrier variable binding in the union-find kind-checked, `CarrierRef.resolve` the one read (a second walker over the same chain as `find`, no path compression, placed in `NativeTypes.fs` because the numeric predicates and Composer read it); the operator schemes stated once in the intrinsic table and instantiated fresh per use (`- % * /`, unary minus and plus); `+` as the D5 kind dispatch through `Constraint.OperandOf` on the operand variable; generalisation over measure and carrier variables with column Hermite simplification; same-kind instantiation from one minting place; the `Application` node's `Scheme.Instantiation` annotation; CCS8047 and CCS8001 at non-generalisable value bindings; measure-only schemes emitted as one body. Departures, each sanctioned: (1) comparison, `min` and `max` keep the shared-variable typing (`'T -> 'T -> bool`), which at numerics is the one-dimension scheme; a carrier-only scheme would refuse `=` on strings, chars, bools and unions. (2) `abs` and `sign` are not operator names: they are library functions with the (c) schemes at step 3, and an operator name pre-empts binding lookup, so the reviewer's shadowing finding is closed by leaving them to lookup. (3) A named measure variable is scoped to its binding: `withMeasureScope` mints one variable per name written in the parameter and return annotations, the translator seeds its scope from `TypeEnv.MeasureScope`, and a body annotation that names it reads the same variable; `(y: float<'u>) (z: float<'u>)` used at two dimensions is CCS8040. (4) Hermite simplification at full rank keeps the candidates and their names (no change of basis); a dropped column is the measure `1` in every binding, never a variable the scheme must quantify or a local could leave unresolved. (5) Measure variables in `TMeasure` positions (`Arena<'lifetime>`) are neither generalised nor residual-checked; region and lifetime take their own kind at step 5. (6) Type variables are not environment-subtracted (as before); only measure and carrier variables are. (7) The mixed `1 + "a"` reports the type mismatch rather than CCS8000 naming `+`; CS-7 carries the presentation. Carried to step 3: Composer has no witness for `op_UnaryNegation`, `op_UnaryPlus`, `abs` or `sign` (its atomic-operation classifier never knew unary negation; `-x` on a variable fails loudly at emission today and did before CS-6), and non-generalised function bindings with an unbound carrier are reported by Composer's loud failure rather than a located CCS8001.

## CS-7 as built, first half (2026-09-04): every diagnostic on its own CCS code

Decision D3 executed. `DiagnosticCodes` in `Expressions/Types.fs` holds only CCS-series constants, allocated inside the blocks `error-handling.md` fixes, and that chapter's new "CCS code table" is the record; the two generic helpers (`addError`, `addWarning`) and the `FS0001` blanket arm in the unifier-error surfacing are gone, each producer carrying its own code (type mismatch CCS8003, arity CCS8004, infinite type CCS8005, tuple CCS8006, byref CCS8007, undefined constructor CCS8008, undefined value CCS8009, internal invariant CCS8090). Constructs Clef does not have are CCS8060–CCS8064; BCL surface is CCS8080–CCS8083; the null keyword is the one null diagnostic, CCS8010. Inherited lexer and parser diagnostics keep their F# number under the CCS prefix (`CCS0010`, `CCS0058`), rendered by `parseString` and printed by Composer as `error CCS0NNN: file(line,col): text`. The (f) table of this note is superseded by the spec's table wherever they differ. The second half of CS-7, decision D8 (representations declared by the platform description), is CS-7b.

## CS-7b as built (2026-09-04): the platform description declares its widths and representations

Decision D8 executed, with the quotation ruling of the same day (the descriptor is authored as a quotation and stays one; the compiler reads the typed record inside it and never evaluates it). The declaration: BAREWire's `TargetCore` (`Platform/Description.fs`) gains `Widths: WidthDeclaration array` (`{ Name; Bits }`) and `Representations: Representation array` (`{ Name; Capability; Family; Bits; MinMagnitude; MaxMagnitude; Boundary }`, the tags closed-vocabulary strings in `Tags.fs`; `Check.run` refuses duplicates, unknown tags, no bits, missing bounds and a Register width disagreeing with the word size); the Contracts twin (`Contracts/PlatformContracts.clef`) declares the same with lists and `PlatformDescriptor.Core: TargetCore option`. The x86_64 leaf declares Pointer and Register 64, int8..int64 and uint8..uint64 (native, wrap), float32 and float64 (native, exact), posit32 (emulated, saturate), each with its exact decimal range; the RA6M5 leaf declares Pointer and Register 32 and the integer representations; STM32F7, GPU, NPU and the Arty declare `Core = None` until their source packs are staged (a program needing `int` against them is CCS8203 by design; an FPGA site never asks, §7.1 of the architecture chapter).

The compiler: `PSGSaturation/SemanticGraph/PlatformResolution.fs` is the one reader. It follows a quotation (`SemanticKind.Quote`) or a plain binding to the typed `RecordExpr`, reads `Core` through `Some`/`None` in both the pre- and the post-saturation form, and reads only a declaration in a file under the platform binding's project directory: a description value elsewhere in the program is data (BAREWire's RoundTrip sample builds one to run `Check.run` on). `PlatformDeclaration.fill` writes `PlatformContext.Dimensions` (keyed by declared name) and `Representations` once, at the saturation entry in `NativeService.buildResult` after Pass 5; nothing else writes them. `PlatformDeclaration.check` reports the declaration's own defects first, at the declaring node: CCS8206 an element the reader cannot read, CCS8207 a tag outside its vocabulary, a width or representation of no bits, a name declared twice, a Register width disagreeing with `WordSizeBits`, CCS8208 a second description of one form among the binding's sources; then every reachable site whose carrier the declaration does not answer, CCS8203 for an undeclared dimension and CCS8204 for an unoffered representation, once per name at its first site in node order. A seal spelled by name resolves by name; one named through a dimension (`int`, `nativeint`) resolves to the offered representation of its family at the dimension's declared width (`PlatformContext.tryRepresentationOfSeal`), so no name is synthesised and a description names its representations as it likes. Retired: `buildPlatformContext`'s `word_size` reading with its x86_64 and platform-word fallbacks, `PlatformContext.defaultLinux_x86_64`, `fromPlatformPath` and `PointerAlign`; every width read is a `Result` carrying CCS8203's text; a `word_size` key still in a project file is CCS8205 information, and the nineteen Fidelity.Platform project files that carried one no longer do. Composer's `platformWordBits` and `PlatformWordType` read the context's Register and fail with CCS8203's text when it is absent; Alex's architecture table (`platformWordWidth arch`, L-10) is checked against the declaration at `MLIRGeneration.generate` and stops the build on disagreement, and is retired with step 7. Found on the way: a one-line list literal was checked as a comprehension body (`Collections.fs`), so a Contracts `Representations = [ ... ]` read as one element; lists now flatten as arrays do.

Gates: Composer build; BAREWire 309 of 309 with cvc5 dispatched; RoundTrip transcript identical, the binary hash moved from `86f21d93…` to `e10c2ce1…` at the BAREWire slice alone, because RoundTrip's own `Main.clef` calls the extended `Check.run` (the clef and Composer changes leave the hash where that slice put it); harness `--through 2` identical to CS-7's table, no platform code in any leaf; HelloArty `07_output.mlir` unchanged (its compile fails at the pre-existing IntWidth 0 point); HelloProof 23 obligations, PASS; drift gate clean. Probes: Register undeclared → one CCS8203 at `Cursor.fs:22`; int16 declared unavailable → one CCS8204; the RA6M5 leaf without Register → CCS8203 for Register only, Pointer and int32 found; capability `"fast"` → CCS8207 at the declaration, then CCS8204 at the site; Register declared twice → one CCS8207; the x86_64 description authored as `<@ { ... } @>` → compiles clean. Reported, not done: the BAREWire `Check.fs` and `Manifest.fs` additions follow that file's while/mutable idiom (native-compiled, no HOFs there), the owner's call; the x86_64 leaf's `Helpers.clef` and `Syscalls.clef` still opened the F# quotations namespace (unreachable, CCS8080 information), a vestige of the deleted CPU quotation on the canonical note's kill-list; removed in CS-8 under D9.

## CS-8 as built (2026-09-04): the saturation residual, and quotations made intrinsic

**The residual.** At the store boundary in `NativeService.buildResult`, after every node's type is resolved through the substitution, the measure store and the carrier store (`applySubst`, which already resolved `TNum` dimensions and carriers) and before the map is copied per instantiation, `saturationResidual` asserts per node: a resolved type that still mentions a measure or carrier variable no enclosing scheme quantifies is CCS8047 at the node, naming the enclosing binding, once per binding; nothing is defaulted to `1`; from there the node map is immutable (I2). The binding-level check of CS-6 reports a value binding's own type; this one reaches the nodes under a binding whose own type is closed (`0.0<_> + 1.0<_> > 2.0<_>` inside a `unit -> bool`), which compiled clean before. Found on the way and fixed: every walk up the tree in this file read the node's `Parent` field, which the builder sets only where a checker arm calls `SetParent`, so an expression node's was `None` and "quantified by the enclosing scheme" was vacuous; the walks now read a parent index derived from the children lists, which are complete by construction (`parentIndex`, one place); and the binding-level check reported one open variable at two bindings (`let _ = v`), now once, at the first in node order.

**Quotations (D9).** `Expr<'T>` resolves in type position as a built-in constructor and the bare `Expr` as `Expr<_>` (it had been `TError`, and an error type unifies with anything, so `let syscallTable: Expr<Map<string, int>> = <@ ... @>` had been silently accepted with no type: plan L-14, now CCS8706 at the annotation for any undefined type). A binding holding a quotation is a declaration: `Bindings.fs` gives it no `MainPrologue` strategy, `Core.fs` puts it in neither the module-init nor the definition list, `Reachability.computeReachable` does not enter it from its module, and Composer's traversal (`NanopassArchitecture.visitAllNodes`) reads `IsReachable` on a child and does not witness one the graph marks unreachable, which it had never done. A reference to a quotation from executed code is CCS8066 at the reference (module-level) or at the quotation (expression position), except from inside another quotation; a splice is CCS8065 at `op_Splice`/`op_SpliceUntyped`. The x86_64 leaf's two `open`s of the F# quotations namespace are gone; its `syscallTable` quotation stands, unreferenced and unemitted.

**Gates:** Composer build; RoundTrip transcript identical, hash `e10c2ce1…` unchanged from CS-7b (the re-baselined reference, the owner's word of 2026-09-04); harness `--through 2` identical to CS-7's table except the ten M rows, whose first printed error is now the located CCS8706 for the step-5 types (`Stack`, `Flash`, `Peripheral`) instead of a later CCS8009 or a Composer crash, 24 of 46 and 10 of 10 unchanged, no CCS8047 or CCS8066 on any accept leaf; HelloArty `07_output.mlir` unchanged (pre-existing IntWidth 0 failure); HelloProof 23 obligations, PASS; drift gate clean with the F# quotations namespace retired corpus-wide. Probes: comparison residual in `g` → one CCS8047 naming `g` at the literal; `let v = 0.0<_>` with `let _ = v` → one CCS8047; `0.0<_> + 1.0<m>` → clean; an inner value binding under a measure-polymorphic function → clean; `Expr<int>` and bare `Expr` annotations → accepted, and their run-time references → two CCS8066; an unreferenced module-level quotation → compiles clean; `<@ %q + 1 @>` → CCS8065 and one CCS8066 at the run-time reference, none at the in-quotation reference; `let x: Foo = 1` → CCS8706; the quoted x86_64 description → read, clean. Reported: BAREWire's `Check.fs:496` names `BAREWire.Hardware.PeripheralLayout`, undefined in the RoundTrip subset (CCS8706, unreachable, information), which had been a silent error type; HelloProof's tracked `compile.log` is a snapshot from before CS-7 (FS codes, the namespace opens) that its `run.sh` refreshes.

## (a) The annotation on a numeric node

### a.1 The measure component

```fsharp
/// A declared base measure, `[<Measure>] type m`. Identity is the declaration, module-qualified.
type BaseMeasure = { Name: string; Module: ModulePath }

/// A measure inference variable. `_` mints an anonymous one, `'u` a named one.
/// It is a TypeParam of kind Measure; its identity is the measure store's.
type MeasureVar = { Id: int; Name: string option }

/// A point of Z^B (+) Z^M in canonical form: no stored exponent is zero.
/// Both maps empty is the measure 1. Constructed only through Dimension.mk.
type Dimension = { Bases: Map<BaseMeasure, int>; Vars: Map<MeasureVar, int> }

module Dimension =
    val one      : Dimension
    val ofBase   : BaseMeasure -> Dimension
    val ofVar    : MeasureVar -> Dimension
    val mul      : Dimension -> Dimension -> Dimension   // exponent-wise add, drop zeros
    val inv      : Dimension -> Dimension                // negate every exponent
    val pow      : int -> Dimension -> Dimension         // scale every exponent
    val isGround : Dimension -> bool                     // Vars empty
    val resolve  : (MeasureVar -> Dimension option) -> Dimension -> Dimension  // idempotent
    val render   : Dimension -> string                   // the spec's normalised presentation
```

Exponent vectors over $\mathbb{Z}$. Paper §2.1 line 57: "let $\mathcal{D} = \mathbb{Z}^n$ be the dimension space, where $n$ is the number of base dimensions. Each dimension $d \in \mathcal{D}$ is a vector of integer exponents". The three group operations are the Paper's. Line 66: "multiplication adds exponent vectors; division subtracts them; exponentiation scales them." Each is $O(n)$, same line: "decidable in $O(n)$ per operation".

$B$ is not fixed at seven. DBC Abstract line 17: "including but not limited to physical units"; DBC §4.1 line 137: "$[\text{currency} \cdot \text{currency} \cdot \text{time}^{-1}]$". Base measures are declared. `units-of-measure.md` §Measure Definitions line 222: "A primitive measure abbreviation defines a fresh, named measure that is distinct from other measures." The declaration has universe standing. GA-01 §5 line 237: "It is a declaration in the NTU with the same standing as the set of base dimensions." DBC §2.2 line 65 "$\underbrace{\mathbb{Z}^7}_{\text{SI base dimensions}}$" is the SI instance, recorded as a paper rough edge in (i).

Canonical form is the representation, not a normaliser applied on demand. The spec's equality test becomes structural equality on `Dimension` because `Dimension.mk` is the only constructor. `units-of-measure.md` §Relations of Measures line 178: "reduce each to normalized form by using the rules of commutativity, associativity, identity, inverses, and abbreviation, and then compare the syntax." Abbreviations never appear in a `Dimension`. Line 165: "`long-ident` is equivalent to `measure` if a measure abbreviation of the form `[<Measure>] type long-ident = measure` is currently in scope." Integer exponents only in this increment. Paper §2.2 line 84: "The exponents here are integers; whether the same properties extend to the rational exponents … is taken up in a companion paper."

### a.2 The numeric type, and where it sits

```fsharp
/// The numeric kinds. Signedness, width and format are not kinds; they are seals or ranges (D1).
type Carrier = | Int | Real

/// A carrier position: a kind, or a carrier variable of TypeParamKind.Carrier.
/// The carrier variable is the numeric constraint; there is no separate Num constraint to forget.
type CarrierRef = | Kind of Carrier | CVar of TypeParam

type NativeType =
    | TNum     of carrier: CarrierRef * dim: Dimension   // int<1>, float<kg m / s^2>, κ<'u>
    | TMeasure of Dimension   // a measure-sorted positional argument on a non-numeric constructor
    | ...                     // non-numeric forms unchanged

type TypeParamKind = | Type | Measure | Carrier
```

`TNum` is the whole identity of a number at check time, D1 line 178-179 quoted in 0.3. `Int | Real` and not `Integer | Unsigned | Real` because signedness is a range fact, not a kind. `width-inference.md` §1 line 14: "a value's range determines whether it is signed or unsigned (§3), so a representation is never selected by a target type name independent of the range the value actually occupies." Plan §6 D1 addendum line 216: "in the discipline here signedness is derived from". Design B's `Unsigned` carrier is dropped on that anchor.

Bare `float` is `TNum(Kind Real, one)`. `units-of-measure.md` line 125: "non-parameterized types such as `float` are aliases for the parameterized type with `1` as parameter, that is, `float = float<1>`." `float` has arity 0, D4 line 229: "`float` keeps arity 0." A written width is a seal on the width coeffect, not a type. D1 lines 182-184: "A written concrete width (`int32`, `uint8`, `float32`, `posit<32,2>`) is therefore a Tier-3 **seal**". `int` is the bare integer kind with no seal, D1 as amended in (j). `nativeint` is a platform seal, D1 line 184: "`nativeint` is a seal whose width the platform description supplies". `uint` is open, item i.4.

Identity is exact, D2 as amended in (j): unit compared in normalised form, region and access invariant, seal not a component. `TNum` equality is carrier equality plus `Dimension` equality.

Measure-sorted positional parameters remain on non-numeric constructors and unify through the same measure unifier. `native-type-universe.md` line 1146: "Arena<[<Measure>] 'lifetime>"; `units-of-measure.md` lines 236-240: "type Vector<[<Measure>] 'U> = { X: float<'U>". Region and access are an enumeration sort, not a group element, and take their own kind at step 5. Paper §2.5 line 135: "Memory space identifiers … form an enumeration sort in the SMT sense: a finite set of values with equality but no arithmetic operation".

Where the annotation rides today, PHG plan line 101: "$\alpha$ | partial | `Type`, `ArenaAffinity`, `LayoutHint`, `Metadata`; $\delta$/$\kappa$ ride inside `NativeType`". This design keeps δ inside `Type` on α.

### a.3 The measure environment

```fsharp
type MeasureDef =
    | Primitive    of BaseMeasure                         // [<Measure>] type m
    | Abbreviation of BaseMeasure * expansion: Dimension   // [<Measure>] type N = kg m / s^2
```

An abbreviation's right-hand side is translated once, at declaration, through the environment as it stands, so expansion is total and computed in one place. A cycle is detected because the definition is not yet in the environment when its body is resolved, CCS8043. `units-of-measure.md` line 222: "repeatedly eliminating measure abbreviations in favor of their equivalent measures must not result in infinite measure expressions". Parameters on a measure definition are CCS8049. Line 228: "Measure definitions and abbreviations may not have type or measure parameters." Identity is the declaration, so `A.m` and `B.m` are distinct generators.

### a.4 How `float<newtons>` maps to it

One translator, `dimensionOfSyntax : MeasureEnv -> MeasureSyntax -> Result<Dimension, Diagnostic>`, reached from the type-position resolver and the literal resolver, so the two paths cannot disagree. Because `float` has arity 0 in the type sort, every argument of a numeric carrier is read in the measure sort. `units-of-measure.md` line 256: "the type checker distinguishes between type parameters and measure parameters by assigning one of two _sorts_ (Type or Measure) to each parameter … The type checker rejects ill-formed types such as `float<int>` and `IEnumerable<m/s>`."

| Source form | Syntax node, measured `SyntaxTree.fs:173, 185-203, 218-224, 423, 470-472` | Translation |
|---|---|---|
| `float<newtons>` | `SynType.App(float, [arg])`, tycon a numeric carrier of arity 0 | exactly one argument, read as a measure; two or more → CCS8050 |
| `newtons` | `SynMeasure.Named` / `SynType.LongIdent` | `MeasureEnv` lookup: `Primitive` → `ofBase`; `Abbreviation` → stored `Dimension`; absent → CCS8042; found as a type → CCS8045 |
| `kg m`, `kg * m` | `SynMeasure.Seq` / `Product`; `SynType.Tuple` segments without `/` | `mul` |
| `m / s`, `/ s` | `SynMeasure.Divide`; `SynTupleTypeSegment.Slash` | `mul m (inv s)`; `inv s` |
| `m^3`, `s^-2` | `SynMeasure.Power(_, SynRationalConst.Integer n)`; `SynType.MeasurePower` | `pow n` |
| `m^(1/2)` | `SynRationalConst.Rational` | CCS8048 |
| `1` | `SynMeasure.One`; `SynType.StaticConstant 1` | `one` |
| `_` | `SynMeasure.Anon`; `SynType.Anon` | fresh `MeasureVar` |
| `'u` | `SynMeasure.Var`; `SynType.Var` | the in-scope measure variable of the binding, else a fresh one that generalises |
| `float<int>`, `list<m>` | sort mismatch | CCS8045 |
| `bool<m>` | measure on a non-numeric, non-measure-parameterised type | CCS8046 |
| `1.0<m>` | `SynConst.Measure(c, _, synMeasure, _)` | `TNum(carrier of c, dimensionOfSyntax synMeasure)` |
| `1.0<'u>` | `SynMeasure.Var` under `SynConst.Measure` | CCS8044 |
| `2.0`, `3` | unannotated literal | `Dimension.one` |
| `0.0<_>` | `SynMeasure.Anon` on a literal | fresh variable; `float<'U>` |

Anchors. Line 137: "Measure annotations on constants may not include measure variables."; line 147: "`zero` is assigned the type `float<'U>`"; line 63: "measure-atom ^ int32". Bare literal dimensionless, UoM-4 as amended: lines 90-91: "let areaOfTriangle (baseLength:float<m>, height:float<m>) : float<sqm> =\n    baseLength*height/2.0". An unknown measure is a diagnostic, never a silent type. `conformance.md` §5 line 49: "it requires the implementation to say so, loudly and at a located point, rather than to proceed on a silent assumption."

Rendering. `Dimension.render` is the spec's normalised presentation. Lines 171-176: "Powers are positive and greater than 1. This splits the measure into positive powers and negative powers, separated by `/`. Atomic measures are ordered as follows: measure parameters first, ordered alphabetically, followed by measure identifiers, ordered alphabetically." An empty dimension renders as `1`; a `TNum` at `one` renders as the bare carrier. The carrier renders as the seal spelling where the node carries one. This is the one formatter; hover, diagnostics and the reified attribute read it. `/home/hhh/repos/clef/docs/fidelity/phg/Lattice_Consumer_Contract.md` line 47: "`Type` rendered in NTU syntax with dimensions". Abbreviation folding for hover is open, item i.3.

Measured gap replaced: `Literals.fs:42-46, 78`; `Types.fs:947-949, 900-902, 859-873`; `NativeService.fs:1829-1836`.

---

## (b) The unification procedure

### b.1 The problem

Unification is the equation-solving step. GA-01 §2.3 line 35: "Unification is the equation-solving step of ML-style inference, finding a substitution that makes two type expressions equal". For measures it is abelian-group unification. Paper §2.2 line 74: "dimension unification reduces to abelian-group unification over $\mathbb{Z}^n$". It is unitary. GA-01 §3 Proposition 4 line 65: "Unification modulo the theory of finitely generated abelian groups remains unitary and decidable: every solvable problem has a single most general solution". It is not Gaussian elimination. `/home/hhh/repos/arxiv-papers/research/corpus/02-vocabulary-reconciliation.md` line 44: "The corrected description is **abelian-group unification**, which is Kennedy's GCD and Diophantine machinery, not Gaussian elimination."

A constraint $\delta_1 = \delta_2$ is one residual $e = \delta_1 \cdot \delta_2^{-1}$ solved as $e = 1$. GA-02 §5 line 53: "a constraint $d_1 \cdot d_2^{-1} = 1$ resolves by subtraction of exponent vectors, and no case analysis over the direction of the relationship is required."

### b.2 The solver

`solveDim : MeasureStore -> Dimension -> Dimension -> Result<MeasureStore, DimFailure>`. Pure. `MeasureStore` is a persistent map `MeasureVar -> Dimension`; the result extends the input and never rebinds, I2.

1. $e \leftarrow$ `resolve store (mul d1 (inv d2))`.
2. `Vars e` empty: succeed iff `Bases e` empty; else `Mismatch(resolve d1, resolve d2, residual e)` → CCS8040. `units-of-measure.md` lines 199-205: "would eventually result in the constraint `m^2 = s`, which cannot be solved, indicating a type error."
3. One variable $v$ with exponent $k$, residual $r$ without $v$: if $k$ divides every exponent of $r$, bind $v \mapsto r^{-1/k}$ and succeed. This is the spec's case, line 197: "`float<m^2/s^2> = float<'U^2>` would be reduced to the `constraint m^2/s^2 = 'U^2`, which would be further reduced to the primitive equation `'U = m/s`." If $k$ does not divide, fail `NoIntegerSolution(v, k, r)` → CCS8041. `'U^2 = m` has no solution in $\mathbb{Z}$.
4. Several variables: choose $v$ with the smallest $|k|$. Mint fresh $w$ and bind $v \mapsto w \cdot \prod_{g \ne v} g^{-\lfloor e_g / k \rfloor}$. In the new residual $w$ has exponent $k$ and every other exponent is reduced modulo $k$, strictly smaller in magnitude. Recurse. Termination is Euclid on exponent magnitudes.

The result is the most general unifier; principality holds for the whole inference. Paper §2.2 line 84: "The inference is complete … principal (the inferred type is the most general), and decidable (the constraint system is finite and the solution algorithm terminates)."; DBC §5.2 line 204: "HM unification over $\mathbb{Z}^n$ computes the principal type: the assignment with fewest free variables and most constraints satisfied."

Binding targets. Measure variables bind to `Dimension` in the measure store; carrier variables bind to carriers; type variables bind to `NativeType` in the type store. Every read goes through `resolve`. One place pull. The type unifier's rules:

- `TNum(c1, d1) ~ TNum(c2, d2)`: unify carriers, then `solveDim d1 d2`. `Kind Int ~ Kind Real` is a type mismatch. `CVar κ` binds to the other carrier.
- `TVar 'a ~ TNum(c, d)`: bind `'a := TNum(c, d)`, dimension included. Paper §2.2 line 74: "unification of type variables propagates to unification of dimension variables".
- `TNum _ ~ non-numeric`: type mismatch; when the numeric side is an operator signature, CCS8000.
- `TMeasure d1 ~ TMeasure d2`: `solveDim`. The spec's argument-wise decomposition, line 197: "when `type<tyarg11 , ..., tyarg1n> = type<tyarg21, ..., tyarg2n>` is reduced to a series of constraints `tyarg1i = tyarg2i`".

### b.3 Occurs and torsion

No occurs check for measures. $v = v^2 \cdot m$ has residual $v \cdot m$ and solves to $v = m^{-1}$. Step 4 never binds a variable to a term containing itself because the eliminated variable is replaced by a fresh one. The type-level occurs check for `TVar` is unchanged. The only cycle refused is in abbreviations, CCS8043 at declaration, a.3.

Torsion is out of this increment. Plan §1 line 35: "Grade (the parity component of Clifford grade, valued in Z2) is a further generator the PHG paper carries;". When it enters, the group is no longer free and step 3's divisibility test becomes a Smith-normal-form step. Paper §2.1 line 68: "The extended group $\mathbb{Z}^n \oplus \mathbb{Z}_2$ is finitely generated and, on account of the torsion factor, no longer free. Unification remains unitary, the solution procedure moves from Hermite normal form to Smith normal form". `solveDim`'s signature does not change; the `Dimension` record gains a generator with a declared order. No slot is pre-built now.

### b.4 Generalisation at `let`

`units-of-measure.md` line 209: "a generalization procedure produces measure variables over which a value, function, or member can be generalized"; `inference-constraint-solving.md` §Generalization lines 515-518: "Generalization is applied by default at all function, value, and member definitions, except where listed later in this section."; generalizable expressions lines 565-572.

Procedure, after the binding's constraints are solved:

1. Resolve the binding's type through all three stores.
2. Collect free measure variables and free carrier variables; subtract those free in the environment, also through resolution. Apply the spec's non-generalisable cases, lines 540-550.
3. Simplify the scheme. Let $E$ be the integer matrix whose rows are the exponent vectors, over the $m$ candidate measure variables, of each distinct dimension occurrence in the type. Compute unimodular $Q$ with $EQ$ in column Hermite normal form; the columns of $Q$ are the new variables; drop zero columns. The count is $\mathrm{rank}(E)$, the "fewest free variables" of DBC line 204. `float<'u 'v> -> float<'u 'v>` becomes `float<'w> -> float<'w>`. This is where Hermite normal form belongs in the free case; the unifier itself is Euclid.
4. Rename survivors in order of first occurrence and quantify. Instantiation mints fresh variables of the same kind. The `Application` node records the instantiation as its own annotation so hover shows the instance while the body keeps its scheme.

Paper §2.2 line 82: "A function `let scale factor value = factor * value` infers type `float<'d1> -> float<'d2> -> float<'d1 * 'd2>` without any annotation." Here the scheme is `∀κ 'u 'v. κ<'u> -> κ<'v> -> κ<'u 'v>` and the `float` instance is what the Paper shows. Provenance is irrelevant downstream, line 86: "The compilation pipeline treats all annotations identically regardless of provenance".

An unresolved measure variable at a non-generalisable binding after saturation is CCS8047, never defaulted to `1`. NFT §6 line 189: "The presence of unresolved backward judgments or unsatisfied fractional constraints at program scope would produce a design-time error."; GA-01 §4.5 line 191: "an unresolvable support an error and not a runtime fallback". A generalised scheme with no instantiation emits nothing and needs no default.

### b.5 Failure presentation

CCS8040 prints both sides through `Dimension.render` after resolution, plus the residual: `Measure mismatch: 'kg m / s^2' vs 'm'; the residual 'kg / s^2' is not 1`. The residual is the unsatisfiable core. NFT §8.3 line 278: "producing a design-time error at the source location (unsatisfiable core)". The operator or binding node is the primary range; the two operand nodes are related nodes. `numeric-selection.md` §11 line 288: "check-time diagnostics in the same shape as the existing width-inference and FPGA diagnostics (severity, source range, related nodes, reachability)". CCS8041 names the variable, the exponent and the indivisible residual. Surfacing carries the error's own code, never a catch-all. `Lattice_Consumer_Contract.md` line 25: "Diagnostic codes are `CCS8xxx` minted by the checker or by obligation discharge." Measured: `NativeService.fs:246-259` maps every unification error to `FS0001`.

### b.6 `HasMeasure`

Under D4 a measure annotation resolves directly to `TNum(c, d)`; no source form yields "type τ, not yet known to be numeric, has measure μ". The spec grammar has no `'T<m>`, `units-of-measure.md` lines 56-78. The constraint has no producer and is deleted. Plan §5 line 143 says "`HasMeasure` enforced"; the enforcement it wanted is equality on `TNum`, the same fact in one place. Plan amendment in (j). Measured: `NativeTypes.fs:914`, `Unify.fs:379-382`.

---

## (c) Operator typing

All arithmetic is dimension-checked during inference. DBC §6.2 line 264: "Dimensional consistency of every arithmetic operation verified during type inference, at negligible incremental cost." Operators quantify over a carrier variable `κ` and dimension variables. `ρ` is a carrier variable restricted to `Real`, the spec's `F`, `units-of-measure.md` line 309: "`F` is either `float32` or `float`".

| Operator | Scheme | Anchor |
|---|---|---|
| `+`, `-`, `%` numeric | `κ<'u> -> κ<'u> -> κ<'u>` | spec line 315: "`N<'U> -> N<'U> -> N<'U>`"; Paper line 78: "$d(a) = d(b)$" |
| `*` | `κ<'u> -> κ<'v> -> κ<'u 'v>` | spec line 316: "`N<'U> -> N<'V> -> N<'U 'V>`" |
| `/` | `κ<'u> -> κ<'v> -> κ<'u 'v^-1>` | spec line 317: "`N<'U> -> N<'V> -> N<'U/'V>`"; DBC §2.1 line 53: "The operation is subtraction in the exponent algebra" |
| `<`, `>`, `<=`, `>=`, `=`, `<>` numeric arm | `κ<'u> -> κ<'u> -> bool` | spec line 291: "`System.IComparable<float<'u>>` and `System.IEquatable<float<'u>>`"; `types-and-type-constraints.md` line 484: "equality and comparison are resolved through SRTP"; Plan step 3 line 145 |
| unary `-`, unary `+`, `abs` | `κ<'u> -> κ<'u>` | spec line 318: "`N<'U> -> N<'U>`" |
| `sign` | `κ<'u> -> Int<1>` | spec line 319: "`N<'U> -> int`" |
| `sqrt`, if in scope | `ρ<'u^2> -> ρ<'u>` | spec line 313: "`F<'U^2> -> F<'U>`"; `sqrt 1.0<m>` → CCS8041 |
| `atan2`, if in scope | `ρ<'u> -> ρ<'u> -> ρ<1>` | spec line 314: "`F<'U> -> F<'U> -> F<1>`" |
| `pown x n`, `n` a literal | `κ<'u> -> Int<1> -> κ<'u^n>` | spec silent; choice recorded, i.13 |
| `**`, `exp`, `log`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `floor`, `ceiling`, `round` | `ρ<1> -> ρ<1>`, binary `ρ<1> -> ρ<1> -> ρ<1>` | spec lines 321-322 list only "`(+)`, `(-)`, `(*)`, `(/)`, `(%)`, `(~+)`, `(~-)`, `abs`, `sign`, `atan2` and `sqrt`" as measure-aware; a runtime exponent cannot scale a vector; a dimensioned argument is CCS8040 against `1` |
| `min`, `max` | `κ<'u> -> κ<'u> -> κ<'u>` | spec silent; follows comparison |
| carrier conversions `float x`, `int x` | `κ<'u> -> ρ<'u>` and the like; dimension preserved; source must be numeric, CCS8002 | NFT §4 line 88: "Implicit type conversions erase precision and dimensional information"; Plan L-4 line 123; `width-inference.md` §7 line 70: "There is no polymorphic `'T -> Target` conversion." |

### c.1 The numeric constraint, W-2

`bool` is not `TNum`, so `true + true` fails to unify `bool` with `κ<'u>` and reports CCS8000. There is no `Constraints` list to forget; the carrier variable is the constraint. Measured: `UnionFind.fs:430-436` sets `Constraints = []` and `Unify.fs:59-248` never reads it. A carrier variable still unbound at a non-generalisable site is CCS8001, never defaulted to `int`. `width-inference.md` §1 line 14: "an unanalyzable range is a reported error, never a silent default".

### c.2 Dimensionless literals and factors, UoM-4

`2.0 : Real<1>`; `2.0 * 3.0<m> : Real<1 · m> = Real<m>` by canonical form; there is no `MOne` case to special-case. `x / 2.0` keeps `δ(x)`. The Paper's Appendix A line 707 "`g` is assigned dimension variable `'d_g`" is superseded by Appendix C line 784 "let g = 6.674e-11<m^3 * kg^-1 * s^-2>" and by §2.6 line 157: "Dimensional constraints alone do not determine numeric magnitudes". Recorded in i.2 and in the UoM-4 amendment.

### c.3 `+` dispatches on kind, D5

`+` is one intrinsic whose typing is a joint function of its operands' kinds, a hyperedge over `{lhs, rhs}` that fires when both are elaborated, I2. Both `TNum` → the numeric scheme with a range obligation on the result. Both `string` → concat, `string -> string -> string`, with an extent obligation. One of each → CCS8000. Either a bare type variable → the dispatch is attached to the variable and fires when it binds; a generalisable binding carries it in the scheme, resolved at each instantiation, which is what accepts W-6. Unresolved at a non-generalisable binding after saturation → CCS8001. D5 line 230-232: "`+` dispatches on the kind of its operands: on numerics it is the unit-unified add with a range obligation; on strings it is the concat recipe with an extent obligation." `introduction.md` lines 171-175: "the only version of the `+` operator that accepts a left-hand argument of type `string` also takes a `string` as the right-hand argument". `-`, `*`, `/`, `%` and comparison have only the numeric branch.

### c.4 `fma` and the quire

Not an operator of this increment. When the quire pass lands the rule is composition of `*` and `+`. Paper §3.5 line 321: "A quire accumulating products of `float<newtons>` and `float<meters>` carries dimension newtons $\cdot$ meters $=$ joules."

---

## (d) Carriage

### d.1 The position, as amended

The checker never erases the dimension. Plan §0 as amended in (j). `ntu-dimensional-architecture.md` §5.1 lines 320-322: "Dimensional types are first-class in the type system; they don't erase after type checking." It is dropped only at native emission as debug metadata. Paper §1.1 line 29: "dimensional annotations persist as compilation metadata through multi-stage lowering, available at each stage where they inform decisions, and are dropped before native code emission. The annotations do not exist at runtime". The spec chapter's erasure text, `units-of-measure.md` line 12: "Measures play no role at runtime; in fact, they are erased." and line 292: "As a result of erasure, their compiled form is the corresponding primitive type.", describes F#'s early erasure the Paper rejects, §1.1 line 27: "We refer to this as *early erasure*"; the §1 table amendment in (j) records the supersession.

### d.2 The two carriers, I4

1. Codata on the node. δ(v) rides in α.`Type` from elaboration onward. Paper §2.3 line 98: "The Program Semantic Graph preserves dimensional annotations as node attributes."; DBC §3.1 line 83: "Dimensional annotations persist through multi-stage refinement … as PSG codata, available at every stage."; `numeric-selection.md` §10.1 line 248: "recorded as **codata on the PSG beside the dimension, the grade, and the escape class**". At saturation every numeric node's `TNum` is resolved through the stores: ground, or containing only variables quantified by the enclosing scheme. Nothing below the graph re-derives it. NFT §8 line 250: "the zipper witnesses what is already settled and elides it to the dialects."
2. Reified attribute on emitted ops. The witness stamps `clef.dim = "<render δ>"` on every arithmetic, conversion, call and return op whose node carries a non-`one` dimension. Paper §2.3 line 112: "Dimensions are carried as opaque MLIR attributes, and each pass propagates them."; `program-hypergraph.md` §5 line 53: "as a reified annotation, an attribute set on emitted operations that a later pass consumes." MLIR types stay portable. `ntu-types.md` §8.1 line 303: "The middle end (Alex) emits only portable dialect types … and commits to no target." The attribute name is the corpus's silence; `clef.dim` is chosen here.

What Alex reads. To choose the MLIR type it reads the carrier and the settled width and representation coeffect, never the dimension. `ntu-dimensional-architecture.md` §5.2 lines 327-329: "The type mapping in Composer reads the resolved width and layout annotations on each node and emits the corresponding concrete MLIR types; it does not consult the platform context to decide a width". It copies the rendered dimension string. It computes nothing from it, §5.2 lines 329-330: "a mapping that did would be computing a fact the graph already carries". It never resolves a measure variable. NFT §8 line 250 as above.

### d.3 The invariant carriage keeps

Paper §2.3 line 106: "*dimensions never influence control flow or data layout in a way that could cause divergence between a dimensioned and undimensioned compilation of the same program.* The generated instructions are identical". Hence the monomorphisation key for a generalised function excludes measure variables. A measure-only instantiation is one body. Only carrier instantiations split bodies. The only route by which a dimension changes emitted code is representation selection at step 8, through the coeffect.

### d.4 Pass-boundary witnessing, the build-time twin

Preservation is an engineering invariant. Paper §2.3 line 112: "A buggy pass could in principle strip or corrupt dimensional metadata without violating any parametricity property"; `conformance.md` §6 line 65: "A property silently lost in lowering is a conformance violation, detected by the re-check." The design-time equation hyperedge of 0.2 has a build-time counterpart re-derived from the `clef.dim` attributes of the emitted ops and paired under the same anchor name. PHG plan I.3: "Twin pairing is itself a hyperedge with $|S_f| = 2$ … An unpaired *observable* obligation at the saturation boundary is a design-time error"; `/home/hhh/repos/clef/docs/fidelity/phg/Layout_As_Joint_Constraint.md` §4 lines 209-215: "a design-time VC with no build-time twin is a detected leak by the same mechanism that discharges the proof". An arithmetic op whose node has a dimension and whose emitted form lacks the attribute is a detected leak. Drop point: debug metadata at native emission. Paper §2.3 line 104: "lowered to debug metadata (DWARF annotations on x86, equivalent metadata on other targets)". The exact pass is not fixed by the corpus, i.11.

### d.5 Across the wire

The dimension is in the derived schema, not the payload. `program-hypergraph-paper.md` §8.8 line 482: "resolved structure travels as metadata, the payload stays flat, and nothing is left to resolve in flight." DBC §3.1 line 89 says "dimensional metadata accompanies serialized data through BAREWire"; the PHG paper's rule is the more specific; out of scope, i.12.

### d.6 Lattice

Renders from the same graph. `Lattice_Consumer_Contract.md` line 47 quoted in a.4.

---

## (e) Width: a lattice-family coeffect, propagated, never unified

### e.1 The annotation

```fsharp
type Representation =
    | FixedInt    of bits: int * signed: bool          // int32, uint8, int64
    | PlatformInt of WidthDimension * signed: bool     // nativeint: the platform supplies bits
    | Ieee        of bits: int                         // float32; bare float is not a seal
    | Posit       of bits: int * es: int
    | FixedPoint  of total: int * frac: int * signed: bool

/// Precedence is the order of the cases (numeric-selection.md §3.4).
type ClaimTier = | Developer | Platform of WidthDimension | Library

type Seal = { Repr: Representation; Tier: ClaimTier; Site: NodeId }

/// The width coeffect on one numeric node, one entry per configured target.
type WidthAnnotation = {
    Range: Interval          // Unbounded is a value, never a default
    Seal: Seal option        // the binding claim, if any source supplied one
    MayWrap: bool            // sealed arithmetic whose pre-wrap range exceeds the seal
}
```

Per node beside `Type`, the κ(v) of PHG Def. 2.1. Derived from range, not a name. `width-inference.md` §10 line 95: "**Range-driven width**: Integer representation width SHALL be derived from the value's analyzed range, not from a target type name." The seal is a claim. `numeric-selection.md` §3.3 line 88: "The developer writes a concrete representation; the compiler runs selection *in reverse* — verifying that the chosen representation's dynamic range covers the inferred or annotated value range, and emitting a coverage diagnostic if not. Tier 3 is **sealing**". It implies a range claim, §3.4 line 94: "`R₃` (a sealed annotation, which fixes a representation *and* implies its dynamic range as a range claim)." Per target: `Layout_As_Joint_Constraint.md` §2.2 lines 109-112: "`lambda_f` carries `Map<TargetId, LayoutAnnotation>`. A single-target build has a one-entry map."

Seal spellings: `int32` → `FixedInt(32,true)`; `uint8` → `FixedInt(8,false)`; `nativeint` → `PlatformInt(Pointer,true)`; `float32` → `Ieee 32`; `posit32` → `Posit(32,2)`; `int`, `float` → no seal.

### e.2 How a seal arrives, one place pull

A written width at a binding, parameter, literal suffix or return annotation is read once at elaboration into `Seal { Tier = Developer }`. A platform boundary takes its seal at saturation from `PlatformContext.Dimensions` for word and pointer widths, `platform-bindings.md` line 397: "Dimensions: Map<WidthDimension, int> // Pointer → 64, Register → 64, etc.", or from the `Fixed` widths the binding generator emits for C ABI types, `ntu-dimensional-architecture.md` §2.1 lines 94-97: "Farscape resolves C ABI-specific widths (C `int`, C `long`) at code generation time using PlatformABI, emitting Fixed-width NTU types. Only genuinely platform-abstract types (`size_t`, `intptr_t`, F# `int`, `nativeint`) use `Resolved`." D1 as amended in (j). Resolution is in CCS at saturation, §4.3 lines 310-312 quoted in 0.4. A missing `Dimensions` key is a diagnostic at saturation, never an exception. Measured: the indexer at `NativeTypes.fs:448` throws. A Tier-2 library claim is `Tier = Library`. No witness writes a seal; Plan L-10 goes at step 7.

### e.3 Propagation and the seal meet

Interval analysis over dataflow hyperedges to a least fixpoint, joins at merges, forward in dependency order under I2. `width-inference.md` §2 line 20: "Each numeric node is assigned a value range `[a, b]`"; line 22: "**Literals** are point intervals: `124` has range `[124, 124]`."; GA-02 §7.1 line 85: "a tentative support at the binding site, widened by joins at merge points and use sites, checked by ordering ($\beta \subseteq$ mask), recorded on the PSG, read at lowering." Per-operator interval rules per `/home/hhh/repos/clef-lang-site/hugo/content/blog/fpga-and-hardware-inference.md` lines 163-171.

At every flow edge and operator node the seals meet under one rule, D1 consequences (1) and (2), Plan lines 188-189: "two different seals meeting is an explicit-conversion site" and "a bare operand meeting a sealed one adopts the seal when its range is covered":

| lhs | rhs | outcome |
|---|---|---|
| none | none | range by interval arithmetic; no seal |
| s | none, `Range(rhs) ⊆ dynrange(s)` | rhs adopts s; result sealed s |
| s | none, not covered | CCS8012 at rhs |
| s | s | result sealed s; pre-wrap range recorded, e.4 |
| s₁ | s₂ ≠ s₁ | CCS8013; nothing widened or truncated |

Tiers do not merge. `numeric-selection.md` §3.4 line 95: "**The binding range is the claim of the highest present tier** (`R₃` if present, else `R₂`, else `R₁`). Higher tiers *override*; they do not silently merge."

Generalised numeric functions, W-6 as amended. A non-`inline` function has one body whose parameter range is the join over its call sites, the lattice least fixed point. GA-02 §7.1 line 85: "The \"principal solution\" of the general statement in section 3 is therefore the least fixed point of the propagation on the lattice axes, a different and cheaper object than a most general unifier". A call site carries its own range only under explicit `inline`, by expansion; `inline` is never used as a width-solving device. Design B's per-seal-signature instancing is dropped on this anchor. In W-6 the parameter adopts the `int64` seal at the first site; the bare point range at the second is covered; both accepted with one body.

### e.4 Coverage and the wrap rule

For every node with a range and a seal: `dynrange(seal) ⊇ Range`, else CCS8012. `numeric-selection.md` §2.1 lines 50-52: "R_cov(T, [a, b]) = { r ∈ R(T) : dynrange(r) ⊇ [a, b] }" and "The Tier-3 seal check (§5) is a special case of this coverage check applied to a singleton `R`, not a separate mechanism. The coverage constraint is part of the objective, not a post-hoc warning." `dynrange(FixedInt(n,true)) = [-2^(n-1), 2^(n-1)-1]`, `FixedInt(n,false) = [0, 2^n-1]`, `PlatformInt` the same after resolution. Arithmetic between operands carrying the same seal keeps the seal's wrapping semantics; the result stays sealed and covered by construction; `MayWrap` is set when the pre-wrap interval exceeds the seal and CCS8015 warns. `native-type-universe.md` §2.3 line 154: "| Default | Wrapping (two's complement) |"; `width-inference.md` §8 line 83: "the wrapping semantics of the fixed-width types … SHALL be preserved observably, whatever realization carries them." Conversions whose target cannot hold the source are CCS8017. `width-inference.md` §7 line 69: "**Overflow is a type error, not undefined behavior.** A conversion whose target cannot hold the source range is rejected at compile time." A covering seal the open argmin would not have chosen is CCS8014, informational. `numeric-selection.md` §5 line 146: "A suboptimal-but-covering seal SHALL be witnessed at design time with the representation the open argmin would have chosen." Lowering may widen and never narrow, §10 line 96: "lowering MAY widen to a native size for arithmetic but SHALL NOT narrow below the range."

### e.5 The unobservable-range diagnostic, W-4

- Integer, no seal from any source, `Range = Unbounded` → CCS8011. `width-inference.md` §6 line 62: "the compiler does **not** guess a width or fall back to a machine-word default. It reports an error asking the source for an annotation." An exported parameter typed `int` on a CPU target is a platform boundary and takes the word seal, D1 amendment (d); so the diagnostic is for values no platform fact governs.
- Bare real, unbounded → IEEE `f64`, no diagnostic, still propagated. `numeric-selection.md` §13 line 322: "A bare `float` with an unobservable range SHALL lower to IEEE `f64` without error; this is the argmin outcome for an unknown range, not a bypass of selection. Bare reals SHALL still carry range propagation."
- Dimensioned real, unbounded → CCS8011 at the dimensioning seam naming the bare source. §13 line 323: "the range error SHALL fire at the dimensioning boundary and SHALL name the upstream bare source."; §6 line 155: "The dimension is a *promise that a domain range exists*". In PHG terms the `*` hyperedge over `{x, oneNewton}` fires when both sources are saturated; the rule reads δ(x) = 1, Range(x) = Unbounded, δ(result) ≠ 1 and emits CCS8011 with x as the related node.

### e.6 Why width never enters the unifier

1. Wrong algebra. Unification needs inverses to cancel, GA-02 §5 line 53; an interval domain has none and its principal object is a least fixed point, GA-02 §7.1 line 85 quoted in e.3.
2. Disjoint variables, separate discharge. GA-02 §7.2 line 93: "no constraint mentions both a dimensional exponent and a support mask."; `grade-discipline.md` §4.1 line 206: "An implementation SHALL NOT combine them into a single query: QF_BV is not stably infinite"; `program-hypergraph.md` line 47: "a hyperedge SHALL NOT mix families in a single query".
3. Direction. Unification is symmetric and would equate `g 1L 2L` with `g 1 2`; propagation is directed and joins.
4. A seal is checked by an ordering, not solved by an equation. `numeric-selection.md` §3.3 line 88: "it converts the argmin from a chooser into a checker".
5. Identity. D1 puts width outside the type; there is nothing for `unify` to see. `ntu-types.md` §6.1 lines 241-242: "unify(NTUint(Resolved Register), NTUint(Fixed 64)) = Error(TypeMismatch)" is the spec text D1 supersedes, recorded for step 6.

Interim staging for steps 1 and 2. The written-width name is read once into the seal from step 1, e.2, and the unifier never consults it for a dimension decision. Until step 7's meet rule exists the current name-based rejection of `int32 + int64` stays in place and the harness reports W-1 as "right result, wrong mechanism", Plan §3 W-1 as amended. Step 7 moves the check to e.3 and removes the name comparison.

---

## (f) Diagnostics

All codes are in the CCS series, D3 as amended. None reuses a code the spec has bound: `CCS8010`, `CCS8020`-`CCS8022`, `CCS8030`-`CCS8033`, `CCS8100`-`CCS8104`.

**CCS80xx, type system, width and seals**

| Code | Severity | Message | Fires at |
|---|---|---|---|
| CCS8000 | Error | Operator '{op}' requires numeric operands; '{ty}' is not numeric | operator application, W-2 |
| CCS8001 | Error | The kind of the operands of '{op}' cannot be determined at this binding; annotate an operand | non-generalisable binding after saturation, D5 |
| CCS8002 | Error | Conversion '{f}' requires a numeric source; '{ty}' is not numeric | conversion application, L-4 |
| CCS8011 | Error | '{name}' has no bounded range from any source; annotate it or seal its representation | e.5, W-4 (the dimensioning-seam variant is NS-1's numeric-selection-family code, allocated with the D3 table) |
| CCS8012 | Warning, promoted to Error under `--warnaserror` | Sealed representation '{s}' with range {dynrange} does not cover the analysed range {range} of '{name}' | e.4, W-5 |
| CCS8013 | Error | Representations '{s1}' sealed at {site1} and '{s2}' sealed at {site2} meet here; an explicit conversion is required | e.3, W-1 |
| CCS8014 | Info | Seal '{s}' covers the range; the open selection would choose '{r}' | e.4, step 8 |
| CCS8015 | Warning | Sealed arithmetic may wrap: pre-wrap range {range} exceeds '{s}' | e.4 |
| CCS8016 | Warning | Observed range {range} exceeds the declared range {claim} of '{name}' | Tier 2, step 8 |
| CCS8017 | Error | Conversion '{src}' to '{dst}' cannot hold the source range {range} | conversions, L-4, L-9 |
| CCS8018 | Error | Literal suffix '{sfx}' is not a representation Clef supports | literal typing, L-3 |

**CCS804x, units of measure**

| Code | Severity | Message | Fires at |
|---|---|---|---|
| CCS8040 | Error | Measure mismatch: '{lhs}' vs '{rhs}'; the residual '{d}' is not 1 | `solveDim` ground failure |
| CCS8041 | Error | '{v}^{k} = {d}' has no integer solution; the exponents of '{d}' are not all divisible by {k} | `solveDim` divisibility failure |
| CCS8042 | Error | '{name}' is not a measure in scope | measure syntax |
| CCS8043 | Error | Measure abbreviation '{name}' is cyclic: {chain} | measure declaration |
| CCS8044 | Error | A measure variable may not appear in a literal's measure annotation; use '_' | literal annotation |
| CCS8045 | Error | '{arg}' is a type where a measure is required, or a measure where a type is required | sort check, `float<int>` |
| CCS8046 | Error | '{ty}' carries no dimension; a measure cannot be applied to it | `bool<m>` |
| CCS8047 | Error | The measure of '{name}' could not be resolved and this binding is not generalisable; annotate it | end of a non-generalisable binding |
| CCS8048 | Error | Rational measure exponent '{r}' is not supported; exponents are integers | measure syntax |
| CCS8049 | Error | A measure definition may not have type or measure parameters | measure declaration |
| CCS8050 | Error | '{tycon}' takes one measure argument; {n} were given | measure syntax |

**Region and access, step 5, listed for the series**

| Code | Severity | Message | Anchor |
|---|---|---|---|
| CCS8020 | Error | Cannot write to ReadOnly pointer | `access-kinds.md` line 141 |
| CCS8021 | Error | Cannot read from WriteOnly pointer | line 142 |
| CCS8022 | Error | Access kind mismatch in assignment | line 143 |
| CCS8100 | Error | Region mismatch: '{r1}' where '{r2}' is required | `error-handling.md` §Diagnostics as amended 2026-09-04: the null codes that occupied the block are removed |

The site's `E_RANGE_UNBOUNDED` and `W_COVERAGE`, `blog/deferred-inference.md` lines 162 and 189, map to CCS8011 and CCS8012; the post says they are "the designed experience … not screenshots from a build", line 331.

---

## (g) The vet programs

Layout per Plan §3 lines 66-68: `Composer/samples/dimensional/<rule>/{reject,accept}/` with a `.clef`, a `.fidproj` cloned from `BAREWire/samples/RoundTrip/RoundTrip.fidproj`, and `expect.toml` carrying `verdict`, `code`, `range`. Every program ends with `[<EntryPoint>] let main _ = … 0`. Common prelude:

```fsharp
module Vet
[<Measure>] type m
[<Measure>] type s
[<Measure>] type kg
[<Measure>] type N = kg m / s^2
```

| Rule | Program | Verdict |
|---|---|---|
| UoM-1 reject | `let x = 1.0<m> + 1.0<s>` | CCS8040, `'m' vs 's'`, at `+` |
| UoM-1 accept | `let x = 1.0<m> + 2.0<m>` | accept; `x : float<m>` |
| UoM-2 reject | `let x : float<m> = 2.0<m> * 3.0<s>` | CCS8040, `'m s' vs 'm'`, residual `s` |
| UoM-2 accept | `let a : float<m s> = 2.0<m> * 3.0<s>` | accept |
| UoM-3 reject | `let v : float<m> = 6.0<m> / 2.0<s>` | CCS8040, `'m / s' vs 'm'` |
| UoM-3 accept | `let v : float<m/s> = 6.0<m> / 2.0<s>` | accept |
| UoM-4 reject | `let x : float<s> = 2.0 * 3.0<m>` | CCS8040, `'m' vs 's'` |
| UoM-4 accept | `let x : float<m> = 2.0 * 3.0<m>` | accept |
| UoM-5 reject | `let x : float<m> = 1.0<m s> / 1.0<m>` | CCS8040, `'s' vs 'm'` |
| UoM-5 accept | `let x : float<s> = 1.0<m s> / 1.0<m>` and `let y : float<m s> = 1.0<s m>` | accept; canonical form makes `s m` = `m s` |
| UoM-6 reject | `let b = if 1.0<m> < 1.0<s> then 1 else 0` | CCS8040 at `<` |
| UoM-6 accept | `let b = if 1.0<m> < 2.0<m> then 1 else 0` | accept |
| UoM-7 reject | `let f (x: float<m>) = x` then `let r = f 1.0<s>` | CCS8040, `'s' vs 'm'`, at the argument |
| UoM-7 accept | `let r = f 1.0<m>` | accept |
| UoM-8 accept | `let scale f v = f * v` then `let a : float<m> = scale 2.0 3.0<m>` and `let b : float<s m> = scale 2.0<s> 3.0<m>` | accept; scheme `∀κ 'u 'v. κ<'u> -> κ<'v> -> κ<'u 'v>`, rendered `float<'u> -> float<'v> -> float<'u 'v>`; one body |
| UoM-9 reject | `let computeForce (m1: float<kg>) (m2: float<kg>) (r: float<m>) =`<br>`    let g = 6.674e-11<m^3 kg^-1 s^-2>`<br>`    g * m1 * m2 / (r * r)`<br>`let bad = computeForce 1.0<m> 1.0<kg> 1.0<m>` | CCS8040, `'m' vs 'kg'`, at the first argument |
| UoM-9 accept | same definition, `let f = computeForce 1.0<kg> 1.0<kg> 1.0<m>` and `let check : float<N> = f` | accept; inferred `float<kg> -> float<kg> -> float<m> -> float<kg m / s^2>`; `N` expands to `kg m s^-2`, a.3 |

UoM-9 is the verified form: annotated parameters, no return annotation, the Paper's Appendix C literal, `dts-dmm-paper.md` line 784: "let g = 6.674e-11<m^3 * kg^-1 * s^-2>". Design B's fully unannotated variant accepts a `float<m>` for a mass and is not a reject program; verification UoM-9.

W rows, gated by steps 3 and 7, written now so steps 1 and 2 cannot foreclose them. `expect.toml` carries `pending = "step 7"` where noted, Plan §4 lines 106-107.

| Rule | Program | Verdict |
|---|---|---|
| W-1 reject | `let f (x: int32) (y: int64) = x + y` | CCS8013, `int32` meets `int64` |
| W-1 reject | `let g (p: nativeint) (x: int32) = p + x` | CCS8013, `PlatformInt Pointer` meets `FixedInt 32` |
| W-1 accept | `let a = 1 + 1L`; `let b = 1L + 2L`; `let h (x: int64) = x + 1L` | accept; the bare `1`, point range `[1,1]`, adopts `int64`; `ntu-types.md` §6.2 line 258 "let x: int64 = 42 // Error: int ≠ int64" is the spec tension step 6 records |
| W-2 reject | `let z = true + true`; `let w = true - true` | CCS8000 |
| W-2 accept | `let z = 1 + 2`; `let t = "a" + "b"` | accept; D5 string branch |
| W-3 | `type Pair = { Addr: nativeint; Tag: int32 }` and `let p = { Addr = 0n; Tag = 1 }`, one source under two `.fidproj` platform contexts, x86_64 Linux and the Cortex-M33 descriptor of `platform-bindings.md` lines 469-475 "`Dimensions = Map.ofList [ (Pointer, 32); (Register, 32) ]`" | both compile; `LayoutHint` records `Addr` at 8 bytes and 4 bytes; no width text in any Alex file; `expect.toml` names both layouts |
| W-4 reject | `let rec run n = run (n + 1)` with no modulus, comparison or seal | CCS8011 at `n`; unobservable on every target; pending step 7 |
| W-4 reject | `let y (bareInput: float) (oneNewton: float<N>) : float<N> = bareInput * oneNewton` with `bareInput` unbounded | CCS8011 at the `*` seam, related node `bareInput`; pending step 7 |
| W-4 accept | `let f (n: int32) = n + 1` | accept; the sum wraps in the seal, e.4 |
| W-4 accept | `let y (bareInput: float) = bareInput * 2.0` | accept; `f64` |
| W-5 reject | `let x : uint8 = 300` | CCS8012, `[0,255]` does not cover `[300,300]`; pending step 7 |
| W-5 reject | `let c (counter: uint32) : int8 = counter % 1000` | CCS8012, `[0,999]` not covered; pending step 7 |
| W-5 accept | `let x (counter: uint32) : uint8 = counter % 256`; `let y : int8 = -128` | accept; `[0,255]` covered |
| W-6 accept | `let g x y = x + y` then `let a = g 1L 2L` and `let b = g 1 2` | accept; scheme `∀κ 'u. κ<'u> -> κ<'u> -> κ<'u>`; one body; parameter range is the join of the sites, sealed `int64` at the first, bare `[1,2]` covered at the second |

---

## (h) The ordered change list, by role

Each row names the role, the target form, the anchor, and what it removes. Nothing is described by its current code shape.

**Step 1, representable and surviving**

1. Measure algebra, a new module with no dependency on the type DU. `BaseMeasure`, `MeasureVar`, `Dimension` with `mk` as sole constructor, the group operations, `render`, `MeasureStore`, a.1. Removes the syntax-tree measure form `MOne | MVar | MProd | MInv | MCon` and its printer, measured `NativeTypes.fs:993-999`; one normal form, one formatter. Anchor: Paper line 57; spec line 178.
2. Numeric type form. `TNum(carrier, dim)`, `Carrier = Int | Real`, `CarrierRef`, `TypeParamKind.Carrier`; `TMeasure` holds a `Dimension`, a.2. Removes the numeric constructors as arity-0 nominal types whose identity is the width spelling, measured `NativeTypes.fs:1380-1405`; the comment naming a `Ptr<'T, 'region, 'access>` that does not exist, `NativeTypes.fs:727`, and `mkTypeConRefWithMeasures` with zero callers, `:762`. Anchor: D1, D4 amended; Paper line 74.
3. Measure environment. Primitives and abbreviations registered in dependency order, expansions computed once, CCS8043 and CCS8049, a.3. Removes the type-definition fall-through that discards `[<Measure>]` declarations, measured `NativeService.fs:1829-1836`. Anchor: spec lines 213-228.
4. One measure-syntax translator, `dimensionOfSyntax`, reached from the type-position resolver and the literal resolver, a.4; CCS8042, CCS8045, CCS8046, CCS8048, CCS8050. Removes the `MeasurePower → base type` arm, the `Slash → None` drop, and measure names resolved as types, measured `Types.fs:947-949, 900-902, 859-873`. Anchor: spec grammar lines 56-78, line 256.
5. Literal typing. `SynConst.Measure` → `TNum`; bare literal → `one`; `_` → fresh variable; CCS8044; a suffix is read once into the seal, e.2; an unknown suffix is CCS8018, never `int` "for now". Removes both discard arms, measured `Literals.fs:42-46, 78`, and the unknown-suffix fabrication, Plan L-3. Anchor: spec lines 133-147.
6. Type rendering through `Dimension.render`, carrier rendered as the seal spelling where present, a.4. Removes any second formatter. Anchor: `Lattice_Consumer_Contract.md` line 47.
   Gate: UoM programs parse to distinct types, Plan line 140.

**Step 2, Kennedy unification**

7. `solveDim` in the algebra module; the type unifier's `TNum` and `TMeasure` rules call it, b.2. Removes the structural product compare that makes `m s ≠ s m`, the never-binding variable arm, and the succeed-on-mismatch arm, measured `Unify.fs:251-286`. Anchor: Paper line 80; spec line 197; corpus note line 44.
8. Measure store and carrier store. Measure variables bind to `Dimension`, carrier variables to carriers; `resolve` is the only read. Removes the type-store binding of measure variables, measured `UnionFind.fs:67-72`. Anchor: one place pull; Paper line 74.
9. `HasMeasure` removed; no producer, b.6. Removes the no-op solver arm, `Unify.fs:379-382`. Plan amendment in (j).
10. Generalisation and instantiation. Free measure and carrier variables collected through resolution; the spec's generalizable-expression rules; Hermite simplification; kind-preserving instantiation; the `Application` node records the instantiation; CCS8047, b.4. Removes the assumption that only `Type`-kinded parameters are quantified, measured `UnionFind.fs:399-405`. Anchor: spec lines 209, 515-572; DBC line 204.
11. Diagnostics. CCS8040 and CCS8041 minted by `solveDim` and surfaced with their own code; the `CCS804x` and `CCS80xx` entries added to the code table now, the full `FS → CCS` mapping with step 4. Removes the `FS0001` blanket, measured `NativeService.fs:246-259`, and the clef-side `FS8010`-`FS8012` occupants of W-row numbers. Anchor: D3 amended.
12. Monomorphisation key excludes measure variables, d.3. Removes a body per measure instantiation. Anchor: Paper line 106. `src/Compiler/Nanopass/Monomorphization.fs` is untracked and unread, i.15.
13. Saturation residual check. Every numeric node's `Type` resolved through all stores; free variables only under a scheme; CCS8047 otherwise; thereafter immutable, I2. Anchor: Paper §4.1 line 372.
    Gate: UoM-1, -5, -6, -7, -8, Plan line 144.

**Step 3 preview, operators**

14. Operator intrinsic signatures over `κ` and measure variables, c; `+` as a kind dispatch with CCS8001; carrier conversions name source and target and preserve dimension, L-4. Removes the `'T -> 'T -> 'T` and `'T -> 'T -> bool` arms and their unconstrained fresh variable, measured `Intrinsics.fs:817-827`; the `'a -> Target` conversion arms, `Intrinsics.fs:953-976`; the discarded conversion category, L-5. Gate: UoM-2, -3, -4, -9, W-2.

**Steps 6 and 7, carriage and width**

15. Reified `clef.dim` attribute stamped by the witness from the node's rendered dimension; build-time twin, d.2 and d.4. Removes nothing in CCS; retires `NativeTypes.fs:657-658` "CCS preserves type identity; Alex resolves to concrete size" and the `ntu-types.md` §1, §1.1, §3.2, §3.3, §7.1, §9.2 "Alex resolves" sentences, spec edits.
16. Width coeffect pass at saturation. `WidthAnnotation` on every numeric node from `PlatformContext` and the interval fixpoint; seal meet e.3; coverage e.4; unobservable e.5; CCS8011 to CCS8018. Removes name equality as the width mechanism, measured `Unify.fs:88-89`; platform-word minting of bare literals, L-1; witness-side widening and truncation, L-7 to L-9; the CPU default and FPGA throw, L-10; Composer's interim `IntervalAnalysis.fs`.

Order: 1 → 6, then 7 → 13, then 14, then 15 and 16.

---

## (i) Open items the corpus does not settle

1. Region mismatch number. `error-handling.md` line 190 places regions in CCS8100-8199 and line 314 spends CCS8100-8104 on null. Verification M-4: "the spec assigns no number". CCS8110 proposed here; needs the D3 mapping table. The whole collision set is settled by the renumbering in (f) and (j), but the spec edits could not be made.
2. Bare literal dimension. Paper Appendix A line 707 "`g` is assigned dimension variable `'d_g`" and line 718 "inferred from the known value of the gravitational constant" against §2.6 line 157 and Appendix C line 784. Settled dimensionless; a paper rough edge to report.
3. Abbreviation presentation. `units-of-measure.md` line 180: "abbreviations are not expanded for presentation" against base-form diagnostics. Base form taken in the checker; hover folding is a Lattice concern, open.
4. `int` and `uint`. `native-type-universe.md` §2.3 line 124: "**`int` = platform word**" and line 134: "**`int` and `nativeint` are synonyms**"; `ntu-types.md` §4.1 line 131: "| `int` | `NTUint (Resolved Register)` |" against D1 as amended. Three spec texts need reconciling at step 6. `uint` as `Int` carrier with a non-negativity range claim and no width is a choice made here; spec silent on a bare unsigned kind.
5. Wrapping versus coverage. `width-inference.md` §7 line 69 against `native-type-universe.md` §2.3 line 154 and `width-inference.md` §8 line 83. Resolved as e.4; a decision, not a reading.
6. Seal and explicit-conversion syntax. `numeric-selection.md` §14 line 333: "**Seal syntax.** The Tier-3 seal form (operator, attribute, or quotation) … are open"; `width-inference.md` §7: "The surface syntax for an explicit conversion … is open." CCS8013's fix-it has no syntax to suggest. D1 line 202: "seal syntax is open"; a.4 reads every numeric argument as a measure, so a future seal form cannot use the angle brackets.
7. String measures. `/home/hhh/repos/clef-lang-site/hugo/content/docs/design/types/dimensional-type-safety.md` line 148: "[<MeasureAnnotatedAbbreviation>] type CustomerId = string<customerId>". Spec and papers silent. CCS8046 rejects it by construction today, which may be wrong.
8. Access covariance. Plan §1 line 31 "access is covariant" against D2. Settled by the D2 amendment: invariant, coerced only through `Ptr.asReadOnly`. Step 5's concern; recorded because it decides that the enumeration sort needs no ordering.
9. Rational exponents. Paper line 84 defers; the parser accepts them, `SyntaxTree.fs:222`; GA-02 §2 line 23 admits a $\mathbb{Q}$-exponent group. CCS8048 in syntax, CCS8041 in unification.
10. `decimal` carrier. `units-of-measure.md` line 81 lists `decimal` among measured types; the NTU chapters are silent. Open.
11. Drop point of the reified attribute. DBC §3.1 line 89 "then consumed" against NFT §8.2 line 270 and Paper §2.3 line 104. Paper taken: every pass propagates, debug metadata at native emission; the exact pass is unnamed.
12. Dimensional metadata across the wire. DBC §3.1 line 89 against `program-hypergraph-paper.md` §8.8 line 482. PHG paper followed; out of scope.
13. Where `sqrt`, `atan2`, `pown` live. Spec line 321 types them as library functions; CCS has intrinsic arms, measured `Intrinsics.fs:560-563`. The `pown` literal-exponent rule and the dimensionless-only rule for `exp` and `sin` are choices made here; silent in every source.
14. Tier-disagreement tolerance. `numeric-selection.md` §14 line 335: "Whether containment `R_lower ⊆ R_binding` is exact or within an ε … is open". Integers exact; reals open.
15. W-6 on the FPGA leg. The join over call sites gives one body at the joined width, e.3. Whether an FPGA leg should clone per call-site range is not in the corpus. `Monomorphization.fs` unread.
16. Where the Register and Pointer widths already ride the PSG. Plan W-3 "Today" column measures nothing; `NativeTypes.fs:70-72` unverified.
17. `R_eff = ∅` versus `R_cov = ∅` precedence. `numeric-selection.md` §14 item 8. Step 8.
18. The reified attribute's name. `clef.dim` chosen; corpus silent.

---

## (j) Plan amendments

Exact replacement wording per rule, from the verification verdicts. The UoM code substitution `CCS8100 → CCS8040` applies to every UoM row and to hardening step 4. The seal code substitution `CCS8010 → CCS8013` applies to W-1.

**§0 position statement.** Replace with: "Dimensions are part of type identity and are never erased by the checker: CCS infers them, checks them, and resolves the platform-dependent ones against the platform description at saturation, per program-graph section; the resolved values ride on the PSG as annotations, Alex reads them, and they are dropped only at native emission, where they become debug metadata and never touch the instruction stream (DTS/DMM §1.1, §2.3). This is the same rule that settled closures, obligations and layout: the graph decides, the witness observes. One text in the corpus still says otherwise and is corrected as part of this plan (step 6): `ntu-types.md` §1 (\"type WIDTH is an erased assumption\"; \"resolved by Alex via `PlatformContext`\"), §1.1 (\"Alex witnesses platform quotations to determine type width\"), §3.2 (\"Alex resolves type width\"), §3.3 (\"erased before code generation. Alex makes final width decisions\"), §7.1 (\"Alex: Resolves Register dimension\") and §9.2 (\"MUST resolve NTU types using platform quotations\") place resolution below the witness boundary, against that chapter's own §2.1 and §5.1 comments. `ntu-dimensional-architecture.md` §4.3 and §5.2 (spec commit c9571d7, 2026-09-04) and the `NativeTypes.fs:69-72` comment (clef commit dab164124) already state the rule; the plan's earlier citation of them as inverting the design is withdrawn. The platform description is always present (there is no target-free compilation), so cross-apply at saturation is always available; `PlatformContext.resolveWidth` already lives in CCS (`NativeTypes.fs:443-448`), and the layout literals depend on it."

**§1 dimension-family table.** Width row: "| **Width** | the bit width of an integer or real | lattice family, not a group: a bounded interval domain over Z, meet-directed, propagated through the PSG dataflow to a least fixed point and never unified; the width is derived from the analysed range; a written width (`int32`, `uint8`, `nativeint`) is a Tier-3 seal checked for coverage; `Resolved Pointer/Register` seals take their value from `PlatformContext.Dimensions` per section at saturation | `width-inference.md` §1–§3, §5, §10; `numeric-selection.md` §3, §5; `arxiv-papers/research/grade-axis/02` §2 (Width row), §7.1; `ntu-dimensional-architecture.md` §2.1, §4.3 (platform resolution). `ntu-types.md` §3.1, §6.1–§6.2 (width as type identity, `int ≠ int64` by name) is the text decision D1 supersedes |". Memory row: "| **Memory space and access kind** | where a value resides and how it may be accessed, `Ptr<'T, 'Region, 'Access>`, `NTUMemorySpace`, `NTUAccessPattern` | an enumeration sort in the SMT sense, not a group: solved by equality unification over a finite domain in the same inference pass; every component is invariant and there is no subtyping (D2); a `ReadWrite` handle where `ReadOnly` is required passes through an explicit narrowing node (`Ptr.asReadOnly`), never by a checker rule | DTS/DMM §2.5; `arxiv-papers/research/grade-axis/01` §7 (identity check); `access-kinds.md` §Access Kind Coercion and §Diagnostics (`CCS8020`–`CCS8022`); `memory-regions.md`; `platform-bindings.md` §Program-Lifetime Spaces. `ntu-dimensional-architecture.md` §7.2's \"covariant access\" is an open question superseded by D2 |". Units-of-measure row, source column, append: "the spec chapter's erasure passages (line 12, §Measure Parameter Erasure, 'their compiled form is the corresponding primitive type') describe F#'s early erasure and are superseded by DTS/DMM §2.3". Grade sentence: "Grade (the parity component of Clifford grade, valued in Z2) is a further generator the PHG paper carries; it is out of this plan's first increment and enters through the same unification when it does, with the group `Z^n ⊕ Z2` no longer free and the solver moving from Hermite to Smith normal form (DTS/DMM §2.1)." Step 5's parenthesis "(access covariant, region invariant)" changes to "(every component invariant, D2)".

**UoM-1, UoM-2, UoM-3, UoM-5, UoM-7.** Code column: `CCS8040` (measure mismatch) in place of `CCS8100`.

**UoM-4.** Statement: "an unannotated numeric literal is dimensionless (`float = float<1>`, `units-of-measure.md` §Measures; the paper's Appendix A step 1, which gives a bare literal a fresh dimension variable, is superseded by its Appendix C, which annotates the constant); a dimensionless factor scales without changing dimension". Reject `let x : float<s> = 2.0 * 3.0<m>`; accept `let x : float<m> = 2.0 * 3.0<m>`; code `CCS8040`.

**UoM-6.** Code column: `CCS8040`. Statement may add: "comparison is typed at one measured type on both sides (`IComparable<float<'u>>`), so `<` on `float<m>` and `float<s>` fails measure unification".

**UoM-9.** Statement: "the paper's example infers its result without a return annotation". Reject: `let computeForce (m1: float<kg>) (m2: float<kg>) (r: float<m>) = let g = 6.674e-11<m^3 kg^-1 s^-2> in g * m1 * m2 / (r * r)` applied as `computeForce 1.0<m> 1.0<kg> 1.0<m>`. Accept: the same definition with no return annotation, inferred `float<kg m / s^2>`, and `computeForce 1.0<kg> 1.0<kg> 1.0<m>`. Code: `CCS8040`. Note: Appendix A as written (bare `g`) generalises to `float<'a> -> float<'b> -> float<'c> -> float<'a 'b / 'c^2>` under the dimensionless-literal rule of UoM-4, accepts a `float<m>` for a mass, and instantiates to `float<kg^2 / m^2>`; its claim that `'d_g` is inferred from the constant's value has no mechanism in the paper or spec, and Appendix C annotates the literal.

**W-1.** "| W-1 | two different seals meeting is an explicit-conversion site; a bare operand (an unsuffixed literal, whose type `int` is the bare integer kind, D1) adopts a covering seal | `int32 x + int64 y`; `nativeint p + int32 x` | `1 + 1L` (bare literal, point range `[1, 1]`, covered by the seal); `1L + 2L`; `int64 x + 1L` | `CCS8013` (seal mismatch; `CCS8010` is already the spec's null-keyword error, `types-and-type-constraints.md` §Null-freedom) | `1 + 1L` rejected by name, which `ntu-types.md` §6.2 (`let x: int64 = 42 // Error: int ≠ int64`) prescribes and D1 overrides — a spec tension recorded for step 6; seal pairs rejected by name (right result, wrong mechanism) |"

**W-2.** "| W-2 | operands of `-`, `*`, `/`, `%` are numeric; operands of `+` are both numeric or both string (D5), never `bool` | `true + true`; `true - true` | `1 + 2`; `\"a\" + \"b\"` | `CCS8000` | accepted |"

**W-3.** "| W-3 | a seal at a platform boundary comes from the platform description (word and pointer widths from `PlatformContext.Dimensions`; C ABI widths as the `Fixed` seals Farscape emits from `PlatformABI`, `ntu-dimensional-architecture.md` §2.1), resolved in CCS at saturation, never in the witness | (differential: one program compiled under two platform contexts yields layouts carrying each platform's declared widths; `expect.toml` names both layouts) | | | resolved in CCS (`NativeTypes.fs:443-448`; the header comment at `:69-72` now agrees); still contradicted by `NativeTypes.fs:658` and `:663` (\"Alex resolves to concrete size via platform quotations\") and by `ntu-types.md` §1, §1.1, §3.2, §3.3, §7.1, §9.2; `ntu-dimensional-architecture.md` §4.3 and §5.2 already read \"CCS at saturation; Alex reads\" (spec commit c9571d7) |"

**W-4.** "| W-4 | no silent default: an integer whose range is unobservable and that carries no seal from any source (dataflow, library, platform, developer) is a diagnostic; a bare real lowers to IEEE `f64`; a dimensioned real with an unobservable range is a diagnostic at the dimensioning seam that names the bare source. Arithmetic on a sealed operand keeps the seal's wrapping semantics (`native-type-universe.md` §2.3, `width-inference.md` §8), so a sealed result is covered by construction | `let rec run n = run (n + 1)` (no modulus, no comparison, no seal: unobservable on every target); `let y : float<N> = bareInput * oneNewton` | `let f (n: int32) = n + 1` (the sum wraps in the seal); `let y : float = bareInput * 2.0` | `CCS8011` (range unobservable) | no diagnostic in CCS; Alex throws `FPGA0001` on the FPGA leg (`PSGCombinators.fs:121`), CPU leg falls back to the platform word (`:99`) |"

**W-5.** "| W-5 | a seal must cover the analysed range (a bare range meeting a seal is the `width-inference.md` §7.2 conversion check on a singleton candidate set, `numeric-selection.md` §2.1) | `let x : uint8 = 300`; `let c : int8 = counter % 1000` with `counter : uint32` (range `[0, 999]`) | `let x : uint8 = counter % 256` with `counter : uint32` (range `[0, 255]`); `let y : int8 = -128` | `CCS8012` (seal does not cover range) | no range analysis in CCS |"

**W-6.** "| W-6 | width is propagated, never unified (`arxiv-papers/research/grade-axis/02` §2 table, §7.2; `width-inference.md` §2, §5): a non-`inline` numeric function has one body whose parameter range is the join over its call sites (the lattice least fixed point, 02 §7.1); a call site carries its own range only under explicit `inline` | (none) | `let g x y = x + y` used at `g 1L 2L` and `g 1 2` in one program: the parameter adopts the `int64` seal at the first site, the bare point range at the second is covered, both accepted with one body | | second use rejected by name (`Bindings.fs:397` disables generalisation, so `'T` binds to `int64` at the first use); `ntu-types.md` §6.1 prescribes that rejection (`unify(NTUint(Resolved Register), NTUint(Fixed 64)) = Error`), a spec tension for step 6 |"

**M-1.** "| M-1 | no write through a `ReadOnly` handle | `let w (p: Ptr<byte, Flash, ReadOnly>) = Ptr.write p 0uy` | `let w (p: Ptr<int, Stack, ReadWrite>) = Ptr.write p 1` | `CCS8020` | `Ptr<'T, 'Region, 'Access>` is not a type constructor CCS knows: `mkTypeConRefWithMeasures` (`NativeTypes.fs:762`) has no caller, `Ptr` appears only in a comment (`:727`), and the samples call `Ptr.read`/`Ptr.write` on a bare `nativeint` (`stm32l5-blinky/STM32L5.fs:92-94`), so there is no access component to check |"

**M-2.** "| M-2 | no read through a `WriteOnly` handle | `let r (q: Ptr<uint32, Peripheral, WriteOnly>) = Ptr.read q` | `let r (q: Ptr<uint32, Peripheral, ReadWrite>) = Ptr.read q` | `CCS8021` | as M-1: no `Ptr` type constructor exists in CCS; `Ptr.read` is applied to a bare `nativeint` in the samples |"

**M-3.** "| M-3 | access is part of identity, no subtyping: a `ReadWrite` handle where `ReadOnly` is required passes only through the explicit coercion `Ptr.asReadOnly` (`Ptr.asWriteOnly` for `WriteOnly`), which is a node in the graph rather than a rule in the checker | `let ro : Ptr<int, Stack, ReadOnly> = rw` with `rw : Ptr<int, Stack, ReadWrite>`; `let rw2 : Ptr<int, Stack, ReadWrite> = ro` | `let ro : Ptr<int, Stack, ReadOnly> = Ptr.asReadOnly rw` | `CCS8022` | as M-1: no `Ptr` type constructor exists in CCS; `ntu-dimensional-architecture.md` §7.2 (Prospective) still says \"Yes, covariant access\" and is corrected with step 6 |"

**M-4.** "| M-4 | region is invariant: an enumeration sort unified by equality (DTS/DMM §2.5) | `let f (p: Ptr<int, Peripheral, ReadWrite>) = Ptr.read p` then `f stackPtr` with `stackPtr : Ptr<int, Stack, ReadWrite>` | `f gpioReg` with `gpioReg : Ptr<int, Peripheral, ReadWrite>` | `CCS81xx` (region mismatch; the spec assigns no number: `error-handling.md` places regions in CCS8100–CCS8199 while its own table already spends CCS8100–CCS8104 on null-freedom, a rough edge to report; clef's Appendix D `FS8003` is on the wrong series and its §9.4 \"Regions form a subtyping hierarchy for assignment\" is retired with step 4) | as M-1: no `Ptr` type constructor exists in CCS |"

**M-5.** "| M-5 | every dimensional component is part of identity (D2): unit, region, access | `let f (b: array<int, 4, Stack>) = b` applied to `s : array<int, 4, Sram>` | same region | region code as M-4 | `NTUQualifiers` are excluded from identity (`NativeTypes.fs:248`, `Unify.fs:86-88`) and no surface form carries a memory space on a numeric: `ntu-dimensional-architecture.md` §2.2 is marked Design (\"could be type-level properties\") and `NTUint(Fixed 32, Global)` is the §7.2 open question, not a program; the numeric-carried memory-space row joins the set when §2.2 leaves Design |"

**D1.** (a) Replace "HelloArty (`Behavior.clef:55-58` declares `Counter: int` and receives 29 bits;" with "HelloArty (`Behavior.clef:55-58` declares `Counter: int` and receives 31 bits by the spec's table (`width-inference.md` §3) and HelloArty's README, 29 by the spec's formula and the site posts, the discrepancy L-7b records;". (b) After "`nativeint` is a seal whose width the platform description supplies." insert: "`int` is not a seal: it is the bare integer kind, the type of an unsuffixed literal (`expressions.md` §Constant Expressions, `86 // int/int32`), whose CPU realisation rounds to the native word (`width-inference.md` §8) and whose FPGA realisation is the inferred width (HelloArty's `Counter: int`). `native-type-universe.md` §2.3 (`int` = platform word; `int` and `nativeint` are synonyms), `ntu-types.md` §2.2 (`int` = `NTUint (Resolved Register)`), §3.1, §6.1 and §6.2 (`let x: int64 = 42 // Error: int ≠ int64`) state the two-regime reading D1 retires; they are the spec conflicts step 6 rewrites, beside `ntu-types.md`'s 'resolved by Alex'." (c) Replace "Ada is the precedent: range and precision belong to the type declaration, a representation clause (`'Size`) is validated against them, and dimensions are an aspect of the numeric type; VHDL puts range and width on the subtype the same way." with "Ada and VHDL are the precedent the site names (`dimensional-type-safety.md` §Historical Foundations, `doubling-down-dmm-dts.md` §The Ada/VHDL Heritage: derived types and physical types); the further Ada facts relied on here (a range on the type declaration, a `'Size` representation clause validated against it, dimensions as a GNAT aspect) are Ada language facts not anchored in the corpus." (d) In consequence (3) replace "the seal at a boundary is supplied by the platform description (its word, pointer, FFI and syscall widths)" with "the seal at a boundary is supplied by the platform description (its word and pointer widths, `PlatformContext.Dimensions`) or by the `Fixed` widths the binding generator emits for C ABI types from `PlatformABI` (`ntu-dimensional-architecture.md` §2.1); an exported function parameter typed `int` on a CPU target is such a boundary and takes the word seal, so W-4's unobservable-range diagnostic is for values no platform fact governs".

**D2.** Replace with: "**D2, dimensional identity (decided: exact match).** Two dimensional types are the same when every component matches: unit (compared in the spec's normalised form), region (the memory space of a `Ptr<'T, 'Region, 'Access>` or `array<'T, n, Region>` handle, an enumeration sort unified by equality per DTS/DMM §2.5), and access kind. There is no subtyping on any component: a `ReadWrite` handle where a `ReadOnly` one is required passes only through the explicit coercion `Ptr.asReadOnly` (`Ptr.asWriteOnly` for `WriteOnly`), which is a node in the graph rather than a rule in the checker; the word \"narrowing\" is not used here, being the spec's term for eliminating a foreign value at the JavaScript boundary. A seal is not a component of identity: under D1 it is the highest-precedence range claim on a value, propagated and never unified, so two seals meeting on one value is an explicit-conversion site (W-1) and a bare operand adopting a seal is not a mismatch. The §1 table row for memory space and access kind and hardening step 5 are corrected to \"access invariant, coerced only by `Ptr.asReadOnly`/`Ptr.asWriteOnly`\"; `ntu-dimensional-architecture.md` §7.2's \"covariant access\" is rewritten with step 6."

**D3.** Replace with: "**D3, diagnostic series (decided: CCS).** Every `FS`-prefixed code is retired, including the lexer and parser codes inherited from FCS (the spec's own `warning FS0058` example in `lexical-filtering.md` §Offside moves with them); a mapping table lands with hardening step 4 and clef's Appendix D moves with it. The table allocates inside the ranges `error-handling.md` §Error Codes already fixes (CCS8000–8099 type system incl. access kinds; CCS8100–8199 memory management; CCS8200–8299 platform bindings; CCS8300–8399 effect system; CCS8400–8499 code generation) and never reassigns a code the spec has bound: `CCS8010` (null not permitted, `types-and-type-constraints.md`), `CCS8020`–`CCS8022` (access kinds), `CCS8030`–`CCS8033` (platform intrinsics), `CCS8100`–`CCS8104` (null-freedom, `error-handling.md` §Diagnostics). The measure-mismatch (`CCS8100`), seal (`CCS8010`–`CCS8012`) and region (`CCS8003`) codes in §3 are renumbered accordingly; papers are silent on any code series."

**D4.** Replace with: "**D4, where the measure lives (decided: on the numeric type).** The measure is a component of the numeric type node, beside the range and representation annotations that accrue to it, as Ada's dimension aspect and VHDL's range constraint sit on the type rather than as a parameter. `float<newtons>` is Kennedy's surface syntax for that component, not a type-constructor application; `float` keeps arity 0, and bare `float` is the component at the dimensionless measure `1` (`float = float<1>`, `units-of-measure.md` §Measures), so a dimensionless operand unifies with `float<1>`. Declared types other than the numeric kinds may still take measure-sorted parameters (`Vector<[<Measure>] 'U>`, `Multivector<'A, [<Measure>] 'P>`, `Ptr<'T, 'Region, 'Access>`): those are the spec's Measure sort in parameter position, checked by the same measure unifier, not the numeric component. The spec's core-library form `type float<[<Measure>] 'U>` is read as presentation of this component, not as a constructor of arity 1; that chapter is reported as a tension."

**§5 step 2, design-derived.** Replace "`HasMeasure` enforced" with "`HasMeasure` removed: under D4 no source form produces it, and the fact it would carry is `TNum` equality, decided in one place". Anchor: b.6; `units-of-measure.md` lines 56-78 has no `'T<m>` form.

**§5 step 4 and §3 codes, design-derived.** The code table of section (f) replaces the Plan's numbers: `CCS8040`-`CCS8050` for measures, `CCS8011`-`CCS8018` for width and seals, `CCS8013` for seal mismatch, region proposed `CCS8110` pending the D3 table.

---

## (k) Verification summary

| Id | Verdict | Decisive anchor |
|---|---|---|
| UoM-1 | amend, code only | `units-of-measure.md` line 315: "`N<'U> -> N<'U> -> N<'U>`"; `error-handling.md` line 314: "| CCS8100 | Error | Cannot use 'null' in Clef" |
| UoM-2 | amend, code only | `units-of-measure.md` line 316: "`N<'U> -> N<'V> -> N<'U 'V>`" |
| UoM-3 | amend, code only | `units-of-measure.md` line 317: "`N<'U> -> N<'V> -> N<'U/'V>`" |
| UoM-4 | amend, state the dimensionless-literal rule | `units-of-measure.md` line 125: "`float = float<1>`"; Paper Appendix C line 784: "let g = 6.674e-11<m^3 * kg^-1 * s^-2>" |
| UoM-5 | amend, code only | `units-of-measure.md` line 178: "reduce each to normalized form … and then compare the syntax" |
| UoM-6 | amend, code and mechanism | `units-of-measure.md` line 291: "`System.IComparable<float<'u>>` and `System.IEquatable<float<'u>>`" |
| UoM-7 | amend, code only | `units-of-measure.md` line 199: "If constraints cannot be solved, a type error occurs." |
| UoM-8 | stands | Paper §2.2 line 82: "infers type `float<'d1> -> float<'d2> -> float<'d1 * 'd2>` without any annotation" |
| UoM-9 | amend, programs and code | Paper Appendix C lines 782-785: annotated parameters, annotated `g`; Paper §2.6 line 157: "Dimensional constraints alone do not determine numeric magnitudes" |
| W-1 | amend, code and spec tension | `types-and-type-constraints.md` line 743: "not permitted in Clef source code (error CCS8010)"; `ntu-types.md` §6.2 line 258: "let x: int64 = 42 // Error: int ≠ int64" |
| W-2 | amend, add the string branch | `units-of-measure.md` line 309: "`N` is any of these types"; `introduction.md` lines 171-175 string `+` |
| W-3 | amend, Today column and FFI source | `ntu-dimensional-architecture.md` §4.3 lines 310-312: "Resolution happens in CCS, at saturation"; §2.1 lines 94-97 `PlatformABI` |
| W-4 | amend, reject program and wrap rule | `width-inference.md` §6 line 62: "does **not** guess a width"; `native-type-universe.md` §2.3 line 124: "**`int` = platform word**" |
| W-5 | amend, fix `counter`'s sign | `numeric-selection.md` §2.1 line 52: "The Tier-3 seal check (§5) is a special case of this coverage check applied to a singleton `R`" |
| W-6 | amend, join not per-site | GA-02 §7.1 line 85: "the least fixed point of the propagation on the lattice axes, a different and cheaper object than a most general unifier" |
| M-1 | amend, `Ptr.write` form and Today column | `access-kinds.md` lines 75-77 and 141: "| CCS8020 | Cannot write to ReadOnly pointer |" |
| M-2 | amend, `Ptr.read` form | `access-kinds.md` lines 79-81 and 142: "| CCS8021 | Cannot read from WriteOnly pointer |" |
| M-3 | amend, `Ptr.asReadOnly`, drop "narrow" | `access-kinds.md` lines 99-101: "let ro : Ptr<int, Stack, ReadOnly> = Ptr.asReadOnly rw  // OK"; `terms-and-definitions.md` line 68 "narrowing" |
| M-4 | amend, code unallocated, no `_` in access slot | Paper §2.5 line 135: "memory dimensions are solved by equality unification over a finite domain"; `memory-regions.md` line 206 grammar |
| M-5 | amend, programs need surface syntax | `ntu-dimensional-architecture.md` §2.2 lines 124-128 "could be type-level properties"; `memory-regions.md` line 42 `array<byte, 1024, Stack>` |
| D1 | amend, four insertions | `width-inference.md` §10 line 95: "derived from the value's analyzed range, not from a target type name"; `expressions.md` line 280: "86 // int/int32" |
| D2 | amend, seal out, access invariant, no "narrowing" | Paper §2.5 line 135; `access-kinds.md` lines 99-100; GA-02 §7.1 line 87: "support is propagated, never unified" |
| D3 | amend, honour spec-bound codes | `error-handling.md` lines 189-190 blocks; line 314 CCS8100; `access-kinds.md` lines 141-143; `platform-bindings.md` lines 378-381 |
| D4 | amend, add `float<1>` and measure-sorted parameters | Paper §2.2 line 74: "type variables carry an associated dimension variable"; `numeric-selection.md` §4 line 122: "registered-under, not type-parameterized-by" |
| D5 | stands | `introduction.md` lines 171-175: "the only version of the `+` operator that accepts a left-hand argument of type `string` also takes a `string`" |
| §0 position | amend, withdraw stale citations, name `ntu-types.md` | `ntu-dimensional-architecture.md` §5.2 lines 327-329: "Alex witnesses dimensional types that CCS has already resolved"; Paper §1.1 line 29 |
| §1 table | amend, Width row, Memory row, UoM source, Grade sentence | GA-02 §2 line 24 Width row; Paper §2.1 line 68: "no longer free … from Hermite normal form to Smith normal form" |
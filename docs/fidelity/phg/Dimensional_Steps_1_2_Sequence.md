<!-- Provenance: proposed 2026-09-04 by the harness-and-step-0 workflow from a measured blast radius (clef 394 sites in 18 files, Composer 229 sites in 24 files); the three under-specified items in section 3 are decided in Dimensional_Vetting_Plan.md D7. Read-only proposal; no changeset here has been written yet. -->

# Changeset sequence for hardening steps 1 and 2

Design of record: `Dimensional_Vetting_Plan.md` §5 steps 1–2 and `Dimensional_Step1_2_Design.md` (h) items 1–13, read against the measured blast radius. Nothing below was written into code; this is the proposal.

## 0. Baseline, measured before proposing

| Gate | Command | Result |
|---|---|---|
| Composer build | `dotnet build /home/hhh/repos/Composer/src/Composer.fsproj` | exit 0 |
| RoundTrip compile | `cd /home/hhh/repos/BAREWire/samples/RoundTrip && Composer compile RoundTrip.fidproj` | exit 0, `targets/roundtrip` |
| RoundTrip run + diff | `./targets/roundtrip > out; diff out expected.txt` | run exit 0, diff empty: byte-identical |
| Vet, step-2 rows (per-leaf transcripts, `vet.sh --no-intermediates`) | `Composer/samples/dimensional` | UoM-1 and UoM-6 compile both reject and accept (measure dropped); UoM-5, UoM-7, UoM-8 fail every leaf with `FS0001 Arity mismatch` because `float<m>` in type position re-applies the measure argument to the arity-0 numeric tycon (`Types.fs:900-902`); no leaf prints a CCS code |

The working tree already carries the plan's step-0 "now" items, unreviewed: L-3 (`Literals.checkConst` returning `Result`, CCS8018 in `DiagnosticCodes`, callers in `NativeService.fs`, `Patterns.fs`, `Bindings.fs`) and L-5 (`ConversionCategory`, the MLIR op name and the dead citation removed from `SRTPResolution.fs`). Call that **CS-0**; the sequence below starts after it and does not re-touch it. `src/Compiler/Nanopass/Monomorphization.fs` is untracked but compiled (fsproj line 299); CS-3 edits an uncommitted file.

## 1. Why the middle of (h) collapses into one slice

Three dependencies fix the shape, and they are why the sequence departs from the literal 1→6, 7→13 order:

1. `Measure = MOne|MVar|MProd|MInv|MCon` is the payload of `TMeasure` **and** of `Constraint.HasMeasure` (`NativeTypes.fs:914, 945, 996-1001`). Removing it (h.1's removal half) forces `TMeasure of Dimension` (h.2), `HasMeasure` gone (h.9), the occurs/free-vars arms in `UnionFind.fs:208-220, 285-297`, the `unifyMeasure` arms in `Unify.fs:250-286` (h.7), the Arena producer `Intrinsics.fs:573-574` and the diagnostic arm `Collections.fs:211` into the same diff.
2. The 19 numeric tycons are the identity of every number (`NativeTypes.fs:1380-1443`). Removing them (h.2) forces every `tycon.NTUKind` reader in clef and Composer, the literal form (`NativeLiteral.Int/UInt/Float of _ * NTUKind`, h.5) and the renderer `formatType` (h.6) into the same diff.
3. The `TNum ~ TNum` unifier arm must be written once. An interim "ground equality, variables unsupported" arm would be a second shape for one fact and would falsely reject RoundTrip's `Arena<'lifetime>` measure variables that today pass through the never-binding arm. So `solveDim` and the measure store (h.7, h.8) land with `TNum`, and CCS8040/CCS8041 land with `solveDim` (no silent failure: the day a measure equation can fail it carries its code).

Consequence: h.2, h.5, h.6, h.7, h.8, h.9, the wiring half of h.3/h.4 and the measure half of h.11 are one changeset (CS-4). Everything else is additive before it or a consumer after it. h.12 is pulled forward (CS-3) because the first day a measure variable binds, the monomorphisation key would otherwise split bodies per dimension and RoundTrip could change.

## 2. The changesets

### CS-1 — The dimension algebra

- **Anchors:** (a.1), (b.2), (b.3); (h) 1 (the additive half).
- **Files by role:** one new file, the measure-algebra module, placed in the fsproj before `NativeTypedTree/NativeTypes.fs` (line 236) with no dependency on the type DU: `BaseMeasure`, `MeasureVar`, `Dimension` with `mk` as the sole constructor (canonical form, no stored zero), the group operations, `isGround`, `resolve`, `render` (the spec's normalised presentation: variables first, then identifiers, alphabetical, positives `/` negatives, `1` for empty), `MeasureStore` (persistent `MeasureVar -> Dimension`), `DimFailure = Mismatch | NoIntegerSolution`, and `solveDim` (steps 1–4 of b.2: residual, ground check, single-variable divisibility, Euclid elimination with a fresh variable). `Clef.Compiler.Service.fsproj` gains one `Compile Include`.
- **Removes:** nothing yet (the old DU's removal is CS-4; two forms must not both be consumed, so the old one is not touched here).
- **Gate:** Composer builds; RoundTrip byte-identical; `vet.sh --through 2` unchanged from baseline. No vet row turns green.
- **Size:** ~250 new lines, 1 file + fsproj.
- **Risk:** low. `solveDim` has no consumer, so its correctness is unobserved until CS-4; the owner may want the Euclid step exercised on the spec's `m^2/s^2 = 'U^2` and `'U^2 = m` cases by hand before CS-4 lands.

### CS-2 — The measure environment and the one syntax translator

- **Anchors:** (a.3), (a.4); (h) 3 and 4 (definitions only; wiring is CS-4).
- **Files by role:** the algebra module (or a sibling) gains `MeasureDef = Primitive | Abbreviation of BaseMeasure * Dimension` and `MeasureEnv` with a registration function that translates an abbreviation's right-hand side once, in dependency order, through the environment as it stands (absent-self detects the cycle, CCS8043; parameters, CCS8049). The type-position resolver file (`Expressions/Types.fs`) gains `dimensionOfSyntax : MeasureEnv -> <measure syntax> -> Result<Dimension, Diagnostic>` covering the a.4 table (`SynMeasure.*`, `SynType.App` on a numeric carrier, `Tuple`/`Slash` segments, `MeasurePower`, `StaticConstant 1`, `Anon`, `Var`) with CCS8042, CCS8045, CCS8046, CCS8048, CCS8050. `TypeEnv` (`Types.fs:102`) gains a `Measures: MeasureEnv` field, initialised empty at its constructors. `DiagnosticCodes` gains the CCS804x entries the translator mints.
- **Removes:** nothing; the translator has no caller until CS-4 (the `MeasurePower → base` and `Slash → None` arms are removed there, when their replacement can produce a `TNum`).
- **Gate:** build; RoundTrip; vet unchanged.
- **Size:** ~200 lines, 3 files.
- **Risk:** low. The `[<Measure>]` declaration arm in `NativeService.fs` is not yet redirected, so declarations still fall through to `ClassDef`/`unitType`; that is deliberate (nothing reads the env yet) and is stated in the diff.

### CS-3 — The monomorphisation key excludes measure variables

- **Anchors:** (d.3); (h) 12; Paper line 106.
- **Files by role:** `Nanopass/Monomorphization.fs`: the scheme parameters that form the instance key are those of kind `Type` (later `Carrier`); `Measure`-kinded parameters are neither key material nor substituted at cloning; `matchTypeArgs` learns nothing from a `TMeasure`/`TMeasure` pair instead of falling to its "shapes disagree" arm.
- **Removes:** a body per measure instantiation (latent today: measure variables never bind, so the key already renders them `?`).
- **Gate:** build; RoundTrip byte-identical (must be, since no measure variable binds yet); vet unchanged.
- **Size:** ~20 lines, 1 file (untracked; the owner should know the diff lands on an uncommitted file).
- **Risk:** the `TMeasure, TMeasure -> ok <- false` arm today makes `matchTypeArgs` return `None` for any generic over `Arena<'l>`; the pass's handling of `None` should be read before this changeset to be sure it is a diagnostic and not a skip. Not verified here.

### CS-4 — `TNum`: the numeric type, the measure form, and the unifier (the one large slice)

- **Anchors:** (a.2), (a.4) wiring, (b.2), (b.6), (e.2) "read once", (e.6) interim staging; (h) 2, 5, 6, 7, 8, 9, the wiring of 3 and 4, and the CCS8040/8041 half of 11.
- **Files by role, clef:**
  - the type universe (`NativeTypes.fs`): `NativeType.TNum(carrier, dim)` (plus the interim seal component, see U-1), `Carrier = Int | Real`, `CarrierRef = Kind | CVar`, `TypeParamKind.Carrier`, `TMeasure of Dimension`; the seal form `Representation` of (e.1) with the e.1 spelling table as the single name↔seal fact; the numeric `Types.*Type` values redefined as `TNum` at `Dimension.one` with their seal (the names stay because ~90 intrinsic signatures, the Baker recipes and `StringPatterns.fs:162` read them: they are the one place); `tryGetNTUKind`/`isNumericType`/`isIntegerType`/`isFloatType` become reads of `TNum`; `layoutOf`, `resolveSize`, `resolveAlign` read the seal (bare `Int` keeps today's `PlatformWord`, bare `Real` `Inline(8,8)`: today's behaviour, L-10 retired at step 7); `NativeLiteral.Int/UInt/Float` carry the suffix seal instead of an `NTUKind`; `formatType` renders `TNum` through `Dimension.render` with the carrier as its seal spelling; `NTUKind.name` loses its numeric rows.
  - the literal resolver (`Literals.fs`): `SynConst.Measure` → `TNum(carrier, dimensionOfSyntax …)`, bare → `one`, `_` → fresh `MeasureVar`, `'u` → CCS8044.
  - the type-position resolver (`Types.fs`): `SynType.App` on a numeric carrier and `MeasurePower` go through `dimensionOfSyntax`; the numeric rows of `resolveTypeName` produce `TNum` values (still by name here; the pull to one table is CS-5).
  - the declaration checker (`NativeService.fs`): the `[<Measure>] type` arm registers into `TypeEnv.Measures` and no longer falls through to `ClassDef`.
  - the unifier (`Unify.fs`): `TNum ~ TNum` (carriers, then `solveDim`), `TVar ~ TNum`, `TMeasure ~ TMeasure` via `solveDim`, `CVar` binding; `UnificationError` gains `MeasureMismatch` and `NoIntegerSolution`; the `HasMeasure` arm and the `Constraint` case go.
  - the stores (`UnionFind.fs`): measure variables bind in the measure store, carrier variables in the carrier store, `resolve` the only read; occurs and free-vars walk `Dimension.Vars`; `freshMeasureVar` mints a `MeasureVar`.
  - the diagnostics table (`Types.fs` `DiagnosticCodes`) and the surfacing (`NativeService.fs:246-259`): `MeasureMismatch` → CCS8040 with both sides rendered plus the residual, `NoIntegerSolution` → CCS8041; the other cases keep their present code until CS-7.
  - the intrinsic table (`Intrinsics.fs:573-574`): the Arena lifetime is `TMeasure (Dimension.ofVar v)`.
  - the recipes: `MatchRecipes.fs:509-547` (the inverse `NTUKind → type` table is deleted; a literal's type is `TNum` of its carrier at `one` with its seal), `Primitives.fs:377, 386, 875`, `Decomposition.fs:310, 314` (literal constructors take the seal), `IntrinsicElaboration.fs:41-42` (`mapsToIndex` reads `PlatformInt(Pointer, _)`), `Collections.fs:211`.
- **Files by role, Composer (reads only):** `TypeMapping.fs:101-146, 158-200, 664-676`, `SSAAssignment.fs:47-131`, `LiteralPatterns.fs:49, 54, 64`, `ApplicationPatterns.fs:470-471, 511-512`. Each is today's table re-keyed from `tycon.NTUKind`/the literal's `NTUKind` to the `TNum` carrier and seal read off the node's type, with the same right-hand sides: `FixedInt(n, _)` → `TInt n`; `PlatformInt(Register, _)` and bare `Int` → the platform-word arm (CPU) / `IntWidth 0` (FPGA) exactly as `Resolved Register` does today; `PlatformInt(Pointer, _)` → `TIndex`; `Ieee 32/64` and bare `Real` → `F32`/`F64`; signedness at 470/511 read from the seal's `signed` flag, bare `Int` signed as `NTUint` is today. `TMeasure -> failwith` at `TypeMapping.fs:404`, `mapNTUKindForPlatform` and the non-numeric `NTUKind` arms are untouched. No Composer site gains a decision it does not make today; the pre-existing platform-word default (L-10) is kept, named, and removed at step 7.
- **Removes:** the `Measure` DU and `formatMeasure`; `HasMeasure` and its no-op arm; the 19 numeric tycons and `mkTypeConRefWithMeasures` (`:762`) and the `Ptr<'T,'region,'access>` comment (`:727`); the numeric `NTUKind` constructors `NTUint|NTUuint|NTUfloat|NTUposit` and `NTUWidth` (`WidthDimension` stays: `PlatformContext.Dimensions` and `PlatformInt` use it); the never-binding, positional and succeed-on-mismatch measure arms; the `MeasurePower → base` and `Slash → None` drops; the measure-discarding literal arm; `ntuKindToType`; the `Measure`-declaration fall-through.
- **Gate:** UoM-1 reject/accept, UoM-6 reject/accept, UoM-7 reject/accept green with CCS8040; UoM-5 accept's `let y : float<m s> = 1.0<s m>` green by canonical form; the `FS0001 Arity mismatch` on every annotated leaf gone; RoundTrip byte-identical; HelloProof unchanged. Not yet green (see U-3): UoM-5's division halves and UoM-8, which need the `*`/`/` schemes of (h) 14.
- **Size:** clef ≈ 600–700 lines across 14 files (`NativeTypes.fs` alone ≈ 300 of its 133 sites; `Unify.fs` ≈ 60; `UnionFind.fs` ≈ 50; `Literals.fs` ≈ 40; `MatchRecipes.fs` ≈ 50 removed; the rest ≤ 30 each); Composer ≈ 120 lines across 4 files. ≈ 800 total.
- **Risk:** the largest diff of the set and the one the owner reviews slowest. Its size depends on U-1 and U-2 below: if the store is threaded (U-2 persistent), every `applySubst`/`find` reader including `Monomorphization.fs` and `SSAAssignment.fs:125` changes signature; if the seal is not carried in the type (U-1), Composer cannot map the width of any un-annotated node and RoundTrip cannot be identical. `decimal` stays a nominal `NTUdecimal` tycon (open item i.10); `uint`'s interim seal is i.4. `IntervalAnalysis.fs:289` and `EscapeAnalysis.fs:152` read non-numeric kinds and are untouched.

### CS-5 — The seal spelling read in one place

- **Anchors:** (e.1) seal spellings, (e.2) "read once"; one-place pull.
- **Files by role:** the four name→type tables become reads of the spelling table introduced in CS-4: the type-position resolver rows (`Types.fs:828-846`), the conversion targets and the conversion name set (`SRTPResolution.fs:215-219, 297-315`), the `Convert` intrinsics (`Intrinsics.fs:961-975`) and the `Parse.*`/`Format.*` dispatch on `'int'|'int64'|'float'` (`Intrinsics.fs:292-315`). Composer's `SSAAssignment.fs:505-509` cost table on the same operation-name strings is a Composer compute site (plan L-4/L-9 territory) and is left for step 3.
- **Removes:** three of the four independent name→type tables and the string set.
- **Gate:** build; RoundTrip byte-identical; `vet.sh --through 2` unchanged from CS-4.
- **Size:** ~120 lines, 4 files.
- **Risk:** low; behaviour-preserving by construction (same spellings, one table). Not an (h) row; included because (e.2) requires the width name to be read once and CS-4 leaves it read four times.

### CS-6 — Generalisation and instantiation over measure and carrier variables

- **Anchors:** (b.4); (h) 10; spec lines 209, 515-572; DBC line 204.
- **Files by role:** the free-variable collection and scheme builder (`UnionFind.fs` `collectFreeTypeParams`, `canonicalizeVars`, `generalizeType`) collect measure and carrier variables through `resolve`, subtract the environment's, apply the spec's non-generalisable cases, and simplify by column Hermite normal form over the exponent matrix (rank many survivors, renamed in first-occurrence order); the instantiation (`NativeTypes.instantiate`, `Identity.fs:87-125`) mints fresh variables of the same kind; the `Application` node records its instantiation as an annotation (the application checker in `Expressions/Applications.fs`); the top-level generalisation site in `Bindings.fs` (the disabled path at `:397-399` is left as it is: nested generalisation is not this step); CCS8047 in `DiagnosticCodes` for an unresolved measure variable at a non-generalisable binding.
- **Removes:** the assumption that only `Type`-kinded parameters are quantified (`UnionFind.fs:399-405`).
- **Gate:** build; RoundTrip byte-identical (measure-only schemes emit one body by CS-3). The design's row is UoM-8, which also needs the `*` scheme (U-3); until that is decided no listed row is this changeset's own gate, and I recommend the owner add an accept leaf `let id (x: float<'u>) = x` used at `float<m>` and `float<s>` with the scheme rendered `float<'u> -> float<'u>` in the `-k` types index.
- **Size:** ~180 lines, 5 files.
- **Risk:** medium. The Hermite step is the one piece of new numerical code beyond `solveDim`; the environment-free-variable subtraction must resolve through the measure store or a variable bound after generalisation is quantified twice.

### CS-7 — Diagnostics on their own codes

- **Anchors:** (b.5), (f); (h) 11 (the remainder); D3.
- **Files by role:** the diagnostic table (`Types.fs` `DiagnosticCodes`) gains the (f) CCS80xx and CCS804x entries not yet minted (CCS8000–8002, 8011–8017, 8042–8050 where not added by CS-2/CS-4/CS-6) and retires the clef-side `FS8010`–`FS8013` occupants of W-row numbers; the surfacing (`NativeService.fs:246-259`) carries each `UnificationError` case's own code.
- **Removes:** the `FS0001` blanket, to the extent D3's table names a code for `TypeMismatch`, `InfiniteType`, `ArityMismatch`, the tuple and byref mismatches. (f) allocates none of those (CCS8000 is the operator-numeric message), and (h) 11 says the full `FS → CCS` mapping lands with step 4; so this changeset as written mints the measure and width codes and leaves the blanket on the non-measure cases until step 4's table, stated in the diff.
- **Gate:** every green reject row prints its own code; no vet leaf or RoundTrip prints an `FS804x`/`FS801x` code; RoundTrip byte-identical.
- **Size:** ~50 lines, 2 files.
- **Risk:** low mechanically; blocked in scope by the missing general-mismatch number (step 4).

### CS-8 — The saturation residual check

- **Anchors:** (0.4), (b.4) last paragraph; (h) 13; I2.
- **Files by role:** the point where every node's type is resolved through the substitution before the graph is built (`NativeService.fs:512-515`, the one place types leave the stores) resolves `TNum`/`TMeasure` through the measure and carrier stores as well, and a check module beside it asserts, per numeric node, ground or quantified-by-the-enclosing-scheme, else CCS8047 with the binding named; thereafter the node map is the immutable input to `Monomorphization.run` and the nanopasses. It runs where saturation begins in the pipeline (the resolved node map is what `BakerSaturation.fanOut` consumes, `NativeService.fs:573-574`); it uses the reserved term only for that boundary.
- **Removes:** nothing; it is the assertion that makes "never defaulted to `1`" observable.
- **Gate:** build; RoundTrip byte-identical; no CCS8047 on any accept leaf; a `0.0<_>` at a non-generalisable module binding reports CCS8047 (not a vet row; recommend one).
- **Size:** ~80 lines, 2 files.
- **Risk:** low; the check is a fold over the node map. If U-2 chooses a threaded store, this is where the store's final value is read, and the place is right.

**Order:** CS-0 (in tree) → CS-1 → CS-2 → CS-3 → CS-4 → CS-5 → CS-6 → CS-7 → CS-8; then (h) 14 as step 3. Each leaves Composer building and RoundTrip byte-identical by the gate stated; the Composer edits are confined to CS-4 and are reads.

## 3. Where the design note is under-specified for implementation

**U-1. Where the seal rides between steps 1–2 and step 7.** (a.2) makes `TNum` carrier plus dimension and its equality carrier plus dimension; (e.1) puts the seal on a per-node `WidthAnnotation` that step 7 creates; (e.2) says the written width is "read once at elaboration into `Seal`" *from step 1*; (e.6) says the interim keeps the name-based rejection of `int32 + int64` while "the unifier never consults it for a dimension decision". Before step 7 there is no propagation pass, so a seal on a node does not reach the use sites of a sealed binding; the only carriage that reaches every node today is the type flowing through unification, and Composer's width reads (and RoundTrip's byte identity) depend on every node's width being readable. Decision needed: an interim third component on `TNum` (compared by the unifier for the W-1 interim verdict and removed at step 7), or a node annotation now with an explicit propagation the design defers to step 7. `Seal.Site: NodeId` (e.1) cannot sit in a shared `Types.int32Type` value either way, so the interim form is `Representation`, not `Seal`; the note should say so.

**U-2. How the stores are carried.** (b.2) gives `solveDim : MeasureStore -> … -> Result<MeasureStore, _>`, pure over a persistent map, and (h) 8 says `resolve` is the only read. The type store is the mutable union-find (`TypeParam.Parent`), `unify` is `NativeType -> NativeType -> SourceRange -> unit` raising `UnificationException`, and `applySubst`/`find` are read without any handle from `formatType`, `Monomorphization.fs`, `NativeService.fs:512` and Composer (`SSAAssignment.fs:125`). Decision needed: thread a persistent measure/carrier store through `unify`, `solveConstraints`, `applySubst` and every reader (a signature change that reaches Composer's one `find` site and fixes CS-4's size at its upper estimate), or hold the measure and carrier bindings in kind-checked cells of the existing union-find with `resolve` as the single accessor (functional at the API, mutable underneath, as the type store already is). The standing rule against by-reference state and the existing union-find pull in opposite directions; the note does not choose.

**U-3. The step-2 gate rows that need step-3 operator schemes.** Plan step 2 and the leaves' `pending = "step 2"` gate UoM-5 and UoM-8 at step 2, but UoM-5's verdicts turn on `/` and UoM-8's on `*`, whose schemes (`κ<'u> -> κ<'v> -> κ<'u 'v>`, `κ<'u 'v^-1>`) are (h) 14, step 3; under today's `'T -> 'T -> 'T` those programs cannot report as expected (the UoM-5 reject prints CCS8040 at `/` for the wrong reason; the UoM-5 accept and UoM-8 accept are rejected). Decision needed: pull the `*` and `/` rows of (c) forward into step 2 (a small addition to CS-6 touching `Intrinsics.fs:817-822`), or re-gate UoM-5 and UoM-8 at step 3 and let step 2's gate be UoM-1, -6, -7 plus the `s m = m s` half of UoM-5.
# The strategy: native elaboration, staged delivery and decision gates

This chapter owns the recommended engineering direction. Build a native constraint-preserving elaborator, with dimensional and NFT obligations integral to its judgments, and retain ML-style inference where its generalization rules remain valid.

Horizons describe increasing evidence and engineering commitment with no calendar implications. The gates below qualify the chosen direction. They are not a reason to postpone choosing it. The full comparison matrix and Clef implementation experiments remain unexecuted. H1.1 includes separately identified checks of its small F# examples.

## Recommendation and scope

Adopt qualified, constraint-bearing schemes as the interface between local inference and the native disciplines. Use HM(X) as a design model for retained constraints, not as a claim that an existing theorem already covers Clef. Keep rank-1 inference for ordinary code, dimension-group unification for measures, unique-label rows for structural records, qualified requirements for nominal operations, and annotation-guided checking at higher-rank interfaces. Add explicit NFT value/instance/use judgments and deferred numeric/realization judgments in the existing CCS/Baker owners.

This combination is preferable for Clef because it separates the relationships the native universe must retain without requiring every relationship to become ordinary type equality or subtype inclusion. It preserves useful local inference, gives structural reuse a direct account, and makes resource and numeric evidence available before representation commitment. It also fits the retained-constraint and revision model already present in the PSG architecture. Its combined metatheory still has to be established for the admitted fragments.

The native universe determines the language problem. Targets can contribute capability constraints and realization obligations. A target may motivate an explicit language profile, but a different inferred meaning must not arise accidentally from which solver happened to run.

| Decision | Recommended choice | Why it fits the current remit |
|---|---|---|
| Core elaboration | Native schemes plus explicit dimensional, NFT, effect/demand and numeric obligations | Carrier-type inference alone cannot express restoration, live rights or deferred precision. |
| Structural abstraction | Unique-label measured rows with explicit update/replacement | Directly preserves an unknown tail and dimensional relationships with a clear native/JS field contract. |
| Nominal operations | Retained qualified requirements with checked resolution | Preserves nominal identity, getters, effects, equality and foreign handles without premature selection. |
| Rich polymorphism | Bidirectional checking with interface annotations | Delivers useful higher rank without making unrestricted impredicative inference a prerequisite. |
| Global algebraic subtyping | Exclude from the core rollout. Admit specific checked views later. | Its broad joins/bounds add a second large interaction surface before NFT, demand and numeric preservation are settled. |
| Numeric realization | Preserve symbolic/contextual facts and select a proved construction at commitment. | Supports richer precision across CPU, FPGA and JavaScript without width-named source numerics. |
| Differential compilation | Stable semantic identities and dependency-complete evidence reuse | Avoids unnecessary rework while retaining required ABI, resource, equality and platform invalidation. |
| Safety contract | No `unsafe` form or source-level obligation bypass, including library code | Low-level access and foreign integration require admitted contracts and evidence. Missing premises cannot be waived by syntax. |

Implement the evidence/scheme contract and NFT/deferred rules first (H1.4–H1.6), then measured structural interfaces (H1.1), the small annotated higher-rank interface (H1.3), and the shared JS/native-boundary examples (H1.8 and chapter 2). Establish the subtyping boundary in H1.2 and collect H1.7 measurements throughout. These identifiers name work items, not calendar phases.

## What the departure must earn

**The primary gain must be a richer native contract that ordinary compilation can infer, check and carry forward as evidence.** Accepting more source programs is useful. For Fidelity, the larger opportunity is to make relationships that currently live in API conventions, separate analyses or programmer reasoning part of the compiler's explicit contract.

Every experiment therefore has three comparison arms:

| Arm | What it contributes | What to record |
|---|---|---|
| Standard F# and its inference tooling | The production baseline: ordinary inference, nominal resolution, units of measure, generalization restrictions and inline member constraints. FSharp.Compiler.Service exposes resolved signatures, symbols and typed expressions. | The inferred interface, required annotations, diagnostics and available typed information, with compiler and tooling versions pinned. |
| Dave Thomas's `write-you-an-inference-in-fsharp` | Inspectable implementations that separate HM representation choices, split constraint solving, row polymorphism and annotated rank-N checking. | The exact mechanism and its scope rules. Identify any instrumentation or extension needed for the experiment. |
| The proposed Clef contract | Native schemes with explicit dimensional, row, demand and NFT judgments, connected to deferred numeric and boundary obligations. | The additional relationship expressed, its checked derivation, its assumptions, and what survives instantiation and lowering. |

Production F# is a stronger baseline than a small HM implementation. In particular, units of measure already reject dimensional mistakes, and inline member constraints already support useful generic access. Those successes belong in the comparison. The inference repository makes alternative mechanisms accessible. It does not already implement Clef's native obligations or provide their proofs.

For each case, distinguish an unchanged program in a shared fragment, an idiomatic encoding that preserves the required behavior, and a new language capability. A missing prototype feature is recorded as unsupported. Different evaluation or arithmetic semantics require an explicit correspondence before results can be compared.

### Tier 1 proof expression is a delivery criterion

Here, **Tier 1 means the admitted structural judgments established through inference and checking**. It does not mean every fact discovered during editing. Clef should enlarge the useful statements this layer can express and retain the derivations that justify them. That is a central reason to change inference, even when an ordinary F# program can compute the same result.

Consider a reusable function that divides a measured distance by a measured duration. F# already checks the relationship between those measures. Clef must preserve that result and connect it to the particular fields, instantiation and source revision that established it. A later numeric procedure can then use the dimensional conclusion while separately establishing a nonzero divisor, sufficient intermediate capacity and the promised accuracy. The first conclusion remains useful without pretending to prove the others.

The proposed gains are concrete:

| Experiment | Tier 1 statement to express and check | Additional obligation kept visible |
|---|---|---|
| E01–E02: measured records | The required field exists with the inferred measure. The row tail is bound consistently. Extension requires an absent label, and replacement follows its declared rule. | A replacement's unchanged field values need the checked operation semantics. A resource-bearing tail requires an admitted retention or borrow rule. |
| E05–E06, E24: polymorphism and lazy sharing | Each quantified variable is eligible for generalization. Instantiation respects scope. A captured live instance stays rigid, and sharing does not create another right to consume it. | Facts about mutable storage must hold at actual demand. Higher-rank checking does not establish arbitrary effect safety. |
| E07: dimensional composition | The result dimension follows from the input dimensions under the recorded substitution and generalization. | Range, definedness, error and representation coverage require their own evidence. This dimensional result is also a success of the F# baseline. |
| E12, E23: finite NFT use | Under the admitted matching premise, consuming a particular live right removes that instance from the remaining obligations. Equal creation values do not merge distinct instances. | The matching equality must itself be established. Structural use checking alone does not prove an arbitrary inverse, physical cleanup or eventual completion. |
| E14, E27–E28: evidence after edits | The same checked judgment can be reused only while its participants, scope and premises still apply. | Valid reuse and its performance benefit need separate invalidation checks and measurements. |

For example, the initial NFT fragment should make this transition inspectable:

```text
Before: live instance k is paired with creation value v of type A.
Premise: candidate w matches v under the admitted equality for A.
Action: consume the right associated with k.
After: k is absent from the live-resource map.
```

Copying an ordinary value does not recreate `k`. Nor can a second, distinct instance be discharged merely because it has the same creation value. If matching depends on a runtime observation, retain that condition and the checked success/failure paths. Do not report an unconditional static equality proof.

**A Tier 1 claim must include a checkable derivation and a failing control.** Record the proposition, admitted rules, substitutions, scope, participants, assumptions and checking route. Change a required field, measure, scope or live instance and demonstrate rejection for that reason. An editor should be able to explain which relationship was established and which obligation remains. A longer printed type or a green diagnostic alone does not demonstrate the gain.

Three results remain distinct: this example's judgment checks, the inference procedure is sound or principal for its stated fragment, and the actual compiler preserves the judgment through lowering. H1 must deliver the first and state the required metatheory. H2 binds the evidence to production compilation and artifacts. H3 extends the mechanized compiler argument.

## Horizon 1 — establish the useful fragment

### H1.1: add measured rows and qualified nominal requirements

**Select two complementary mechanisms, with the current behavior as a control:**

- the current nominal/pending-member baseline;
- unique-label measured structural rows: extension requires an absent label, and replacement/update is an explicit checked operation;
- generalized qualified member constraints that retain an operation or field requirement until an admitted use discharges it.

The first example is a reusable immutable `Value` projector applied to records carrying different measures and extra fields, followed by a transformer preserving the unknown tail. The mathematical scheme `forall a rho. {Value:a | rho} -> a` describes the proposed structural contract. Syntax remains an implementation decision.

Keep nominal getters/methods in a qualified operation contract with their effects. Do not silently reinterpret every nominal F# record or its equality as structural. Reject duplicate-label extension in the selected row fragment. Retain the corpus's scoped-label semantics only as a comparison, not Clef's default.

**Why include it:** the source seam is precise. DTS+DMM currently keeps ordinary non-inline unresolved member access monomorphic pending nominal context. A better admitted rule could improve useful inference and enlarge structural Tier 1 evidence. It would be a language change, not merely an optimization. [DTS §2.2, lines 84–109; source binding in chapter 5.]

#### The language change in code

Start with ordinary F# named records. Their `Value` fields have different measures:

```fsharp
[<Measure>]
type m

[<Measure>]
type s

type LengthReading =
    { Value: float<m>
      Sensor: string }

type TimeReading =
    { Value: float<s>
      Clock: string }

let lengthReading: LengthReading =
    { Value = 3.0<m>
      Sensor = "distance" }

let timeReading: TimeReading =
    { Value = 2.0<s>
      Clock = "elapsed" }

let projectLength (reading: LengthReading) : float<m> =
    reading.Value

let namedLength: float<m> = projectLength lengthReading
// projectLength timeReading fails: TimeReading is not LengthReading.
```

Removing the parameter annotation does not turn this into an open-record function. In this declaration context, with `TimeReading` declared after `LengthReading`, F# resolves the unannotated field access to `TimeReading`:

```fsharp
let projectInferred reading = reading.Value
let inferredProjector: TimeReading -> float<s> = projectInferred
let inferredTime: float<s> = projectInferred timeReading
```

F# also has an existing way to generalize this access. An inline, statically resolved member constraint admits both record types and retains their measures:

```fsharp
let inline projectValue (reading: ^Reading) : ^Value =
    ((^Reading) : (member Value: ^Value) reading)

let projectedLength: float<m> = projectValue lengthReading
let projectedTime: float<s> = projectValue timeReading
// projectedLength + projectedTime fails: meters and seconds do not match.
```

These positive and negative cases were checked with .NET SDK 10.0.401 and F# Interactive 15.2.401.0 for F# 10.0. Both negative cases produce FS0001 for the intended mismatch.

**Clef's proposed change is to admit an explicit structural row contract as ordinary reusable polymorphism.** The following is mathematical scheme notation, not proposed final Clef syntax. Begin with pure operations on immutable, freely shareable fields:

```text
project  : forall a rho. {Value: a | rho} -> a

mapValue : forall a b rho.
           (a -> b) -> {Value: a | rho} -> {Value: b | rho}

In both schemes: Value is absent from rho.
```

`rho` names the other fields and their types. For the length-shaped input, it contains `Sensor: string`. For the time-shaped input, it contains `Clock: string`. Each call instantiates `a` with its own measured type. The same `mapValue` contract says how the selected field may change while the remaining field types are retained. The existing nominal F# records do not silently become Clef structural records. A structural value or an admitted conversion supplies that boundary.

The distinction from the F# inline projector matters. A requirement for a `Value` member says how to access that member. It does not by itself state a relation between the unknown fields of an input record and an updated output record. F# can express useful alternatives through declared interfaces, operations and encodings. The proposed row rule puts this particular relationship directly in the reusable source scheme, without requiring a separately declared update operation for each nominal shape.

The row scheme constrains field types. The checked replacement rule and its elaboration must additionally establish that untouched field values are carried through. If the remaining fields contain a live completion right, the pure shareable example no longer suffices. E13 must refuse that case until an explicit retention/use rule is admitted.

##### Where the Tier 1 gain becomes visible

E01 must retain the field-membership, measure and instantiation derivation. E02 must retain the label-absence or replacement derivation and the unchanged row relationship. Removing a required field, combining incompatible measures in an operation or extending an existing label must fail for the corresponding rule. An explicitly typed transformation from one measure to another remains valid. A library author gets a reusable structural contract whose native obligations remain available to callers and later compiler stages.

The mechanism has a direct predecessor in `HMPure-Rowpolymorphism` and `HMMutable-RowPolymorphism` in Dave Thomas's`write-you-an-inference-in-fsharp`. Their selection, extension and restriction implementations make the row-solving work concrete. Clef deliberately chooses unique labels rather than the corpus's scoped duplicate labels, then adds measures, demand and resource premises. That is the specific extension to implement and justify.

**Deliverable:** a named declarative fragment, explicit generalization/instantiation rules, a proof-producing prototype or executable reference, positive/negative derivations, and a comparison with the baseline. Do not assume unresolved overload alternatives destroy principal qualified schemes. Examine entailment and ambiguity in the actual constraint calculus.

Select qualified `Eq`/`Ord`-style requirements for structural fields and the complete tail, at the same instantiated row type. Derived comparison uses a stable label order and must agree with equality. Nominal records retain their declared nominal equality. Cross-domain equality requires an explicit contract. E10 checks comparator coherence and persistent collections under this policy.

**Advance:** the implementation admits the specified abstractions, retains scope/demand/resource premises, and establishes the claimed soundness and principality or qualified-principality result for the fragment.

**Narrow the feature if necessary:** reject unrestricted polymorphic mutation, silent nominal/structural reinterpretation and discarded obligations. Rows remain the selected source contract. Realizing row/lacks constraints through existing qualified-constraint machinery is an implementation choice, not a reopening of that decision. Do not create a second semantic authority for row syntax.

### H1.2: keep unrestricted algebraic subtyping outside the core rollout

**Do not adopt a global subtype/union/intersection inference regime now.** Rows directly serve tail-preserving transformations. Qualified constraints serve nominal operations. Adding unrestricted subtype interaction to dimensions, live indices, mutable aliases and deferred evidence creates a larger theory than the immediate contracts require. Keep Simple-sub as a serious reference and challenge implementation, but do not make solving that whole combination a dependency of the native rollout.

A union of metre and second values can be an intentional sum-like type. Its existence does not by itself weaken dimensional safety. The relevant negative case is an operation that treats incompatible alternatives as one dimension without justified refinement. Likewise, deterministic native layout and absence of implicit boxing do not by themselves rule out static views, specialization or checked projections.

**Choose explicit sums/tagged alternatives for heterogeneous measured values.** Do not introduce implicit measured unions as the numeric default. Such unions can be sound, but moving a dimensional mismatch from a branch join to a later consumer makes the calculation's contract less direct. Explicit alternatives preserve intentional heterogeneity and its correlation while keeping ordinary measured arithmetic predictable.

**Allow a narrower route:** admit checked structural views or adapters when a concrete library/foreign interface needs them, with explicit read/write variance, observations and resource retention. A view does not imply discarded fields or copied identity. Establish it through existing source elaboration. The backend must not invent a coercion.

**Reopen the global decision only if** a concrete corpus shows substantial capability or annotation gains over the selected rows/qualified design, and an admitted combined calculus retains readable contracts, correlation and the required resource/demand properties. That is a specific reason to reconsider, not an open-ended request to benchmark every theory first.

**Outside the current core remit:** unrestricted top/unknown escapes, implicit measured joins, arbitrary impredicative subtype inference, or unproved writable covariance. Structural subtyping itself is not rejected as unsound or inherently OO.

### H1.3: use annotations for higher-rank interfaces

**Select annotation-guided bidirectional checking.** Use it for a callback required at two type/measure instantiations and a polymorphic record field. Retain ordinary synthesis elsewhere. State predicativity, subsumption and skolem scope. This buys the desired interface without asking everyday source inference to discover unrestricted higher-rank types.

The concrete mechanism reference is `HMRankN` and `Hindley-Milner-RankN.md` in `write-you-an-inference-in-fsharp`. Compare its annotated checking and skolem handling with the best applicable F# interface encoding. Clef's additional requirement is to carry qualified native and resource premises through that same scope boundary. E05 must expose those differences in signatures and derivations.

#### The difference between a generic function and a polymorphic callback

Ordinary F# infers a reusable generic function here. Each use of the let-bound `identity` can instantiate its type separately:

```fsharp
let identity value = value

let integerResult: int = identity 3
let booleanResult: bool = identity true
```

Passing a function as an ordinary parameter is a different case:

```fsharp
// Rejected by F#: transform has one parameter type in this body.
let useBoth transform = (transform 3, transform true)
```

The first call constrains the callback's input to `int`. The second requires `bool`, so F# reports a type mismatch. The fact that the caller might pass `identity` does not give this parameter a separately instantiable generic type.

F# has a working encoding through an interface with a generic method:

```fsharp
type IIdentity =
    abstract Apply<'T> : value: 'T -> 'T

let encodedIdentity =
    { new IIdentity with
        member _.Apply<'T>(value: 'T) : 'T = value }

let useBothEncoded (transform: IIdentity) : int * bool =
    transform.Apply 3, transform.Apply true

let integerResult, booleanResult = useBothEncoded encodedIdentity
```

Each invocation of `Apply` can choose its type argument. The same encoding works with measured types. Using the `m` and `s` declarations from H1.1:

```fsharp
let useMeasuredEncoded (transform: IIdentity) : float<m> * float<s> =
    transform.Apply 3.0<m>, transform.Apply 2.0<s>

let measuredPair: float<m> * float<s> =
    useMeasuredEncoded encodedIdentity
```

These two positive fixtures and the rejected ordinary-callback fixture were checked with .NET SDK 10.0.401 and F# Interactive 15.2.401.0 for F# 10.0. The positive runs produced no warnings. The negative run produced the expected FS0001 error. F# already supports the encoded interface. The proposed Clef gain is a direct function or field contract, together with explicit native obligations.

#### The proposed Clef annotation

The following blocks use mathematical schemes and schematic expressions. They explain the proposed checking rules and do not claim implemented Clef syntax:

```text
identity : forall a. a -> a
identity value = value

useBoth : (forall a. a -> a) -> (int * bool)
useBoth transform = (transform 3, transform true)

useBoth identity
```

The inner `forall` is the important change. The caller supplies one callback that must work for every admitted `a`. The body of `useBoth` may therefore instantiate it at `int` for one call and `bool` for the other. An unannotated callback parameter does not acquire this capability automatically. The selected discipline checks the explicitly polymorphic interface while retaining ordinary inference elsewhere.

The initial fragment instantiates `a` only with monotypes, such as `int`, `bool` or a measured numeric type, rather than polymorphic schemes. Higher-rank capability comes from the explicit quantifier in the parameter or field contract.

The same contract can appear inside a record field:

```text
type Transform = { Apply: forall a. a -> a }

transform : Transform
transform = { Apply = identity }

useRecord : Transform -> (int * bool)
useRecord item = (item.Apply 3, item.Apply true)
```

Here, the field itself is polymorphic. A record parameter whose field merely has type `a -> a` for one already chosen `a` would not meet this contract. This is useful when a component stores a reusable callback and its consumers need different instantiations without introducing a nominal generic-method wrapper.

E05 must retain the declared quantifier, both instantiations and the callback's scope and native requirements. That supplies a concrete Tier 1 statement: each use satisfies the same checked polymorphic interface. It does not by itself establish callback termination or an arbitrary behavioral law.

#### Two failures the annotation must show

First, a callback cannot let its private type escape into a single typed cell allocated outside it:

```text
saved = cell None                 // one shared cell outside the callback

escaping : forall a. a -> a
escaping value =
    write saved (Some value)       // reject: a would escape into saved
    value
```

When checking `escaping`, treat `a` as a fresh, fixed type placeholder. It must work without choosing that placeholder to match the outer cell's element type. Allowing that choice would defeat the promise that the callback supports every admitted type. This is the scope check often described as preventing a skolem escape. An explicitly admitted existential package would be a different storage contract.

Second, one shared mutable cell must not be generalized as though it were separate storage at every type:

```text
shared = cell []

// Invalid generalization of the same allocated cell:
shared : forall a. Cell<List<a>>

write shared<int> [42]
wrong : List<bool> = read shared<bool>
```

Both views would refer to the same cell, so the final read would treat stored integers as booleans. The generalization rule must reject this contract. Adding a higher-rank annotation cannot make it sound.

These controls address different questions: whether a callback-local type escapes its scope, and whether shared mutable storage was generalized unlawfully. A callback's use of unrelated monomorphic state, such as an integer counter, is not automatically a scope escape. It still needs the appropriate effect and demand contract. Captured live resource identities likewise retain the separate use and generalization rules from H1.4 and H1.6.

**Advance:** annotations buy a concrete interface capability, checking has the claimed soundness/completeness scope, and diagnostics remain usable on partial editor programs.

**Defer:** the only gain is speculative future expressiveness, or an impredicativity/recursion feature lacks an admitted inference contract. SuperF is a relevant research lead, but its terminating heuristic can reject valid programs. Do not describe it as unrestricted complete inference.

### H1.4: make judgments and evidence explicit

**Required across all H1 experiments.** Record the judgment and its derivation, including:

- binder scope; rigid/flexible type, row, measure and resource identities;
- actual environment dependencies and generalization exclusions;
- instantiation and retained qualified constraints;
- effects, lazy demand, aliasing and resource-use premises;
- source revision, participants, contextual assumptions and invalidation dependencies;
- the checking mechanism and unsupported, pending, contradiction and timeout outcomes.

This is an admitted family of source judgments, not a demand for one universal algebra. Start with the existing Baker ingredients, recipes and retained relations. Identify a missing fact before proposing a new representation or owner.

Use a scheme of the conceptual form `forall flexible variables. requirements => source type`. Quantified variables can include admitted type, row and measure variables. A live resource instance is not another freely quantified variable: retain its scope and use state separately, along with the creation-value relation. Context-specific ranges and platform/foreign facts keep their own dependency identities. This is the interface to implement, rather than flattening all obligations into host type equality.

Use `HMSplitSolve` in `write-you-an-inference-in-fsharp` as the scheduling reference. Its let-bound constraints are solved before generalization against the updated environment. Clef must make the corresponding boundary explicit even when some native requirements remain in a qualified scheme. Compare the resulting interface with F#'s inferred signature and value-restriction diagnostics. Then show the additional evidence for every native requirement retained or excluded.

**Generalization baseline:** select effect/coeffect-indexed rules, beginning with a conservative pure-immutable fragment. Inspect the computation that produces a shared binding at first demand, including allocation, reads/writes, foreign effects and captured rights. Generalize only admitted flexible variables independent of the environment and shared storage/resource assumptions. Retain eligible qualified requirements in the resulting scheme. Keep affected variables monomorphic when safety cannot be established.

A thunk is not automatically a safe value, and an unresolved qualified requirement is not automatically a reason to forbid generalization. Distinguish latent per-call effects from effects of producing the shared binding. E05/E06/E24 are required controls.

A checked answer proves only its stated conclusion. To claim principal inference, separately establish that every admitted solution is represented by the inferred scheme under the declared ordering. A canonical specialized substitution is not enough. A solution-set-preserving trace may contribute evidence, but the procedure's completeness and generalization theorem still need their own statement.

### H1.5: deferred numeric and stateful inference

**Make deferred numeric and transition judgments part of the selected elaboration contract.** They are not later FPGA optimizations. Keep source structure/dimension separate from contextual ranges, representation width and physical realization. Compare alternative solving schedules within that contract, preserving the same admitted judgments. [Site and platform evidence in chapter 2.]

Use a bounded state transition and a numerical reduction. Infer a reusable source scheme and retain admitted relations and pending obligations. Instantiate them at two distinct input domains, then establish a shared envelope or justified specialization.

Cross a counter bound from `2^29−1` to `2^29`: the unsigned capacity requirement changes from 29 to 30 bits without changing the field count or source dimensional scheme. Unknown range remains pending until the required commitment point. Proven noncoverage is a hard coverage error. No target may silently repair the example with a convenient width.

Repeat under CPU, FPGA and JSIR capability declarations. Include an actual Fidelity.Platform quotation and an immutable alias, preserving typed declaration identity and the selected binding. Change one capability or emulation policy and check that only conclusions with the affected premises are retained. Numeric accuracy selection, physical cost and availability are distinct judgments. A narrow inferred width does not establish DSP mapping or timing.

For stateful behavior, retain each output's transitive input/state dependencies. Compare Mealy and Moore forms at explicitly defined observation points across software and hardware realizations. For the reduction, distinguish a fixed rounded tree from an exact merge construction. Preserve intermediate capacity, partition coverage and accepted-contribution multiplicity through suspension and recovery. An inferred record shape cannot establish those relations alone.

Partas.Solid provides a practical comparison for the JavaScript side. Its F# component model passes through Fable transformations into JSX and then Solid's compiler. Its own engineering account distinguishes F# type checking from preservation of reactive property reads in the generated result. Use that distinction to frame E21–E22: a source contract must retain the relevant dependency and demand relationships, and the lowering must preserve them. A richer inferred type does not remove that second obligation. [Partas.Solid engineering walkthrough](https://shayanhabibi.github.io/shayanhabibi/partas-solid/)

Admit concurrent workflows only under a complete progress contract. Include blocking through ownership, capacity and cleanup, establish continuation progress, and retain the selected fairness and external-outcome/delivery premises. The promised request outcome may be a declared failure. A persistent service need not terminate. An unresolved call cannot acquire a liveness/deadlock proof merely by enabling supervision.

Graph coloring supplies proposed concurrent groups. Validate sound conflict edges and whole-group resource constraints, then establish permitted arithmetic and target profitability separately. E32–E33 make these obligations explicit. [Exact source and implementation-status binding in chapter 7.]

**Deliverable:** explicit interfaces among source inference, relational numeric/transition procedures and target constraints; derivations for the bounded examples; one deliberately stale range, quotation and recovery premise rejected by the appropriate checker. State which judgments are admitted as Tier 1, which require other procedures, and where runtime or host premises enter. A combined source principality claim needs its own theorem. Sound numeric bounds alone do not supply it.

**Advance:** the candidate preserves reusable schemes and justified contextual evidence, supplies a useful precision/automation or design-time gain, and binds each claimed realization to its actual premises.

**Defer or narrow:** obligations disappear at generalization, mutable observations survive invalidly until demand, capabilities alter source meaning silently, or the claimed proof is only a property of an unbound model. A better analysis schedule within the existing source theory is a valid positive result.

### H1.6: an explicit NFT elaboration fragment

**Put NFT elaboration in the native foundation.** Start with the manuscript's admitted finite immutable data and pure decidable equality, with no hidden consumable resources inside an indexed value. Track ordinary type/measure variables, the creation value or snapshot, and the distinct rigid live-instance identity.

Admit resource-bearing aggregates through explicit use/retention rules as the next extension. Opaque mutable foreign objects require a protocol interpretation. Neither is automatically covered by the initial reciprocal core.

Define rules for let, branches, closures, calls, instantiation and result access in a small source fragment. State how branch-specific resource states reconcile, which indices may escape in a declared package, and how demand affects captured facts. Include only explicitly supported recursion/loop forms. Inferring the index supplied to a constructor and discharging a later equality obligation are different tasks. A dynamic equality check is not a theorem of complete static inference.

Use exact XOR restoration, two equal values with distinct live instances, a deferred one-shot result and an admitted carrier change. Then connect the fragment to H1.5: the same creation value and rule snapshot must survive deferred numeric selection and recovery. Specify the chosen equality for any admitted floating values, including NaN/signed-zero policy where relevant. Exact elimination, numerical tolerance and probabilistic error budgets remain different judgments.

**Deliverable:** an executable reference/checker and derivations for E12 and E23–E26, with explicit unsupported outcomes. E13 initially requires a located refusal until its aggregate/resource admission rule is established. The first positive case tracks the right separately beside the indexed data.

Implement the selected NFT rules through existing Baker facts wherever they suffice, then connect H1.1–H1.3 to the same judgments. An existing-inference-plus-constraints implementation is a valid way to realize this direction if it preserves the contract. A new production owner or intermediate language is not required.

**Advance:** the admitted fragment has the claimed soundness/generalization properties and retains identity, equality, demand and resource evidence through its specified operations. Establish any principality, completeness or termination claim separately. NFT's central role is the recommended direction. This gate determines which operations are ready to ship.

**Defer or narrow:** live identities become ordinary freely generalized type variables; equality or branch/resource effects are unspecified; a lossy encoding passes exact matching; or the proposed core merely renames unresolved obligations. Failure of a broad adapter correspondence does not invalidate a useful finite NFT fragment.

### H1.7: Better inference reducing graph work

**Recommend as a measured hypothesis.** More stable schemes, deferred commitments and precise dependencies could produce fewer changed facts and less invalidation for the same edit. That could improve differential compilation. Richer inference can also cost more, reveal additional necessary dependencies or move work to checking. Neither outcome follows from theory elegance alone.

Compare candidate procedures on their shared admitted corpus, reporting newly admitted programs separately. Start from the same source/configuration binding, apply the same bounded edit sequence and compare each incremental result with full recomputation. Include edits preserving an exported scheme, changes confined to one invocation's range, and changes to a platform, boundary or resource premise that must invalidate evidence. Distinguish source-type stability from layout/protocol stability: an unchanged printed type is not a universal reuse key.

Measure semantic fact changes, recipes revisited, relations touched, evidence invalidated/reused, inference time, checking time, time to a valid diagnostic/settlement and peak retained state.

Ranvier offers a useful operational comparison: dependencies come from reads, equality can stop further value propagation, and pending/error states remain distinct from settled values. Its ownership relationships are separate from its dependency edges. Apply those distinctions to E14/E27–E28 when designing traces that explain why inference work ran or was reused. Ranvier is a reactive runtime, not an inference proof engine. Clef's stopping rule must compare the relevant judgment and its premises, because an unchanged value or printed type can coexist with changed proof dependencies. [Ranvier engineering walkthrough](https://shayanhabibi.github.io/shayanhabibi/ranvier/)

Separate irrelevant renaming or serialization changes from semantic changes using the declared equivalence. That equivalence must preserve live-instance and effectful-call identity. Equal values or arguments do not justify merging occurrences. Record unresolved obligations as well as settled answers so a quiet but less informative graph does not score as an improvement.

**Advance:** equal or stronger admitted results agree with full recomputation, every discriminating dependency mutation is caught, and repeated bound workloads demonstrate lower unnecessary work or improved latency at a stated memory/checking cost.

**Defer or reject the performance claim** if fewer updates arise from omitted dependencies, weaker inference, unstable identity matching or postponed required work, or if total edit-to-result cost does not improve. A sound expressive gain can remain worthwhile even if it is slower. Report the tradeoff instead of calling it faster differential compilation.

### H1.8: carry elicited foreign contracts into native lowering

**Use Farscape's existing owners and evidence as the native-boundary path.** Derive source-facing adapters from declaration, layout and provenance evidence while preserving ABI family/width, nominal handle identity, conversion/access premises and the declared foreign-effect contract. Combine H1.5's deferred coverage with H1.6's instance/equality discipline and H1.7's reuse measurements. This makes FFI part of the selected elaboration strategy rather than a separate inference system.

Use the three cases E29–E31 below. Keep foreign behavioral assumptions explicit. Prove the admitted marshaling/access contract, not an unspecified C algorithm. Distinguish a graph-obligation check, a fresh-versus-reused compilation comparison and an actual native execution oracle. None substitutes for the others.

The corresponding JavaScript signpost is Shayan Habibi's Xantham: its declaration-to-binding work follows TypeScript relationships and makes mapping decisions inspectable. Use an Xantham-shaped declaration case alongside the Farscape cases. Compare the source declaration, the F# binding it can express, and the proposed Clef row or qualified contract. Record where optionality, overloads, identity or a wider generated type changes what the consumer can establish. This connects E01/E10–E11/E15 to the boundary work. Declaration evidence can justify an adapter's static requirements, but it cannot prove that an arbitrary runtime object honors them. Dynamic narrowing, effects and numeric premises keep their own checks. [Xantham engineering walkthrough](https://shayanhabibi.github.io/shayanhabibi/xantham/)

The existing BoundaryConformance driver does not claim all these categories, and current wiki reuse status remains unsettled. [Source and status bindings in chapter 2.]

**Advance:** the same source schemes consume correctly bound foreign evidence, required descriptor/resource changes invalidate their dependents, and each claimed native path has the appropriate artifact and execution evidence. A different inference strategy must improve a demonstrated capability, clarity or measured cost while preserving this boundary.

**Defer or reject:** equal spelling/layout/addresses merge distinct declarations or resources; a post-return check is used to justify an earlier foreign write; source width is defaulted from ABI width; or a compiler-only check is described as executed native behavior. Extend C++/callback/ownership coverage only through explicitly admitted cases.

**Horizon 1 exit:** a checked, bounded native elaboration contract, its executable reference, source-facing row/qualified examples, and one JS numeric plus one native-boundary realization case. The handoff must show the additional Tier 1 statements and checked derivations beside the standard F# and inference-corpus results. Publish exact unsupported cases and the graph-work measurements. A failed feature is narrowed or deferred. It does not leave the entire architecture undecided. Revise the foundation only when a counterexample or demonstrably better contract warrants it.

### The first deliverable increment

Build a thin vertical slice across the work items above: a bounded immutable measured-record function and its explicit qualified scheme, finite NFT restoration/one-shot examples with separately tracked rights, and numeric obligations instantiated under two ranges. Demonstrate an exact JS integer/fixed-point calculation with named rounding and a native `long` boundary with an explicit ABI envelope. Keep the code small enough that each inferred requirement and its invalidation can be inspected.

The handoff must contain the rules, retained Baker/PSG facts, a checker or checkable derivation for the admitted judgments, the corresponding emitted-operation evidence, and E01/E02/E07/E09/E12/E19/E23/E25/E28/E29 controls.

Present E01/E02/E07/E12/E18 side by side across all three comparison arms before making a superiority claim. Show what F# already establishes, what the selected corpus mechanism adds, and which extra Clef relationship now has a checked derivation. Then connect those source judgments to the numeric, NFT-instance and boundary controls. This is the first concrete demonstration of the proposed Tier 1 gain.

If the proposed JSIR route cannot yet emit the case, report the missing implementation owner and finish that narrow path. A reference evaluator is useful earlier evidence but does not satisfy the realization gate. This increment establishes the selected architecture's first coherent slice instead of beginning with a broad compiler rewrite.

## Common shape and mutation matrix

Use stable identifiers so conclusions can be traced to exact examples. The source notation is schematic. Bind executable syntax and expected judgments in the implementation charter.

**Every E01–E33 result requires the three comparison arms defined above.** Pin the F# compiler and any editor/FSharp.Compiler.Service versions used. Identify the inference-corpus implementation and any experimental extension. Retain the Clef scheme, native judgments, checking outcomes and dependencies. Mark a case outside an arm's domain explicitly rather than inventing an equivalent feature or score. Only the small F# examples in H1.1 have been executed in this document increment.

| ID | Shape / positive case | Discriminating failure or alternative |
|---|---|---|
| E01 | Project one immutable field across two measured record shapes | Early nominal selection, lost measure relation, or an unconstrained mutable field |
| E02 | Extend an absent label and explicitly replace an existing field | Reject duplicate extension; preserve the declared update contract and any resource obligation; scoped-label behavior is a comparison only |
| E03 | Return explicit tagged alternatives with different measured payload types | Lose correlation, accept an unsupported payload operation, or silently introduce implicit measured joins |
| E04 | Read a narrow interface; separately write through an alias | Unsound writable covariance or severed alias by an implicit copy |
| E05 | Check an annotated callback at two instantiations | Escaped skolem; separately test generalized shared mutable storage |
| E06 | Share a lazy value containing a completion right | Duplicate a one-shot right or reuse a pre-mutation premise at first demand |
| E07 | Establish a dimension equation and a valid numeric range | Same dimension with missing capacity, error or definedness proof |
| E08 | Exact sum of two values in [0,255], followed by reduction | Use the final [0,255] range to justify an overflowing earlier exact sum |
| E09 | Add two exact half-cent results then round half-even | Round each half first and claim the two schedules equivalent |
| E10 | Persistent map/set operation with comparator-equivalent keys | Change old state, collapse distinct nominal keys, or change traversal policy |
| E11 | Validate a foreign shape, including optional values | Conflate missing/None/undefined/null; ignore getter/proxy effects |
| E12 | Restore an indexed temporary and consume its reciprocal | Omit restoration while retaining the same carrier type |
| E13 | Project a record containing a live completion right | Silently discard the right; compare retained-residual/view accounts |
| E14 | Reuse evidence after a local edit | Add a writer/member use outside the old participant set and retain stale evidence |
| E15 | Infer one source module for CPU, FPGA and JS capabilities | Silently change source meaning instead of faithful realization, explicit profile or capability failure |
| E16 | Translate a virtual/base-view call | Select the wrong implementation or lose receiver/subobject identity |
| E17 | Translate eager construction and exceptional cleanup | Defer required effects under lazy defaults or skip/double destruction |
| E18 | Produce a valid but specialized inferred scheme | Accept a principality label merely because its substitution checks |
| E19 | Reuse one numeric/state scheme at two ranges; cross a power-of-two bound | Export a call-specific range universally, choose insufficient intermediate width, or change source identity with representation |
| E20 | Settle the same source under two Platform bindings, including a quotation | Reuse stale capability evidence, execute arbitrary quotation code, or equate pointer/register width with source numeric range |
| E21 | Preserve a state transition and per-output Mealy/Moore dependencies across targets | Change initial output, input dependence or observable step timing without an established trace correspondence |
| E22 | Recover an exact reduction after partition retries and suspension | Count a contribution twice, lose accepted-state consistency, or serialize a rounded subtotal where exact state is required |
| E23 | Track two equal creation values with distinct live resource instances | Merge instance identities, consume one twice, or treat value equality as permission to duplicate |
| E24 | Elaborate branches and closures carrying declared live obligations | Lose branch-specific consumption, let a live identity escape its scope, or freely generalize it |
| E25 | Preserve indexed matching through an admitted carrier encoding | Preserve range but lose selected equality; collide instance IDs; leave floating equality undefined |
| E26 | Reconstruct from the same immutable input and rule snapshot at demand | Change captured storage/version before demand, retain mismatched metadata, or use approximate reconstruction for exact elimination |
| E27 | Apply edits that preserve a source scheme or affect one contextual use | Rebuild unrelated semantic facts, confuse serialization churn with semantic change, or suppress required range/layout updates |
| E28 | Reuse boundary/resource evidence after an explicitly relevant contract edit | Keep stale ABI, equality, ownership or effect dependencies because the printed source type is unchanged |
| E29 | Marshal the same source `int` to correctly labeled LP64/LLP64 `long` boundaries | Admit `2^40` at an insufficient boundary, silently truncate, or reuse the other profile's coverage evidence |
| E30 | Track two effectful foreign acquisitions with equal arguments | Merge calls or successive address lifetimes; let one release/completion discharge the other |
| E31 | Distinguish same-spelled foreign declarations under different headers/packing/macros | Attach one unit's measured layout to the other; retain stale ABI evidence after an edit; disagree with fresh compilation |
| E32 | Establish deadlock freedom and request completion for an admitted workflow under its execution premises | Omit a cleanup/capacity wait, assume an unmodeled foreign call terminates, or turn unresolved supervision/race freedom into a progress proof |
| E33 | Validate a colored concurrent group and its chosen target realization | Miss an alias/conflict edge, exceed a joint resource bound, change rounding semantics, or infer a speedup from coloring alone |

The mutation column is as important as the successful example. Distinguish an intentional source-language difference from an unsoundness: accepting heterogeneous data is not the same as accepting an invalid arithmetic operation on it.

### Proof-expression improvement

| Cases | Required comparison and evidence |
|---|---|
| E01–E06, E10 | Compare F# record/member/collection contracts with corpus rows and rank-N rules. Show Clef's field/tail, qualified equality, scope and permitted-use derivations. Do not count existing F# generic projection as a missing capability. |
| E07–E09, E15, E19–E22 | Compare dimensional schemes separately from arithmetic, state and target contracts. Include idiomatic F# exact-arithmetic or rounding-controlled encodings where applicable. Clef must retain the links from structural judgments to range, trace and realization evidence. Those additional analyses do not become Tier 1 merely because compilation invokes them. |
| E12–E13, E23–E26 | Compare carrier/API encodings with explicit creation-value and live-instance judgments. Show successful use, rejected duplication and the retained matching premise. E13 remains unsupported until its aggregate rule exists. An arbitrary inverse or lossy reconstruction cannot be licensed by a type spelling. |
| E11, E16–E17, E29–E31 | Compare what source declarations and bindings express with what actual boundary behavior requires. Separate interface derivations from dispatch, evaluation order, marshaling, ownership and native execution evidence. |
| E14, E27–E28 | Compare type-resolution behavior across all three arms. Separately test whether Clef reuses only derivations whose dependencies remain valid. Report the cost of richer checking as well as avoided graph work. |
| E18 | Exhibit a valid specialized answer and the evidence needed for a principal one. A checked typing instance must not be promoted into a theorem about every solution. |
| E32–E33 | Identify structural/use judgments that contribute to workflow or parallel-group admission. Retain the separate progress theorem, conflict completeness, joint resource, arithmetic and target premises. Type acceptance alone establishes neither request completion nor a speedup. |

## Evaluation

Measure accepted/rejected/pending cases and evidence quality before assigning a numerical ranking. For candidates claiming equivalent judgments, compare schemes modulo the appropriate equivalence and retained constraints. Do not require byte-identical proof terms.

For the same bound workload, measure annotation burden, inferred-interface readability, diagnostic locality, edit-to-diagnostic latency, inference versus checking time, evidence size, invalidation scope and realization cost. Record cold/warm conditions, target/configuration identity and failures. Do not hide a broader type system's cost behind a smaller benchmark or count weaker checking as a speed improvement.

Separate four outcomes: a new valid typing; a principal/complete inference result; a new structural theorem; and a measured engineering improvement. They justify different claims and manuscript changes.

Add a proof-expression result to each report: which native statement became expressible, whether its derivation was checked, which assumptions remain, and which mutation invalidates it. A new source capability with a checked structural contract can justify the departure even without a speedup. Faster inference that drops those obligations cannot.

## Horizon 2 integrate the selected fragment

**Integrate the selected contract through the existing source owners.** Carry the H1 NFT, dimensional, row/qualified and deferred numeric judgments into production in bounded increments. Promote each operation when its gate passes. The sequencing is conditional on evidence. The architectural direction is explicit.

1. **Settle the source contract.** State compatibility changes and exported schemes. Clarify nominal identity, equality, mutation, effects and demand. If profiles differ, make their boundary and interface correspondence explicit.
2. **Bind evidence to existing PSG facts.** Preserve recipe ingredients, relation identity, instantiations, completeness dependencies and the intermediate rewrite record. Publication copies these facts. It does not create missing premises.
3. **Establish incremental reuse.** Compare with full recomputation after the E14 and E19–E31 edits and measure H1.7. A stable printed type or a cache hit is not sufficient evidence. Reuse must remain valid for changed generalization, demand, transition, range, selected equality and resource/target premises, including selected platform and foreign declarations. Proof and code dependencies may differ.
4. **Establish each claimed realization.** JS objects, comparator trees, BigInt operations, native layouts and FPGA resources have different obligations. Binding a source type does not prove a library or emitted operation implements it.
5. **Measure the design-time result.** Quantify the gains and costs under the pinned workload rather than predicting them from pure versus mutable implementation style.

The editor-facing result should retain the familiar usefulness of F# tooling while exposing the additional native judgments. For a selected expression, show its scheme, established structural relationships, pending nonstructural obligations and the source of a failure. The editor consumes CCS/Baker's evidence. It does not introduce another inference authority. FSharp.Compiler.Service remains the F# comparison surface rather than being assumed to recognize new Clef judgments.

**Advance:** source proofs, mutations, implementation checks and the affected consumer/target evidence agree. The implementer runs the shape matrix and discriminating mutations before handoff. Substantial acceptance uses unfiltered leased suites with a frozen dependency closure. Accepted baselines from other agents are reused. The reviewer audits binding and anomalies rather than rerunning a baseline solely to re-establish it.

**Stop or narrow:** integration requires semantic repair in Alex, publication or a retired plugin; different producers silently change source meaning; proof reuse omits dependencies; or realization only passes by narrowing the promised contract without declaring that change.

This review does not authorize a gate shortcut. No focused passing result establishes complete F/C acceptance.

Develop reusable laws and their semantic bridges with the planned cvc5/Rocq ecosystem in parallel with production integration. Bind the admitted solver/checker dependencies and the actual artifact, not merely a source theorem or tool exit status. Framework and domain authors provide reusable checked constructions. Supported application cases should obtain those instances through ordinary compilation. [Proof-composition roles and exact source binding](07-explaining-clefs-departure.md)

## Horizon 3 extend proofs & the language remit

**Pursue compiler correctness and self-hosting as explicit workstreams.** Mechanize the admitted source and intermediate semantics, prove nanopass preservation and composition, and bind executable implementations to those proofs. Apply the same artifact and dependency discipline to the compiler as it becomes self-hosted. Record the bootstrap compiler, transformations, checking environment and final executable. Independently checked evidence must break any circular claim that the compiler proves itself merely by compiling itself.

This extends the planned proof ecosystem into an accountable path toward a proved compiler. Program guarantees, artifact correspondence, transformation correctness and bootstrap trust are related obligations that can advance together. The current Composer proof-composition owner explicitly names self-hosting as a long-term goal. Use its current support-completeness and generation-binding rules, not superseded proof-pipeline diagrams. The [positioning document](07-explaining-clefs-departure.md) gives the audience-facing account and source anchors.

**Exploratory recommendation.** Investigate an NFT-informed admitted-adapter calculus and selected Transpose fragments once smaller judgments are understood. This horizon concerns broader correspondence, not whether to investigate NFT's own elaboration: that is already central in H1.6. A small correspondence counterexample can be studied in Horizon 1. A general calculus belongs here.

Specify which observations an adapter preserves; its identity and composition laws; coherence of competing paths; arrow variance; permission to retain, hide or discard components; and the treatment of effects, demand and live indices. Decide whether subtype inclusion, resource completion and reversible decomposition are connected by a proved translation or remain distinct but composable judgments.

An arbitrary map `A -> B` does not establish the intended implicit compatibility. Current value-specific `1/v` is not already a general `B/A` rule. A `Fin 3` embedding into `Fin 5` has an inverse only on its image. This is a useful challenge to any overly broad reversibility claim.

Use Transpose as a demanding corpus: structural object interfaces, virtual dispatch, aliasing, identity/equality, source evaluation order, exceptions and C++ destruction. Begin with one precisely admitted source fragment. A source language's full object system is not one feature. Atelier presents the recipe, evidence and gaps. Language-specific analysis and CCS/Baker supply semantics.

**Advance:** a correspondence or preservation theorem for the named fragment, checked examples and mutation rejection, and a demonstrated simplification or capability gain over the alternatives.

**Defer indefinitely if appropriate:** the adapter theory restates existing relations without reducing obligations, cannot establish coherence/resource discipline, or broad porting needs unsupported behavior. A complementary role for NFT and structural subtyping is a successful finding. Total replacement is not a required outcome.

## Source anchors and ownership

The formal motivation and open proof claims are bound to `arxiv-papers@d2bab3376032929dc7a4eca7e0bc807247a88c03`: DTS+DMM, lines 84–109, 131–143 and 351–382; PHG, lines 84–120, 324–339 and 453–463; DBC, lines 197–216 and 440–450; NFT, lines 139–208, 218–236, 313–368, 412 and 437–461. The normative evidence contract is `clef-lang-spec@a69ac8a91b49f97bd5a5e7bea2934246c2d54edd`, `spec/conformance.md:67–90` and `spec/terms-and-definitions.md:98`. Chapters 2 and 6 bind the site, Platform, Farscape and Bozzetto sources and the retrieval record.

The mechanism comparisons reuse `write-you-an-inference-in-fsharp@4a6f852f36115ad45ac9640753a0bd38f551300c`: `README.md:8–19`, `HMSplitSolve/HMSplitSolve.fs:232–257`, `HMPure-Rowpolymorphism/HMPureRowpolymorphism.fs:145–223`, `HMPure-Rowpolymorphism/Program.fs:55–77`, `HMMutable-RowPolymorphism/HMMutableRowpolymorphism.fs:208–235,311–348` and `Hindley-Milner-RankN.md:72–119`. These are mechanism anchors, not a claim that the prototypes have passed the native experiment matrix.

The production comparison uses the official F# accounts of [type inference](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/type-inference), [automatic generalization](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/generics/automatic-generalization), [records](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/records), [statically resolved type parameters](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/generics/statically-resolved-type-parameters), [units of measure](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/units-of-measure) and [FSharp.Compiler.Service's resolved symbols and signatures](https://fsharp.github.io/fsharp-compiler-docs/fcs/symbols.html), consulted November 1, 2026. The Xantham, Partas.Solid and Ranvier connections use the author's engineering walkthroughs cited at the relevant work items. They identify useful comparison cases and preservation questions. They are not new audits of those implementations or evidence of a Clef integration.

**Document owner and growth reason:** this inquiry owns the horizon decisions and experimental agenda. The chapter supplies the requested advance/defer/stop criteria and creates no new compiler owner.

# The strategy: native elaboration, staged delivery and decision gates

This chapter owns the recommended engineering direction. Build a native constraint-preserving elaborator, with dimensional and NFT obligations integral to its judgments, and retain ML-style inference where its generalization rules remain valid.

Horizons describe increasing evidence and engineering commitment without assigning calendar dates. The gates below qualify the chosen direction. The full comparison matrix and Clef implementation experiments remain unexecuted. H1.1 includes separately identified checks of its small F# examples.

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

Implement the evidence/scheme contract, NFT/deferred rules and bounded service-inference foundation together (H1.4–H1.6 and H1.9). Then extend measured structural interfaces (H1.1), the small annotated higher-rank interface (H1.3), and the shared JS/native-boundary examples (H1.8 and chapter 2). Establish the subtyping boundary in H1.2. Differential compilation is part of the architecture from the start. H1.7 measures whether these inference changes improve it. These identifiers name work items, not calendar phases.

## What the proposed approach must deliver

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

Fai is another relevant comparison: its published language account already includes open structural records and inferred effect rows. Compare those established features with the proposed measured row, lazy demand and live-resource requirements rather than presenting structural records as a Clef invention. [Fai at the inspected revision](https://github.com/Krzysztof-Cieslak/fai/blob/3e03dd1ce3222dab895a71f4556af5fbff1109a1/README.md)

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

This family of source judgments builds on the existing Baker ingredients, recipes and retained relations. Identify a missing fact before proposing a new representation or owner.

Use a scheme of the conceptual form `forall flexible variables. requirements => source type`. Quantified variables can include admitted type, row and measure variables. A live resource instance is not another freely quantified variable: retain its scope and use state separately, along with the creation-value relation. Context-specific ranges and platform/foreign facts keep their own dependency identities. This interface preserves the distinct obligations that host type equality alone cannot express.

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

#### Following a universal relationship into parallel lowering

The following F#-style examples are design sketches. Names such as `parallelMap`, `Cl3`, `e1` and `e2` make the relationships readable. They do not declare a settled parser form or claim that these APIs are implemented. The written `float` types are illustrative quantity carriers, not a requirement to use CLR types or binary64 on every target. In particular, an interior label or an inferred relationship can carry a judgment without introducing a new surface-language `forall`.

```fsharp
// 'u is a measure variable. This is a source type relationship.
let identityMeasured (x: float<'u>) : float<'u> =
    x

// The same relationship is instantiated separately at each call.
let distance: float<m> = identityMeasured 3.0<m>
let duration: float<s> = identityMeasured 2.0<s>
```

The generic relationship says that the result has the measure of its argument. It does not request parallel execution. Now consider a separate operation whose admitted contract permits independent element evaluation:

```fsharp
// parallelMap stands for an admitted parallel operation, not a finalized API.
let calibrate (gain: float) (samples: float<volt>[]) =
    samples |> parallelMap (fun sample -> gain * sample)
```

The relevant index relationship can be inferred and retained inside CCS/Baker:

```fsharp
// Interior evidence, shown as source-like notation for discussion:
// forall valid i: result[i] = gain * samples[i]
// forall distinct valid i, j: writes for i and j are disjoint
// captured gain and samples satisfy the admitted access and demand contract
```

CCS/Baker must establish the index bounds, complete participant set, alias/access and effect conditions, and the permitted observation and demand behavior. The algebraic type of `gain` does not establish those properties. A pure-looking callback is not enough if it captures shared state or live resources. Likewise, reordering work must not silently change exceptions, required first-demand effects or a specified arithmetic reduction.

Once the source operation and premises are settled, the PSG retains them. Alex witnesses the settled structure passively. Composer may use `scf.forall` on an appropriate pathway, or another faithful realization on a different target. That decision needs a correspondence to the actual source operation and artifact. Parallel eligibility does not promise simultaneous execution on every device. It also does not turn the type-level measure variable into an execution index.

This control must fail the independence check unless a separately admitted synchronization or reduction contract accounts for the shared update:

```fsharp
let mutable total = 0.0

samples |> parallelMap (fun sample ->
    total <- total + sample
    sample)
```

For a numerical reduction, race freedom is only the first condition. A different floating-point association can change the answer. Use a declared fixed tree, a supported exact accumulation with adequate capacity and named rounding, or another construction whose error contract admits the change. Merely choosing `scf.forall` proves none of those properties.

#### Geometric algebra and Cayley elimination

The useful result for geometric algebra is **retained structure that selects the computations the declared algebra actually permits**. It is not a claim that row polymorphism or higher-rank callbacks alone discover a geometric theorem.

In a declared three-dimensional Euclidean algebra, suppose `e1` and `e2` name basis vectors:

```fsharp
// Illustrative algebra values; basis-declaration syntax is not decided here.
let v = e1 + e2
let product = e1 * v

// Algebraic result: 1 + e12.
// Inferred possible output support: { scalar; e12 }.
```

The signature and basis determine the blade products. The support analysis knows that the input on the right may contain `e1` and `e2`; the two candidate pairs reach the scalar and `e12` components. Baker can settle those contributions and their signs instead of constructing a dense full-multivector product. This is the sense of **Cayley elimination** used here: eliminate structurally impossible product paths, not the algebra's required sign rules or every coefficient that happens to cancel for one input.

For a separate declared degenerate algebra, a null basis vector gives another structural case:

```fsharp
// e0 belongs to an algebra whose declaration says e0 * e0 = 0.
let nullSquare = e0 * e0
```

The declared zero rule can exclude that contribution in the admitted algebra and numeric interpretation. Support is an upper bound on possible nonzero components. A component admitted by the support can still evaluate to zero. Conversely, an excluded component must be absent for all admitted inputs and operations.

The established disciplines are distinct: algebra identity and signature select the product rules; parity is exact for the admitted parity-homogeneous fragment; blade support is a lattice-valued over-approximation; measures, ranges and numeric representations have their own rules. Support constraints may use a separate bitvector procedure. They must not be relabeled Tier 1 simply because inference generated them. Baker settles the sparse product, coefficient signs, layout and joint numeric premises. Publication copies the settled graph, Alex witnesses it, and Composer realizes it on the chosen target. A later stage must not reconstruct missing source semantics.

This gives the new inference strategy a precise job: preserve the algebra identity, supported structural relationships and qualified requirements across generic functions, measured rows and module boundaries. Bind each resulting obligation to its actual context. It may avoid premature specialization or make a previously inexpressible reusable interface possible. **It does not create the blade-support rules or prove their soundness merely by adopting a new HM-family algorithm.**

There is a specific design boundary to test. The current grade specification keeps blade support as a PSG coeffect outside ordinary type generalization and joins the masks at call sites. It does not already provide a freely quantified support variable in a generic type scheme. Retaining that baseline is a valid implementation. Per-call specialization or a qualified support-polymorphic scheme would need a separately specified fragment, bounded compilation policy, soundness and realization evidence. Compare both approaches on the same operations and show exactly what additional relationship survives generalization.

#### A concrete AI training contract

For an ADM parameter restricted to the three bivector coordinates of a 3D Euclidean algebra, the paper's example has three stored coordinates rather than eight full-multivector positions. Two such unrestricted bivector supports present nine candidate coefficient pairs, compared with 64 for a dense eight-by-eight expansion. These are structural counts, not measured speedups. A compiler or hand-written kernel that already exploits the same support can obtain the same exclusions.

```fsharp
// Schematic types: the parameter and tangent share the admitted support.
let trainStep (learningRate: Scalar) (weight: Bivector<Cl3>)
              (gradient: Bivector<Cl3>) =
    weight - learningRate * gradient
```

When the tangent directions and their defined scalar combination remain in the admitted support, and the update is dimensionally compatible, the updated parameter stays in that support. This is a bounded structural invariant. It is not a claim that every ambient gradient has that support, that training converges, or that the trained model is accurate or safe.

Dimensions supply a different check. For a dimensionless loss and a parameter measured in meters, a gradient has reciprocal-meter dimension. One possible compatible learning-rate dimension is meters squared:

```fsharp
// Illustrative source contract for a dimensionless loss.
let update (rate: float<m^2>) (weight: float<m>)
           (gradient: float<1/m>) : float<m> =
    weight - rate * gradient
```

The inferred product has dimension `m`, so the subtraction is dimensionally meaningful. A rate measured only in `m` would yield a dimensionless update and must not be subtracted from a meter-valued weight. The check says nothing by itself about gradient-estimator variance, value range, rounding error or preservation of a nonlinear rotor constraint.

Forward-mode training adds a concrete resource tradeoff: each tangent can carry the parameter's support, but simultaneous directions need additional live state, while sequential directions need additional work. A quire can accumulate *represented* products exactly within its admitted capacity and round at the declared boundary. Input conversion, nonlinear operations, sampling uncertainty, distributed contribution identity and later updates keep separate obligations. The chosen target needs a valid hardware or software construction; the name of an arithmetic format does not provide one.

**Decision and experiment:** include this as a cross-domain discriminator in E07/E19/E23–E26/E32–E33. Compare the existing inference baseline with the proposed scheme on the same bivector update and parallel element operation. Record retained algebra and support, the dimensional gradient/update derivation, permitted resource uses, selected numeric premises, generated coefficient-pair count, and the target-specific realization. Mutate one support, basis, measure, alias or rounding premise at a time. An unsupported case must remain visible. Report compilation and runtime costs alongside any smaller construction.

**Evidence and status:** `clef-lang-spec@a69ac8a91b49f97bd5a5e7bea2934246c2d54edd`, `spec/grade-discipline.md:17–35,84–100,140–190,218–242`, specifies parity, support, sparse product and target obligations. `arxiv-papers@d2bab3376032929dc7a4eca7e0bc807247a88c03`, `adaptive-domain-models.md:76–104,477–491`, supplies the training example and bounded support result. `clef-lang-site@15d381634f7a08c2a44884a0598d0e634083b313`, `hugo/content/docs/design/constrained-machine-learning/architecture-and-arithmetic.md:14–76`, distinguishes a justified parameter restriction from the representation a model actually learns. These are design and manuscript statements. The examples above are an implementation agenda, not a claim that the full cross-target path has been executed or proved.

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

**Build on differential compilation as a foundational architecture.** The program hypergraph keeps each multi-participant relationship, its roles and supporting evidence together across revisions. A changed type, source participant, protocol, boundary or target premise can therefore identify the judgments and realized fragments that depend on it. Stable identity, complete dependencies and correct retraction are necessary to make that capability sound. A hypergraph alone does not prove that the recorded dependency set is complete.

That foundation already has concrete implementation pieces. Baker's `Ingredients/Obligations.fs:1–37` describes the obligation-node and constraining-hyperedge contract and combines recipe enrichments. `Fidelity.PSG/src/Fidelity.PSG/Revision.fs:1–65` defines revision-carried projections, including explicit demand relations whose frontier can remain pending. These are inspectable mechanisms at the revisions bound in H1.9. They do not by themselves establish complete differential invalidation or a passing end-to-end reuse gate.

The distinction from a query-centered compiler needs precise wording. Fai's own account describes a **demand-driven** Salsa query engine with definition-level incremental work and a warm workspace database. Rust likewise describes a demand-driven query DAG with memoized results. Both are incremental systems, so calling either one simply a push compiler would misstate their documented evaluation model. Clef's chosen unit is a revisioned *semantic relationship*: the graph retains a multi-party judgment and the evidence and realization facts bound to its participants. An edit revises those relationships and revalidates the affected closure. The precise eager, deferred or mixed scheduling of individual updates is a separate implementation question. It must be established from the actual producer and revision contracts, not inferred from the word “differential.”

Compare the same edit across the systems where a faithful case exists. Record query evaluations or graph relations revisited, retained and rechecked evidence, unchanged versus changed semantic results, and time to a valid result. A query system can track dependencies and stop propagation when results are unchanged. The proposed Clef advantage must be demonstrated in the identity, composition and reuse of the relevant multi-participant semantic and proof facts, not claimed merely because one approach is incremental. [Fai at inspected revision](https://github.com/Krzysztof-Cieslak/fai/blob/3e03dd1ce3222dab895a71f4556af5fbff1109a1/README.md), [Rust query evaluation](https://rustc-dev-guide.rust-lang.org/queries/query-evaluation-model-in-detail.html), [Salsa red-green algorithm](https://github.com/salsa-rs/salsa/blob/master/book/src/reference/algorithm.md)

MLKit's region inference and the Scheme Nanopass framework are useful precedents for distinct parts of the design. Clef's specific direction puts small source-owned recipes and native judgments on a revisioned hypergraph, then uses complete dependencies to revalidate affected evidence and realization. [MLKit](https://github.com/melsman/mlkit), [Nanopass framework](https://github.com/nanopass/nanopass-framework-scheme)

**Measure the additional inference hypothesis.** More stable schemes, deferred commitments and precise dependencies could produce fewer changed facts and less invalidation for the same edit. That could improve an already selected differential approach. Richer inference can also cost more, reveal additional necessary dependencies or move work to checking. Neither outcome follows from theory elegance alone.

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

### H1.9: infer the service and weave its data and control flow

**Select a bounded coexponential service-inference path as part of the native foundation.** A concurrent language needs more than the types of a request and reply. It needs to relate the client pool, the service's state, each invocation, the control waiting for its result, the resources retained while it waits, and the valid way to complete it. These relationships belong in the same CCS/Baker evidence contract as dimensions, NFT and demand.

This continues work already present in the compiler. `NativeTypedTree/UnionFind.fs` uses mutable type-variable links with path compression, giving a concrete point of comparison with the mutable HM examples in `write-you-an-inference-in-fsharp`. `Unify.fs` has native type and measure-specific failure cases. These mechanisms are evidence of an implementation direction, not evidence that Clef already implements the corpus's row or higher-rank systems.

The existing Baker owner goes further than ordinary type unification. `Ingredients/BindingDemand.fs` analyzes a bounded first-demand case for mutable-cell snapshots. `Recipes/BindingDemandRecipes.fs` retains participating identities and rewrites the corresponding source schedule. `Ingredients/Continuations.fs` constructs frame reads, writes and dispatch using settled identities, and `Recipes/ContinuationObligationRecipes.fs` states frame-layout and reservation obligations with their participants. These are concrete ingredients and recipes for Clef's native semantics. They are not a completed coexponential reconstruction or a proof of every runtime behavior.

Farscape gives a corresponding boundary example. Its `TypeMapper.fs` records ABI family, width, provenance stratum and C spelling separately, with profile-dependent widths such as LP64 versus LLP64 `long`. Baker's `Ingredients/Boundaries.fs` captures platform and source premises, including native type identities and operation forms. Extend those existing owners so the same declaration, invocation, frame and proof dependencies remain connected across the marshaled boundary. The inspected implementation is a concrete foundation; it is not a completed proof of an arbitrary foreign body or of all incremental reuse. [Boundary analysis](02-js-numerics-and-interop.md)

| Existing foundation | Connection to the inference work | What remains to establish |
|---|---|---|
| Mutable union-find and native unification | A real CCS implementation of mutable substitutions to compare with the corpus's mutable HM variants | Lawful native generalization and the selected row, qualified and higher-rank fragments |
| Binding-demand ingredient and recipe | A bounded way to retain first-demand participants and settle a source schedule, relevant to inference under laziness | General demand/effect/resource composition and revision-bound rechecking beyond that specific case |
| Continuation ingredients and obligation recipes | Existing source-identity, frame and multi-participant obligation machinery for the data/control relationship | Service reconstruction, protocol witnesses, completion and runtime correspondence |
| Farscape descriptors and Baker boundary premises | Declared and measured foreign facts enter native settlement with explicit platform and source identities | Coverage, marshaling, foreign hypotheses and complete invalidation through each admitted target path |
| PSG hyperedges and revisions | Joint source judgments and evidence have an existing representation to revisit when participants change | Dependency-complete differential reuse and measured edit-to-result behavior |

Xantham's TypeScript declaration and binding work is a complementary comparison on the JavaScript side. Farscape and Xantham address different source ecosystems. Compare the declaration identities, structural contracts and evidence each path can expose; do not assume a shared implementation or that either declaration alone proves runtime behavior.

#### One interaction, two flows, one retained relationship

The following F#-style block is an explanatory sketch. The computation expression and operation names are not a claim about finalized surface syntax. Interior labels and judgments may carry the relationships without appearing in application code.

```fsharp
let handle state request =
    service {
        // When this operation is reached, its admitted contract submits both.
        let! jobs = submitBoth workerA request.Left workerB request.Right
        let! left = await jobs.Left
        let! right = await jobs.Right
        let reply = combine left right
        return reply, updateState state reply
    }
```

The service invocation is deferred under Clef's lazy-by-default rules until its admitted execution boundary. Creating a binding does not itself prove that either request has started. Once the stated `submitBoth` operation is reached, its contract accounts for both submissions and their distinct identities. The two replies may arrive in either admitted order. The join waits for both before the dependent combination.

The **data flow** carries the request values, state, replies and combined result. The **control flow** carries the suspended invocation, its return point and its remaining computation. Weaving the braid in the PSG means preserving their actual interleaving: each submitted operation, matching reply, captured value, owned resource and wait dependency remains attached to the right invocation. In the paper's initial nonreentrant actor fragment, a suspended handler retains exclusive state ownership. Other actors may run, while another handler of that same actor waits. A reentrant service requires a separately admitted state-sharing contract.

One research direction investigates an interaction-net realization alongside delimited-continuation control: local reductions can expose independent work while continuations represent dependent resumption. The compiler must connect both to the same source interactions and observations. A net implementation that selects one permitted service order has not thereby proved equivalence with every allowed order. Its source-to-net and net-to-target correspondences, including effects and resource use, require their own results. E46 makes that proposed weave a concrete experiment.

For each suspension, retain a frame corresponding to `<invocation, return point, live environment, owned resources>`. Bind the completion authority and its actor generation to the matching request. A duplicate reply or a late reply from an earlier generation must not resume another frame. Sharing a deferred result does not manufacture another completion right. These are proposed extraction and checking obligations tied to the paper's finite construction, not a claim that every production service already has a checked witness.

#### Select a bounded reconstruction and explicit fallback

Start with a fixed finite set of message tags and payload/reply shapes, tracked reply authority, admitted state representation, and a finite control abstraction or explicitly supported recursive combinator. Infer a finite message/ownership/wait summary. Check a supplied finite service derivation in the named protocol fragment. Develop source-to-protocol reconstruction as a separate procedure with its own termination and soundness result.

The result must distinguish:

1. **A complete checked witness for the named fragment**, including the premises required to apply its theorem.
2. **Checked local facts with residual obligations**, when an explicitly defined composition rule says what follows despite the unknown boundary.
3. **No service witness from this analysis**, with a diagnostic and any independently established facts retained.

If no sound partial-composition rule exists, retain the independently checked facts and withhold the whole-interface claim. A timeout or supervised operation is a useful protocol outcome under its contract, but it is not by itself a static deadlock-freedom or completion proof. An unknown callback may transfer a resource or introduce a wait; its boundary contract must account for those possibilities.

This is a portfolio of procedures under one native semantics: ordinary type and qualified-scheme inference, finite graph summarization, checking of an explicit service derivation, and a possible reconstruction algorithm. A finite-domain worklist can terminate under stated conditions without proving that protocol reconstruction is complete or principal. A checked source derivation does not by itself establish target progress.

#### Scheduling needs the replies as well as the state

```fsharp
// Conceptual handler: return the old count, then increment it.
let next count = count, count + 1
```

Starting at zero, serving A then B gives final state 2 and replies A=0, B=1. Serving B then A also gives final state 2, but replies A=1, B=0. The updates commute, yet the client-visible results differ. Do not reorder the calls under a claim of equivalent observations unless the state **and each request-labelled reply** are preserved. If reply timing, external effects or sampled values are observable, include their declared relations too. E39 makes this a required negative control.

#### From the finite service to target execution

The H1 result is a checked finite source fragment with an executable reference and explicit unsupported cases. The first realization gate is one small service path that preserves its state, frame, request and reply identities on one named target. H2 carries the same evidence through actual boundary and runtime bindings and compares revised compilation with full recomputation. H3 investigates recursive protocols, reusable mechanized correspondence and other processor classes under their own fairness and resource assumptions.

The coexponential paper's finite service construction and conditional state/reply preservation are the starting evidence. Its finite-batch completion result needs complete blocking dependencies, total correctness of whole continuations, request-selection and scheduling fairness, and required external terminal outcomes. A persistent service need not terminate. Padovani's fair-termination result concerns a specified valid infinitary calculus; runtime scheduler fairness is not automatically the same condition. A source-to-runtime correspondence must establish the transfer. Nor does the metaphor of a braid by itself establish mathematical braid laws or a combined adjoint/coexponential metatheory.

**Advance:** H1's checked witness and controls distinguish complete, partial and unsupported cases, retain first-demand and resource premises, and support one artifact-bound realization without missing wait or identity dependencies.

**Narrow or defer:** reconstruction would require unchecked endpoint provenance, silently generalized live rights, incomplete wait coverage or an unsupported recursion rule. Preserve the sound finite core and its independent local facts. Do not turn unknown behavior into a proof, and do not require arbitrary actor-program inference before shipping a useful admitted fragment.

**Evidence:** `arxiv-papers@d2bab3376032929dc7a4eca7e0bc807247a88c03`, `coexponential-exploration.md:116–161,196–248,260–355,665–682,729–780,856–879`; `research/coexponential-inference/04-inference-ladder-design.md:7–75`, `05-decidability-map.md:7–72`, `06-validation-plan.md:13–69`, `09-adjoint-logic-and-the-fork.md:23–88`, and `10-strategy-net-substrate-cgra-qkb.md:15–55`. Implementation binding: `clef@e3fbdc71a8d86ad5097f2db767f325d0fafc8b8a`, `src/Compiler/NativeTypedTree/UnionFind.fs:1–48`, `Unify.fs:1–47`, `src/Compiler/Baker/Ingredients/BindingDemand.fs:1–27`, `Recipes/BindingDemandRecipes.fs:1–42`, `Ingredients/Continuations.fs:1–8,55–75`, `Recipes/ContinuationObligationRecipes.fs:1–38`, `Ingredients/Boundaries.fs:1–35,45–85`, and `Ingredients/Obligations.fs:1–37`. Revision binding: `Fidelity.PSG@2a0025ad2176df86acc829121dbfa10fad071548`, `src/Fidelity.PSG/Revision.fs:1–65`. Farscape binding: `Farscape@053206a98240190b43231f901f3e7f3747c4ec16`, `src/Farscape.Core/TypeMapper.fs:21–75,181–194`. These are inspected source mechanisms, not execution or acceptance receipts.

### H1.10: test the foundation against AI and quantum computation

**Use AI and quantum cases to shape the native contract now.** These are not promises that every solver, model or quantum target is already implemented. They are discriminators for the same issues that arise in ordinary concurrent programs: which values are related, which resources are live, what a computation observes, and what must survive specialization and lowering.

The ripple effect is concrete. A single distributed update can relate a particular model revision, sampled execution, two worker requests, their replies, an accumulator and the continuation that consumes the result. The hypergraph can retain those participants together while distinct procedures check types, sample correspondence, ownership, numeric accuracy and progress. If a model or sampling premise changes, differential compilation must revalidate its affected evidence without discarding unrelated established work. That benefit depends on complete dependencies and an actual realization; a shared graph does not collapse the separate proofs into one.

#### AI: preserve the relationship between observations

The bivector and dimensioned-update cases in H1.5 test structural support, arithmetic and target selection. The coexponential paper adds a different failure: two correctly typed worker replies can be combined into the wrong learned metric if they no longer describe the same sampled execution.

```fsharp
// Schematic: r0 and r1 are independent standard-normal observations
// from the same admitted execution.
let offsetScore r0 r1 = r0 + r1
let gainScore r1 = r1

let crossTerm r0 r1 =
    offsetScore r0 r1 * gainScore r1
```

The expectation of `crossTerm` is 1. If the second worker silently substitutes an independently resampled `r1`, the corresponding expectation is 0. Individual values can have the right carrier types and marginal distributions in both cases. The missing fact is the **joint sample identity or an explicitly justified coupling**.

For the distributed case, infer or retain the model and loss versions, parameter point, selected directions, observation, sampling plan, task identities and permitted reduction. A join accepts each assigned contribution once. Its numerical and probability bounds remain separate from that protocol fact. The inference strategy should make those dependencies reusable across service and numerical boundaries. It does not itself establish estimator variance, convergence, model quality or a correct arbitrary training algorithm.

Forward-mode differentiation supplies a second discriminator. A tangent can retain its parameter's dimensional and blade-support contract. Sequential directions can reuse storage, while simultaneous directions require their combined live state. Compare the work, storage, representation and accuracy obligations for the actual workload. No automatic claim follows that forward mode always uses less total memory or work than reverse mode.

#### Quantum: distinguish a circuit description from a live resource

```fsharp
// Schematic operations, not a claim of a current quantum backend.
let circuit = buildCircuit gates
let anotherDescription = circuit

// Executing the description uses separately admitted live resources.
let! outcome = runCircuit circuit qubits
```

A closed immutable classical circuit description can be shared as data. That does not duplicate the authority to use an unknown live quantum state as two independent resources. The source and interpretation must retain the identity and permitted use of each execution resource. Preparing two fresh resources from a shared recipe is a different operation from copying an unknown quantum state.

A typed matrix or a negative/fractional type annotation also does not make an arbitrary operation unitary. A checked gate interface needs the appropriate adjoint and inverse equations in its declared ideal interpretation. The real matrix below is a simple negative control:

```fsharp
// Schematic: a square shape is not sufficient for a unitary gate.
let shear = matrix [[1.0; 1.0]; [0.0; 1.0]]
let gate = requireUnitary shear  // the required equations do not hold
```

Coherent uncomputation and measurement followed by reset can both complete an auxiliary-resource protocol, but they do not have the same observable effect on the data. Preserve the operation, outcome, state and probability contract. NFT contributes directed and resource-use structure only through an explicit quantum interpretation. It does not supply an arbitrary inverse, a cloning operation or an automatic proof of physical fidelity.

**Decision and gates:** use E47–E49 for constrained learning and E50–E52 for quantum descriptions and resources. Start with small, finite reference interpretations and check the retained judgments and counterexamples. A simulator and a physical device have different representation, error and execution obligations. A generic pure-state simulator can require `2^n` complex amplitudes. No target or asymptotic improvement follows from the shared source description alone.

**Evidence:** `arxiv-papers@d2bab3376032929dc7a4eca7e0bc807247a88c03`, `adaptive-domain-models.md:76–104,477–491`; `coexponential-exploration.md:578–660`; `negative-fractional-types-in-fidelity.md:535–624`; and `research/quantum/circuit-as-typed-value-substrate-neutrality.md:1–25,70–94`. The manuscript is the primary account where the older research note makes broader claims about automatic unitarity. Unitarity and each source-to-target quantum interpretation remain explicit obligations.

**Horizon 1 exit:** a checked, bounded native elaboration contract, its executable reference, source-facing row/qualified examples, a finite service witness and one admitted service realization, and one JS numeric plus one native-boundary realization case. The handoff must show the additional Tier 1 statements and checked derivations beside the standard F# and inference-corpus results. AI and quantum cases identify the evidence to retain and the first bounded experiments. Publish exact unsupported cases and the graph-work measurements. A failed feature is narrowed or deferred. It does not leave the entire architecture undecided. Revise the foundation only when a counterexample or demonstrably better contract warrants it.

### The first deliverable increment

Build a thin vertical slice across the work items above: a bounded immutable measured-record function and its explicit qualified scheme, finite NFT restoration/one-shot examples with separately tracked rights, and numeric obligations instantiated under two ranges. Demonstrate an exact JS integer/fixed-point calculation with named rounding and a native `long` boundary with an explicit ABI envelope. Keep the code small enough that each inferred requirement and its invalidation can be inspected.

The handoff must contain the rules, retained Baker/PSG facts, a checker or checkable derivation for the admitted judgments, the corresponding emitted-operation evidence, and E01/E02/E07/E09/E12/E19/E23/E25/E28/E29 controls.

Present E01/E02/E07/E12/E18 side by side across all three comparison arms before making a superiority claim. Show what F# already establishes, what the selected corpus mechanism adds, and which extra Clef relationship now has a checked derivation. Then connect those source judgments to the numeric, NFT-instance and boundary controls. This is the first concrete demonstration of the proposed Tier 1 gain.

If the proposed JSIR route cannot yet emit the case, report the missing implementation owner and finish that narrow path. A reference evaluator is useful earlier evidence but does not satisfy the realization gate. This increment establishes the selected architecture's first working slice.

## Common shape and mutation matrix

Use stable identifiers so conclusions can be traced to exact examples. The source notation is schematic. Bind executable syntax and expected judgments in the implementation charter.

**Every E01–E52 result requires the three comparison arms defined above.** Pin the F# compiler and any editor/FSharp.Compiler.Service versions used. Identify the inference-corpus implementation and any experimental extension. Retain the Clef scheme, native judgments, checking outcomes and dependencies. Mark a case outside an arm's domain explicitly rather than inventing an equivalent feature or score. The bounded F# documentation fixtures in H1.1 and H1.3 were executed separately. The full comparison matrix and Clef implementation cases remain unexecuted.

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
| E34 | Derive and check a finite service interface with two message alternatives and one owned state | Omit a message branch, confuse client and server choices, or claim a principal protocol from one checked derivation |
| E35 | Retain sound local ownership and wait facts when a callback contract is unresolved | Export a complete service guarantee without a sound residual-composition rule, or erase an independently checked fact |
| E36 | Track fresh reply endpoints and two client invocations with equal payloads | Merge distinct endpoints or require a globally known runtime identity to recognize fresh local authority |
| E37 | Capture a shared deferred input and actor state across suspension | Force an effect before its admitted demand, reuse a stale mutable observation, or duplicate a live resource through sharing |
| E38 | Complete one invocation once under reply/timeout competition | Resume twice, accept a late reply from an earlier generation, or assume local timeout undoes remote effects |
| E39 | Compare two service orders with state and request-labelled replies | Declare old-value counter increments equivalent because both orders end at state 2 while their labelled replies differ |
| E40 | Build a complete may-wait abstraction including state, capacity and cleanup | Omit a callback or same-actor dependency and accept an unrepresented circular wait |
| E41 | Complete an admitted finite request batch while the service remains available | Infer completion from fairness alone, from terminating local segments, or from termination of the persistent server |
| E42 | Carry a request and reply across a measured foreign or wire boundary | Conflate payload type with endpoint identity, ignore conversion/access premises, or claim a proof of arbitrary foreign behavior |
| E43 | Recompile a service while an earlier revision has a suspended frame | Rebind its return point, owned storage or completion to the new revision without an admitted migration |
| E44 | Realize the same finite service contract on two named target pathways | Preserve final values while changing permitted observations, frame ownership, progress assumptions or the target-bound evidence |
| E45 | Check a named recursive protocol and its validity witness | Treat finite testing, an unproved reconstruction algorithm or scheduler fairness as the infinitary theorem's validity and fairness premises |
| E46 | Relate an admitted service to a continuation/interaction-net realization | Lose a request, state capability or labelled reply, or present one selected schedule as equivalence with all permitted source behavior |
| E47 | Preserve a declared bivector support through a restricted training update | Admit an out-of-support update, or count nine candidate products as an already measured speedup |
| E48 | Infer a dimensionally valid gradient and learning-rate update | Accept an update with incompatible dimensions, or treat units as a proof of numeric accuracy |
| E49 | Assemble a distributed metric from related observations of the same execution | Independently resample one cross-term operand, merge invocation identities or mistake exactly-once receipt for a statistical guarantee |
| E50 | Share a classical circuit description and execute it with distinct admitted resources | Treat sharing the description as cloning or duplicating authority over an unknown live quantum state |
| E51 | Compose a gate carrying checked adjoint and inverse premises | Accept an arbitrary square matrix as unitary because its shape or NFT spelling type-checks |
| E52 | Compare coherent uncomputation with measurement followed by reset | Equate their observable state or outcome laws, or omit physical preparation and measurement assumptions |

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
| E34–E46 | Compare F# actor/interface encodings and the inference corpus's actual scope with Clef's service judgment. Show the finite witness, request/endpoint and continuation identities, demand and wait dependencies, residuals, and the observations preserved by each admitted realization. Separate protocol checking, reconstruction, completion and target correspondence. |
| E47–E49 | Compare the expressed support, dimension, observation and reduction contracts with available F# and corpus cases. Check sample coupling and numeric premises separately from service completion and model quality. |
| E50–E52 | Compare classical circuit descriptions and live-resource contracts. Require explicit gate, measurement and source-to-target interpretations; unsupported prototype cases are recorded as such. |

## Evaluation

Measure accepted/rejected/pending cases and evidence quality before assigning a numerical ranking. For candidates claiming equivalent judgments, compare schemes modulo the appropriate equivalence and retained constraints. Do not require byte-identical proof terms.

For the same bound workload, measure annotation burden, inferred-interface readability, diagnostic locality, edit-to-diagnostic latency, inference versus checking time, evidence size, invalidation scope and realization cost. Record cold/warm conditions, target/configuration identity and failures. Do not hide a broader type system's cost behind a smaller benchmark or count weaker checking as a speed improvement.

Separate four outcomes: a new valid typing; a principal/complete inference result; a new structural theorem; and a measured engineering improvement. They justify different claims and manuscript changes.

Add a proof-expression result to each report: which native statement became expressible, whether its derivation was checked, which assumptions remain, and which mutation invalidates it. A new source capability with a checked structural contract can justify the added inference machinery even without a speedup. Faster inference that drops those obligations cannot.

## Horizon 2 integrate the selected fragment

**Integrate the selected contract through the existing source owners.** Carry the H1 NFT, dimensional, row/qualified, service and deferred numeric judgments into production in bounded increments. Promote each operation when its gate passes. The sequencing is conditional on evidence. The architectural direction is explicit.

1. **Settle the source contract.** State compatibility changes and exported schemes. Clarify nominal identity, equality, mutation, effects and demand. If profiles differ, make their boundary and interface correspondence explicit.
2. **Bind evidence to existing PSG facts.** Preserve recipe ingredients, relation identity, instantiations, completeness dependencies and the intermediate rewrite record. Publication copies these facts. It does not create missing premises.
3. **Establish incremental reuse.** Compare with full recomputation after the E14, E19–E31 and E35/E40/E43 protocol or continuation edits, and measure H1.7. A stable printed type or a cache hit is not sufficient evidence. Reuse must remain valid for changed generalization, demand, transition, range, selected equality and resource/target premises, including selected platform and foreign declarations. Proof and code dependencies may differ.
4. **Establish each claimed realization.** JS objects, comparator trees, BigInt operations, native layouts and FPGA resources have different obligations. Binding a source type does not prove a library or emitted operation implements it.
5. **Measure the design-time result.** Quantify the gains and costs under the pinned workload rather than predicting them from pure versus mutable implementation style.

The editor-facing result should retain the familiar usefulness of F# tooling while exposing the additional native judgments. For a selected expression, show its scheme, established structural relationships, pending nonstructural obligations and the source of a failure. The editor consumes CCS/Baker's evidence. FSharp.Compiler.Service supplies the F# comparison surface, while CCS handles Clef judgments.

**Advance:** source proofs, mutations, implementation checks and the affected consumer/target evidence agree. The implementer runs the shape matrix and discriminating mutations before handoff. Substantial acceptance uses unfiltered leased suites with a frozen dependency closure. Accepted baselines from other agents are reused. The reviewer audits binding and anomalies rather than rerunning a baseline solely to re-establish it.

**Stop or narrow:** integration requires semantic repair in Alex, publication or a retired plugin; different producers silently change source meaning; proof reuse omits dependencies; or realization only passes by narrowing the promised contract without declaring that change.

This review does not authorize a gate shortcut. No focused passing result establishes complete F/C acceptance.

Develop reusable laws and their semantic bridges with the planned cvc5/Rocq ecosystem in parallel with production integration. Bind the admitted solver/checker dependencies and the actual artifact, not merely a source theorem or tool exit status. Framework and domain authors provide reusable checked constructions. Supported application cases should obtain those instances through ordinary compilation. [Proof-composition roles and exact source binding](07-explaining-clefs-position.md)

## Horizon 3 extend proofs & the language remit

**Pursue compiler correctness and self-hosting as explicit workstreams.** Mechanize the admitted source and intermediate semantics, prove nanopass preservation and composition, and bind executable implementations to those proofs. Apply the same artifact and dependency discipline to the compiler as it becomes self-hosted. Record the bootstrap compiler, transformations, checking environment and final executable. Independently checked evidence must break any circular claim that the compiler proves itself merely by compiling itself.

Extend the finite coexponential service result through an explicit recursive-protocol and runtime interpretation where the evidence warrants it. Mechanize the source/continuation and target correspondence, including request-labelled observations, resources and any applicable validity and fairness premises. The result for one selected execution or finite trace is not automatically equivalence of all service orders or completion of every runtime request.

This extends the planned proof ecosystem into an accountable path toward a proved compiler. Program guarantees, artifact correspondence, transformation correctness and bootstrap trust are related obligations that can advance together. The current Composer proof-composition owner explicitly names self-hosting as a long-term goal. Use its current support-completeness and generation-binding rules, not superseded proof-pipeline diagrams. The [positioning document](07-explaining-clefs-position.md) gives the audience-facing account and source anchors.

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

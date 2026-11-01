# Clef: a concurrent language with its own native type universe

This is the recommended public positioning for the selected architecture. It addresses F#, Haskell and Scala programmers, with sections for Rust, C and C++ developers. Present-tense language about Clef's contract describes its design. Implementation coverage is governed by the [delivery gates](04-horizons-and-experiments.md).

## The short explanation

Clef is a concurrent programming language with ML-family syntax and its own native type universe. Its inferred contracts describe more of what a program means: a quantity's units, a value's identity, who may use a resource, how services communicate, and the precision a calculation must preserve. Familiar generic functions remain useful. Their contracts also record what must be established before a resource can be consumed or a calculation can run faithfully on a particular target.

The compiler should establish those relationships while it has the relevant information, preserve them as it transforms the program, and connect its guarantees to the code it emits. That is the direction from convenient type inference toward proof-bearing compilation—and ultimately toward a compiler whose own transformations are proved.

Clef is lazy by default: a binding can name shared deferred work, and demand determines when that work occurs. This differs from the eager defaults in F# and many other ML-family languages, while offering Haskell programmers a familiar starting point. That execution model changes what the compiler must know about effects, captures, observation and resource use when it infers and generalizes a program.

## Weaving data flow and control flow

A concurrent service can receive a request, own state, call other services, suspend and later return a reply. The data are the request, state, intermediate values and result. The control flow is the particular computation that waits, resumes and completes. Clef's compiler needs both, together with the ownership and identity that connect them.

The coexponential service account describes a service and its client pool. A delimited continuation retains one waiting invocation's return point, live values and resources. In the PSG, weaving the braid means relating these control and data dependencies as independent work is submitted, suspended and joined. A proposed interaction-net interpretation explores how local rewrites can be interleaved with that continuation control. It needs its own preservation and target correspondence. A hyperedge retains the participants of a relationship together, so a change can be traced to the affected judgments and evidence. This is the foundation for Clef's differential compilation, subject to complete dependency recording and valid rechecking. The structure can also guide native realization on a CPU, accelerator, FPGA or JavaScript pathway when that pathway satisfies the corresponding contract.

This is why Clef's reach extends well beyond changing an F# type checker. A function's carrier types may be unchanged while its request identity, wait dependencies or completion authority change. The proposed native inference must preserve those relationships through compilation. The current finite service construction and its conditional results provide a starting point. A general reconstruction algorithm, target correspondence and a mathematical interpretation of the braid remain work to establish. [Service strategy and experiments](04-horizons-and-experiments.md)

The compiler project has already started toward this architecture: native unification, bounded first-demand analysis, continuation ingredients and proof-obligation hyperedges exist alongside Farscape's ABI evidence. The roadmap identifies the remaining source judgments and connects them to those components. The full inference and proof-reuse path remains in development.

The same foundation reaches into learned and quantum computation. A distributed AI update can depend on two observations belonging to the same sampled execution even when their individual types and distributions look correct. A quantum circuit description can be shared as classical data, but executing it requires separately tracked live resources, gate laws and measurement effects. Retaining these distinctions makes useful guarantees expressible across targets. It does not make model convergence, arbitrary unitarity or physical fidelity automatic.

## A continuation of the ML tradition

ML's connection to proof is foundational. It grew as the language used to program proof strategies in LCF. Its abstract types helped ensure that a claimed theorem could be constructed only through the system's inference rules. Useful automation and disciplined trust were designed together. Clef's opportunity is to bring that relationship into ordinary native compilation. [Cambridge's history of LCF and HOL](https://www.cl.cam.ac.uk/research/hvg/HOL/history.html)

Braidpoint's [The French Connection](https://braidpoint.tech/blog/the-french-connection/) already makes the practical case: evidence about a qualified tool and an independently checkable argument answer different questions. Its sensor example connects a divisor's nonzero property to a platform declaration or a source branch, then keeps uses of that fact dependent on its origin. The inference work gives that argument a more explicit language foundation. A changed premise should withdraw the guarantees that depend on it. [Local article binding below.]

For example, a sensor contract that allows values from 1 through 4095 can justify using a reading as a divisor. If that contract changes to include zero, the dependent division needs a new justification—perhaps a branch that handles zero first. Retaining this connection is useful both for correctness and for compilation: the compiler knows which conclusions need to be revisited and which remain valid.

This tradition brings substantial engineering depth: express the semantics, retain the conditions, automate the supported work, and make the result checkable.

## Familiarity and changes

**For F# programmers,** functions, algebraic data, records, measures and local inference remain the starting point. Kennedy's dimensional inference is especially important: it demonstrates that useful mathematical relationships can be inferred with very little ceremony. Clef extends that ambition into a native semantic model.

The current compiler and tooling run on .NET. Clef's native semantics define the identity and permitted uses of its values and constrain their representation. A source quantity can retain its dimension while its justified representation differs across targets. It may be difficult for F# developers to grasp at first, but the value of this approach is demonstrable. We're excited to have an opportunity to show that value in the Fidelity Framework.

**For Haskell programmers, Clef being lazy by default will be the most immediate point of familiarity.** Demand and sharing are part of the language's ordinary execution model. That model also governs Clef's resource and numeric contracts. Conditions on mutable observations must hold when a computation actually demands them. Sharing a computed value does not create additional one-shot completion rights.

Qualified schemes provide another familiar connection, retaining requirements with a polymorphic function instead of forcing every decision immediately. Deferring execution and deferring a compiler's representation choice remain distinct, coordinated concerns.

**For Scala programmers,** contextual requirements and rich interfaces provide another useful entry. The Clef proposal keeps operation requirements explicit and resolves them under a native contract. It chooses measured rows for structural record reuse and qualified requirements for nominal operations, with annotated higher-rank checking where an interface needs it. Broad subtype bounds and implicit heterogeneous joins remain outside the foundation of this rollout.

These languages already extend simple Hindley–Milner inference in different ways. Clef changes what an inferred contract needs to describe. Relevant precedents include F#'s member/subtype constraints, Haskell's class-qualified types and Scala's contextual abstractions. [F# specification](https://fsharp.github.io/fslang-spec/types-and-type-constraints/), [Haskell report](https://www.haskell.org/onlinereport/haskell2010/haskellch4.html), [Scala contextual abstractions](https://docs.scala-lang.org/scala3/book/ca-contextual-abstractions-intro.html)

**For C and C++ programmers,** the invitation is control over native behavior with stronger retained contracts. Layout, ABI, ownership, intermediate capacity and foreign effects remain concrete engineering concerns. Our Farscape binding generator already separates source numeric spelling from foreign ABI representation evidence. Clef should use that evidence to justify marshaling and native lowering, while keeping the foreign function's behavioral assumptions explicit. A boundary proof is useful precisely because its scope is clear.

## The Rust comparisons

Rust has shown the practical value of using ownership and types to make concurrent and parallel code safer to write. Clef extends that ambition through three commitments in its language contract: **fearless concurrency, fearless parallelism, and no `unsafe` anywhere in the language.** The last applies to library code as well as applications. Low-level access needs a supported contract and evidence. There is no source form that waives a missing obligation. [Rust's concurrency model](https://doc.rust-lang.org/book/ch16-00-concurrency.html), [Rust's explicit unsafe boundary](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html)

**Fearless concurrency** means establishing compatible access and ownership, preserving invariants across suspension, and keeping replies and completion rights attached to the correct computation. Our negative and fractional types whitepaper contributes distinct live instances and permitted use. Effect, demand, lifetime and protocol analysis establish the surrounding conditions. A shared lazy result cannot manufacture another right, and an immutable binding to a mutable object does not freeze that object's contents.

Clef's contract guarantees liveness and deadlock freedom for compiler-admitted workflows, without defensive coordination code or proof escape pragmas in application code. The evidence covers every blocking dependency and the required scheduling, delivery, cleanup and external-call conditions. Each admitted request must reach its protocol's defined success or failure outcome. An ongoing service can continue accepting new requests.

**Fearless parallelism** also concerns the meaning of the calculation. The compiler must establish which partitions, orderings and merges preserve its exactness, error and rounding contract. A race-free floating-point reduction can still depend on regrouping. An exact accumulator can still count a retried contribution twice. Clef's selected architecture brings arithmetic, identity and coordination into the same evidence-bearing graph so parallelization can be justified against the actual result contract.

Graph coloring in the nanopass design groups work whose recorded dependencies permit concurrent execution. Each group is checked against conflicts and joint resource constraints. Target information then guides which valid grouping is worth running in parallel. Numerical equivalence and hardware benefit have their own evidence, rather than following from the coloring alone.

**No unsafe escape** changes how difficult cases are handled. A native pointer, memory-mapped device operation or foreign call must enter through a declared boundary whose value, access and resource requirements are established. Our FFI binding strategy keeps pointer-bearing operations behind those contracts. Unchecked pointer arithmetic does not spread into Clef source. Foreign behavior and platform guarantees remain explicit assumptions. A return check cannot repair an earlier unauthorized write, so the relevant access preconditions must be established before admitting the call.

If a requirement is still unresolved in the editor, the compiler raises specific diagnostics to identify what is missing. Before emitting that operation, it must establish the requirement, select a supported checked protocol, or produce a compiler error. Imported libraries may contain unsafe operations. Clef exposes them only through these boundary contracts and their stated assumptions.

The useful promise is concrete: source code cannot opt out of the obligations that make the supported concurrent or parallel realization valid. In Clef and the Fidelity Framework, the notions of delivery, progress, cancellation and failure remain part of the specified protocol rather than being loosely associated with race freedom. This connects native systems control to the same proof discipline used for precision and resource use. [Realization and boundary strategy](02-js-numerics-and-interop.md)

## Our native inference contract

The selected approach keeps ordinary local inference and the solving of dimensional equations, then gives other native relationships their own explicit rules.

A qualified scheme lets a generic function retain requirements that its callers must satisfy. A measured row lets a function accept records with particular measured fields while preserving their additional fields.

Negative and fractional types, or NFT, add rules for directed operations, matching a particular value and consuming a particular resource right. Numeric analysis retains ranges, precision requirements and intermediate results until there is enough evidence to choose a representation.

These facts cooperate, but they answer different questions. Knowing that a quantity is measured in meters does not tell us how large it can be. Equal values do not necessarily identify the same live resource. Finding one valid type does not show that the function remains usable in every intended context. Knowing that a target supports an operation does not prove the generated code implements the whole calculation correctly.

That is why the strategy uses several procedures under one language contract. It is also why an interface can require an annotation or a tagged alternative when that makes its meaning clearer. The aim is to infer the useful everyday cases and make the remaining requirements understandable.

Clef's treatment of **negative and fractional types** makes the need for richer contracts especially tangible. A scratch value restored to zero and one still holding a temporary result can both have an ordinary integer type. *The type alone does not establish that the cleanup was completed.* Likewise, two separately created completion rights do not become one right merely because they refer to equal values. Clef must preserve those distinctions through branches, closures, lazy evaluation and generated code.

Recovery also has concrete limits. Rounding an amount can discard a fraction. Keeping only one field of a record can leave other information behind. To recover the original, the program must retain what is needed or use an operation with an established reversal rule. **Negative and fractional types give Clef a unique way to express and check those obligations.** They do not make every computation reversible or every interface conversion valid. The first implementation starts with precisely defined immutable values. More complex resources and foreign handles receive explicit rules as support expands.

## More of the contract becomes checkable during inference

This is the proposed **Tier 1 gain**: ordinary compilation can establish more of the native relationships a program depends on, and retain the reasoning for later compiler stages. F# already checks valuable relationships, including units of measure and resolved member requirements. Clef should preserve those strengths while adding explicit structural record, scope and resource-use judgments.

For a record transformer, the contract can state which field changes and which remaining field types are retained. For a one-shot result, it can distinguish sharing a value from creating another right to consume it. The compiler must retain the admitted derivation and reject a change that violates its premises. Library authors can then export more of their actual contract, and callers can receive the applicable checked instance through ordinary inference.

That does not turn every program property into a type check. A field relationship does not establish numeric accuracy. A valid consumption rule still needs its matching premise, and it does not by itself prove eventual completion. The useful advance is to connect these obligations explicitly, so later analyses and lowering can use established facts without silently discarding their conditions.

The [worked F# comparison and experiment criteria](04-horizons-and-experiments.md) make the proposed approach concrete. They connect standard F# inference, the row and rank-N mechanisms in `write-you-an-inference-in-fsharp`, and the proposed native contract. The same roadmap uses Xantham's binding work, Partas.Solid's transformation boundaries and Ranvier's dependency model to identify practical tests of the design.

## JavaScript's richer numerics opportunity

Separating source meaning from a host carrier changes what JavaScript lowering can deliver. An exact integer computation may use ordinary numbers where every intermediate satisfies the required range. A wider exact or scaled computation may need an integer-backed construction. A reduction may require an exact accumulator and deterministic final rounding. A floating computation may require a justified error bound or residual construction.

The native contract selects which guarantee matters, and the compiler selects a supported construction that preserves it. A Clef numeric value need not become one JavaScript scalar. Nor may a lowering silently change a declared rounding schedule merely because another construction is mathematically attractive.

This connects directly to Beancounter's integrity rules: amounts, currencies, rational rates, named rounding, persistent collections and coherent displayed results. It also reaches past arithmetic. Suspended work must resume with valid premises. Replies must belong to the correct request. Retries must not become additional contributions. These are obligations the compiler can retain together instead of asking application code to reconstruct their relationship at every boundary. [Numeric and JS delivery strategy](02-js-numerics-and-interop.md)

FPGA makes the same separation visible in registers and circuits. A state field remains one field while its proven range determines a physical width. Mealy/Moore dependencies describe how outputs relate to state and input across software as well as hardware. Native, FPGA and JavaScript realizations differ, but that is a reason to preserve the source contract more carefully.

## Rocq/Coq and the proof ecosystem

Rocq, formerly Coq, belongs near the center of this account. It provides a mature setting for formal definitions, reusable theorems and machine-checked proofs, with a kernel implemented in OCaml and extraction routes to OCaml and Haskell. Clef should use that ecosystem to establish reusable laws and check the interpretations connecting them to native compilation. Application authors should receive supported instances through ordinary compilation. They should not have to choose a prover for every expression. [Rocq project](https://rocq-prover.org/)

The current proof-composition design names the following roles. They are concrete integration directions, with library bridges and coverage still to be established. This is not a list of already interchangeable installed backends.

| Role | Tools and bodies of work to bring into the fold |
|---|---|
| Admitted arithmetic and analysis obligations | **cvc5**, with its actual evidence and trust dependencies retained. |
| Reusable checked definitions, laws and relational arguments | **Rocq/Coq**, with a compatible, pinned **OPAM** environment prepared outside the editor's keystroke loop. |
| Ownership, invariants and communication | **Iris, Actris, Aneris and RCLib**, through explicit Clef and protocol interpretations. |
| Distributed transformations and trace refinement | **Verdi and Trillium**, under stated fault and observation models. |
| Probabilistic and approximate relational arguments | **Clutch, Approxis and Foxtrot**. Distribution/coupling guarantees remain distinct from floating-point roundoff. |
| Machine code, MMIO and structured automation | **Islaris/Isla** and the **RefinedC** body of work, with target-specific semantic bridges. |
| Circuit and FPGA realization | **Colibri**, existing **PSL/SBY** assets and the proposed **VHDL-to-Rocq** route. **QWIRE** offers a separate possible quantum interpretation. |

The engineering task is to connect each reused result to Clef's actual semantics, premises and artifacts. A tier number alone does not name the trusted base: a relational result may depend on Rocq even when its discovery is classified below the top tier. The updated account should preserve the French Connection article's evidence argument while replacing its older top-tier-only Rocq description. [Proof-composition source binding below.]

## From proved programs to a proved compiler

The destination should be explicit: supported program guarantees attached to actual artifacts, followed by a compiler whose admitted transformations and their composition are mechanically justified. Self-hosting makes the compiler itself a native Clef program to which the same discipline can be applied.

Four assurance obligations connect that destination:

1. **Establish the source claim.** Check the admitted typing, resource, numeric and protocol judgments with their premises.
2. **Connect it to the emitted artifact.** Preserve or independently validate the relevant operations, layouts, boundary behavior and target assumptions through the actual build.
3. **Prove the compiler transformations.** Show that each small compiler pass preserves the required behavior, then show that the sequence does too. Include effects, lazy evaluation, numeric choices and resource identities. Connect the executable pass implementation to the function or relation that was actually proved correct.
4. **Account for bootstrapping and self-hosting.** Bind the compiler source, bootstrap tools, generated compiler and checking environment. Use independently checked evidence and an explicit trusted-base argument so the compiler is not simply asserting its own correctness.

These workstreams can advance together. Self-hosting is an important milestone in this plan. Its preservation and bootstrap obligations are what turn that milestone into a compiler-correctness result.

CompCert provides a useful precedent for stating the theorem precisely: its manual identifies the verified compiler stages and treats assembly/linking assurance separately. MetaRocq's extraction work likewise distinguishes executable support from proved coverage and the subsequent toolchain. That discipline is particularly relevant to Clef's lazy semantics. We should adopt the precision of those accounts while pursuing the broader native remit. [CompCert manual](https://compcert.org/man/manual001.html), [MetaRocq verified extraction](https://github.com/MetaRocq/rocq-verified-extraction)

The public message can therefore be ambitious and specific: **Clef is extending the ML tradition so that inferred native contracts survive into execution, and so that the compiler can eventually be subject to the same proof discipline as the programs it produces.** The [strategy chapter](04-horizons-and-experiments.md) turns that message into a delivery sequence.

## Source and editorial binding

The language decisions are this guide's recommendations, supported by chapters 1–6. The proof-tool roles and self-hosting goal are bound to `FidelityFramework/Composer@74493a128a08a5333a9991a8e1dc147b036d4be4`, `docs/Proof_Composition_Architecture.md:3,24,31–79,95–127,174–207`, and `arxiv-papers@d2bab3376032929dc7a4eca7e0bc807247a88c03`, `decidable-by-construction.md:234–272,330,635–645`. Library integrations are explicitly proposed in the owning architecture. F* and Dafny are cited workflow influences, not additional announced backend integrations. Z3 is historical in this account.

The French Connection binds to `braidpoint-site@cd24eb28919107f433ba80c43939473b83aba519`, `hugo/content/blog/The French Connection.md:94–160`. Its concrete dependency argument is retained. Its Rocq/TCB tier wording at lines 156–158 is reconciled with the current Composer contract at lines 42–47 and 176. No blog edit was made here. Public primary references support the historical and ecosystem comparisons. They are not evidence that Clef already inherits their verification results.

The concurrency guarantee is tied to the workflow model in `arxiv-papers` at the revision above, `coexponential-exploration.md:280–308,665–676`: complete blocking-dependency coverage, total correctness of continuations, fair scheduling/request selection and eventual external terminal outcomes/delivery. Its runtime/Rocq correspondence remains a proposed realization at line 934. The current `clef-lang-spec@a69ac8a91b49f97bd5a5e7bea2934246c2d54edd`, `spec/synchronous-rpc-liveness.md:65–85,132–138`, also permits unresolved supervised modes. It needs reconciliation with the selected no-escape contract, as recorded in chapter 5. The source guarantee and implementation gate must stay distinguishable.

Graph-coloring support binds to `clef-lang-site@15d381634f7a08c2a44884a0598d0e634083b313`, `hugo/content/docs/internals/pipeline/speed-and-safety-with-graph-coloring.md:15–55,111–135`, and Composer at the revision above, `docs/PRDs/C-08-ArithmeticConstruction.md:3,99–122`. The PRD is marked in progress. These are design obligations, not a new scheduling or performance acceptance receipt.

**Document owner and growth reason:** this inquiry owns the user-requested final positioning document for the F#, Haskell, Scala, Rust and native-language audience. It translates the selected strategy into a usable explanation without creating another language specification.

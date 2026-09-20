# Baker Saturation Architecture

## Document purpose and authority

Baker elaborates admitted Clef operations into typed PSG structure and the graph
relationships needed to justify their implementation. This document describes the
three-layer organization and its current construction APIs. It does not establish
native coverage merely because a recipe exists.

This revision reconciles the earlier design with the removal of the unused
`Decomposition.mk*Node` constructors, deprecated metadata aliases, and unused
shadow-builder fields. The language and representation contracts remain in
`clef-lang-spec`; the [design supersession register](phg/Design_Supersession_Register.md)
records decisions that supersede historical implementation sketches, including the
collection sentinel and bounded-link contracts. Current native coverage and open
obligations are recorded in Composer's C-06/C-07 PRDs and language coverage waypoints.

## 1. Responsibility and boundary

A source operation such as `Seq.map`, an Option elimination, or a pattern match
must retain its Clef semantics through elaboration: operand evaluation order,
selected callback execution, source binding identity, dimensional types, and the
applicable representation and lifetime obligations. Baker makes these structures
explicit in the graph. Alex witnesses the settled structures; it cannot infer a
missing source algorithm, fabricate a carrier, or repair missing proof premises.

An older PRD may specify the behavior without naming the hypergraph relationships
needed to establish it. A fact whose validity is local can remain a node coeffect.
When a conclusion depends jointly on several participants, the recipe retains
their exact incidence and provenance through fan-out/fold-in. For example, an
additive loop enclosure depends on its guard, induction cell, initial values,
step and actual stores; the cell's resulting range alone does not retain those
proof dependencies. Representation and proof consumers read the same settled
participants rather than reconstructing those relationships independently.

The bootstrap implementation is written in F#. Its use of F# types and parser
computation expressions does not import CLR collection, object, or scheduling
semantics into Clef. Clef operations are admitted and elaborated according to their
native contracts and the declared platform.

The distinction between a primitive and an operation recipe is an implementation
boundary, not an exemption from proof. For example, the settled collection design
requires arena-relative bounded links, a sentinel image and residence evidence,
read-only access, and guarded payload reads. Listing `empty`, `head`, or `cons`
in an ingredient module does not prove those obligations or complete their native
implementation.

## 2. Three construction layers

| Layer | Current responsibility | Representative files |
|---|---|---|
| Primitives | Construct typed nodes, emit them through saturation state, and attach enrichment metadata. | `Baker/Ingredients/Primitives.fs`, `SaturationCombinators.fs` |
| Reusable structures | Compose nodes into a particular graph protocol, with explicit operands, formals, references, and result types. | `Ingredients/Patterns.fs`, `Sequences.fs`, `Continuations.fs`, `Closures.fs` |
| Operation recipes | Apply an admitted operation's semantics using those structures and return a graph change. | `Baker/Recipes/OptionRecipes.fs`, `ResultRecipes.fs`, `SeqRecipes.fs`, `MatchRecipes.fs` |

The nanopasses discover applicable sites, invoke recipes, and fold their results
into the graph. Algorithms belong in ingredients and recipes; orchestration
preserves and composes their results.

### 2.1 Saturation state and primitives

[`SaturationCombinators.fs`](../../src/Compiler/Baker/Ingredients/SaturationCombinators.fs)
defines `SaturationParser<'T>` using the bootstrap XParsec parser. The exported
`saturation` computation expression threads a `SaturationState` containing emitted
nodes, name bindings, the inspiring source node and range, expansion identity,
operation name, and platform. `run` returns the result and emitted nodes in
construction order. A parser error is reported with construction context; it is
not silently treated as a successful empty recipe.

[`Primitives.fs`](../../src/Compiler/Baker/Ingredients/Primitives.fs) owns common
construction operations such as:

```fsharp
createWithChildren : SemanticKind -> NativeType -> NodeId list -> SaturationParser<NodeId>
createAndEmit      : SemanticKind -> NativeType -> SaturationParser<NodeId>
letBind            : string -> NodeId -> NativeType -> SaturationParser<NodeId>
evaluateBefore     : NodeId list -> NodeId -> NativeType -> SaturationParser<NodeId>
unitLit            : SaturationParser<NodeId>
```

These are API signatures, not source-language declarations. `createWithChildren`
creates, marks, and emits a node; its caller supplies the semantic type and actual
structural children. Higher-level ingredients must also preserve reference and
provenance relationships required by the node kind. `unitLit` constructs the typed
unit value. Numeric literal constructors must agree with their declared NTU type;
there is no platform-independent license to insert a fixed-width literal carrier.

The node constructors internal to `Primitives` use F# assembly visibility. That
visibility does **not** enforce an Ingredients-only boundary. The layer boundary
is maintained through API use, review, and graph tests; it must not be described
as a folder-level compiler restriction.

### 2.2 Reusable graph protocols

A reusable ingredient carries more than a convenient node spelling. For example,
[`Sequences.fs`](../../src/Compiler/Baker/Ingredients/Sequences.fs) builds the
iterator binding, guarded pull, and immediate current read used by consumers and
producer bodies. The current-read admission pass verifies that protocol against
exact iterator, guard, and loop identities. Short-circuit consumers compose their
stop condition with that protocol; Alex does not rediscover it from source syntax.

[`Continuations.fs`](../../src/Compiler/Baker/Ingredients/Continuations.fs) uses
shared primitive construction and adds the settled slot identity, type, and range
needed by frame operations. Its range-bearing operations are not interchangeable
with an arbitrary literal or field-read constructor.

Sequence producers evaluate their supplied expressions in the forming scope,
retain explicit snapshots and captures, and construct a unit-valued generator
body. Consumers retain eager operands before starting iteration. Accumulator and
callback result types come from their own admitted arguments; they cannot be
substituted with the input element type.

These examples describe implemented construction responsibilities. They do not
assert that every old recursive recipe has been migrated or that every payload,
escape, or lifetime case has native coverage.

### 2.3 Operation recipes

[`Decomposition.fs`](../../src/Compiler/Baker/Recipes/Decomposition.fs) now contains
only the active context/result bridge:

```fsharp
type Context = {
    SourceRange: SourceRange
    ElementType: NativeType
    Platform: PlatformContext option
    OriginalHOF: string
    ExpansionId: int
    InspiringNode: NodeId
}

type Result = {
    NewNodes: SemanticNode list
    ResultNodeId: NodeId
    AuxFunctions: SemanticNode list
}
```

`mkContext` creates an expansion identity; `mkResultNoShadow` packages the emitted
nodes, result root, and auxiliary functions. The retained function name has no
shadow-tree side effect.

Recipes run a saturation computation and package its emitted structure. There is
no target line-count requirement: eager argument snapshots, guarded extraction,
source identities, and proof dependencies take precedence over making a recipe
look short. Existing ingredients should be composed where their contracts match;
a distinct semantic protocol needs an explicit ingredient, not a copied private
node constructor.

## 3. Fan-out and fold-in

[`BakerSaturation.fs`](../../src/Compiler/Nanopass/BakerSaturation.fs) maps admitted
sites to operation recipes. Its `toRecipe` bridge includes both `NewNodes` and
`AuxFunctions`, the original source node, and the replacement root.

[`Recipe.fs`](../../src/Compiler/Nanopass/Recipe.fs) defines the ordinary replacement
artifact:

```text
Recipe = original node + replacement root + emitted nodes + new hyperedges + elaboration description
RecipeSet = recipes keyed by original node + replacement map + attempt diagnostics
```

An attempt returns `RecipeCreated`, `NotApplicable`, or `CreationFailed` with
context. These outcomes are distinct; a catalog entry or a non-applicable recipe
is not evidence of completed lowering.

[`FanOut.fs`](../../src/Compiler/Nanopass/FanOut.fs) currently enumerates selected
nodes and creates recipes **sequentially**. Although some older comments say
“parallel”, the implementation uses `List.map` deliberately: fresh node IDs come
from shared allocation, and parallel creation would make identities
nondeterministic.

[`FoldIn.fs`](../../src/Compiler/Nanopass/FoldIn.fs) applies the replacement map to
both existing and newly emitted references. This includes cross-recipe references,
structural children, declaration roots, module mappings, and resident hyperedges.
`Recipe.NewEdges` retains every source participant, target, class, role and
ordinal. Existing and newly contributed hyperedges pass through the same
simultaneous replacement map; recipe serialization retains the original
participants for inspecting the fan-out artifact. Startup construction and
exclusive branch occurrences use this path for their joint relationships.
An emitted node at an existing identity takes precedence, which supports replacing
a pattern binding with a value-producing binding while retaining source references.
The fold reconstructs indexes and invalidates downstream coeffects for later
analysis. A pass scheduled after range or placement must preserve or recompute the
appropriate facts explicitly; the generic fold is not an unconditional
post-analysis mutation API.

Parent pointers are maintained for traversal, but they are not sufficient evidence
for shared ownership, evaluation order, capture lifetime, or activation coverage.
Those judgments use the graph's actual structural/reference incidence and typed
relations.

### 3.1 Relation and obligation enrichment

Not every Baker result is an ordinary node replacement.
[`Ingredients/Obligations.fs`](../../src/Compiler/Baker/Ingredients/Obligations.fs)
defines:

```fsharp
type Enrichment = {
    NewNodes: SemanticNode list
    NewEdges: Hyperedge list
    Annotated: SemanticNode list
}
```

Obligation and sequence recipes use this form when their result includes graph
relations or annotations at existing identities. A dedicated nanopass folds that
result according to its own contract. For example, `SequenceOwnership` replaces
its delimiter projection while retaining unrelated edges; it does not manufacture
evaluation segments or a frame from ownership alone.

Ordinary replacement recipes can also supply `NewEdges`. Use the enrichment
form when the pass changes a relation projection or annotates existing identities
without an ordinary replacement root. Neither path stores proof incidence as
strings in metadata or leaves it to be inferred later by a witness.

## 4. Metadata, provenance, and editor projection

The active marking and query API is
[`SemanticGraph/Elaboration.fs`](../../src/Compiler/PSGSaturation/SemanticGraph/Elaboration.fs):
`markBaker`, `markIntrinsic`, `isEnriched`, `tryGetKind`, `tryGetFor`, `tryGetId`, and
`tryGetInfo`. The shared primitive constructors apply Baker marking through this
API. The deleted `Decomposition` metadata constants and aliases are not an
alternative API.

Enrichment labels explain why a node was synthesized. They do not replace typed
proof, ownership, evaluation, or source-definition relationships. Transformations
must preserve the original binding identity or supply the established provenance
needed by source-facing tools. Likewise, elaborated hidden formals must not leak
into a callable's public source signature.

### 4.1 Shadow display is separate work

`Baker/ShadowAST.fs` retains a historical representation and renderer for describing
synthesized code. Current `Decomposition.Context` and `Result` do not carry a
shadow builder or tree, and the recipe/fan-out/fold-in path described above does
not populate a shadow registry for editor display. Neither automatic shadow
construction during saturation nor complete derivation from the final PSG is
implemented by these APIs.

Any future shadow display must be a source-facing projection of the authoritative
graph and preserve provenance. Its scheduling, rendering, and integration require
their own implementation and tests. The former snippets should not be used as
instructions to recreate a second semantic tree alongside Baker.

## 5. Traversal, scheduling, and fusion

Discovery and traversal locate graph sites; recipes own their semantic changes.
A Huet focus can carry the position and surrounding context needed for a
projection without becoming a second store of inferred semantics. Alex's focus
must consume the settled graph and reject missing required facts.

Parallel saturation and fusion remain design directions, not properties established
by the current sequential fan-out. Disjoint module names do not prove independent
work: recipes may share references, replace existing identities, and depend on
joint proof premises. A future scheduler needs deterministic identity allocation,
explicit dependency/conflict handling, and preservation of the same graph
consequences before parallel execution is admissible. No actor or general Clef
computation-expression support follows from an F# scheduling sketch.

Likewise, a fusion rewrite must preserve eager formation, callback ordering and
selection, suspension behavior, dimensions, and lifetime/proof incidence. Removing
an intermediate structure is not sufficient evidence of equivalence. This document
does not prescribe an unimplemented traversal or incremental invalidation API.

## 6. Implementation and review guidance

For an operation change:

1. Establish its admitted source scheme and precise evaluation behavior from the
   canonical Clef contract, including independent payload and result dimensions.
2. Compose the appropriate ingredients and return a replacement or enrichment
   through the existing nanopass seam.
3. Preserve source identities and required structural/reference relationships;
   express new proof premises as typed graph incidence.
4. Verify the relevant source diagnostics and graph invariants. Where native
   coverage is claimed, also verify the settled representation, stock MLIR path,
   and observable native behavior with the associated oracle.

A successful source check is not a native conformance result. A native exit test
is not, by itself, a lifetime proof. Missing facts stay explicit residuals until
the owning upstream pass establishes them. This boundary is what allows additional
Clef surface to reuse Baker's construction machinery without moving semantics
into Alex or maintaining a competing metadata or shadow implementation.

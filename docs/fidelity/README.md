# Clef Compiler Service (CCS)

CCS is the front end of the Fidelity toolchain: it lexes, parses and type-checks Clef source in the
Native Type Universe (NTU) and produces the **Program Semantic Graph (PSG)**, a hypergraph that is the
sole, exhaustive semantic authority for everything downstream. Composer's middle end (Alex) witnesses
the saturated graph into MLIR; the editor tooling (Lattice) witnesses it into hover, diagnostics and
proof surfacing. Neither computes anything the graph does not already carry.

CCS descends from a surgical fork of dotnet/fsharp's front end (lexer, parser, syntax tree, diagnostics
infrastructure). The typed tree, IL generation, optimizer, FSI, MSBuild tasks and the inherited test
corpus have been removed; what remains is the Clef checker and the graph it saturates.

## Where the design lives

| Document | What it is |
|---|---|
| [phg/](phg/) | The design of record: the PSG-to-PHG plan, layout as joint constraint, the closure retooling plan, the **Design Supersession Register**, and [`drift-gate.sh`](phg/drift-gate.sh), which makes retired vocabulary a lint failure across the corpus |
| The language specification | lives in `clef-lang-spec/spec/` and nowhere else: `native-type-universe.md`, `ntu-types.md`, `ntu-dimensional-architecture.md`, `units-of-measure.md`, `width-inference.md`, `numeric-selection.md`, `access-kinds.md`, `memory-regions.md`, `platform-bindings.md`, `error-handling.md`. The parallel copies this folder carried (`ccs-specification.md`, `native-type-universe.md`, `NTU_Type_System.md`) were retired on 2026-09-04 as drift sources |
| [Baker_Saturation_Architecture.md](Baker_Saturation_Architecture.md) | Baker: ingredients and recipes that saturate the graph (collections, obligations, closures, suspension) |
| [CCS_Lazy_Seq_Coroutine_Intrinsics.md](CCS_Lazy_Seq_Coroutine_Intrinsics.md) | Lazy, seq and coroutine intrinsics as CCS elaborates them |
| [Platform_Predicates.md](Platform_Predicates.md) | Platform description as declared authority; predicates read structurally from the graph |
| [SMT_Integration_Strategy.md](SMT_Integration_Strategy.md) | Obligations born in the PSG, dispatched to cvc5 at design time and re-checked at build time |
| [From_FSharp_to_Clef.md](From_FSharp_to_Clef.md), [Clef_Language_Vision.md](Clef_Language_Vision.md) | Orientation: how Clef differs from F#, and why |
| [Safety_Critical_Certification.md](Safety_Critical_Certification.md), [Certification_Lab_Strategy.md](Certification_Lab_Strategy.md) | The certification posture the proof story serves |

The normative language specification is [clef-lang-spec](https://github.com/FidelityFramework/clef-lang-spec);
the Composer-side architecture (Alex, the witness boundary, the thin middle end) is in `Composer/docs/`.

## Source layout

```
src/Compiler/
├── SyntaxTree/        lexer, parser, syntax tree (inherited front end)
├── NativeTypedTree/   the Clef checker: NTU types, unification, expressions, NativeService (the pipeline)
├── PSGSaturation/     the semantic graph: nodes, hyperedges, reachability, platform resolution
├── Baker/             ingredients and recipes that saturate the graph
├── Nanopass/          fan-out / fold-in passes, obligation elaboration and discharge, monomorphization
├── Project/           .fidproj loading and project checking
├── Driver/, Facilities/, Utilities/   inherited infrastructure that survived the pruning
└── Clef.Compiler.Service.fsproj
```

CCS builds inside Composer's solution as a project reference; it is not a standalone .NET library.

## The one rule

The design decides; the code conforms. Where code and design disagree, the code is the gap, and the
[register](phg/Design_Supersession_Register.md) records what was retired and why. Run the drift gate
before proposing a change to any document in this tree:

```
docs/fidelity/phg/drift-gate.sh
```

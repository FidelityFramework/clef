# Lattice Consumer Contract

> What the editor tooling (Lattice) and the IDE (Atelier) read from the Program Semantic Graph,
> who owns each fact, and what exists today. Design of record, 2026-09-04. Companion to
> [Design_Supersession_Register.md](Design_Supersession_Register.md); enforced in part by
> [`drift-gate.sh`](drift-gate.sh) (retired vocabulary, and the per-fork count of references to
> the F# Compiler Service typed tree, which is the size of the migration this contract defines).

## 1. The rule

The editor witnesses the graph exactly as Alex does.

- **One authority.** CCS saturates the PSG. Lattice witnesses it into hover, diagnostics, lenses,
  tokens and proof status; Atelier witnesses it into panes. Neither computes a semantic fact: no
  inference, no symbol resolution of its own, no diagnostic decided by an editor-side rule, no
  prose keyed on a type constructor's name, no fact synthesised from an artifact (DWARF, emitted
  MLIR text, a parallel grammar) that the graph already carries or should.
- **One instance.** One graph service per workspace. The LSP server, the IDE panes and the build
  read the same graph version. A second `Compiler.create ()` beside the language server is two
  saturations of one file with no stated authority.
- **Versioned reads, no caches.** Every answer carries the graph version it was read from
  (project, saturation stamp). The editor holds handles and subscribes to "graph updated"; it does
  not own a typed-tree cache with its own invalidation policy, and it does not decide when or how
  much to re-check.
- **CCS's vocabulary.** Diagnostic codes are `CCS8xxx` minted by the checker or by obligation
  discharge. Node kinds, edge classes and roles are those of `SemanticGraph/Types.fs`. Layouts are
  literal offsets. The wire schema of every projection is derived from the PSG's own type
  definitions (BAREWire) and compiled by both sides of a bridge; no client declares a PSG-shaped
  type of its own.
- **Analyzers are not a category.** A rule over program semantics is either (a) a display of facts
  the graph settles, which is a query in §2, or (b) new semantics, which is a Baker recipe or an
  obligation in CCS. Nothing runs "over the typed tree" in the editor.
- **Presentation is not semantics.** Syntax colouring, folding by brackets, indentation and
  theme are the editor's. A second grammar of the language (TextMate, Lezer, a GPU tokenizer) is
  tolerated only for first-paint colouring and must never feed structure or meaning; every
  additional grammar is a maintenance hazard to be named, and semantic tokens from the graph are
  the truth.

## 2. The query surface (Lattice, server side)

Every row is a read. "Exists" means the fact is on the graph today; "scheduled" names the plan
that lands it; "index" means the data exists but the query that serves it has not been written.

| Query | Serves | Returns | Status |
|---|---|---|---|
| `nodeAt(file, pos)` | every position-keyed feature | the innermost node covering the position and its parent chain | index (every node has `Range` and `Parent`; the index belongs in CCS, not a linear scan in the editor) |
| `hover(node)` | hover, status-bar signature, info panel | `Kind`; `Type` rendered in NTU syntax with dimensions; `LayoutHint` (size, alignment, literal offsets); `ArenaAffinity` and `Resides`; escape/lifetime class; `SRTPResolution`; `IsReachable`; attached obligation nodes and their verdicts | exists for type, SRTP, residence, reachability (as a boolean), obligations; layout exists for string literals and the closure forms as they land; escape class is Composer-interim ([Closure_Retooling_Plan](Closure_Retooling_Plan.md)) |
| `diagnostics(file, version)` | squiggles, problems panel | `{Code; Severity; Range; Message; RelatedNodes; Reachability}` with `effectiveSeverity` tiered by reachability, plus each obligation node's discharge verdict as a diagnostic at its `Source` | exists (`SemanticGraph/Diagnostics.fs`; the obligation ledger `06a`/`06b`); live re-dispatch on edit is scheduled |
| `scope(node)` | completion | bindings, module members and type members visible from the node, each with `Kind`, `Type`, reachability | index (`Parent` chain, `SemanticGraph.Modules`, `TypeDef` members exist) |
| `definition(node)` | go to definition, type definition | the target `Range` of the node's `Reference` edge with role `Definition`, `TypeDefinition` or `IntrinsicImplementation` | exists |
| `references(defNode)` | references, highlights, rename, reference lens | source `Range`s of every `Reference`-class hyperedge into the definition; read/write kind from `Set`/`FieldSet`/`IndexSet` | exists |
| `rename(node, name)` | rename | definition and reference ranges; identifier legality from the CCS lexer | exists (legality query not written) |
| `declarationRoots(file)` | signature lens, outline | `DeclarationRoots` and the structural tree of `ModuleDef`/`TypeDef`/`MemberDef`/`Binding` with `Range` and rendered `Type` | exists |
| `inlayHints(file, range)` | inlay hints | un-annotated `Binding`/`Lambda`/`PatternBinding` nodes with `Type`; `Argument` edges with `Ordinal` matched to the callee's parameter names | exists |
| `semanticTokens(file, range)` | colouring | `(Range, Kind, modifiers)` for every leaf: mutable, unreachable, residence (stack / arena / rodata), has-obligations | exists |
| `signatureHelp(pos)` | signature help | the enclosing `Application`'s callee `Type` as curried groups; the active `Argument` ordinal | exists |
| `pipelineStages(file)` | pipeline hints | `Application` nodes whose callee is `|>`, with the stage `Type`s | exists |
| `layout(node)` | layout table, cache-line map | `TypeLayout` with literal field offsets; residence; the target's cache-line size from the platform description | partial (see hover) |
| `srtpWitness(node)` | witness table | `WitnessResolution` (operator, argument type, resolved member, implementation) | exists |
| `platformBindings(project)` | binding table | `PlatformBinding` nodes with their per-target resolution from `PlatformContext` | exists (nothing is hard-coded in the editor) |
| `obligations(scope)` | proof lens, gutter, ledger view | obligation nodes `{Id; Kind; Logic; Statement; Source; Refs; Body}`, their `Constrains`/`Resides` edges, the design-time cvc5 verdict, and the build-time twin status once the artifact has been re-checked | exists at design time (23 obligations, 23 unsat on HelloProof); twin status is the build-time dispatch |
| `provenance(node)` / `provenance(op)` | pipeline inspector, source↔MLIR navigation | the emitted op(s) a node was witnessed into, and back | scheduled (only `clef.obligations` anchors are reified on ops today; the `loc()` carrier is the witness's to stamp) |
| `reachability(node)` | dimming, per-target matrix | the per-target reachability bitvector and the Live/Latent/Fresh state | scheduled (`IsReachable: bool` today; [PSG_to_PHG_Plan](PSG_to_PHG_Plan.md) Phase 1) |
| `project(fidproj)` | workspace peek, explorer, status | ordered sources, dependencies, target, platform template, output kind, as CCS's loader returns them | exists (`Project/FidprojLoader.fs`, `ProjectChecker.fs`); the editor parses nothing |
| `graphUpdated` (notification) | everything | the new graph version for (project, file) | scheduled |

Formatting stays syntactic and stays outside the contract. The one FCS-shaped dependency a
formatter brings (Fantomas over the F# syntax tree) is noted, not endorsed.

## 3. The host surface (Atelier)

Atelier adds panes, not facts. Each pane reads one of these.

| Surface | Reads | Owner | Status |
|---|---|---|---|
| Graph projection export | the saturated graph (nodes with annotations, the hyperedge set, obligations) serialised under a BAREWire schema derived from the PSG's type definitions | CCS (export), BAREWire (schema) | scheduled; today the JSON phase artifacts `01_psg0` … `05_psg2`, `02`/`04` recipes, `06a`/`06b` obligations are files |
| Phase comparison | per-phase snapshots and the `ccs_diff` artifacts, with soft-delete reachability marks | CCS | exists as files |
| Pipeline inspector | node → witnessed op → pathway artifact → address | Composer (witness provenance), the pathway (addresses) | scheduled with `provenance` |
| Continuation inspector | the frame node of the suspension recipe: delimiter edge, cuts with discriminant values, live-across slots at literal offsets, segments, resumption edge; plus the live process's frame bytes read at those offsets | CCS (frame), the debug adapter (bytes) | scheduled ([Design_Supersession_Register](Design_Supersession_Register.md), Phase 3); there is no continuation runtime and no lifecycle event to listen for |
| Flow-loss and cost views | per-node critical path, per-loop serialisation counts, placed as saturation annotations; substrate cost models as declared fields of the platform description | CCS (annotations), platform description (costs) | not designed; if wanted, a CCS saturation pass (precedent: `DepthAnalysis.fs` for combinational depth), never an IDE computation |
| Knowledge layer | the PSG projection (read-only) plus Atelier's own weave and ledger, kept as a second, derived source that cites projections and never carries a fact the graph did not | Atelier (weave, ledger); CCS for any graph fact it wants: stable node identity, semantic delta between versions, an admissible-lowering annotation | not designed; each wanted fact is a CCS deliverable named here, not an inference |
| Build / saturate | a request to the same CCS instance the language server reads; Composer's CLI for pathway artifacts (`composer compile <proj>.fidproj -k`) | CCS, Composer | CLI exists; the in-process request and the daemon do not |
| Transport | standard LSP for editor features; BAREWire frames over the WebView bridge; one protocol module compiled by both sides (the WrenHello pattern) | Atelier (transport), CCS/Lattice (protocol module) | WrenHello proves the bridge with an ASCII encoding; the BAREWire codec compiled under both sides is the next step |
| What-if saturation | the solution re-saturated under a hypothetical target set, for migration proposals | CCS | not designed |

## 4. What the editor stops doing

Retired outright, because the graph does not carry the fact or the platform has no such thing:
F# Interactive and every `fsi.*` surface (Clef has no REPL); MSBuild, `dotnet` tasks and
`coreclr` launch; F1 help URLs into the .NET API; the .NET test explorer; the FSAC analyzer and
linter policy block pushed as settings; `.ionide` workspace configuration; client-side project
discovery over `.fsproj`; `fsharp/*` private protocol. Replaced by the graph: editor-owned graph
caches and invalidation; hover prose keyed on type names; the hard-coded platform-binding list;
DWARF-derived layouts; the coordinator's own compiler instance; PSG-shaped types declared in a
client; a Lezer grammar or GPU tokenizer as a source of structure. Extensions beyond standard LSP
are named here first, under one namespace, `clef/*`, and each is a focus-and-observe pair over a
`NodeId`; `fidelity/*` and `fsnative/*` sketches elsewhere are superseded by this section.

## 5. Where the forks stand (measured 2026-09-04)

| Repo | What it is | Post-fork work | Authority it assumes |
|---|---|---|---|
| ClefAutoComplete | FsAutoComplete at v0.82.0 (2025-12-16) | 11 commits: a rename (with mangled upstream URLs as the tell) and a ~3,200-line bridge under `HAVE_FNCS` that references `~/repos/fsnative/…`, a path with no compiler, and opens namespaces that no longer exist; the repo does not build | FCS: 401 references, `FSharpChecker` instantiated by the server; only 7 of ~50 handlers ever route to the graph; go-to-definition by name equality, completion scope-blind, diagnostics minted with invented codes |
| lattice-vscode | ionide-vscode-fsharp 7.30.0 | 5 commits; three rename layers disagree (manifest `lattice-fsharp`, code `fsharp.*`/`ionide-fsnative`, build `ionide`); 53 declared commands have no handler; bundles upstream `fsautocomplete` from NuGet | FSAC over FCS on .NET, in docs, settings, spawn logic and DTOs; README promises `.fidproj`, native type display and FS8xxx codes, none implemented |
| lattice-vim | Ionide-vim | 1 commit: a relabel that stopped halfway; the default Neovim backend cannot initialise (`lattice.setup{}` on an unassigned global; `require("ionide")` of a moved module) | FSAC; regex syntax file asserting a .NET vocabulary; `dotnet fsi` |
| lattice-analyzers | ionide-analyzers | 1 commit: relabel; codes still `IONIDE-001..012`, help links to ionide.io, CI paths dead | FCS typed tree; of 12 rules, four are void under the NTU (null, `System.String`, CLR list, `--langversion`), two suggest residence the graph settles, the rest are §2 queries |
| lattice-vscode-helpers | ionide-vscode-helpers | 4 commits; committed solution references a deleted project | none (generated VS Code bindings); design-irrelevant plumbing |
| FsNativeAutoComplete, Ionide-vim-fsnative | the previous generation under the old name | ClefAutoComplete is FsNativeAutoComplete plus two housekeeping commits; Ionide-vim-fsnative has one commit (MLIR navigation by regex over emitted text, Multi-LSP notes) that lattice-vim lacks and that this contract retires anyway | as above |
| ionide-native-analyzers, fsnative | not repositories; an agent-cache stub and an empty shell | — | — |

The user's description ("barely more than search-and-replace for product names") is verified,
with the qualification that the rename itself is incomplete in every repo and that the one
substantive addition is bound to a compiler that no longer exists.

## 6. The migration position

The rename is the first step and the gate counts it; it is not the migration. The migration is
replacing the assumed authority, and the measured shape of the forks argues against doing that
inside them: FsAutoComplete is an architecture for computing from a typed tree, and routing shims
inside it leave the other forty handlers computing. The position this contract takes:

1. **Write the Lattice server fresh, thin, against CCS.** Standard LSP transport (the protocol
   library, not the FSAC body) plus the query surface of §2 answered by one in-process CCS graph
   service. F# inside Composer's solution first, where CCS already builds; Clef when self-hosting
   reaches it. Retire the FSAC fork's body; keep nothing that computes.
2. **Reduce the clients to registration and Clef views.** lattice-vscode becomes a `LanguageClient`
   over the new server plus the panes that need a client (proof lens, ledger view, reachability
   dimming, project explorer over `project(fidproj)`); lattice-vim becomes the sixty-line
   registration shim it already is once its rename is finished; the helpers repo stays plumbing.
3. **Retire the analyzers repo.** Each surviving rule is a §2 query or a CCS diagnostic; the SDK
   contract (a typed tree handed to third-party code) has no place under the transport rule.
4. **Archive the previous generation** (FsNativeAutoComplete, Ionide-vim-fsnative) and delete the
   two non-repositories (ionide-native-analyzers, fsnative).
5. **Atelier reads through the same server and the same export.** Its host-side facts are named in
   §3; those not designed (flow-loss annotations, stable identity, semantic delta, what-if
   saturation) are CCS deliverables to be designed in `phg/`, not computed in the IDE.

Decisions this contract leaves to you: whether the front end of Atelier can be Clef through the
JSIR pathway (it needs a reactive surface JSIR does not yet carry; until then the front end is F#
through Fable, a .NET dependency the docs must name as interim); the Transcribe naming conflict
between Atelier's binding ingestion and Composer's source absorption; and which of the
knowledge-layer facts CCS should own at all.

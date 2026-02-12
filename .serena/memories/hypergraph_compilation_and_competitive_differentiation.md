# Hypergraph Compilation and Competitive Differentiation

> **Created**: February 2026
> **Context**: Keystone's hypergraph-native compilation model vs. industry "graph compiled" approaches.

## The Hypergraph Compilation Model

Keystone's compilation artifacts are hypergraph-native. Where standard graphs have edges connecting pairs of nodes, hypergraphs have hyperedges connecting *sets* of nodes. This distinction is structurally significant throughout the architecture:

- **Interaction net ports** connect multiple agents simultaneously - these are hyperedges
- **Incremental stabilization wavefronts** touch multiple nodes across multiple substrates in a single logical step
- **BAREWire contracts** at substrate boundaries are multi-party agreements between producer and consumer node sets
- **Proof obligations** spanning multiple PSG nodes attach to sets of nodes as invariants over subgraphs

The PSG (Program Semantic Graph) and interaction net representation are hypergraph-native, which provides a richer representation than MLIR's standard region/block/operation structure.

## What "Graph Compiled" Means in Industry vs. Keystone

Industry approaches (e.g., Modular/Mojo, XLA, TVM) use "graph compilation" to mean: take an ML model's computational graph and optimize/lower it to hardware. The graph is the *model* (an external artifact), while the language itself remains conventional control-flow (Python or a Python superset).

Keystone's approach is fundamentally different: the *program itself* is a graph. The PSG is the compilation artifact. Interaction nets are the evaluation model. Incremental<'T> is a dependency hypergraph spanning substrates.

| Dimension | Industry graph compilation | Keystone |
|---|---|---|
| What's a graph | The ML model (external artifact) | The program itself (the PSG) |
| Language model | Conventional control-flow | Graph-native - the program IS the graph |
| Graph scope | ML inference/training operations | All computation - any pure functional subgraph |
| Evaluation | Standard execution + graph optimization for models | Interaction net reduction (graph rewriting IS computation) |
| Hardware targeting | Graph partitioning of ML ops across devices | Dimensional types on the hypergraph inform substrate dispatch for arbitrary computation |
| Scheduling | Ahead-of-time graph optimization | Live runtime structure with incremental wavefront propagation |
| Proof obligations | None | Lemma-carrying through the hypergraph structure |

## Proof-Aware Compilation (F* / SMT Connection)

The connection between Keystone and F*'s proof system enables proof obligations to flow through the hypergraph. This means the PSG carries not just type information and dimensional qualifiers but also proof terms and lemmas.

Don Syme was resistant to creating a formal F*/F# bridge, likely because it risked pulling F#'s pragmatic positioning toward the academic end. From Keystone's position this concern does not apply - Keystone's audience (systems polyglots, hardware engineers, formal methods practitioners) values the rigor. The Rust audience in particular understands "the compiler proves properties of your program" as a concrete value proposition.

Proof-carrying compilation through a hypergraph structure enables:
- Invariants that span subgraphs (a proof obligation attached to a set of PSG nodes)
- Substrate-crossing proofs (a property verified on the CPU portion that guarantees safety of the FPGA portion)
- Incremental proof checking (if a subgraph's inputs haven't changed, its proofs don't need reverification)

## Architectural Differentiation

Five capabilities that are structurally unique to the hypergraph-native approach:

1. **The program IS the graph**: the language is graph-native by design, meaning the PSG is the primary compilation artifact for all computation, not just ML models.

2. **Proof obligations on the graph**: the F*/SMT connection means the hypergraph carries lemmas and proof terms through compilation. This requires dependent or refinement types at the language level.

3. **Interaction net evaluation**: graph rewriting as the computation model is a different execution semantics from conventional eager evaluation. The program compiles to a graph that reduces via local rewriting rules.

4. **Dimensional hyperedges**: type system annotations on the graph carry hardware-relevant information (memory space, access pattern, numeric format) that informs substrate dispatch for arbitrary computation.

5. **Incremental stabilization as scheduling**: the hypergraph is a live runtime structure where wavefronts propagate changes across substrates, enabling dynamic scheduling tied to the dependency structure.

## Related Blog Material

- SpeakEZ Blog: "Proof-Aware Compilation" - the F*/Keystone bridge and lemma-carrying
- SpeakEZ Blog: "Hyping Hypergraphs" - the hypergraph structure beyond standard MLIR

## Cross-References

- `keystone_language_identity_and_vision` - Language thesis and naming
- `firefly_multi_substrate_fanout_architecture` - Multi-substrate fan-out (the substrates the hypergraph spans)
- `ntu_dts_lingua_franca` - Dimensional types (the annotations on hyperedges)
- `psg_control_flow_vs_data_flow_witness_architecture` - Control-flow / data-flow pivot
- `coeffect_analysis` - Coeffect infrastructure

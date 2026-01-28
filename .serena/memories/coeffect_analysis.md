# Coeffects - Pre-Computed Analysis Results from PSGElaboration

> **Related:** `/home/hhh/repos/Firefly/docs/Coeffect_Analysis_Architecture.md`  
> **Context:** Firefly Compiler - MiddleEnd Architecture  
> **Date:** January 28, 2026

---

## What Are Coeffects?

**Coeffects are the OUTPUTS of PSGElaboration passes.**

PSGElaboration is a series of analysis passes in Firefly's MiddleEnd (above Alex in the pipeline). These passes analyze the fully-elaborated PSG structure and produce pre-computed results. These pre-computed results are called "coeffects."

```
FNCS → PSGElaboration Passes → Coeffects (packaged outputs) → Alex Witnesses (read coeffects)
```

---

## Key Architectural Principle: "Mise-en-Place"

> **Mise-en-place** (French): "Everything in its place" - prep work done before cooking begins.

In Firefly:
- **Prep work (PSGElaboration):** ALL analysis happens here - SSA assignment, mutability analysis, capture analysis, etc.
- **Cooking (Alex):** Witnesses READ pre-computed coeffects and EMIT MLIR. NO analysis during emission.

**Alex witnesses are NOT analysis engines. They are observers that read pre-computed data.**

---

## PSGElaboration Passes and Their Outputs (Coeffects)

PSGElaboration runs multiple passes over the PSG. Each pass produces outputs that become coeffects:

| Pass | Output (Coeffect) | Type | Purpose |
|------|-------------------|------|---------|
| **SSA Assignment** | SSA mappings | `Map<NodeId, SSA list>` | Pre-assigns SSAs to every PSG node based on structural analysis |
| **Mutability Analysis** | Mutable bindings | `Set<NodeId>` | Identifies which bindings are mutable (for Seq internal state, ref cells) |
| **Capture Analysis** | Closure layouts | `ClosureLayout` | Complete closure struct layout (captures, heap allocation SSAs, extraction SSAs) |
| **Pattern Binding Analysis** | Binding scopes | Pattern binding SSAs | Match expression decomposition SSAs |
| **String Collection** | String table | Literal index mappings | String literals for data section |
| **Yield State Analysis** | Seq state indices | State machine layout | Seq MoveNext state machine structure |

**CRITICAL:** These are PASSES that run in PSGElaboration. Alex does NOT run these passes. Alex READS their outputs.

---

## SSA Assignment: Structural Analysis, Not Runtime Computation

The SSA Assignment pass computes EXACTLY how many SSAs each PSG node needs based on its structure.

**Example from `/src/MiddleEnd/PSGElaboration/SSAAssignment.fs`:**

```fsharp
/// Compute SSA cost for SeqExpr based on PSG structure
let private computeSeqExprSSACost (graph: SemanticGraph) (bodyId: NodeId) 
                                  (captures: CaptureInfo list) : int =
    let numCaptures = List.length captures
    // PSGElaboration READS the PSG subtree to count mutable bindings
    let numInternalState = countMutableBindingsInSubtree graph bodyId
    
    // Structural SSA cost calculation:
    // 5 base ops (zero, undef, insert state, addressof, insert code_ptr)
    // + 1 per capture (InsertValue)
    // + 2 per internal state (const zero + InsertValue)
    5 + numCaptures + (numInternalState * 2)

/// Count mutable bindings in PSG subtree (for Seq internal state)
let rec private countMutableBindingsInSubtree (graph: SemanticGraph) 
                                              (nodeId: NodeId) : int =
    match Map.tryFind nodeId graph.Nodes with
    | None -> 0
    | Some node ->
        let thisCount =
            match node.Kind with
            | SemanticKind.Binding (_, isMutable, _, _) when isMutable -> 1
            | _ -> 0
        let childCount =
            node.Children
            |> List.sumBy (fun childId -> countMutableBindingsInSubtree graph childId)
        thisCount + childCount
```

**Key Insight:** PSGElaboration READS the PSG structure (e.g., "count mutable bindings in subtree") and computes exact SSA requirements BEFORE Alex starts. This is NOT runtime analysis - it's structural analysis of the semantic graph.

---

## How Alex Witnesses Use Coeffects

Witnesses receive coeffects through `WitnessContext`:

```fsharp
type WitnessContext = {
    Coeffects: TransferCoeffects  // ← Pre-computed by PSGElaboration
    Accumulator: MLIRAccumulator
    Graph: SemanticGraph
    Zipper: PSGZipper
}

/// TransferCoeffects packages PSGElaboration outputs
type TransferCoeffects = {
    SSA: SSAAssignment              // ← From PSGElaboration SSA Assignment pass
    MutableBindings: Set<NodeId>    // ← From PSGElaboration Mutability Analysis pass
    ClosureLayouts: Map<NodeId, ClosureLayout>  // ← From PSGElaboration Capture Analysis pass
    PatternBindings: Map<NodeId, SSA list>      // ← From PSGElaboration Pattern Binding pass
    StringTable: Map<string, int>               // ← From PSGElaboration String Collection pass
    Platform: Platform                          // ← Target platform context
}
```

**Witnesses READ from coeffects:**

```fsharp
let witnessSeqExpr (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    // READ pre-assigned SSAs from coeffects (PSGElaboration already assigned them)
    let ssas = getNodeSSAs node.Id ctx.Coeffects.SSA
    
    // READ mutable bindings from PSG (PSGElaboration already counted them)
    let internalState = extractMutableBindings ctx.Graph bodyId ctx.Coeffects.SSA arch
    
    // Delegate MLIR emission to Pattern (NO analysis, just emission)
    match tryMatch (pBuildSeqStruct codePtr captures internalState ssas arch) ... with
    | Some ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
    | None -> WitnessOutput.error "SeqExpr pattern match failed"
```

**Witnesses do NOT:**
- Compute SSA counts (they lookup pre-assigned SSAs from `ctx.Coeffects.SSA`)
- Analyze mutability (they read mutable bindings from PSG that PSGElaboration already identified)
- Decide closure layouts (they lookup from `ctx.Coeffects.ClosureLayouts`)
- Perform ANY analysis (they observe and emit)

---

## Pipeline Position

```
┌─────────────────────────────────────────────────────┐
│ FNCS (F# Native Compiler Services)                  │
│ - Type checking                                     │
│ - Intrinsic elaboration                            │
│ - Baker saturation                                 │
│ → Produces: Fully elaborated PSG                   │
└─────────────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────────────┐
│ PSGElaboration Passes (Firefly MiddleEnd)          │
│ - SSA Assignment Pass                              │
│ - Mutability Analysis Pass                         │
│ - Capture Analysis Pass                            │
│ - Pattern Binding Analysis Pass                    │
│ - String Collection Pass                           │
│ → Produces: Coeffects (pre-computed results)       │
└─────────────────────────────────────────────────────┘
                    ↓
┌─────────────────────────────────────────────────────┐
│ Alex Witnesses (Firefly MiddleEnd)                 │
│ - READ coeffects from TransferCoeffects            │
│ - OBSERVE PSG structure via Zipper                 │
│ - EMIT MLIR via Patterns                           │
│ → Produces: MLIR                                   │
└─────────────────────────────────────────────────────┘
```

**PSGElaboration sits ABOVE Alex.** All analysis happens in PSGElaboration. Alex consumes the results.

---

## Why "Coeffects" (Not "Effects")?

The term "coeffect" comes from programming language theory:

- **Effect:** What a computation PRODUCES (output, side effects, exceptions)
- **Coeffect:** What a computation REQUIRES (inputs, context, resources)

In Firefly:
- PSGElaboration passes PRODUCE analysis results
- Alex witnesses REQUIRE those results to emit MLIR
- The analysis results are "required inputs" to Alex (coeffects), not "produced outputs"

From Alex's perspective, coeffects are CONTEXT - they describe what Alex needs to know about the PSG to generate correct MLIR.

---

## The Control-Flow ↔ Dataflow Pivot

Coeffects enable informed translation between representations:

- **F# source:** Declarative, dataflow-oriented (immutability, expressions, purity)
- **Native code:** Imperative, control-flow-oriented (mutability, statements, side effects)

PSGElaboration analyzes the declarative PSG structure and produces coeffects that describe how to map it to imperative native code:
- Which variables need SSA versioning
- Which bindings are mutable (need memory locations)
- Which closures need heap allocation vs stack allocation
- Which strings go in the data section

Alex uses these coeffects to generate efficient MLIR without re-analyzing the PSG.

---

## "Only Pay for What You Use"

Coeffect passes are demand-driven:
- No seq expressions → No yield state analysis pass
- No closures with captures → No closure layout pass
- No pattern matches → No pattern binding analysis pass

Each pass checks if relevant PSG nodes exist before running.

---

## Common Misconceptions (Anti-Patterns)

### ❌ WRONG: "Witnesses compute SSA counts"

```fsharp
// WRONG - Witness computing SSA requirements
let witnessSeqExpr ctx node =
    let ssaCount = 5 + captures.Length + (internalState.Length * 2)
    let ssas = allocateSSAs ssaCount  // NO! SSAs already assigned by PSGElaboration
```

**Correct:** Witnesses READ pre-assigned SSAs from `ctx.Coeffects.SSA`

### ❌ WRONG: "Witnesses analyze mutability"

```fsharp
// WRONG - Witness analyzing which bindings are mutable
let witnessSeqExpr ctx node =
    let mutableBindings = analyzeMutability bodySubtree  // NO! PSGElaboration already did this
```

**Correct:** Witnesses READ mutable bindings from PSG (PSGElaboration already identified them)

### ❌ WRONG: "Coeffects are computed during Alex"

```fsharp
// WRONG - Running analysis during Alex
let witnessSeqExpr ctx node =
    let coeffects = runCoeffectAnalysis node  // NO! Coeffects already computed by PSGElaboration
```

**Correct:** Coeffects are PRE-COMPUTED by PSGElaboration before Alex starts

### ❌ WRONG: "Need future coeffects"

```fsharp
// WRONG - Waiting for "future coeffects"
// TODO: Extract internal state from lambda analysis coeffect
let internalState = []  // Placeholder until coeffect available
```

**Correct:** If data isn't in coeffects, it's in the PSG itself (read from PSG nodes)

---

## Related Memories

- `psg_elaboration_fold_architecture` - How PSGElaboration produces elaborated PSG
- `alex_compositional_architecture_elements_patterns_witnesses` - How witnesses use coeffects
- `psg_awareness_implementation_protocol` - How to implement witnesses that read PSG/coeffects

---

## Summary

**Coeffects are outputs of PSGElaboration passes, not analysis phases in Alex.**

1. **PSGElaboration** runs multiple analysis passes (SSA Assignment, Mutability Analysis, Capture Analysis, etc.)
2. **Outputs** of these passes are packaged into `TransferCoeffects`
3. **Alex witnesses** READ coeffects and EMIT MLIR
4. **Witnesses do NOT analyze** - they observe pre-computed data

> **"Mise-en-place"** - All prep work (analysis) done by PSGElaboration before emission (Alex) begins.

---

**This is the correct understanding of coeffects. Any documentation suggesting "coeffect analysis during Alex" is pollution and must be corrected.**

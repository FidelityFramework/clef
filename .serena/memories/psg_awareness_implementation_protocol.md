# PSG Awareness Implementation Protocol (NO GUESSING ALLOWED)

**Date:** January 28, 2026  
**Context:** Firefly Compiler - Alex Witness Implementation  
**Status:** ARCHITECTURAL MANDATE

---

## The Cardinal Rule

**GUESSING IS NOT ALLOWED. THIS IS ARCHITECTURE.**

When implementing any witness or pattern that needs to understand PSG structure, you MUST follow this exact protocol.

---

## Two Sources of Truth

Understanding witness implementation requires consulting TWO sources:

1. **FNCS (fsnative):** Defines PSG STRUCTURE (semantic node types, what data each node carries)
2. **PSGElaboration (Firefly):** Computes COEFFECTS (SSA assignments, mutability analysis, capture layouts)

**CRITICAL:** Do not confuse these. FNCS creates the PSG. PSGElaboration analyzes it and produces coeffects. Alex reads BOTH.

---

## Step 1: Read FNCS Design Documents (via Serena)

FNCS defines the PSG structures that Alex witnesses. ALWAYS check Serena memories for FNCS architectural decisions:

```
mcp__serena-local__read_memory for relevant FNCS memories
```

**Example for Lazy:**
- Memory: `lazy_thunk_calling_convention` (FNCS)
- Document: `/home/hhh/repos/fsnative/docs/fidelity/FNCS_Lazy_Seq_Coroutine_Intrinsics.md`

These documents specify:
- What PSG semantic nodes are created (e.g., `LazyExpr`, `LazyForce`)
- Whether operations are elaborated or atomic
- Calling conventions (how thunks are called)
- Struct layouts (semantic structure, e.g., {computed, value, code_ptr, captures})

**What FNCS docs do NOT specify:**
- Exact SSA counts (that's PSGElaboration structural analysis)
- Which SSAs map to which nodes (that's PSGElaboration SSA Assignment pass)
- Whether bindings are mutable (that's PSGElaboration Mutability Analysis pass)

---

## Step 2: Examine PSG Source Code (Types, Collections, Applications)

The PSG structure is DEFINED in FNCS source code. Read the actual implementation:

### Critical Files:

**`~/repos/fsnative/src/Compiler/PSGSaturation/SemanticGraph/Types.fs`**
- Defines `SemanticKind` discriminated union
- Shows what data each semantic node carries
- Example: `LazyExpr of body: NodeId * captures: CaptureInfo list`
- Example: `LazyForce of lazyValue: NodeId`
- Example: `SeqExpr of body: NodeId * captures: CaptureInfo list`

**`~/repos/fsnative/src/Compiler/NativeTypedTree/Expressions/Collections.fs`**
- Shows how FNCS creates semantic nodes for collection-like operations
- Example: LazyExpr creation with thunk Lambda

**`~/repos/fsnative/src/Compiler/NativeTypedTree/Expressions/Applications.fs`**
- Shows how FNCS creates semantic nodes for function applications
- Example: LazyForce creation from `Lazy.force` call

**`~/repos/fsnative/src/Compiler/NativeTypedTree/NativeTypes.fs`**
- Defines `CaptureInfo` structure (lines 874-882):
```fsharp
type CaptureInfo = {
    Name: string
    Type: NativeType          // ← Resolved by FNCS type checker
    IsMutable: bool
    SourceNodeId: NodeId option
}
```

---

## Step 3: Understand PSGElaboration Coeffects (Firefly)

PSGElaboration (in Firefly's MiddleEnd, ABOVE Alex) runs analysis passes and produces coeffects.

### Critical File:

**`/home/hhh/repos/Firefly/src/MiddleEnd/PSGElaboration/SSAAssignment.fs`**
- Shows how SSA assignment works via structural analysis
- Example: `computeSeqExprSSACost` function:

```fsharp
let private computeSeqExprSSACost (graph: SemanticGraph) (bodyId: NodeId) 
                                  (captures: CaptureInfo list) : int =
    let numCaptures = List.length captures
    // PSGElaboration READS PSG structure to count mutable bindings
    let numInternalState = countMutableBindingsInSubtree graph bodyId
    
    // Structural cost: 5 base + captures + internal state
    5 + numCaptures + (numInternalState * 2)
```

**Key Insight:** PSGElaboration performs STRUCTURAL ANALYSIS of the PSG to compute exact SSA requirements. This happens in Firefly, NOT in FNCS.

**`/home/hhh/repos/Firefly/src/MiddleEnd/PSGElaboration/Coeffects.fs`**
- Defines coeffect types: `NodeSSAAllocation`, `ClosureLayout`, `DULayout`
- Shows that coeffects are PRE-COMPUTED outputs, not analysis during witnessing

---

## Step 4: Inspect PSG Intermediates (Samples)

After FNCS runs and PSGElaboration completes, intermediates are written to:

```
samples/console/FidelityHelloWorld/<sample>/target/intermediates/
```

**Ordinal Artifacts (Pipeline Order):**
- `01_psg0.json` - Initial PSG with reachability (PSG₀)
- `02_intrinsic_recipes.json` - Intrinsic elaboration recipes
- `03_psg1.json` - PSG after intrinsic fold-in (PSG₁)
- `04_saturation_recipes.json` - Baker saturation recipes
- `05_psg2.json` - **Final saturated PSG to Alex (PSG₂)** ← THIS IS WHAT ALEX SEES
- `06_coeffects.json` - **Coeffects from PSGElaboration** ← SSA assignments, layouts, etc.

**For Lazy specifically:**
- Sample 14: `samples/console/FidelityHelloWorld/14_Lazy/`
- Inspect `05_psg2.json` to see LazyExpr and LazyForce nodes
- Inspect `06_coeffects.json` to see SSA assignments for those nodes

The PSG JSON shows:
- Node structure (what FNCS created)
- What fields each node has
- Whether nodes are single or elaborated subgraphs

The coeffects JSON shows:
- SSA assignments (what PSGElaboration computed)
- Closure layouts (what PSGElaboration computed)
- Mutability info (what PSGElaboration computed)

---

## Step 5: Understand Single Node vs Elaborated Subgraph

This is CRITICAL and easy to get wrong by guessing.

**Single Semantic Node:**
- One PSG node of specific SemanticKind
- Alex witness sees it once
- Example: `LazyExpr(body, captures)`, `LazyForce(lazyValue)`

**Elaborated Subgraph:**
- FNCS (via Baker saturation) expands high-level operation into multiple PSG nodes
- Creates If/Then/Else, loops, state machines, etc.
- Alex witnesses multiple nodes in structure
- Example: String interpolation → concat operations

**How to Know:**
1. Check `Types.fs` - Is it a SemanticKind variant? → Single node
2. Check Baker saturation recipes (`04_saturation_recipes.json`) - Does it have a recipe? → Elaborated
3. Check FNCS docs - Does it say "elaborated" or "atomic"?

---

## Step 6: Understand Where Data Comes From

When implementing a witness, you need to know where each piece of data originates:

| Data | Source | How to Access |
|------|--------|---------------|
| **Semantic node type** | FNCS | `node.Kind` pattern match |
| **Node children (bodyId, etc.)** | FNCS | Extract from `node.Kind` data |
| **Captures (CaptureInfo list)** | FNCS | In node data (e.g., `LazyExpr(body, captures)`) |
| **Capture types** | FNCS | `capture.Type` (from CaptureInfo) |
| **SSA assignments** | PSGElaboration | `ctx.Coeffects.SSA` lookup |
| **Closure layouts** | PSGElaboration | `ctx.Coeffects.ClosureLayouts` lookup |
| **Mutable bindings** | PSG structure | Read from PSG nodes (PSGElaboration already identified them) |
| **Platform/Architecture** | TransferCoeffects | `ctx.Coeffects.Platform` |

**Example - SeqWitness:**

```fsharp
let witnessSeqExpr (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    // Match semantic node structure (FNCS created this)
    match tryMatch pSeqExpr ctx.Graph node ctx.Zipper ctx.Coeffects.Platform with
    | None -> WitnessOutput.skip
    | Some ((bodyId, captures), _) ->
        // Get SSAs (PSGElaboration assigned these via structural analysis)
        let ssas = getNodeSSAs node.Id ctx.Coeffects.SSA
        
        // Get capture types (FNCS provided these in CaptureInfo)
        let captureVals = captureInfosToVals captures ctx.Coeffects.SSA ctx.Graph arch
        
        // Read mutable bindings from PSG (PSGElaboration already identified them)
        let internalState = extractMutableBindings ctx.Graph bodyId ctx.Coeffects.SSA arch
        
        // Delegate to Pattern for MLIR emission
        match tryMatch (pBuildSeqStruct codePtr captureVals internalState ssas arch) ... with
        | Some ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
```

**Key Points:**
- `bodyId` and `captures` come from FNCS (PSG node structure)
- `ssas` come from PSGElaboration (coeffects)
- `capture.Type` comes from FNCS (CaptureInfo)
- Mutable bindings are READ from PSG (PSGElaboration already counted them in SSA cost calculation)

---

## Step 7: Verify Calling Conventions (FNCS)

For operations involving function calls, FNCS defines calling conventions.

**Lazy Thunk Example (from FNCS):**

```
Thunk Signature: llvm.func @thunk(%lazy_ptr: ptr) -> T

Force Operation:
  %code_ptr = llvm.extractvalue %lazy[2]
  %lazy_ptr = llvm.alloca (const 1)
  llvm.store %lazy, %lazy_ptr
  %result = llvm.call %code_ptr(%lazy_ptr) : (ptr) -> T
```

This is NOT something you infer - it's SPECIFIED in FNCS documentation.

**What PSGElaboration Provides:**
- The EXACT SSAs for each operation (extract SSA, alloca SSA, store SSA, call SSA)
- These SSAs were computed by `computeLazyForceSSACost` in PSGElaboration

---

## Step 8: Implement Using Established Elements/Patterns

Once you understand the PSG structure and coeffects, implement using ONLY established Elements/Patterns:

```fsharp
let pBuildLazyForce (lazySSA: SSA) (resultSSA: SSA) (ssas: SSA list) (arch: Architecture)
                    : PSGParser<MLIROp list * TransferResult> =
    parser {
        // Use SSAs that PSGElaboration pre-assigned
        let codePtrSSA = ssas.[0]
        let constOneSSA = ssas.[1]
        let ptrSSA = ssas.[2]
        // resultSSA passed as parameter (ssas.[3])
        
        // Use ESTABLISHED Elements (no hand-jamming)
        let! extractCodePtrOp = pExtractValue codePtrSSA lazySSA [2]  // MLIRElements
        let! constOneOp = pConstI constOneSSA 1L                       // ArithElements
        let! allocaOp = pAlloca ptrSSA (Some 1)                       // LLVMElements
        let! storeOp = pStore lazySSA ptrSSA                          // LLVMElements
        let! callOp = pIndirectCall resultSSA codePtrSSA [ptrSSA]    // LLVMElements
        
        return ([extractCodePtrOp; constOneOp; allocaOp; storeOp; callOp], 
                TRValue { SSA = resultSSA; Type = mlirType })
    }
```

**Notice:**
- We READ SSAs from the list (PSGElaboration assigned them)
- We do NOT compute how many SSAs we need (PSGElaboration already did that)
- We use Elements to emit MLIR (no hand-jamming)

---

## What NOT To Do (ANTIPATTERNS)

### ❌ Guessing PSG Structure

```fsharp
// WRONG - Assuming LazyForce is elaborated without checking FNCS
match node.Kind with
| "LazyForce" ->
    // Assume we'll see If/Then/Else nodes...
    // Maybe there's a computed flag check?
    // Probably need to update the lazy struct?
```

**Why wrong:** LazyForce is a SINGLE semantic node. FNCS does NOT elaborate it.

### ❌ Computing SSA Counts

```fsharp
// WRONG - Computing SSA requirements in witness
let ssaCount = 5 + captures.Length
let ssas = allocateSSAs ssaCount
```

**Why wrong:** SSA counts were computed by PSGElaboration via structural analysis. Witnesses READ pre-assigned SSAs from `ctx.Coeffects.SSA`.

### ❌ Attributing SSA Assignment to FNCS

```fsharp
// WRONG - Saying "SSAs from FNCS"
// SSA counts come from FNCS coeffects...
```

**Why wrong:** FNCS creates PSG structure. PSGElaboration (Firefly) assigns SSAs. These are separate phases.

### ❌ Creating "Future Coeffects" Placeholders

```fsharp
// WRONG - Waiting for "future coeffects"
// TODO: Extract internal state from lambda analysis coeffect
let internalState = []  // Placeholder until coeffect available
```

**Why wrong:** If data isn't in coeffects, it's in the PSG itself. Read from PSG nodes. PSGElaboration already did the counting (e.g., `countMutableBindingsInSubtree`), witnesses just READ the results.

---

## The Protocol in Action: LazyWitness Case Study

**What I Was Asked:** Implement LazyWitness correctly

**What I Did WRONG Initially:**
- Assumed LazyForce would be elaborated with If/Then/Else
- Created control flow patterns for memoization checking
- Guessed at struct layout and calling conventions

**What I Should Have Done (This Protocol):**

1. ✅ Read Serena memory `lazy_thunk_calling_convention` (FNCS)
2. ✅ Read FNCS doc `FNCS_Lazy_Seq_Coroutine_Intrinsics.md` (FNCS)
3. ✅ Examined `Types.fs` → Found `LazyExpr` and `LazyForce` are single nodes (FNCS)
4. ✅ Examined `Collections.fs` → Saw LazyExpr creation (FNCS)
5. ✅ Examined `Applications.fs` → Saw LazyForce creation (FNCS)
6. ✅ Checked `SSAAssignment.fs` → Saw `computeLazyForceSSACost` returns fixed 4 (PSGElaboration)
7. ✅ Checked sample 14 intermediates → Confirmed single nodes in PSG₂, SSAs in coeffects
8. ✅ Implemented using established Elements → No hand-jamming, read pre-assigned SSAs

**Result:** Correct implementation in ~40 lines, using established architecture.

---

## Key Resources

### Serena Memories (FNCS Semantics)
- Use `mcp__serena-local__list_memories` to find relevant memories
- Search for feature-specific memories (e.g., `lazy_thunk_calling_convention`, `fncs_seq_generator_protocol`)

### FNCS Documentation (PSG Structure)
- `/home/hhh/repos/fsnative/docs/fidelity/FNCS_*.md`
- Authoritative semantic contracts for what FNCS creates

### FNCS Source Code (PSG Node Definitions)
- `~/repos/fsnative/src/Compiler/PSGSaturation/SemanticGraph/Types.fs` - SemanticKind definitions
- `~/repos/fsnative/src/Compiler/NativeTypedTree/Expressions/*.fs` - PSG node creation
- `~/repos/fsnative/src/Compiler/NativeTypedTree/NativeTypes.fs` - CaptureInfo, NativeType

### PSGElaboration Source Code (Coeffect Computation)
- `/home/hhh/repos/Firefly/src/MiddleEnd/PSGElaboration/SSAAssignment.fs` - SSA assignment pass
- `/home/hhh/repos/Firefly/src/MiddleEnd/PSGElaboration/Coeffects.fs` - Coeffect type definitions

### PSG Intermediates (Actual Runtime Data)
- `samples/console/FidelityHelloWorld/<sample>/target/intermediates/05_psg2.json` - PSG structure
- `samples/console/FidelityHelloWorld/<sample>/target/intermediates/06_coeffects.json` - Coeffects

---

## Summary

**The Protocol:**
1. Read FNCS design documents (Serena memories) for semantic contracts
2. Examine PSG source code (`Types.fs`, `Collections.fs`, `Applications.fs`) for node structure
3. Examine PSGElaboration source code (`SSAAssignment.fs`, `Coeffects.fs`) for coeffect computation
4. Inspect PSG intermediates (`05_psg2.json`, `06_coeffects.json`) for actual data
5. Understand single node vs elaborated subgraph
6. Understand where each piece of data comes from (FNCS vs PSGElaboration)
7. Verify calling conventions (from FNCS docs)
8. Implement using established Elements/Patterns (read pre-assigned SSAs)

**The Rule:**
> **GUESSING IS NOT ALLOWED. THIS IS ARCHITECTURE.**

Every assumption about PSG structure must be verified against FNCS source code, documentation, or actual PSG intermediates.

Every assumption about coeffects must be verified against PSGElaboration source code or actual coeffect intermediates.

**Two sources of truth:**
- **FNCS:** PSG structure (semantic nodes, captures, types)
- **PSGElaboration:** Coeffects (SSA assignments, layouts, mutability)

---

**This protocol is MANDATORY for all PSG-aware witness implementation.**

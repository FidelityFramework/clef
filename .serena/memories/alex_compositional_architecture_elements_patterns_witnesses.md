# Alex Compositional Architecture: Elements → Patterns → Witnesses

**Date:** January 28, 2026  
**Context:** Firefly Compiler - Alex XParsec Remediation  
**Status:** CANONICAL - Core architectural principle

---

## The Three-Layer Composition Model

Alex generates MLIR through **compositional building** across three layers:

```
Elements (atoms) → Patterns (molecules) → Witnesses (observers)
     ↓                    ↓                      ↓
  pAlloca          pStructWithCaptures    witnessSeqExpr
  pStore           pStructPtrCall         witnessLazyForce
  pExtractValue    pForEachLoop          witnessForEach
  pConstI          pBuildLazyStruct      
  pIndirectCall    pBuildSeqStruct
```

Each layer has a **specific responsibility** and **composes upward**.

---

## Layer 1: Elements (Atoms)

**Location:** `/src/MiddleEnd/Alex/Elements/`  
**Visibility:** `module internal` - Witnesses CANNOT import  
**Purpose:** Atomic MLIR operation emission

**Characteristics:**
- One Element = One MLIR operation
- XParsec state threading for platform/type context
- No control flow logic, no conditional emission
- Examples: `pAlloca`, `pStore`, `pLoad`, `pExtractValue`, `pConstI`, `pIndirectCall`

**Example:**
```fsharp
/// Emit Alloca (stack allocation) operation
let pAlloca (ssa: SSA) (size: int option) : PSGParser<MLIROp> =
    parser {
        let! state = getUserState
        let ty = mapNativeTypeForArch state.Platform.TargetArch state.Current.Type
        return MLIROp.LLVMOp (LLVMOp.Alloca (ssa, ty, size))
    }
```

Elements are the **vocabulary** - individual words, not sentences.

---

## Layer 2: Patterns (Molecules)

**Location:** `/src/MiddleEnd/Alex/Patterns/`  
**Visibility:** `public` - Witnesses call these  
**Purpose:** Reusable compositions of Elements into semantic operations

**Characteristics:**
- Compose multiple Elements into meaningful sequences
- Reusable across witnesses (not witness-specific)
- Still relatively small (10-50 lines typical)
- Return `PSGParser<MLIROp list>` or `PSGParser<MLIROp list * TransferResult>`

**Pattern Categories:**

### Struct Construction Patterns
Patterns for building structs with specific layouts:

```fsharp
/// Lazy struct: {computed: i1, value: T, code_ptr: ptr, captures...}
let pLazyStruct (codePtr: SSA) (captures: Val list) (ssas: SSA list) 
               : PSGParser<MLIROp list> =
    parser {
        let! undefOp = pUndef ssas.[0]
        let! falseConstOp = pConstI ssas.[1] 0L
        let! insertComputedOp = pInsertValue ssas.[2] ssas.[0] ssas.[1] [0]
        let! insertCodeOp = pInsertValue ssas.[3] ssas.[2] codePtr [2]
        // ... insert captures ...
        return undefOp :: falseConstOp :: insertComputedOp :: insertCodeOp :: captureOps
    }
```

### Calling Convention Patterns
Patterns for specific calling conventions:

```fsharp
/// Struct pointer passing: alloca → store → call with pointer
let pStructPtrCall (structSSA: SSA) (codePtrSSA: SSA) (resultSSA: SSA) 
                   (ssas: SSA list) : PSGParser<MLIROp list> =
    parser {
        let! constOneOp = pConstI ssas.[0] 1L
        let! allocaOp = pAlloca ssas.[1] (Some 1)
        let! storeOp = pStore structSSA ssas.[1]
        let! callOp = pIndirectCall resultSSA codePtrSSA [ssas.[1]]
        return [constOneOp; allocaOp; storeOp; callOp]
    }
```

### Control Flow Patterns
Patterns for common control flow idioms:

```fsharp
/// ForEach iteration: while (moveNext()) { body }
let pForEachLoop (seqSSA: SSA) (codePtrSSA: SSA) (bodyOps: MLIROp list) 
                 (ssas: SSA list) : PSGParser<MLIROp list> =
    parser {
        // Alloca + store seq struct
        // While loop with MoveNext condition
        // Body extracts current value + executes bodyOps
        // ...
    }
```

Patterns are **phrases** - common expressions, not full paragraphs.

---

## Layer 3: Witnesses (Observers)

**Location:** `/src/MiddleEnd/Alex/Witnesses/`  
**Visibility:** `public` - Called by traversal orchestration  
**Purpose:** Thin observers that match PSG structure and emit MLIR via Patterns

**Characteristics:**
- **~20-40 lines per witness** (target)
- Match PSG semantic nodes via XParsec
- Delegate MLIR emission to Patterns
- **NO direct Element usage** (use Patterns instead)
- **NO MLIR hand-jamming** (no direct `MLIROp.LLVMOp(...)` construction)

**Canonical Example - LazyWitness.fs:**

```fsharp
module Alex.Witnesses.LazyWitness

open XParsec
open Alex.Patterns.ElisionPatterns  // Import Patterns, NOT Elements
open Alex.XParsec.PSGCombinators
open Alex.Traversal.TransferTypes

/// Witness LazyExpr: Build lazy struct with thunk and captures
let witnessLazyExpr (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    match tryMatch pLazyExpr ctx.Graph node ctx.Zipper ctx.Coeffects.Platform with
    | None -> WitnessOutput.skip
    | Some ((bodyId, captures), _) ->
        let ssas = getNodeSSAs node.Id ctx.Coeffects.SSA
        let codePtr = (* recall from accumulator *)
        let captureVals = getCaptures captures ctx
        
        // Delegate to Pattern - NO direct Element usage
        match tryMatch (pBuildLazyStruct codePtr captureVals ssas ctx.Coeffects.Platform.TargetArch) 
                       ctx.Graph node ctx.Zipper ctx.Coeffects.Platform with
        | Some ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
        | None -> WitnessOutput.error "LazyExpr emission failed"

/// Witness LazyForce: Call thunk via struct pointer passing
let witnessLazyForce (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    match tryMatch pLazyForce ctx.Graph node ctx.Zipper ctx.Coeffects.Platform with
    | None -> WitnessOutput.skip
    | Some (lazyNodeId, _) ->
        let ssas = getNodeSSAs node.Id ctx.Coeffects.SSA
        let lazySSA = (* recall from accumulator *)
        
        // Delegate to Pattern - NO direct Element usage
        match tryMatch (pBuildLazyForce lazySSA ssas.[3] ssas ctx.Coeffects.Platform.TargetArch)
                       ctx.Graph node ctx.Zipper ctx.Coeffects.Platform with
        | Some ((ops, result), _) -> { InlineOps = ops; TopLevelOps = []; Result = result }
        | None -> WitnessOutput.error "LazyForce emission failed"
```

Witnesses are **observers** - they recognize structure and delegate composition.

---

## Pipeline Context: PSGElaboration Provides Coeffects

Before understanding why this architecture works, understand WHERE witnesses get their data.

**The Pipeline:**
```
FNCS → PSGElaboration (analysis passes) → Coeffects → Alex Witnesses (observe + emit) → MLIR
```

**PSGElaboration (above Alex):**
- SSA Assignment Pass: Pre-assigns SSAs to every PSG node via structural analysis
- Mutability Analysis Pass: Identifies which bindings are mutable
- Capture Analysis Pass: Computes complete closure layouts
- Pattern Binding Analysis Pass: Decomposes match expressions
- String Collection Pass: Builds string table for data section

**Witnesses READ pre-computed coeffects:**
```fsharp
type WitnessContext = {
    Coeffects: TransferCoeffects  // ← PSGElaboration outputs
    Accumulator: MLIRAccumulator
    Graph: SemanticGraph
    Zipper: PSGZipper
}

let witnessSeqExpr (ctx: WitnessContext) (node: SemanticNode) : WitnessOutput =
    // READ pre-assigned SSAs (PSGElaboration already computed these)
    let ssas = getNodeSSAs node.Id ctx.Coeffects.SSA
    
    // READ from PSG (PSGElaboration already identified mutable bindings)
    let internalState = extractMutableBindings ctx.Graph bodyId ctx.Coeffects.SSA arch
    
    // DELEGATE emission to Pattern
    match tryMatch (pBuildSeqStruct codePtr captures internalState ssas arch) ... with
    | Some ((ops, result), _) -> { InlineOps = ops; ... }
```

**Witnesses are thin because they DON'T analyze - they READ pre-computed data and EMIT.**

> **"Mise-en-place"** - All analysis (PSGElaboration) done before emission (Alex) begins.

---

## Why This Architecture?

### 1. Prevents "Chock Full of Primitives" Anti-Pattern

**Wrong (Witness with direct Elements):**
```fsharp
// BAD: Witness doing primitive construction
let witnessSeqExpr ctx node =
    let! undefOp = pUndef ssas.[0]           // Element call
    let! constOp = pConstI ssas.[1] 0L       // Element call
    let! insertOp = pInsertValue ...         // Element call
    // 50 more lines of Element calls...
```

**Right (Witness delegates to Pattern):**
```fsharp
// GOOD: Witness delegates composition
let witnessSeqExpr ctx node =
    match tryMatch pSeqExpr ctx.Graph node ... with
    | Some (captures, _) ->
        let captureVals = getCaptures captures ctx
        // Delegate to Pattern
        match tryMatch (pBuildSeqStruct codePtr captureVals ssas arch) ... with
        | Some ((ops, result), _) -> { InlineOps = ops; ... }
```

### 2. Enables Reuse Across Witnesses

Multiple witnesses can reuse the same Pattern:

- `LazyWitness` uses `pStructPtrCall` (struct pointer passing)
- `SeqWitness` uses `pStructPtrCall` (MoveNext calls)
- `ClosureWitness` uses `pStructPtrCall` (closure invocation)

**Pattern is written once, used by many witnesses.**

### 3. Maintains PSG Awareness

Witnesses remain **thin observers** focused on PSG structure:
- Match semantic nodes (SeqExpr, LazyForce, ForEach)
- Extract PSG data (captures, types, children)
- Lookup coeffects (SSAs, platform)
- **Delegate MLIR emission to Patterns**

Witnesses don't "know" MLIR details - Patterns handle that.

### 4. Clear Separation of Concerns

| Layer | Knows About | Does NOT Know About |
|-------|-------------|---------------------|
| **Elements** | MLIR ops, XParsec state | PSG structure, witnesses |
| **Patterns** | Elements, composition | PSG nodes, specific witnesses |
| **Witnesses** | PSG structure, coeffects | MLIR details, Element APIs |

---

## The Library Metaphor

Think of Patterns like a **library organization**:

- **Newspapers/Periodicals (front)**: Simple, frequently used patterns (struct construction)
- **Reference Material (back)**: Complex, domain-specific patterns (state machines, iteration)

Access difficulty scales with complexity:
- Trivial patterns: inline in witness (2-3 Elements)
- Common patterns: Pattern module (5-20 Elements)
- Complex patterns: Potentially sub-folders (50+ Elements)

**Guiding Principle:** If a witness is becoming "chock full of primitives," those primitives should be extracted into a Pattern.

---

## Pattern Extraction Heuristic

When should code move from Witness → Pattern?

### Extract to Pattern if:
1. **Reusable across witnesses** - Multiple witnesses need this composition
2. **Exceeds ~10 Element calls** - Too many primitives in the witness
3. **Domain-specific idiom** - Represents a recognized pattern (e.g., struct pointer passing)
4. **Stable interface** - The composition has a clear input/output contract

### Keep inline in Witness if:
1. **Witness-specific** - Only one witness will ever use it
2. **Very simple (2-3 Elements)** - Not worth abstracting
3. **Highly contextual** - Deeply coupled to specific PSG node structure

**Example Decision:**
- Lazy struct construction: **Extract to Pattern** (reusable, 15+ Elements)
- Extract single capture from CaptureInfo: **Keep inline** (3 lines, witness-specific context)

---

## Composing Up: The Ripple Effect

When primitives compose correctly, benefits ripple upward:

```
Good Elements → Good Patterns → Good Witnesses → Good MLIR → Good Native Code
```

**PRD-11 Example:**
- Flat closure Elements (pFlatClosure)
- Compose into Closure Patterns (pBuildClosure)
- Used by ClosureWitness
- **AND** used by LazyWitness (Lazy = closure + memoization)
- **AND** used by SeqWitness (Seq = extended closure + state)

Getting the Patterns right at the "middle layer" creates positive ripple effects:
- Less code duplication
- Easier maintenance
- Clear architectural boundaries
- Witnesses stay thin

---

## Anti-Patterns to Avoid

### ❌ Witness Using Elements Directly

```fsharp
// WRONG - Witness calling Elements
let witnessSeqExpr ctx node =
    let! alloca = pAlloca ssa (Some 1)    // Element call - TOO LOW LEVEL
    let! store = pStore value ssa         // Element call - TOO LOW LEVEL
```

### ❌ Pattern That's Too Witness-Specific

```fsharp
// WRONG - Pattern knows about specific witness concerns
let pBuildSeqExprForSample15 (node: SemanticNode) ... =
    // If it's "for Sample 15" or mentions specific witness, it's too specific
```

### ❌ Mixing Layers

```fsharp
// WRONG - Witness mixing Pattern calls with Element calls
let witnessSeqExpr ctx node =
    let! patternResult = pBuildSeqStruct ...  // Pattern call (good)
    let! allocaOp = pAlloca ssa (Some 1)      // Element call (BAD - mixing layers)
```

---

## Key Memories

Related memories that must reflect this architecture:

- `alex_element_pattern_witness_architecture` - Core three-layer model
- `xparsec_correct_usage_pattern` - XParsec in all three layers
- `psg_awareness_implementation_protocol` - Witnesses observe PSG, delegate emission
- `compose_from_standing_art_principle` - Reuse existing Patterns

---

## Summary

The compositional architecture is:

1. **Elements** provide atomic MLIR operations (module internal)
2. **Patterns** compose Elements into reusable semantic operations (public)
3. **Witnesses** match PSG structure and delegate to Patterns (public, ~20-40 lines)

**Witnesses are NOT construction engines - they are thin observers that recognize PSG structure and delegate MLIR composition to Patterns.**

This keeps witnesses maintainable, enables Pattern reuse, and creates clear architectural boundaries.

> "If your witness is chock full of primitives, you're doing it wrong. Extract a Pattern."

---

**This is the architectural footprint for all Alex witnesses going forward.**

## Multi-Substrate Extension

The three-layer model extends to multi-substrate compilation:
- **Elements** fork per substrate (LLVM/, GPU/, AIE/, CIRCT/ modules)
- **Patterns** dispatch based on SubstrateKind from coeffects
- **Witnesses** remain substrate-agnostic (observe PSG structure, delegate to Patterns)

See `firefly_multi_substrate_fanout_architecture` for complete design.

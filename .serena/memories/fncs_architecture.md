# FNCS Architecture (F# Native Compiler Services)

## Overview

FNCS is the native type checker for Firefly. It performs complete type checking from `SynExpr` (parsed syntax) and builds the **SemanticGraph** with types attached during construction (not post-hoc).

**Key Design Principles:**
- BCL-free: No .NET runtime dependencies
- Types attached during construction
- SRTP resolved via native WitnessResolution
- Soft-delete reachability preserves full graph for debugging

## Core Data Structure: SemanticGraph

```fsharp
type SemanticGraph = {
    Nodes: Map<NodeId, SemanticNode>
    EntryPoints: NodeId list
    Modules: Map<ModulePath, NodeId list>
    Types: Map<string, NodeId>
}

type SemanticNode = {
    Id: NodeId
    Kind: SemanticKind
    Type: NativeType
    IsReachable: bool    // Soft-delete marker
    Children: NodeId list
    Parent: NodeId option
    SRTPResolution: WitnessResolution option
    ...
}
```

## Phase Pipeline

FNCS operates as a nanopass compiler with inspectable intermediates:

```
Phase 0: PARSING
  Input:  Source text
  Output: ParsedInput (SynExpr tree)
         ↓
Phase 1: STRUCTURAL CONSTRUCTION
  Input:  SynExpr + TypeEnv
  Output: SemanticGraph with nodes, edges, TYPES ATTACHED
  Emit:   fncs_phase_1_structural.json
         ↓
Phase 2: CONSTRAINT SOLVING
  Input:  SemanticGraph + Constraint list
  Output: SemanticGraph with resolved types
         ↓
Phase 3: SRTP RESOLUTION
  Input:  SemanticGraph with TraitCall nodes
  Output: SemanticGraph with WitnessResolution attached
         ↓
Phase 4: REACHABILITY ANALYSIS
  Input:  SemanticGraph + EntryPoints
  Output: SemanticGraph with IsReachable marks
  Emit:   fncs_phase_4_reachability.json
         ↓
Phase 5: FINAL RESULT
  Input:  SemanticGraph + Diagnostics
  Output: CheckResult
  Emit:   fncs_phase_5_final.json
```

## Key Modules

| Module | Location | Purpose |
|--------|----------|---------|
| NativeService.fs | Checking.Native/ | Public API, orchestrates checking |
| SemanticGraph.fs | Checking.Native/ | Graph types, reachability |
| CheckExpressions.fs | Checking.Native/ | Expression type checking |
| NativeTypes.fs | Checking.Native/ | Native type representation |
| Unify.fs | Checking.Native/ | Type unification |
| SRTPResolution.fs | Checking.Native/ | SRTP constraint solving |
| Infrastructure/ | Checking.Native/ | Phase config and emission |

## Enabling Phase Emission

```fsharp
// In Firefly CLI with -k flag
FNCSPhaseConfig.enableAllPhases intermediatesDir
```

This enables:
- Soft-delete reachability (preserves full graph)
- JSON emission at phases 1, 4, 5
- Node tracing for debugging

## Integration Points

### Firefly Compilation Flow
```
.fidproj → ProjectChecker → NativeService.checkParsedInputs
                         → SemanticGraph with CheckResult
                         → FNCSTransfer → MLIR
                         → Toolchain → Native Binary
```

### MLIR Generation (FNCSTransfer)
- Traverses SemanticGraph from entry points
- Follows VarRef definitions to inline bodies
- Platform bindings via Alloy.Primitives.Bindings convention
- Generates LLVM dialect MLIR

## FSharpNativeExpr: Expression-Centric View

FSharpNativeExpr is FNCS's own typed expression type that provides an expression-centric view over SemanticGraph. It is a **projection** - materialized from SemanticNode + SemanticKind on demand.

**Key Design:**
- Replaces any need for FCS's FSharpExpr
- Native types only (NativeType), no CLR types
- SRTP resolution captured via WitnessResolution
- BCL-free, freestanding capable

**Output Files:**
- `fncs_expr.json` - Structured JSON for programmatic analysis
- `fncs_expr.txt` - Human-readable text for debugging

**Example Output:**
```
=== Entry Point 0 ===
Module HelloWorldDirect:
  Let main =
    Lambda(argv) ->
      Seq:
        App(Var(Console.Write -> 12356), [Literal(String "Hello, World!")])
        Seq:
          App(Var(Console.WriteLine -> 12362), [Literal(String "")])
          Literal(Int32 0)
```

**Key Cases:**
```fsharp
type FSharpNativeExpr =
    | LetBinding of name * isMutable * value * body * ty
    | Lambda of parameters * body * returnType * srtp
    | Application of func * args * returnType * srtp
    | Variable of name * ty * isMutable * definitionId
    | PlatformBinding of entryPoint * args * ty
    | TraitCall of memberName * constrainedTypes * arg * resolution * ty
    | ...
```

**Usage:**
```fsharp
// From entry points
let exprs = FSharpNativeExpr.fromEntryPoints graph

// From specific node
let expr = FSharpNativeExpr.fromNode graph nodeId

// Pretty print
let text = FSharpNativeExpr.prettyPrint 0 expr
```

## FNCS Intrinsics (Layer 1 Operations)

FNCS provides intrinsics for operations that are **native to the type universe**. These require no external binding library - they are primitive operations that FNCS emits directly.

### Sys Module (System Operations)
```fsharp
module Sys =
    val write : fd:int -> buffer:nativeptr<byte> -> count:int -> int
    val read  : fd:int -> buffer:nativeptr<byte> -> maxCount:int -> int
    val exit  : code:int -> 'a
```

### NativePtr Module (Pointer Operations)
```fsharp
module NativePtr =
    val set : nativeptr<'T> -> int -> 'T -> unit
    val get : nativeptr<'T> -> int -> 'T
    val add : nativeptr<'T> -> int -> nativeptr<'T>
    val stackalloc : int -> nativeptr<'T>
    val copy : dest:nativeptr<'T> -> src:nativeptr<'T> -> count:int -> unit  // llvm.memcpy
    val fill : dest:nativeptr<'T> -> value:'T -> count:int -> unit           // llvm.memset
```

### NativeDefault Module (Default Values)
```fsharp
module NativeDefault =
    val zeroed<'T> : 'T     // Zero-initialized value
    val unreachable<'T> : 'T // Unreachable code marker
```

**Why these are intrinsics, not library functions:**
- They operate on the fundamental memory model
- No F# implementation can express their semantics
- FNCS must emit them directly as MLIR operations
- No quotation carrier needed - types carry full semantic information

**Contrast with Binding Libraries (Layer 2):**
- GTK bindings carry memory layout, ownership info via quotations
- CMSIS peripherals carry volatile semantics, register layouts
- These REQUIRE quotation semantic carriers because types alone are insufficient

## Related Memories
- `fncs_phase_debugging_protocol` - How to debug using phase files
- `platform_binding_recognition` - SUPERSEDED: see Firefly `binding_architecture_unified`
- `quotation_semantic_carriers` - Layer 2 binding mechanism
- `compilation_pipeline` - Full Firefly compilation flow
- **Firefly**: `binding_architecture_unified` - **CANONICAL** three-layer binding architecture
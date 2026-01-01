# Codata & Coeffect Zipper Architecture

## Core Principle: Codata is Demand-Driven

**Codata** = Computation defined by how it's CONSUMED (observed), not produced.
**Coeffects** = Track what code NEEDS from environment (requirements, not products).

This is the mathematical foundation for MLIR generation in Firefly.

## The Vocabulary (MANDATORY)

| Term | Meaning | Use in Zipper |
|------|---------|---------------|
| **witness** | To observe and record a computation | The fold witnesses each PSG node |
| **observe** | To note a context requirement | Note string literals, externs needed |
| **yield** | To produce on demand | Generate SSA names, block labels |
| **bind** | Associate observation with identity | Link PSG NodeId → SSA value |
| **recall** | Retrieve a prior observation | Look up what SSA was generated for a node |
| **extract** | Collapse accumulated context to final value | Produce final MLIR text |

## Architecture: Dual Zipper Model

```
PSGZipper (or FNCS SemanticGraph traversal)
    ↓ witnesses each node
MLIRZipper (codata accumulator)
    ↓ extract
MLIR text output
```

### PSG/FNCS Side (Input Navigation)
- Traverses the semantic graph structure
- Post-order: children before parents (SSAs available when parent visited)
- Provides node data to witness

### MLIRZipper Side (Output Composition)  
- Accumulates observations via witness functions
- Tracks coeffects (string literals, externs, buffers)
- Produces MLIR on demand via extract

## CRITICAL ANTI-PATTERNS

### 1. NO "Emitter" or "Scribe" Layer
"Emitter" and "Scribe" are dispatch-based antipatterns. They were removed twice.
The zipper WITNESSES; it does not DISPATCH or ROUTE.

### 2. NO Pattern Matching on Symbol Names
```fsharp
// WRONG - NEVER DO THIS
match funcName with
| "Console.Write" -> ...
| "Console.writeln" -> ...
```

Dispatch is based on **SemanticKind**, not symbol names.

### 3. NO Central Routing Table
There is no handler registry. The fold visits nodes; pattern matching at each node is LOCAL and structural.

### 4. Centralization at OUTPUT, not DISPATCH
The MLIR Builder (extract) is where output centralizes.
Traversal/dispatch never centralizes.

## Implementation Pattern

```fsharp
// Witness pattern for a node
let witnessNode (node: SemanticNode) (zipper: MLIRZipper) : MLIRZipper * TransferResult =
    match node.Kind with
    | SemanticKind.Literal lit ->
        // Witness the literal, yield SSA
        let ssaName, zipper' = witnessConstant lit zipper
        zipper', TRValue (ssaName, typeOf lit)
        
    | SemanticKind.Application { Func = func; Args = args } ->
        // Recall children's SSAs (post-order: they're already witnessed)
        let argSSAs = args |> List.choose (fun a -> recallNodeSSA a.NodeId zipper)
        // Witness the call
        let ssaName, zipper' = witnessCall funcName argSSAs zipper
        zipper', TRValue (ssaName, returnType)
        
    | SemanticKind.PlatformBinding marker ->
        // Platform binding: witness syscall based on marker
        let zipper' = witnessPlatformCall marker args zipper
        zipper', TRVoid
```

## Platform Bindings

Platform bindings are identified by `SemanticKind.PlatformBinding` markers from FNCS.
The marker contains the binding name (e.g., "writeBytes", "readBytes").
Alex provides platform-specific implementations based on target:

```fsharp
// Alex/Bindings/ConsoleBindings.fs
let witnessWrite (fd: string) (bufPtr: string) (len: string) (zipper: MLIRZipper) =
    // sys_write = 1 on Linux x86_64
    let sysNum, z1 = MLIRZipper.witnessConstant 1L I64 zipper
    let result, z2 = MLIRZipper.witnessSyscall sysNum [(fd, "i64"); (bufPtr, "!llvm.ptr"); (len, "i64")] (Integer I64) z1
    z2, result
```

## The Fold Structure

```fsharp
let rec foldGraph (node: SemanticNode) (zipper: MLIRZipper) : MLIRZipper * TransferResult =
    // Post-order: process children first
    let zipper', childResults = foldChildren node.Children zipper
    
    // Witness this node with children's SSAs available
    witnessNode node childResults zipper'
```

## Files

- `Alex/Traversal/MLIRZipper.fs` - The OUTPUT zipper with codata vocabulary
- `Alex/Traversal/FNCSTransfer.fs` - FNCS SemanticGraph → MLIRZipper (the witnessing fold)
- `Alex/Bindings/*.fs` - Platform-specific witness implementations

## Key Insight: SSA IS Functional Programming

From Appel 1998: SSA form IS a functional program in disguise.
- SSA variables = immutable let bindings
- Phi nodes = function parameters
- Basic blocks = continuations

The zipper makes this explicit: F# structure maps directly to MLIR via witnessing.

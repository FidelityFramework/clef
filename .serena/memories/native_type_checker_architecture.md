# Native Type Checker Architecture

## Overview

This document specifies the architecture for FNCS's native type checker. The goal is to **change the type universe** (native types instead of BCL) while **preserving FCS's design-time infrastructure**.

## CRITICAL PRINCIPLE: FCS Preservation

FNCS is NOT a complete replacement of FCS. The valuable parts of FCS must be preserved:

### What MUST Be Preserved From FCS

| FCS Component | Purpose | Preservation Strategy |
|---------------|---------|----------------------|
| `FSharpSymbol` | Symbol info for navigation | Keep symbol tracking infrastructure |
| `FSharpCheckFileResults` | Per-file analysis results | Adapt to use native types |
| `GetToolTip` | Hover information | Preserve API, native type descriptions |
| `GetDeclarationLocation` | Go to definition | Preserve source location tracking |
| `GetSymbolUseAtLocation` | Find symbol at cursor | Preserve symbol use tracking |
| `GetAllUsesOfAllSymbols` | Find all references | Preserve cross-file symbol tracking |
| `SemanticClassification` | Syntax highlighting | Preserve semantic classification |
| Parser (SynExpr, SynModule) | Syntax parsing | Use unchanged |
| Source locations/ranges | Navigation, error reporting | Preserve throughout pipeline |

### What Changes For Native

| Aspect | FCS | FNCS |
|--------|-----|------|
| Type source | IL assemblies + source | Source only |
| String literal | `System.String` | `NativeStr` (UTF-8) |
| Option type | Reference, nullable | `voption` (value type) |
| `obj` | Universal base | **Does not exist** |
| SRTP timing | Post-hoc overlay | During construction |

## Design Goals

1. **Preserve FCS Design-Time APIs**: Editor services must continue to work
2. **Native Types Only**: No BCL, no IL imports, no `obj`
3. **SRTP Intrinsic**: Resolution during type checking, not post-hoc
4. **PSG Construction**: FNCS builds the PSG, not Firefly
5. **Full Symbol Information**: PSG carries symbol info for navigation
6. **Memory Layout Aware**: Types determine representation

## Architecture Layers

```
┌─────────────────────────────────────────────────────────────────────┐
│                         Source Files (.fs)                          │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                           PARSER                                    │
│  ─────────────────────────────────────────────────────────────────  │
│  F# parser producing SynExpr, SynModule, etc.                       │
│  (Largely unchanged from FCS - syntax is F# syntax)                 │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      TYPE ENVIRONMENT                               │
│  ─────────────────────────────────────────────────────────────────  │
│  NativeGlobals: Built-in types (string→UTF8, option→ValueOption)   │
│  ImportedModules: Source-only imports (no IL assemblies)           │
│  Witness Tables: SRTP resolution targets (Alloy hierarchy)         │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                     UNIFIED CHECKER                                 │
│  ─────────────────────────────────────────────────────────────────  │
│  Walks SynExpr, produces SemanticNode with types ATTACHED           │
│                                                                     │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐          │
│  │ Constraint   │───▶│ Unification  │───▶│ Generalize   │          │
│  │ Generation   │    │ (Union-Find) │    │ (let-poly)   │          │
│  └──────────────┘    └──────────────┘    └──────────────┘          │
│         │                   │                   │                   │
│         └───────────────────┴───────────────────┘                   │
│                             │                                       │
│                    ┌────────▼────────┐                              │
│                    │ SRTP Resolution │ ← Intrinsic, not post-hoc    │
│                    └─────────────────┘                              │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                     REACHABILITY ANALYSIS                           │
│  ─────────────────────────────────────────────────────────────────  │
│  Entry point → transitive closure → HARD PRUNE unreachable          │
│  (Not soft-delete - unified representation needs no correlation)    │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    NATIVE SEMANTIC GRAPH                            │
│  ─────────────────────────────────────────────────────────────────  │
│  Output to Firefly: SemanticNode with                               │
│  - Types attached                                                   │
│  - SRTP resolved                                                    │
│  - Memory hints attached                                            │
│  - Only reachable nodes                                             │
└─────────────────────────────────────────────────────────────────────┘
                                   │
                                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      FIREFLY (Consumer)                             │
│  ─────────────────────────────────────────────────────────────────  │
│  Lowering nanopasses → Alex/Zipper → MLIR → LLVM → Native           │
└─────────────────────────────────────────────────────────────────────┘
```

## Core Data Structures

### Native Type System

```fsharp
/// Type constructor reference (not IL-based)
type TypeConRef = {
    Name: string
    Module: ModulePath
    Arity: int
    Layout: TypeLayout  // Determines memory representation
}

/// Type parameter with constraints
type TypeParam = {
    Id: int
    Name: string
    Constraints: Constraint list
    // Union-Find parent pointer for efficient substitution
    mutable Parent: TypeParamState
}

and TypeParamState =
    | Unbound
    | Bound of NativeType

/// The native type representation
type NativeType =
    | TForall of TypeParam list * NativeType
    | TApp of TypeConRef * NativeType list
    | TTuple of NativeType list * isStruct: bool
    | TFun of NativeType * NativeType
    | TVar of TypeParam
    | TMeasure of Measure
    | TAnon of AnonRecordType  // Anonymous records
    | TByref of NativeType * ByrefKind

/// Type layout (for memory representation)
type TypeLayout =
    | Inline of size: int * align: int      // Stack-allocated, known size
    | Reference of arena: ArenaAffinity     // Arena-allocated
    | Opaque                                 // Platform-specific

/// Arena affinity for memory management
type ArenaAffinity =
    | CurrentActor      // Default: current actor's arena
    | Explicit of string  // Named arena
    | Stack             // Stack allocation (no arena)
```

### Constraint System

```fsharp
/// Constraints generated during type checking
type Constraint =
    | Equals of NativeType * NativeType * range: Range
    | HasMember of ty: NativeType * name: string * signature: NativeType * range: Range
    | HasMeasure of NativeType * Measure * range: Range
    | Subtype of sub: NativeType * super: NativeType * range: Range  // Minimal, for inheritance
    | LayoutCompatible of NativeType * TypeLayout * range: Range

/// Constraint solving state
type SolverState = {
    // Union-Find state is in TypeParam.Parent
    Deferred: Constraint list
    Errors: TypeError list
    SRTPResolutions: Map<SRTPKey, WitnessResolution>
}
```

### Semantic Graph

```fsharp
/// Semantic node - the unified representation
type SemanticNode = {
    Id: NodeId
    Kind: SemanticKind
    Range: Range
    
    // Type attached during construction (not post-hoc)
    Type: NativeType
    
    // SRTP resolution (if applicable)
    SRTPResolution: WitnessResolution option
    
    // Memory hints
    ArenaAffinity: ArenaAffinity
    LayoutHint: TypeLayout option
    
    // Graph structure
    Children: NodeId list
    Parent: NodeId option
}

type SemanticKind =
    | SBinding of name: string * isMutable: bool
    | SApplication of func: NodeId * args: NodeId list
    | SLambda of params: (string * NativeType) list * body: NodeId
    | SLiteral of value: LiteralValue
    | SMatch of scrutinee: NodeId * cases: MatchCase list
    | SSequential of nodes: NodeId list
    | SWhileLoop of guard: NodeId * body: NodeId
    | SForLoop of var: string * start: NodeId * finish: NodeId * body: NodeId
    | SRecord of fields: (string * NodeId) list
    | SUnionCase of case: string * payload: NodeId option
    | STupleExpr of elements: NodeId list
    | STypeAnnotation of expr: NodeId * annotatedType: NativeType
    | SPlatformBinding of name: string  // Platform.Bindings marker
    // ... etc
```

## Module Structure

```
src/Compiler/Checking.Native/
├── NativeGlobals.fs         # Built-in types (string, int, option, etc.)
├── NativeTypes.fs           # Type representation (NativeType, TypeParam)
├── Constraints.fs           # Constraint types and generation
├── UnionFind.fs             # Efficient substitution via Union-Find
├── Unify.fs                 # Unification algorithm with occurs check
├── CheckExpr.fs             # Expression checking → SemanticNode
├── CheckPattern.fs          # Pattern checking
├── CheckDecl.fs             # Declaration checking
├── SRTPResolution.fs        # SRTP witness lookup
├── Generalize.fs            # Let-polymorphism
├── Reachability.fs          # Entry point → hard prune
└── SemanticGraph.fs         # Output graph structure
```

## Key Algorithms

### 1. Unified Checking (CheckExpr)

```fsharp
/// Check expression, returning SemanticNode with type ATTACHED
let rec checkExpr (env: TypeEnv) (syn: SynExpr) : SemanticNode =
    match syn with
    | SynExpr.Const(SynConst.String(s, _, _), range) ->
        // String literal → NativeStr (UTF-8), not System.String
        { Id = newId()
          Kind = SLiteral(StringLit s)
          Range = range
          Type = env.Globals.StringType  // Already native
          SRTPResolution = None
          ArenaAffinity = CurrentActor
          LayoutHint = Some(Inline(16, 8))  // Fat pointer
          Children = []
          Parent = None }
          
    | SynExpr.App(_, _, funcExpr, argExpr, range) ->
        let funcNode = checkExpr env funcExpr
        let argNode = checkExpr env argExpr
        
        // Generate constraint: funcType = argType -> ?result
        let resultVar = freshTypeVar()
        addConstraint(Equals(funcNode.Type, TFun(argNode.Type, TVar resultVar), range))
        
        // Check for SRTP (operator application)
        let srtpRes = tryResolveSRTP env funcNode argNode
        
        { Id = newId()
          Kind = SApplication(funcNode.Id, [argNode.Id])
          Range = range
          Type = TVar resultVar  // Will be solved
          SRTPResolution = srtpRes
          ArenaAffinity = inferArena env [funcNode; argNode]
          LayoutHint = None
          Children = [funcNode.Id; argNode.Id]
          Parent = None }
          
    | SynExpr.LetOrUse(_, _, bindings, body, _, _) ->
        // Check bindings, generalize, check body
        let bindingNodes = bindings |> List.map (checkBinding env)
        
        // CRITICAL: Solve constraints NOW, then generalize
        solveConstraints()
        let generalizedEnv = generalize env bindingNodes
        
        let bodyNode = checkExpr generalizedEnv body
        // ...
```

### 2. Union-Find Unification

```fsharp
/// Find representative with path compression
let rec find (typar: TypeParam) : TypeParam * NativeType option =
    match typar.Parent with
    | Unbound -> (typar, None)
    | Bound(TVar other) ->
        let (rep, ty) = find other
        typar.Parent <- Bound(TVar rep)  // Path compression
        (rep, ty)
    | Bound ty -> (typar, Some ty)

/// Unify two types
let rec unify (t1: NativeType) (t2: NativeType) (range: Range) : unit =
    match (t1, t2) with
    | TVar v1, TVar v2 ->
        let (rep1, bound1) = find v1
        let (rep2, bound2) = find v2
        match (bound1, bound2) with
        | None, None when rep1.Id <> rep2.Id ->
            rep1.Parent <- Bound(TVar rep2)  // Union
        | None, Some ty -> 
            if occursIn rep1 ty then raise(InfiniteType(rep1, ty, range))
            rep1.Parent <- Bound ty
        | Some ty, None ->
            if occursIn rep2 ty then raise(InfiniteType(rep2, ty, range))
            rep2.Parent <- Bound ty
        | Some ty1, Some ty2 -> unify ty1 ty2 range
        
    | TVar v, ty | ty, TVar v ->
        let (rep, bound) = find v
        match bound with
        | None ->
            if occursIn rep ty then raise(InfiniteType(rep, ty, range))
            rep.Parent <- Bound ty
        | Some bound -> unify bound ty range
        
    | TApp(con1, args1), TApp(con2, args2) when con1 = con2 ->
        List.iter2 (fun a1 a2 -> unify a1 a2 range) args1 args2
        
    | TFun(d1, r1), TFun(d2, r2) ->
        unify d1 d2 range
        unify r1 r2 range
        
    | TTuple(elems1, s1), TTuple(elems2, s2) when s1 = s2 && List.length elems1 = List.length elems2 ->
        List.iter2 (fun e1 e2 -> unify e1 e2 range) elems1 elems2
        
    | _ -> raise(TypeMismatch(t1, t2, range))
```

### 3. SRTP Resolution (Intrinsic)

```fsharp
/// Resolve SRTP during type checking (not post-hoc)
let tryResolveSRTP (env: TypeEnv) (funcNode: SemanticNode) (argNode: SemanticNode) : WitnessResolution option =
    match funcNode.Kind with
    | SBinding name when isSRTPOperator name ->
        // Get the concrete argument type (may need solving first)
        let argType = applySubstitution argNode.Type
        
        // Search witness hierarchy (Alloy modules)
        match env.Witnesses.TryFind(name, argType) with
        | Some witness ->
            Some { 
                Operator = name
                ArgType = argType
                ResolvedMember = witness.Member
                Implementation = witness.Implementation
            }
        | None ->
            // Defer if type not yet concrete
            if hasUnboundVars argType then
                addDeferredConstraint(HasMember(argType, name, funcNode.Type, funcNode.Range))
                None
            else
                raise(NoSRTPWitness(name, argType, funcNode.Range))
    | _ -> None
```

### 4. Hard Prune Reachability

```fsharp
/// Compute reachable nodes from entry points
let computeReachable (graph: SemanticGraph) (entries: NodeId list) : Set<NodeId> =
    let rec walk (visited: Set<NodeId>) (nodeId: NodeId) =
        if Set.contains nodeId visited then visited
        else
            let node = graph.Nodes.[nodeId]
            let visited = Set.add nodeId visited
            node.Children |> List.fold walk visited
    
    entries |> List.fold walk Set.empty

/// HARD prune unreachable nodes (not soft-delete)
let pruneUnreachable (graph: SemanticGraph) (entries: NodeId list) : SemanticGraph =
    let reachable = computeReachable graph entries
    { graph with 
        Nodes = graph.Nodes |> Map.filter (fun id _ -> Set.contains id reachable) }
```

## Integration Points

### API Boundary: fsnative → Firefly

```fsharp
/// The public API for Firefly consumption
module FSharp.Native.Compiler.Service

/// Check a project and return the semantic graph
let checkProject (sources: SourceFile list) (options: CheckOptions) : CheckResult =
    let env = createTypeEnv options
    
    // Parse all sources
    let synTrees = sources |> List.map Parser.parseFile
    
    // Check with unified construction
    let semanticNodes = synTrees |> List.collect (checkModule env)
    
    // Solve any remaining constraints
    solveAllConstraints()
    
    // Hard prune to reachables
    let entries = findEntryPoints semanticNodes
    let prunedGraph = pruneUnreachable (buildGraph semanticNodes) entries
    
    { Graph = prunedGraph
      Errors = collectErrors()
      Warnings = collectWarnings() }

type CheckResult = {
    Graph: SemanticGraph
    Errors: Diagnostic list
    Warnings: Diagnostic list
}
```

### Native Globals

```fsharp
/// Built-in types with native semantics
let createNativeGlobals() = {
    StringType = TApp({ Name = "string"; Layout = Inline(16, 8) }, [])  // UTF-8 fat ptr
    IntType = TApp({ Name = "int"; Layout = Inline(4, 4) }, [])
    Int64Type = TApp({ Name = "int64"; Layout = Inline(8, 8) }, [])
    FloatType = TApp({ Name = "float"; Layout = Inline(8, 8) }, [])
    BoolType = TApp({ Name = "bool"; Layout = Inline(1, 1) }, [])
    UnitType = TApp({ Name = "unit"; Layout = Inline(0, 1) }, [])
    
    // Option is value-type, not reference
    OptionTypeCon = { Name = "option"; Layout = Inline(-1, -1); Arity = 1 }  // Size depends on 'T
    
    // Array is fat pointer (ptr + length)
    ArrayTypeCon = { Name = "array"; Layout = Inline(16, 8); Arity = 1 }
}
```

## Memory Management Integration

### Arena Affinity Tracking

```fsharp
/// Infer arena affinity for an expression
let inferArena (env: TypeEnv) (subNodes: SemanticNode list) : ArenaAffinity =
    match env.CurrentArena with
    | Some arena -> Explicit arena
    | None ->
        // Check for stack hints
        if subNodes |> List.forall (fun n -> n.LayoutHint = Some(Inline _)) then
            Stack  // All inline, can be stack
        else
            CurrentActor  // Default to actor arena

/// Memory region from UMX-style annotations
type MemoryRegion =
    | Sram
    | Flash
    | Peripheral
    | Dma
    | Arena of name: string

/// Pointer type with region (absorbed from UMX)
// Ptr<'T, 'region, 'access> becomes native
type NativePtr = {
    PointeeType: NativeType
    Region: MemoryRegion
    Access: AccessKind
}
```

## Differences from FCS

| Aspect | FCS | FNCS |
|--------|-----|------|
| Type source | IL assemblies + source | Source only |
| String literal | `System.String` | `NativeStr` (UTF-8) |
| Option type | Reference, nullable | Value type, no null |
| `obj` | Universal base | **Does not exist** |
| PSG construction | Firefly builds PSG | **FNCS builds PSG** |
| Design-time APIs | Full support | **Preserved (critical)** |
| SRTP timing | Post-hoc overlay | During construction |
| Memory info | None | Layout + arena affinity |

## PSG Construction (FNCS Responsibility)

FNCS outputs a **Program Semantic Graph (PSG)** that:
- Contains full type information (native types)
- Preserves symbol information for editor navigation
- Has SRTP already resolved
- Is "correct by construction" for Firefly consumption

Firefly consumes this PSG and focuses purely on code generation (Alex/Zipper → MLIR → LLVM).

## Success Criteria

1. ✅ Types attached during construction (no correlation pass)
2. ✅ SRTP resolved during type checking (intrinsic)
3. ✅ Graph hard-pruned before handoff
4. ✅ Memory layout determinable from types
5. ✅ Arena affinity tracked
6. ✅ No IL/BCL machinery anywhere
7. ✅ `obj` does not exist in type system
8. ✅ API compatible with Firefly consumption

## Next Steps

1. Implement `NativeGlobals.fs` with built-in types
2. Implement `UnionFind.fs` for efficient substitution
3. Port constraint generation from FCS (remove IL parts)
4. Implement unified `CheckExpr.fs`
5. Implement SRTP resolution with Alloy witness tables
6. Implement hard-prune reachability
7. Create integration tests with Firefly

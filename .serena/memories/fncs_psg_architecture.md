# FNCS PSG Construction Architecture

> **Created**: January 2026
> **Purpose**: Document how FNCS builds the Program Semantic Graph (PSG)

## Core Principle

**FNCS builds the PSG, not Firefly.** Firefly consumes the PSG as "correct by construction" and focuses purely on code generation.

## What Is the PSG?

The Program Semantic Graph (PSG) is:
- A unified semantic representation of the F# program
- Types attached during construction (not post-hoc)
- SRTP already resolved to concrete witnesses
- Full symbol information for design-time tooling
- "Correct by construction" for Firefly consumption

## PSG Construction Pipeline

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              Source Files (.fs)                              │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PARSER (from FCS)                                  │
│  F# parser producing SynExpr, SynModule, etc.                               │
│  (Largely unchanged from FCS - syntax is F# syntax)                         │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                        NATIVE TYPE CHECKER                                   │
│  ─────────────────────────────────────────────────────────────────────────  │
│  • Native globals (string=UTF-8, option=voption, no obj)                    │
│  • Constraint generation and unification                                    │
│  • SRTP resolution during checking (Alloy witnesses)                        │
│  • Symbol information attached to nodes                                     │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         PSG CONSTRUCTION                                     │
│  ─────────────────────────────────────────────────────────────────────────  │
│  Build graph from typed syntax:                                             │
│  • Nodes with native types attached                                         │
│  • Edges (ChildOf, DefUse, etc.)                                            │
│  • SRTP resolution info on applicable nodes                                 │
│  • Symbol info (FSharpSymbol) preserved for design-time                     │
│  • Source ranges preserved throughout                                       │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                      PSG OUTPUT (to Firefly)                                 │
│  ─────────────────────────────────────────────────────────────────────────  │
│  A complete semantic graph:                                                  │
│  • All types are native (no BCL)                                            │
│  • SRTP resolved to concrete implementations                                │
│  • Ready for code generation                                                │
│  • Symbol info available for diagnostics                                    │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         FIREFLY (Consumer)                                   │
│  Lowering nanopasses → Alex/Zipper → MLIR → LLVM → Native                   │
│  NO TYPE CHECKING - trusts PSG as "correct by construction"                 │
└─────────────────────────────────────────────────────────────────────────────┘
```

## PSG Node Structure

Each PSG node contains:

```fsharp
type PSGNode = {
    Id: NodeId
    Kind: SyntaxKind              // Application, Binding, Literal, etc.
    Range: Range                   // Source location (PRESERVED)
    
    // Type information (native types, attached during construction)
    Type: NativeType option
    
    // SRTP resolution (if applicable)
    SRTPResolution: WitnessResolution option
    
    // Symbol information (PRESERVED from FCS)
    Symbol: FSharpSymbol option
    
    // Graph structure
    Children: NodeId list
    Parent: NodeId option
    
    // Additional edges (def-use, etc.)
    Edges: PSGEdge list
}
```

## Key Design Decisions

### 1. Types Attached During Construction

Unlike the old architecture where typed trees were overlaid post-hoc, FNCS attaches types during construction:

```fsharp
// OLD (Firefly PSG building)
let node = buildNode synExpr          // No type
let typedNode = overlayType node fsharpExpr  // Type added later

// NEW (FNCS PSG construction)
let node = checkAndBuild synExpr env  // Type attached immediately
```

### 2. SRTP Resolution Is Intrinsic

SRTP is resolved during type checking, not as a post-hoc nanopass:

```fsharp
// When checking: let inline WriteLine s = WritableString $ s
// The `$` operator is resolved to concrete implementation DURING checking
let srtpInfo = resolveWitness "$" argType env.Witnesses
// srtpInfo is attached to the PSG node
```

### 3. Symbol Information Flows Through

FCS-style symbol information is preserved for design-time:

```fsharp
// When building PSG node for `Console.Write "hello"`
let symbol = lookupSymbol "Console.Write" env  // FSharpSymbol
let node = { ... Symbol = Some symbol ... }
// Later: GetToolTip can use node.Symbol
```

## Contract: FNCS → Firefly

FNCS guarantees:
1. All types are native (no BCL types anywhere)
2. All SRTP constraints are resolved
3. All symbols have source locations
4. No `obj` or boxing exists
5. The graph is semantically valid

Firefly assumes:
1. Type checking is complete
2. Name resolution is complete
3. SRTP is resolved
4. The PSG is "correct by construction"

## Files Involved

### FNCS (builds PSG)
- `src/Compiler/Checking.Native/NativeService.fs` - Public API
- `src/Compiler/Checking.Native/CheckExpressions.fs` - Type checking
- `src/Compiler/Checking.Native/SemanticGraph.fs` - Graph structure
- `src/Compiler/Checking.Native/SRTPResolution.fs` - SRTP resolution

### Firefly (consumes PSG)
- `src/Core/IngestionPipeline.fs` - PSG consumption entry point
- `src/Alex/Traversal/` - Zipper traversal of PSG
- `src/Alex/Pipeline/` - MLIR generation from PSG

## Historical Note

Previously, Firefly built the PSG from FCS output. This architecture has been superseded:

| Old Architecture | New Architecture |
|-----------------|------------------|
| FCS → typed trees | FNCS → PSG |
| Firefly builds PSG from FCS output | FNCS builds PSG directly |
| Baker correlates syntax/typed trees | No correlation needed |
| SRTP resolved in nanopass | SRTP resolved during checking |
| BCL types filtered in Firefly | BCL rejected at source in FNCS |

## Success Criteria

1. FNCS produces complete PSG with native types
2. No BCL types in PSG
3. SRTP resolved for all generic calls
4. Symbol information preserved for design-time
5. Source locations available for diagnostics
6. Firefly can consume PSG without type checking

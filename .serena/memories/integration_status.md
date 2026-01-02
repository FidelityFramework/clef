# FNCS Integration Status (January 2026)

## Architecture Correction (CRITICAL)

**FNCS builds the PSG** - this is the correct, current architecture.
Firefly consumes the PSG as "correct by construction" and focuses on code generation.

## Current Status: FOUNDATIONAL WORK IN PROGRESS

The native type checker infrastructure exists but has **architectural gaps** that must be addressed:

### What Exists ✅

**Namespace Rename: DONE**
- Project file: `FSharp.Native.Compiler.Service.fsproj`
- Assembly: `FSharp.Native.Compiler.Service`
- Namespace: `FSharp.Native.Compiler.*`
- Build succeeds

**Core Infrastructure: PARTIAL**
- `Checking.Native/NativeTypes.fs` - Type representation
- `Checking.Native/NativeGlobals.fs` - Built-in types
- `Checking.Native/UnionFind.fs` - Path compression, occurs check
- `Checking.Native/Unify.fs` - Unification with detailed errors
- `Checking.Native/SemanticGraph.fs` - Graph structure
- `Checking.Native/CheckExpressions.fs` - Expression checking
- `Checking.Native/SRTPResolution.fs` - SRTP during type checking
- `Checking.Native/NativeService.fs` - Public API surface

### What's Missing ❌

**1. Principled Name Resolution**
- `open` declarations are currently IGNORED (root cause of BCL detection issues)
- Name resolution uses syntactic names without proper qualification
- Need compositional resolver pattern (function composition, not mutable maps)

**2. FCS Design-Time Infrastructure Preservation**
- FCS provides rich infrastructure for design-time tooling that MUST be preserved
- Currently unclear what's preserved vs. lost in the native type checker
- Need explicit audit and preservation plan

**3. PSG Construction**
- PSG construction logic exists but needs integration with design-time services
- Full symbol information must flow through PSG for editor tooling

### What Must Be Preserved From FCS

| FCS Component | Purpose | FNCS Status |
|---------------|---------|-------------|
| `FSharpSymbol` | Symbol info for navigation | MUST PRESERVE |
| `FSharpCheckFileResults` | Per-file analysis results | MUST PRESERVE |
| `GetToolTip` | Hover information | MUST PRESERVE |
| `GetDeclarationLocation` | Go to definition | MUST PRESERVE |
| `GetSymbolUseAtLocation` | Find symbol at cursor | MUST PRESERVE |
| `GetAllUsesOfAllSymbols` | Find all references | MUST PRESERVE |
| `SemanticClassification` | Syntax highlighting | MUST PRESERVE |
| Source locations/ranges | Navigation, error reporting | MUST PRESERVE |

### What Changes (Native Type Universe)

| Aspect | FCS | FNCS |
|--------|-----|------|
| String literal | `System.String` | `NativeStr` (UTF-8 fat pointer) |
| Option type | Reference, nullable | `voption` (value type, non-null) |
| `obj` / `System.Object` | Universal base | **Does not exist** |
| Type source | IL assemblies + source | Source only |
| SRTP timing | Post-hoc overlay | During construction |

## Correct Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              FNCS (fsnative)                                 │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │ PRESERVED FROM FCS:                                                      ││
│  │  • Parser (SynExpr, SynModule)                                          ││
│  │  • Symbol infrastructure (FSharpSymbol, locations, references)          ││
│  │  • Editor service APIs (GetToolTip, GetDeclaration, GetSymbolUses)     ││
│  │  • Typed tree structure (FSharpExpr)                                    ││
│  └─────────────────────────────────────────────────────────────────────────┘│
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │ CHANGED FOR NATIVE:                                                      ││
│  │  • Type universe (native types, not BCL)                                ││
│  │  • String literals → UTF-8 fat pointer semantics                        ││
│  │  • Option → voption (stack-allocated, non-null)                         ││
│  │  • SRTP resolution → Alloy witness hierarchy                            ││
│  │  • No obj/System.Object                                                  ││
│  └─────────────────────────────────────────────────────────────────────────┘│
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │ NEW IN FNCS:                                                             ││
│  │  • PSG construction                                                      ││
│  │  • Native type checking (Checking.Native/)                              ││
│  │  • Principled name resolution (compositional)                           ││
│  └─────────────────────────────────────────────────────────────────────────┘│
│                                                                              │
│  OUTPUT: PSG with native types, full symbol info, design-time capabilities  │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                              Firefly                                         │
│  • Consumes PSG as "correct by construction"                                │
│  • Alex/Zipper traversal → MLIR generation                                  │
│  • Platform bindings                                                         │
│  • LLVM → Native binary                                                      │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Immediate Next Steps

1. **Audit Checking.Native/** - Document what FCS infrastructure is preserved vs. lost
2. **Implement principled name resolution** - Compositional resolvers, process `open` declarations
3. **Define PSG output interface** - Contract between FNCS and Firefly
4. **Preserve editor service APIs** - Ensure design-time tooling works

## DO NOT Claim Percentages

Previous claims of "85-90% done" were **inaccurate**. Progress should be measured by:
- Architectural correctness (FCS preservation, PSG construction, name resolution)
- Working end-to-end samples (HelloWorld compiles and runs)
- Design-time feature validation (hover, go-to-definition, find references)

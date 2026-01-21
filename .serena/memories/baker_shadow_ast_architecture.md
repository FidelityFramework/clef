# Baker Shadow AST Architecture

> **Created**: January 2026
> **Context**: PRD-13a Collection Decomposition, Baker/Recipes infrastructure

## The Problem

When Baker decomposes HOFs (List.map, Seq.collect, etc.) into primitive PSG nodes, there's no source syntax for the expanded code. Developers need **editing transparency** - the ability to see what's "their code" vs "compiler-saturated code" at design time.

## The Solution: Two-Level Model

### Level 1: Semantic Shadow (Developer-Facing)

The shadow AST captures the **semantic meaning** of the expansion, not every PSG node. This is what tooling shows developers.

```fsharp
// For simple recursive patterns (List.map, List.fold, etc.)
type SimpleShadow =
    | RecursivePattern of {
        Operation: string           // "List.map"
        BaseCase: string            // "empty list → empty list"
        RecursiveCase: string       // "cons(f(head), recurse(tail))"
        SourceRefs: Map<string, NodeId>  // Links to real source
    }

// For state machines (Seq operations)
type SeqShadow =
    | StateMachine of {
        States: string list
        OuterSource: ShadowRef
        InnerMapper: ShadowRef option
        YieldPoints: YieldPoint list
        Transitions: Transition list
    }
    | Transform of input * operation * mapper
    | Concat of inner * outer
```

### Level 2: PSG Nodes (Compiler-Facing)

The full PSG structure with all nodes. This is what Alex witnesses. The shadow doesn't mirror this 1:1.

## Key Principle: XParsec Templates Produce Both

The XParsec combinator/template that describes an expansion produces **both** the PSG nodes AND the semantic shadow as a single unit. No separate construction pass.

```fsharp
type Expanded<'a> = {
    Value: 'a                    // The PSG node(s)
    Shadow: ShadowExpr           // Semantic description
    Provenance: Provenance       // Link to inspiring source
}
```

The template IS the documentation. When you read the template, you understand both what PSG is built AND what the semantic shadow captures.

## Provenance

Every shadow node tracks:
- **InspiringNode**: The source PSG node that triggered expansion
- **SourceRange**: Original source location (for IDE navigation)
- **ExpandedOperation**: What HOF was expanded (e.g., "Seq.collect")
- **Depth**: For nested expansions

## Tooling View

```
// Expanded from Seq.collect at MyFile.fs:42:5
// State Machine: Initial → InOuter → InInner → Done
//   Outer source: «xs»
//   Inner mapper: «f»
//   Yields: innerEnum.Current when in InInner state

[Expand to see full PSG structure...]
```

## Anti-Patterns

1. **Two separate construction passes** - Shadow must be built alongside PSG, not after
2. **1:1 shadow-to-PSG mapping** - Shadow is semantic, not syntactic
3. **Ad-hoc patterns per operation** - All decompositions use same infrastructure
4. **Forgetting provenance** - Every shadow node must link back to source

## Files Involved

- `src/Compiler/Baker/ShadowAST.fs` - Shadow types and rendering
- `src/Compiler/Baker/Recipes/*.fs` - Templates produce Expanded<'a>
- `src/Compiler/Baker/HOFDecomposition.fs` - Orchestration, registry
- `fsnative-spec/` - Formal specification of the model

## Connection to PSG Construction Model

Normal PSG: `AST + TypedTree → PSG Node` (with real source range)

Baker PSG: `Template + Provenance → (PSG Nodes, Semantic Shadow)`

The PSG nodes ARE first-class nodes (same SemanticNode type), but their provenance is tracked via the shadow registry, enabling tooling to distinguish source from saturated code.

## Implementation Status (January 2026)

**FULLY IMPLEMENTED**

### Core Infrastructure

1. **ShadowAST.fs** - Complete type system:
   - `ShadowId`, `Provenance`, `ShadowRef`, `ShadowExpr` (11 expression variants)
   - `SemanticShadow` with 4 patterns: RecursivePattern, StateMachine, Transform, TreeTraversal
   - `ShadowTree`, `ShadowRegistry`, `ShadowBuilder`
   - `Expanded<'a>` result type
   - `Render` module for human-readable output

2. **Decomposition.fs** - Integration layer:
   - Context carries `InspiringNode` and `ShadowBuilder`
   - Result includes optional `ShadowTree`
   - Helper functions: `shadowPrimitive`, `shadowApp`, `shadowIfThenElse`, etc.
   - Semantic helpers: `mkRecursivePatternSemantic`, `mkTransformSemantic`

### Recipe Implementations

All recipe files updated with parallel shadow construction:

| File | Operations | Shadow Type |
|------|------------|-------------|
| OptionRecipes.fs | map (full), bind, filter | Transform |
| ListRecipes.fs | map, fold, filter, exists, forall, length, rev, append, collect | RecursivePattern |
| MapRecipes.fs | toList, tryFind, add, containsKey, keys, values, forall | TreeTraversal |
| SetRecipes.fs | add, contains, remove, union, intersect, difference | TreeTraversal |

### Pipeline Integration

- **HOFDecomposition.fs**: Returns `DecompositionResult` with Graph + ShadowRegistry
- **NativeService.fs**: Extracts graph; shadow registry ready for tooling

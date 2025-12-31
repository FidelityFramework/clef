# FSNI: F# Native Interactive

## Why Keep Interactive Module

The Interactive module (`src/Compiler/Interactive/fsi.fs`) is kept in FNCS even though:
1. FNCS is for type checking, not code generation
2. The current fsi.fs uses IL generation which FSNI won't use

**Rationale**: FSNI will leverage FNCS for type checking, but replace the IL backend with MLIR via Firefly/Alex.

## Current fsi.fs Architecture

```
User Input → Parse → Type Check (FCS) → Generate IL → .NET JIT → Execute
```

Uses IL helpers: `mkILTypeDefs`, `mkILCustomAttrs`, `mkILSimpleModule`, etc.

## Future FSNI Architecture

```
User Input → Parse → Type Check (FNCS) → PSG → Alex → MLIR → LLVM ORC JIT → Execute
```

**Key change**: IL generation is completely replaced with MLIR generation.

## What to Keep from fsi.fs

- Input handling and REPL loop structure
- Session state management patterns
- Error reporting integration
- Command parsing (`:help`, `:reset`, `:memory`, etc.)

## What Will Be Replaced

- All IL generation code (`mkIL*` calls)
- .NET JIT execution
- GC-based memory management
- System.Reflection-based value display

## IL Helper Pruning Decision

Deleted from IL.fs (unused, not needed for FSNI either):
- `typesOfILParams`
- `mkILFieldsLazy`, `emptyILFields`
- `mkILMethodsFromArray`, `mkILMethods`, `emptyILMethods`
- `emptyILProperties`
- `emptyILEvents`
- `emptyILMethodImpls`
- `mkILNestedTyRef`

Kept (used by fsi.fs currently):
- `mkILTypeDefs`, `mkILTypeDefsFromArray`, `emptyILTypeDefs`
- `mkILCustomAttrs`, `storeILCustomAttrs`
- `mkILTy`, `mkILArrTy`
- `mkILSimpleModule`
- `mkILExportedTypes`

When FSNI is built, the kept helpers will also become dead code as fsi.fs is rewritten.

## FSNI Implementation Phases

1. FNCS completes (type checking works)
2. Firefly/Alex MLIR generation stabilizes
3. Create FSNI frontend using FNCS + Alex
4. Replace fsi.fs IL code with MLIR backend
5. Add ORC JIT integration

## Reference

See Firefly docs: `/docs/FSNI_Architecture_Guide.md`

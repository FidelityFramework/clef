# Checking.Native/ Audit - FCS Preservation Status

> **Audit Date**: January 2, 2026
> **Status**: CRITICAL GAP IDENTIFIED

## Summary

The current `Checking.Native/` module is a **complete replacement** of FCS type checking, NOT a modification that preserves FCS infrastructure. Design-time capabilities from FCS are **NOT preserved**.

## Files Audited

| File | Purpose | Status |
|------|---------|--------|
| `CheckExpressions.fs` | Expression type checking | REPLACEMENT (not FCS-based) |
| `NativeService.fs` | Service interface | REPLACEMENT (not FCS-based) |
| `NameResolution.fs` | Compositional name resolution | NEW (correct architecture, NOT USED) |
| `NativeTypes.fs` | Native type definitions | NEW |
| `NativeGlobals.fs` | Global type environment | NEW |
| `SRTPResolution.fs` | SRTP resolution | NEW |
| `UnionFind.fs` | Type inference | NEW |
| `Unify.fs` | Type unification | NEW |
| `SemanticGraph.fs` | PSG construction | NEW |

## FCS Infrastructure Status

### PRESERVED (Used Correctly)

| FCS Component | Usage in FNCS |
|--------------|---------------|
| `SynExpr`, `SynModule`, `SynBinding` | Parser output consumed by Checking.Native |
| `range` | Source locations preserved |
| Parser infrastructure | FCS parser is used unchanged |

### NOT PRESERVED (Missing)

| FCS Component | Purpose | FNCS Status |
|--------------|---------|-------------|
| `FSharpSymbol` | Symbol info for navigation | NOT USED |
| `FSharpExpr` | Typed tree | NOT USED |
| `FSharpCheckFileResults` | Per-file analysis | NOT USED |
| `GetToolTip` | Hover information | NOT AVAILABLE |
| `GetDeclarationLocation` | Go to definition | NOT AVAILABLE |
| `GetSymbolUseAtLocation` | Find symbol | NOT AVAILABLE |
| `GetAllUsesOfAllSymbols` | Find references | NOT AVAILABLE |
| `SemanticClassification` | Syntax highlighting | NOT AVAILABLE |

## Critical Issues Found

### Issue 1: NameResolution.fs - NOW INTEGRATED ✓

The compositional resolver module is now integrated:
- `CheckExpressions.fs` imports `NameResolution`
- `TypeEnv.Resolution` uses `ResolutionContext` (not Map<string, Binding>)
- `addBinding` uses `NameResolution.registerBinding`
- `tryLookupBinding` uses `NameResolution.resolve`
- `addOpen` function added for namespace opens
- `NativeService.fs` processes `SynModuleDecl.Open` declarations

### Issue 2: BCL Heuristic - CLEANED UP ✓

BCL detection has been cleaned up:
- `isBclReference` now only checks definitively BCL prefixes: `System.`, `Microsoft.`, `mscorlib.`, `netstandard.`
- Removed library-aware heuristics like `Console. && not Alloy`
- Purpose: User-friendly FS8500 errors (better than generic "undefined")
- BCL remains structurally impossible via compositional resolver

### Issue 3: No Design-Time API Surface

FNCS currently provides:
- `parseString` / `parseStringWithDefaults`
- `checkExpression` / `checkLetBinding` / `checkModuleDecl`
- `parseAndCheck`

FNCS does NOT provide (but SHOULD for editor services):
- Symbol lookup at position
- Declaration location resolution
- Reference finding
- Hover information

## Recommended Actions

### Phase 2: Integrate NameResolution.fs

1. **Refactor TypeEnv**
   - Replace `Bindings: Map<string, Binding>` with `ResolutionContext`
   - Use `NameResolution.resolve` for lookups

2. **Process `open` Declarations**
   - Currently ignored in `checkModuleDecl`
   - Should call `NameResolution.addOpen`

3. **Remove BCL Heuristics**
   - Delete `isBclReference` function
   - BCL structurally impossible when using compositional resolver

### Future: Restore Design-Time Infrastructure

**CRITICAL**: Native types are INTRINSIC to FNCS. They are the type universe, not wrappers or mappings.

The path forward is to build symbol tracking infrastructure that works with FNCS's native type system directly. FCS symbol infrastructure assumes BCL types - it cannot be "wrapped" or "adapted" because the type universes are fundamentally different.

Options:
1. **Build native symbol infrastructure**: Create symbol tracking in FNCS that understands native types intrinsically
2. **Extend SemanticGraph**: Add symbol location and reference tracking to SemanticNode

The goal is editor services (hover, go-to-definition, find-references) that understand native types as first-class citizens, not as translations of BCL types.

## Architectural Principle Reminder

> **FNCS outputs a PSG that is "correct by construction"**

The current implementation has the right goal but incomplete execution. The compositional resolver (NameResolution.fs) embodies the correct pattern - it just needs integration into the actual type checking flow.

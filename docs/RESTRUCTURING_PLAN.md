# clef Directory Restructuring Plan

**Date**: January 2026
**Status**: DRAFT - Awaiting Review

---

## Guiding Principle: NTU Coherence

The Native Type Universe (NTU) is the single source of truth for types in native compilation. All design-time tooling (LSP, autocomplete, hover, diagnostics) should resolve types through NTU, not through FSharpType/reflection.

```
┌────────────────────────────────────────────────────────────────┐
│  Source Code                                                   │
│      ↓                                                         │
│  Parser (SynExpr, SynPat, SynType) ← Syntax layer preserved    │
│      ↓                                                         │
│  NTU Resolution ← Direct lookup, no reflection                 │
│      ↓                                                         │
│  NativeType / SemanticGraph                                    │
│      ↓                                                         │
│  MLIR → LLVM → Native Binary                                   │
└────────────────────────────────────────────────────────────────┘
```

**Key insight**: SynType is valuable as **syntax** (parser output) but unnecessary as **indirection** (callback threading). Type resolution is a direct NTUKind lookup.

---

## Phase 1: DELETE - Remove Dead Code

### 1.1 `Microsoft.FSharp.Compiler/` → DELETE

**Reason**: Empty placeholder with only `let main _ = 0`

```bash
rm -rf src/Microsoft.FSharp.Compiler/
```

### 1.2 `FSharp.VisualStudio.Extension/` → DELETE (or ARCHIVE)

**Reason**: VS extension not priority for native tooling. ClefAutoComplete will be the primary IDE integration path.

```bash
rm -rf src/FSharp.VisualStudio.Extension/
# OR: mv src/FSharp.VisualStudio.Extension/ archive/
```

### 1.3 `Microsoft.CommonLanguageServerProtocol.Framework.Proxy/` → EVALUATE

**Reason**: Contains only a .csproj reference. If we use a different LSP library, delete. Otherwise keep for protocol types.

```bash
# Check if anything references it
grep -r "CommonLanguageServerProtocol" src/ --include="*.fsproj"
```

---

## Phase 2: RENAME - Adapt for Native Context

### 2.1 `FSharp.Compiler.LanguageServer/` → `FSharp.Native.Compiler.LanguageServer/`

**Current state**: Uses FCS patterns (FSharpWorkspace, FSharpType)
**Target state**: Uses NTU patterns (NativeWorkspace, NativeType)

```bash
mv src/FSharp.Compiler.LanguageServer/ src/FSharp.Native.Compiler.LanguageServer/
```

**Required changes**:
- Rename namespace: `FSharp.Compiler.LanguageServer` → `FSharp.Native.Compiler.LanguageServer`
- Replace `FSharpWorkspace` with native workspace concept
- Replace FSharpType resolution with NTU resolution
- Update project file name and references

### 2.2 `FSharp.Compiler.Interactive.Settings/` → `FSharp.Native.Compiler.Interactive.Settings/`

**Current state**: REPL settings with CLR event loop
**Target state**: Native REPL settings (may need different event model)

```bash
mv src/FSharp.Compiler.Interactive.Settings/ src/FSharp.Native.Compiler.Interactive.Settings/
```

**Required changes**:
- Rename namespace
- Evaluate if event loop model applies to native context
- Update project file

### 2.3 `fsi/` → `fnsi/` (Clef Interactive)

**Current state**: F# Interactive targeting CLR
**Target state**: Native REPL with JIT or interpreted execution

```bash
mv src/fsi/ src/fnsi/
```

**Required changes**:
- Rename projects within
- Adapt for native execution model
- Consider MLIR interpreter or native JIT approach

---

## Phase 3: EVALUATE - Determine Fate

### 3.1 `FSharp.Core/` → ARCHIVE (Reference Only)

**Current state**: Full FSharp.Core BCL implementation (~34k lines)
**Native reality**: FSharp.Core is NOT used at runtime in native compilation

**Options**:
1. **ARCHIVE**: Move to `reference/FSharp.Core/` - Keep as pattern reference
2. **DELETE**: Remove entirely - NTU defines what exists
3. **EXTRACT**: Pull specific patterns into CCS documentation

**Recommendation**: ARCHIVE. The code documents F# semantics that inform CCS intrinsic design, but should not be in the active `src/` tree.

```bash
mkdir -p reference/
mv src/FSharp.Core/ reference/FSharp.Core/
```

### 3.2 `FSharp.DependencyManager.Nuget/` → KEEP (Design-Time)

**Reason**: Package resolution is still needed for design-time tooling. When user writes `#r "nuget: Foo"`, we need to resolve package metadata (even if runtime is native).

**Changes needed**:
- Ensure it doesn't assume runtime loading
- Metadata extraction only, no assembly loading

---

## Phase 4: INTERNAL COMPILER CLEANUP

### 4.1 `Compiler/TypedTree/` → EVALUATE

**Question**: Is FCS TypedTree (`FSharpExpr`) still needed?

**Current use**: PSG construction uses typed tree overlay for SRTP resolution

**Analysis**:
- If SRTP resolution moves to NTU, TypedTree may become unnecessary
- If we keep FCS frontend, TypedTree remains useful for inference results

**Recommendation**: KEEP for now, mark for future evaluation

### 4.2 `Compiler/Service/` → EVALUATE

**Question**: What FCS services are needed for native?

**Likely needed**:
- Parsing services (SynExpr production)
- Symbol resolution basics

**Likely NOT needed**:
- Assembly metadata loading
- FSharpType construction
- Reflection-based type resolution

### 4.3 `Compiler/Symbols/` → EVALUATE

**Question**: Are FCS symbols (FSharpSymbol hierarchy) needed?

**Native alternative**: PSG nodes carry semantic information directly. FSharpSymbol may be unnecessary indirection.

---

## Phase 5: NEW STRUCTURE

### 5.1 Proposed Final Structure

```
src/
├── Compiler/                              # Core compiler (KEEP, already native)
│   ├── Baker/                             # HOF decomposition
│   ├── Nanopass/                          # PSG transformations
│   ├── NativeTypedTree/                   # NTU, type checking
│   ├── PSGSaturation/                     # Semantic graph
│   ├── SyntaxTree/                        # Parsing (FCS syntax)
│   ├── Driver/                            # Compilation orchestration
│   ├── Facilities/                        # Error handling, diagnostics
│   ├── Utilities/                         # Shared utilities
│   └── ...
│
├── FSharp.Native.Compiler.LanguageServer/ # LSP for IDE integration
│   ├── Handlers/                          # LSP request handlers
│   ├── Common/                            # Shared LSP types
│   └── ...
│
├── FSharp.Native.Compiler.Interactive/    # Native REPL
│   └── Settings/                          # REPL configuration
│
├── FSharp.DependencyManager.Nuget/        # Package resolution (design-time)
│
└── fnsi/                                  # Native F# Interactive executable

reference/                                 # Archived for reference only
└── FSharp.Core/                           # BCL patterns (not compiled)
```

---

## Execution Order

### Step 1: Safe Deletions
```bash
# Delete empty/unused directories
rm -rf src/Microsoft.FSharp.Compiler/
rm -rf src/FSharp.VisualStudio.Extension/
```

### Step 2: Archive FSharp.Core
```bash
mkdir -p reference/
mv src/FSharp.Core/ reference/FSharp.Core/
# Update solution file to remove FSharp.Core project
```

### Step 3: Rename Language Server
```bash
mv src/FSharp.Compiler.LanguageServer/ src/FSharp.Native.Compiler.LanguageServer/
# Update namespaces in all .fs files
# Update .fsproj filename and contents
# Update solution references
```

### Step 4: Rename Interactive Settings
```bash
mv src/FSharp.Compiler.Interactive.Settings/ src/FSharp.Native.Compiler.Interactive/
# Consolidate Settings into subdirectory
# Update namespaces and project files
```

### Step 5: Rename fsi
```bash
mv src/fsi/ src/fnsi/
# Update internal project names
# Update build scripts
```

### Step 6: Evaluate and Clean Compiler Internals
- Review Compiler/Service/ for needed vs legacy code
- Review Compiler/Symbols/ for needed vs legacy code
- Review Compiler/TypedTree/ for continued necessity

---

## Validation Checklist

After restructuring:

- [ ] `dotnet build` succeeds for all remaining projects
- [ ] No broken project references in .sln
- [ ] No dead namespace references in code
- [ ] Firefly compiler still builds against clef
- [ ] Regression tests pass
- [ ] LSP server starts (even if limited functionality)

---

## Open Questions

1. **TypedTree dependency**: Can we eliminate FSharpExpr dependency entirely, or is it needed for type inference results?

2. **FCS Service boundary**: What's the minimal FCS surface needed? Just parsing?

3. **Interactive model**: For native REPL, do we JIT compile or interpret? MLIR interpreter?

4. **Package metadata**: How do we extract type information from NuGet packages without loading assemblies?

---

## Notes

This plan prioritizes **clarity over incrementalism**. The goal is a clean native compiler structure where:

- NTU is the type universe (no FSharpType indirection)
- Syntax parsing is preserved (SynExpr, SynPat, SynType as syntax)
- Design-time tooling works without reflection
- The codebase structure reflects native compilation reality

# Alex XParsec Remediation Progress Checklist

**Plan:** `/home/hhh/.claude/plans/elegant-marinating-summit.md`  
**Started:** January 27, 2026  
**Last Updated:** January 28, 2026  
**Status:** In Progress - Phase 0 Complete, Documentation Cleanup Complete

---

## Phase 0: NULL ERADICATION ✅ COMPLETE (January 28, 2026)

**Goal:** Remove ALL null references from PRDs, memories, documentation, infrastructure, and code.

**Status:** ✅ COMPLETE - Audit passes with zero null references

**Completed Work:**
- ✅ Collection Witnesses (Map, List, Set) - 678 lines, null-free, compositional
- ✅ MemoryWitness & LambdaWitness - Using `TypeSizing.computeSize` (compile-time sizeof)
- ✅ Infrastructure - No `nullPtrSSA` or `SizeNullPtrSSA` in PSGElaboration
- ✅ C-04-CoreCollections.md - Correct flat closure model documented
- ✅ C-02-HigherOrderFunctions.md - Fixed env pointer reference (line 44)
- ✅ FNCS_Architecture.md - Consistent null-free semantics
- ✅ FNCS_FSharp_Feature_Audit.md - Correct null handling documented
- ✅ Validation script passes - Zero null references across 156 files

**PRD Null References (All Legitimate):**
- T-02, T-04: pthread FFI (`pthread_mutex_init(%mutex, %null)`)
- F-01, F-02: C string null terminators in documentation
- F-08: "nullable values" (describing Option type semantics)
- C-05: Negative example (documents WRONG approach with nulls)

**Duration:** Complete (all work done in previous session)

---

## CRITICAL DISCOVERY: PSGElaboration Pollution (January 28, 2026)

### Problem Found

During Phase 0 audit, discovered MAJOR architectural misunderstanding:
- ❌ Described witnesses as "deciding SSA counts" and performing "analysis"
- ❌ Suggested witnesses "wait for coeffects" or "need future coeffects"
- ❌ Pollution in memories: `coeffect_analysis`, `psg_awareness_implementation_protocol`
- ❌ Pollution in code: SeqWitness.fs TODOs, ElisionPatterns.fs misleading comments

### Root Cause

**Incorrect understanding:** Thought coeffects were "analysis phases during Alex"  
**Correct understanding:** Coeffects are OUTPUTS of PSGElaboration passes (above Alex)

**The Pipeline:**
```
FNCS → PSGElaboration (ALL analysis) → Coeffects → Alex (reads + emits) → MLIR
```

### Cleanup Work Completed ✅

**Memories Cleaned:**
1. ✅ `coeffect_analysis` - Complete rewrite (was "Coeffect Analysis" → now "Coeffects - Pre-Computed Results")
2. ✅ `psg_awareness_implementation_protocol` - Complete rewrite (clarified FNCS vs PSGElaboration)
3. ✅ `alex_compositional_architecture_elements_patterns_witnesses` - Added PSGElaboration context section

**Code Files Fixed:**
1. ✅ `SeqWitness.fs` - Fixed pollution:
   - Removed "TODO: need coeffects" comments
   - Added `extractMutableBindings` that READS from PSG (not analyzes)
   - Fixed `captureInfosToVals` to use proper type mapping
   - Updated all comments to reflect PSGElaboration provides everything

2. ✅ `ElisionPatterns.fs` - Fixed pollution:
   - Line 185: Clarified capture types from ClosureLayout coeffect (PSGElaboration)
   - Line 797: Fixed string literal comment (StringCollection from PSGElaboration)

**Code Files Verified Clean:**
- ✅ All Elements/*.fs (8 files) - No pollution
- ✅ LazyWitness.fs - Uses ctx.Zipper, reads SSAs from coeffects (CANONICAL)
- ✅ ArithWitness.fs - Clean
- ✅ LiteralWitness.fs - Clean

**Duration:** ~4 hours (unplanned but critical)

---

## Phase 1: Elements Layer Foundation ⬜ NOT STARTED

**Goal:** Consolidate atomic MLIR operations into ~5-6 files organized by MLIR tier

**Status:** Elements already exist and are clean. May skip this phase or audit for completeness.

**Existing Elements:**
- `MLIRElements.fs` - Struct operations (already ~50 lines)
- `LLVMElements.fs` - Memory/call/branch ops
- `ArithElements.fs` - Arithmetic operations
- `SCFElements.fs` - Structured control flow
- `FuncElements.fs` - Function operations
- `CFElements.fs` - Control flow
- `IndexElements.fs` - Index operations
- `VectorElements.fs` - Vector operations

**Validation Checklist:**
- [ ] All Elements are `module internal`
- [ ] All functions use `parser { }` CE
- [ ] All functions prefixed with `p`
- [ ] Each function emits EXACTLY ONE MLIROp
- [ ] No composition logic (that's Patterns)

**Estimated Duration:** 2-4 hours (audit/validation only, may skip)

---

## Phase 2: Patterns Layer ⬜ NOT STARTED

**Goal:** Compose Elements into semantic patterns

**Primary File:** `src/Alex/Patterns/ElisionPatterns.fs`

**Current:** ~920 lines with many patterns already implemented  
**Target:** ~400-500 lines of composable patterns (may already exceed due to growth)

**Status:** ElisionPatterns.fs already has many patterns. Need to audit for:
- Pattern completeness (are gaps filled?)
- Proper Element composition
- No direct MLIR construction
- Reusability across witnesses

**Key Patterns to Verify:**
- ✅ Lazy patterns (pLazyStruct, pBuildLazyStruct, pBuildLazyForce) - EXIST
- ✅ Seq patterns (pSeqStruct, pBuildSeqStruct) - EXIST
- ⚠️ ForEach pattern (pBuildForEachLoop) - EXISTS but UNIMPLEMENTED (pfail gap)
- ✅ Closure patterns (pFlatClosure, pClosureCall) - EXIST
- ✅ Arithmetic patterns (pAddInt, pSubInt, pMulInt, etc.) - EXIST
- ✅ DU patterns (pDUCase, pOptionSome, pResultOk, etc.) - EXIST

**Estimated Duration:** 4-6 hours (audit + gap filling)

---

## Phase 3: Witness Refactoring 🔄 IN PROGRESS

**Goal:** Rewrite all witnesses to LazyWitness pattern (~40 lines each)

**Progress:**

### ✅ Completed Witnesses (Clean, follow canonical pattern)
1. ✅ **LazyWitness.fs** (38 lines) - CANONICAL EXAMPLE
2. ✅ **ArithWitness.fs** (~135 lines) - Clean, uses ctx.Zipper, delegates to Patterns
3. ✅ **LiteralWitness.fs** (~61 lines) - Clean, uses ctx.Zipper, delegates to Patterns
4. ✅ **SeqWitness.fs** (~152 lines) - Fixed pollution, uses ctx.Zipper, delegates to Patterns

### ✅ Completed Witnesses (8 total)
1. ✅ **LazyWitness.fs** (38 lines) - CANONICAL EXAMPLE
2. ✅ **ArithWitness.fs** (~135 lines) - Clean, uses ctx.Zipper, delegates to Patterns
3. ✅ **LiteralWitness.fs** (~61 lines) - Clean, uses ctx.Zipper, delegates to Patterns
4. ✅ **SeqWitness.fs** (~152 lines) - Fixed pollution, uses ctx.Zipper, delegates to Patterns
5. ✅ **MapWitness.fs** (262 lines) - Clean-room rebuild, collection primitives
6. ✅ **ListWitness.fs** (183 lines) - Clean-room rebuild, collection primitives
7. ✅ **SetWitness.fs** (233 lines) - Clean-room rebuild, collection primitives
8. ✅ **OptionWitness.fs** (127 lines, was 257) - **JUST COMPLETED (Jan 28)** - Clean-room rebuild

### ⬜ Witnesses Not Yet Started (9+ remaining)

**Priority Order (from plan):**

**Per-Witness Process:**
1. Audit (30 min) - Create extraction plan table
2. Extract to Elements (30 min) - Should already be done
3. Create Patterns (1 hour) - Add to ElisionPatterns.fs
4. Add XParsec Combinators (30 min) - If needed, add to PSGCombinators.fs
5. Rewrite Witness (30 min) - Follow LazyWitness pattern
6. Validation (15 min) - Line count, no MLIR ops, compile, test

**CHECKPOINT:** Run regression tests after EACH witness before proceeding.

**Estimated Duration:** 10-12 hours for all witnesses

---

## Phase 4: Architectural Enforcement ⬜ NOT STARTED

**Goal:** Prevent architecture degradation via CI

**Tasks:**
- [ ] Create `tests/ArchitectureValidation.fsx` script
- [ ] Update CLAUDE.md with witness creation protocol
- [ ] Wire into CI/build process

**Estimated Duration:** 2-3 hours

---

## Phase 5: Documentation ⬜ NOT STARTED

**Goal:** Preserve architectural understanding

**Tasks:**
- [ ] Update `docs/Alex_Architecture_Overview.md` with remediation results
- [ ] Update Serena memory `alex_element_pattern_witness_architecture`
- [ ] Create `docs/Alex_Feature_Addition_Guide.md`

**Estimated Duration:** 2-3 hours

---

## Phase 6: Validation ⬜ NOT STARTED

**Goal:** Verify functionality preserved

**Tasks:**
- [ ] Run full regression test suite
- [ ] Verify quantitative metrics (LOC, MLIR ops, etc.)
- [ ] Verify qualitative criteria (LazyWitness pattern, etc.)
- [ ] Check functional criteria (samples compile and run correctly)

**Estimated Duration:** 2-4 hours

---

## Phase 7: Knowledge Transfer ⬜ NOT STARTED

**Goal:** Team understanding

**Tasks:**
- [ ] Team review session
- [ ] Update project onboarding

**Estimated Duration:** 1-2 hours

---

## Session Notes (January 28, 2026)

### Architectural Clarification

**Critical correction from user:** "LazyWitness DOES NOT decide SSA count. When the witness is activated the SSAs are already assigned in PSG Elaboration."

This triggered comprehensive cleanup of:
- Memory pollution (3 memories completely rewritten)
- Code pollution (SeqWitness, ElisionPatterns fixed)
- Architectural understanding (mise-en-place principle)

**Key learnings:**
1. PSGElaboration (Firefly MiddleEnd, above Alex) performs ALL analysis
2. Witnesses are THIN observers (~40 lines) that READ and EMIT
3. Coeffects are OUTPUTS of PSGElaboration, not computed during Alex
4. SSA assignment uses structural analysis in PSGElaboration (e.g., `computeSeqExprSSACost`, `countMutableBindingsInSubtree`)
5. Witnesses just READ from PSG and lookup pre-assigned SSAs

**User directive:** "We need to make sure that the documents and memories are clean *first* as context roll-over means the salience of these learnings may be lost."

### README Improvement

Fixed HelloWorld example from low-level syscalls (`Sys.write`, `NativeStr.ptr`) to idiomatic F# (pipe operators, string interpolation, `Console.writeln`). Now shows the F# experience users will actually have.

---

## Next Steps

**Immediate (as of Feb 2026):**
1. ✅ DU stack escape fix implemented (commit 02519cc) — samples 01-06 working
2. Continue Phase 3 (Witness Refactoring) if/when focus returns to remediation
3. Run full regression after any further witness changes

**Note (Feb 2026):** Active work shifted to escape analysis generalization (PRD-06 DU fix).
See `escape_analysis_generalized_design_feb2026` memory for that work.
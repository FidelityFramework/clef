# .NET Determinism Landmines

> **Suggested blog post title**: "The Many Landmines in .NET"
> **Status**: Collecting landmines — do NOT write the blog post yet. Add new discoveries here as they arise.

## Why This Matters

Firefly is a deterministic compiler: identical input MUST produce byte-identical output. This is a core architectural principle (see "Doubling Down" on SpeakEZ blog). .NET's runtime makes several choices that silently violate this guarantee. These are invisible in typical application development but fatal for a compiler that must be referentially transparent.

**This is a primary motivation for self-hosting as soon as possible.** Once Firefly compiles itself, these .NET landmines disappear entirely.

---

## Landmine #1: `Async.Parallel` + Global Mutable State

**Discovery**: February 2026, Sample 05 (Discriminated Unions)
**Symptom**: 7/10 compilations succeeded, 3/10 failed with "arguments not yet witnessed" errors
**Root cause**: Baker's `FanOut.fs` used `Async.Parallel` to create recipes concurrently. Each recipe calls `NodeId.fresh()`, a global mutable `int` counter. Concurrent access = non-deterministic NodeId allocation = different PSGs each run.

**Fix**: Replaced `Async.Parallel` with sequential `List.map` in `FanOut.fs`.

**Lesson**: ANY use of `Async.Parallel` (or `Task.WhenAll`, `Parallel.ForEach`, etc.) that touches global mutable state is a determinism violation. In a compiler where node identity matters, this is catastrophic.

**Detection method**: Compile same sample 3+ times with `-k`, diff the intermediate PSG JSON files. Non-determinism shows up as different NodeId values for the same semantic content.

---

## Landmine #2: `String.GetHashCode()` Randomized Per-Process

**Discovery**: February 2026, Sample 05 (after fixing Landmine #1)
**Symptom**: MLIR output differed between runs — string global names like `@str_170150206` vs `@str_1739374349`
**Root cause**: `LiteralPatterns.fs` used `content.GetHashCode()` to derive global reference names. Since .NET Core, `String.GetHashCode()` is randomized per-process (security mitigation for hash-flooding attacks). The hash seed changes every time the compiler runs.

**Fix**: Replaced with FNV-1a deterministic hash (offset basis 2166136261, prime 16777619) operating on UTF-8 bytes.

**Lesson**: NEVER use `.GetHashCode()` on strings (or any reference type) for anything that affects compiler output. .NET's documentation even warns about this, but it's easy to miss. The insidious part: the compiled binaries still RUN correctly — they just have different symbol names, so binary diffing fails.

**Detection method**: Compile same sample 3+ times with `-k`, diff the MLIR output files.

---

## Landmine #3: .NET Dictionary Iteration Order

**Status**: NOT hit in Firefly (SemanticGraph uses F# `Map`), but worth documenting.

.NET `Dictionary<K,V>` does not guarantee iteration order. Even with the same keys inserted in the same order, iteration order can vary across .NET versions, platforms, or after resize operations. Any code that iterates a Dictionary and produces ordered output (code generation, serialization) is non-deterministic.

**Mitigation**: Use F# `Map<K,V>` (balanced binary tree, deterministic key-ordered iteration) or `SortedDictionary<K,V>` if you must use BCL types.

---

## Pattern: How to Audit for More Landmines

1. **Search for `Async.Parallel`**, `Task.WhenAll`, `Parallel.ForEach`, `PLINQ` — any parallelism touching mutable state
2. **Search for `.GetHashCode()`** — especially on strings, but also on any reference type
3. **Search for `Dictionary<`** — any iteration that affects output ordering
4. **Search for `DateTime.Now`**, `Guid.NewGuid()`, `Random()` — obvious non-determinism sources
5. **Search for `Environment.`** — process-specific values that may differ between runs
6. **Compile 3+ times with `-k`**, diff each intermediate stage to find the FIRST point of divergence

---

## Self-Hosting Endgame

Once Firefly compiles itself:
- No .NET runtime hash randomization
- No BCL Dictionary ordering surprises  
- No temptation to use `Async.Parallel` (Firefly's concurrency model is explicit)
- Determinism is guaranteed by construction, not by vigilance against .NET footguns

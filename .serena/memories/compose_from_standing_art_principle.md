# Compose from Standing Art Principle (January 2026)

## The Insight

**New features MUST compose from recently established patterns, not invent parallel mechanisms.**

When implementing new language features (Lazy, Seq, etc.), the correct approach is to identify what existing architectural patterns apply and EXTEND them, rather than creating feature-specific implementations.

## The Anti-Pattern: Feature-Specific Implementation

```
BAD: "Lazy needs closures, so let's build lazy-specific closure handling"
     → Creates {code_ptr, env_ptr} with nulls for no-capture case
     → Reinvents capture handling specific to lazy
     → Diverges from established closure architecture
```

This happened in January 2026 when an initial Lazy implementation used `{code_ptr, env_ptr}` with null env_ptr - completely ignoring that flat closures had JUST been established as the architecture.

## The Correct Pattern: Compose from Standing Art

```
GOOD: "Lazy needs closures. What's our closure architecture?"
      → Flat closures: {code_ptr, cap₀, cap₁, ...}
      → Lazy extends this: {computed, value, code_ptr, cap₀, cap₁, ...}
      → Reuse capture analysis from Lambda
      → Reuse SSA cost patterns from closure handling
```

## Key Questions Before Implementing Any New Feature

1. **What existing patterns does this feature need?**
   - Closures? Use flat closure architecture
   - Capture analysis? Reuse Lambda's `computeCaptures`
   - SSA assignment? Follow coeffect pattern
   - Struct layout? Follow memory layout principles

2. **What was RECENTLY established?**
   - Check the last 2-3 PRDs for new patterns
   - Read Serena memories for architectural decisions
   - Look at the most recent blog posts for design rationale

3. **How does this feature EXTEND existing patterns?**
   - Identify the base pattern
   - Identify what's new/different
   - Ensure the extension is principled, not ad-hoc

## Concrete Example: PRD-14 Lazy Values

### What Lazy Needed
- Deferred computation (thunk)
- Capture of free variables
- Memoization (future)

### Standing Art Available (January 2026)
- **PRD-11 Flat Closures**: `{code_ptr, cap₀, cap₁, ...}` - NO env_ptr
- **Capture Analysis**: `collectVarRefs` + `computeCaptures` in Applications.fs
- **Coeffect SSA Assignment**: Pre-computed SSA counts, witness observes
- **Four Pillars of Transfer**: Coeffects, Active Patterns, Zipper, Templates

### Correct Composition
```
Lazy<T> = PRD-11 Flat Closure + memoization state
        = {computed: i1, value: T, code_ptr: ptr, cap₀, cap₁, ...}
        
LazyExpr capture analysis = Lambda capture analysis (reuse computeCaptures)

LazyLayout coeffect = ClosureLayout coeffect pattern
```

## The "Ripple Up" Effect

Getting primitives right creates positive ripple effects:

```
Flat Closures (PRD-11)
    ↓ composes into
Lazy Values (PRD-14) - extended flat closure
    ↓ composes into
Sequences (PRD-15) - lazy + iterator state
    ↓ composes into  
Seq Operations (PRD-16) - higher-order seq functions
    ↓ enables
Async (future) - same pattern, different state
```

If PRD-11 closures were wrong, ALL downstream features would inherit that wrongness.

## Process Requirements for Future PRDs

### Before Writing Implementation Code

1. **Review Standing Art**
   - Read the previous 2-3 PRDs
   - Read relevant Serena memories
   - Identify patterns that apply

2. **Identify Composition Points**
   - What existing types/patterns to extend?
   - What existing code to reuse?
   - What coeffects already exist?

3. **Document the Composition**
   - PRD should explicitly state "extends PRD-X pattern"
   - PRD should reference architectural memories
   - PRD should show how new feature composes from base

### During Implementation

4. **Verify Alignment**
   - Is this diverging from established patterns?
   - Am I reinventing something that exists?
   - Does this feel like special-case handling?

5. **Course Correct Early**
   - If implementation diverges, STOP
   - Review memories and PRDs
   - Ask: "What standing art am I ignoring?"

## Related Memories

- `closure_architecture_corrected` - The flat closure decision
- `memory_layout_and_raii` - Struct layout principles
- `coeffect_compilation_strategy` - Coeffect patterns
- `lazy_thunk_calling_convention` - Option B decision

## The Mantra

> "The standing art composes up. Use it."

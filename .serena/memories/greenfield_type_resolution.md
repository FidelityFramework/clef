# Greenfield Type Resolution (January 2026)

## Status: DELETION COMPLETE

The following have been deleted:
- `SynTypes.fs` - old SynType → NativeType conversion
- `NativeGlobals.fs` - old type constructor registry
- `tryFindBuiltinTyCon` in NativeTypes.fs

## Compiler Breaks (These ARE the Spec)

Building FNCS now produces errors that document exactly what greenfield must provide:

### In Coordinator.fs

**Type References (env.Globals.*):**
- `env.Globals.UnitType` - 17 occurrences
- `env.Globals.IntType` - 4 occurrences  
- `env.Globals.StringType` - 1 occurrence
- `env.Globals.CharType` - 3 occurrences
- `env.Globals.BoolType` - 1 occurrence

**Type Constructors:**
- `mkArrayType` - 3 occurrences
- `mkExprType` - 2 occurrences
- `mkLazyType` - 1 occurrence
- `mkSeqType` - 1 occurrence

### Across Expression Handlers

The `checkSynType` callback is threaded through:
- `Coordinator.fs` - definition and dispatch
- `NativeService.fs` - top-level binding checking
- `Patterns.fs` - pattern type annotations
- `Bindings.fs` - let binding type annotations
- `Applications.fs` - TypeApp handling
- `TypeOperations.fs` - casts and type tests

## Greenfield Principles

1. **No central globals registry** - Type resolution should be structural
2. **Preserve polymorphism** - Don't resolve platform types too early
3. **NTUKind is the foundation** - All types flow from NTUKind in NativeTypes.fs
4. **Platform resolution at Alex** - Width/alignment resolved by platform quotations

## What Greenfield Must Provide

1. **Primitive type constructors** - Direct NativeType construction for unit, int, string, char, bool, array, lazy, seq, expr

2. **SynType → NativeType conversion** - New approach that:
   - Preserves type variables
   - Handles type applications
   - Resolves type abbreviations
   - Does NOT assume platform width

3. **TypeEnv without Globals** - Either:
   - Remove `Globals` field entirely, OR
   - Replace with minimal needed state

## NOT in Scope

- Intrinsics (separate from type resolution)
- SRTP resolution (handled by SRTPResolution.fs)
- Constraint solving (handled by Unify.fs)

## Files to Create/Modify

TBD after greenfield design is complete.

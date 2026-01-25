# Greenfield Type Resolution (January 2026)

## Status: BOUNDARY CONVERSION COMPLETE

The SynType elimination work is complete. SynType now exists only transiently at the parser boundary.

## What Was Done

1. **Removed `checkSynType` callback threading** - Eliminated 69 occurrences across 5 modules
2. **Implemented `resolveSynType`** - Single boundary conversion function in Types.fs
3. **Updated 21 conversion sites** - All `ELIMINATE_SYNTYPE` markers replaced with direct `resolveSynType env synType` calls

## Architecture

```
Parser → SynType → resolveSynType → NativeType → Type Checking
              ↑                          ↓
              │                          └── NativeType propagates everywhere
              └── SynType dies here
```

**Key principle**: SynType is transient. It exists because the parser cannot produce fully resolved types without type environment context. Once that context is available (via `env: TypeEnv`), SynType is converted immediately and discarded.

## Files Modified

| File | Changes |
|------|---------|
| `Types.fs` | Added `resolveSynType` and `resolveTypeName` functions |
| `TypeOperations.fs` | 4 conversion sites updated |
| `Applications.fs` | 6 conversion sites updated |
| `Bindings.fs` | 5 conversion sites updated |
| `Patterns.fs` | 2 conversion sites updated |
| `NativeService.fs` | 4 conversion sites updated |

## Documentation

See `/docs/fncs/syntype-boundary-conversion.md` for full architectural explanation.

## Type Width vs Type Identity

- **Type identity** (FNCS): `int32` → `NativeType.TInt32` 
- **Type width** (Alex): `NativeType.TInt32` → `i32` (4 bytes on platform X)

NativeType carries type identity; width is resolved downstream by Alex based on target platform.

## Remaining Globals

The `env.Globals` pattern still exists for:
- `unitType`, `intType`, `stringType`, etc. - Primitive type constants
- `mkArrayType`, `mkExprType`, etc. - Type constructor helpers

These are convenience accessors to NTUKind-based types in NativeTypes.fs, not a separate registry.

## What Greenfield Provides

1. **Primitive type constructors** - Direct NativeType construction via NativeTypes.Types module
2. **Type abbreviation resolution** - Via TypeEnv.TypeAbbrevs
3. **User-defined type resolution** - Via TypeEnv.TypeDefs
4. **Fresh type variables** - Via `freshTypeVar` for inference

## Not In Scope (Separate Concerns)

- Intrinsics (FNCS CheckExpressions.fs)
- SRTP resolution (SRTPResolution.fs)
- Constraint solving (Unify.fs)
- Platform width (Alex/Backend)

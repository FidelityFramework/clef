# UMX Integration into FNCS

## Goal

FSharp.UMX's `[<MeasureAnnotatedAbbreviation>]` pattern becomes **intrinsic to FNCS** - native types carry measure parameters without library workarounds.

## What UMX Provides (as library)

```fsharp
// Library workaround for non-numeric measures
[<MeasureAnnotatedAbbreviation>] type string<[<Measure>] 'm> = string
[<MeasureAnnotatedAbbreviation>] type Guid<[<Measure>] 'm> = Guid

// Tagging/untagging
let id: string<customerId> = %"cust-123"
```

## What FNCS Provides (intrinsic)

```fsharp
// Standard F# types with measure parameters for memory semantics
// Users write familiar type names; FNCS adds measure support
type Ptr<'T, [<Measure>] 'region, [<Measure>] 'access>  // Pointer with region/access
// string has native UTF-8 fat pointer semantics (no wrapper type)
// array<'T> has native semantics with optional region measures

// Memory regions and access kinds as first-class measures
[<Measure>] type peripheral
[<Measure>] type readOnly
[<Measure>] type readWrite
```

**Key Principle**: Users write standard F# type names (`string`, `array`, etc.). FNCS provides native semantics. Measure parameters add memory region/access tracking.

## Implementation Points in FNCS

| File | Change |
|------|--------|
| `TcGlobals.fs` | Native types with measure params, region/access measures |
| `TypedTree.fs` | Representation for measured non-numeric types |
| `ConstraintSolver.fs` | Region/access compatibility checking |
| Native type semantics | Standard types with measure params |
| `MemoryMeasures.fs` (new) | Memory region and access kind measures |

## Error Codes

- FS8001: Cannot read write-only pointer
- FS8002: Cannot write read-only pointer
- FS8003: Memory region mismatch

## Documentation

- `~/repos/FSharp.UMX/docs/fidelity/UMX_Integration_Plan.md` - Detailed plan
- `~/repos/fsnative-spec/docs/fidelity/FNCS_Specification.md` Parts 9-10 - Normative spec

## Status

UMX patterns to be absorbed during FNCS Phase 2-3 (Native Types).

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
// Native types defined WITH measure parameters
type NativePtr<'T, [<Measure>] 'region, [<Measure>] 'access>
type NativeStr<[<Measure>] 'encoding>
type NativeArray<'T, [<Measure>] 'region>

// Memory regions and access kinds as first-class measures
[<Measure>] type peripheral
[<Measure>] type readOnly
[<Measure>] type readWrite
```

## Implementation Points in FNCS

| File | Change |
|------|--------|
| `TcGlobals.fs` | Native types with measure params, region/access measures |
| `TypedTree.fs` | Representation for measured non-numeric types |
| `ConstraintSolver.fs` | Region/access compatibility checking |
| `NativeTypes.fs` (new) | Native type constructors with measures |
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

# Native Type Globals in FNCS

## Overview

FNCS (F# Native Compiler Services) defines the native type universe. The IL layer has been restructured to use native types instead of BCL types.

## Key Change: ILGlobals

**Before (BCL-based):**
```fsharp
member _.typ_Object = mkTy "System.Object"
member _.typ_String = mkTy "System.String"
member _.typ_Int32 = mkValTy "System.Int32"
```

**After (Native):**
```fsharp
member _.typ_String = mkValTy "string"
member _.typ_Int32 = mkValTy "int32"
// No typ_Object - there is no universal base type
```

## Eliminated BCL Concepts

These BCL concepts do not exist in native F#:

1. **obj / System.Object** - No universal base type
2. **System.Type** - No runtime type reflection
3. **System.Array** - Use typed arrays instead
4. **TypedReference** - Not available

## Native Type Semantics

| Type | Native Semantics |
|------|------------------|
| `string` | UTF-8 fat pointer (ptr, length) |
| `char` | Unicode code point (4 bytes) |
| `int32` | 32-bit signed integer |
| `bool` | 1-byte value |
| `option<'T>` | Value type, no null |

## Architecture

```
FNCS (fsnative) defines: Native type universe
    ↓
Alloy uses: Standard F# syntax, FNCS-defined types
    ↓
Firefly/Alex: Generates MLIR from typed tree
```

## Files

- `src/Compiler/AbstractIL/IL.fs` - ILGlobals with native types
- `src/Compiler/AbstractIL/IL.fsi` - Interface

## Relationship to TcGlobals

TcGlobals takes ILGlobals as a constructor parameter. The native types defined in ILGlobals flow through to TcGlobals's type references (`system_String_tcref` → will need renaming to `native_String_tcref` or similar).

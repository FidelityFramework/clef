# FNCS Built-in Bindings

## Summary

FNCS registers F# intrinsic functions and operators as built-in bindings in the type environment. These are defined in `NativeGlobals.BuiltInFunctions`.

## Categories of Built-in Bindings

### 1. Type Conversion Functions
- `int`, `int8`, `int16`, `int32`, `int64`, `nativeint`
- `byte`, `uint8`, `uint16`, `uint32`, `uint64`, `unativeint`
- `float`, `float32`, `decimal`, `double`, `single`
- `char`, `string`

### 2. Union Case Constructors
- `ValueSome`, `ValueNone` (voption)
- `Ok`, `Error` (Result)
- `Some`, `None` (option)

### 3. Arithmetic Operators (SRTP-based)
- `op_Addition`, `op_Subtraction`, `op_Multiply`, `op_Division`, `op_Modulus`

### 4. Comparison Operators
- `op_Equality`, `op_Inequality`
- `op_LessThan`, `op_GreaterThan`
- `op_LessThanOrEqual`, `op_GreaterThanOrEqual`

### 5. Bitwise Operators
- `op_BitwiseAnd`, `op_BitwiseOr`, `op_ExclusiveOr`
- `op_LeftShift`, `op_RightShift`

### 6. Logical Operators
- `op_BooleanAnd`, `op_BooleanOr`, `not`
- `op_UnaryNegation`, `op_LogicalNot`

### 7. Utility Functions
- `abs`, `ignore`, `sizeof`
- `nan`, `nanf`, `infinity`, `infinityf`
- `printf`, `printfn`, `sprintf`, `failwith`, `failwithf`
- `box`, `unbox` (BCL-dependent, emit warnings)

## Struct Type Constructor Registration

Types with `[<Struct>]` attribute are detected during type definition processing. Their names are registered as constructor bindings so they can be used in expressions like `Span(ptr, len)`.

The detection uses `hasStructAttribute` function in `NativeService.fs`.

## Key Files

- `src/Compiler/Checking.Native/NativeGlobals.fs` - `BuiltInFunctions` module
- `src/Compiler/Checking.Native/CheckExpressions.fs` - `createTypeEnv` uses `BuiltInBindings`
- `src/Compiler/Checking.Native/NativeService.fs` - `hasStructAttribute` for struct detection

## Status

As of 2026-01-02:
- All built-in bindings registered
- FNCS generates 12,453 nodes, 42 entry points for HelloWorldDirect sample
- Remaining "Variable not found" errors are in Alex/Firefly emission, not FNCS

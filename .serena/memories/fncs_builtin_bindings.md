# FNCS Built-in Bindings

## Summary

FNCS registers F# intrinsic functions and operators as built-in bindings in the type environment. (Type resolution via resolveSynType in Types.fs)

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

- (See NativeTypes.fs and Types.fs for type system)
- `src/Compiler/Checking.Native/CheckExpressions.fs` - `createTypeEnv` uses `BuiltInBindings`
- `src/Compiler/Checking.Native/NativeService.fs` - `hasStructAttribute` for struct detection

## Distinction: Built-in Functions vs Intrinsics

**Built-in Functions** (this memory):
- Type conversion, operators, union constructors
- Have F# semantics and can be expressed in F#
- Registered in type environment for type checking

**FNCS Intrinsics** (separate category):
- Operations native to the type universe
- Cannot be expressed in F#
- Emitted directly as MLIR operations
- Examples: `Sys.write`, `NativePtr.set`, `NativeDefault.zeroed`

See `fncs_architecture` memory § "FNCS Intrinsics (Layer 1 Operations)" for intrinsics.
See Firefly `binding_architecture_unified` memory for the three-layer architecture.

## Console Module (MIGRATED to Layer 3 - January 2026)

**IMPORTANT**: Console is NO LONGER an FNCS intrinsic. It has been migrated to **Layer 3 user code** in Fidelity.Platform.

Console.* functions in Fidelity.Platform use Sys.* intrinsics internally:
- `Console.write` → Uses `Sys.write` with fd=1 (stdout)
- `Console.writeln` → Uses `Sys.write` with fd=1 + newline
- `Console.readln` → Uses `Sys.read` with fd=0 (stdin)

**See**: Firefly memory `console_layer3_migration_findings` for migration details.

**User code should**: Either use `Sys.*` intrinsics directly, or properly depend on Fidelity.Platform.

## Status

As of 2026-01-04:
- All built-in bindings registered
- Intrinsic saturation added: curried intrinsic calls flattened during construction
- FNCS intrinsics (Sys, NativePtr, NativeDefault, Array) are Layer 1 in unified binding architecture

## Array Module Intrinsics (Added 2026-01-03)

Array operations are FNCS intrinsics because they:
1. Require memory allocation (cannot be expressed in pure F#)
2. Need element size knowledge for layout
3. Are fundamental to the array fat pointer type

| Function | Signature |
|----------|-----------|
| `Array.zeroCreate` | `int -> array<'T>` |
| `Array.create` | `int -> 'T -> array<'T>` |
| `Array.init` | `int -> (int -> 'T) -> array<'T>` |
| `Array.copy` | `array<'T> -> array<'T>` |
| `Array.length` | `array<'T> -> int` |
| `Array.get` | `array<'T> -> int -> 'T` |
| `Array.set` | `array<'T> -> int -> 'T -> unit` |
| `Array.tryItem` | `int -> array<'T> -> voption<'T>` |
| `Array.isEmpty` | `array<'T> -> bool` |

Implementation: `CheckExpressions.fs` handles `Array.*` similar to NativePtr, Sys, NativeDefault
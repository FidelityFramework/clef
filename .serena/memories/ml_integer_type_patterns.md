# ML-Style Integer Type Patterns (North Star for FNCS)

## Core Principle: No Polymorphic Numeric Operators

The BCL/F# approach uses polymorphic operators (`forall 'a. 'a -> 'a -> 'a`) that rely on SRTP
and implicit widening. This is fundamentally incompatible with native compilation.

The ML/Rust/Triton approach uses **type-specific operators** with **explicit conversions**.

## FStar Pattern (Reference: ~/repos/fstar-lang)

### Separate Concrete Types Per Width

```fstar
// Each width is a completely different abstract type
FStar.Int8.t   : eqtype   // 8-bit signed
FStar.Int16.t  : eqtype   // 16-bit signed
FStar.Int32.t  : eqtype   // 32-bit signed
FStar.Int64.t  : eqtype   // 64-bit signed
FStar.UInt8.t  : eqtype   // 8-bit unsigned
FStar.UInt16.t : eqtype   // 16-bit unsigned
FStar.UInt32.t : eqtype   // 32-bit unsigned
FStar.UInt64.t : eqtype   // 64-bit unsigned
```

### Type-Specific Operators (Not Shared)

```fstar
// Each module defines its own operators
FStar.Int32.add  : Int32.t -> Int32.t -> Int32.t
FStar.Int64.add  : Int64.t -> Int64.t -> Int64.t
FStar.UInt32.add : UInt32.t -> UInt32.t -> UInt32.t

// Infix operators use suffix notation
(+^)  // add
(-^)  // subtract
(*^)  // multiply
(/^)  // divide
(%^)  // modulo
(&^)  // bitwise AND
(|^)  // bitwise OR
(^^)  // bitwise XOR
(<<^) // left shift
(>>^) // right shift (logical for unsigned, arithmetic for signed)
```

### Explicit Conversions Only

```fstar
// FStar.Int.Cast module - ALL conversions explicit
uint8_to_uint64  : U8.t  -> U64.t   // Widening (safe)
int32_to_int64   : I32.t -> I64.t   // Widening (safe)
uint32_to_uint8  : U32.t -> U8.t    // Narrowing (truncates)
int64_to_int32   : I64.t -> I32.t   // Narrowing (truncates)
uint32_to_int64  : U32.t -> I64.t   // Sign change + widening
```

### Mixing Types = Compile Error

```fstar
let x : Int32.t = Int32.one
let y : Int64.t = Int64.one
let z = x +^ y  // TYPE ERROR! Cannot mix Int32 and Int64
```

## Application to FNCS

### Current (Wrong) - BCL-Style Polymorphic

```fsharp
// *(DELETED: NativeGlobals.fs)* - WRONG pattern:
let mkPolymorphicBinaryOp () =
    let tyParam = freshTypeParam "'a"
    let tyVar = NativeType.TVar tyParam
    NativeType.TForall([tyParam], NativeType.TFun(tyVar, NativeType.TFun(tyVar, tyVar)))

("op_Addition", mkPolymorphicBinaryOp())  // forall 'a. 'a -> 'a -> 'a
```

### Target (Correct) - ML-Style Type-Specific

```fsharp
// CORRECT pattern (greenfield implementation):
// Platform word (int = nativeint on x86_64 = i64)
("op_Addition", NativeType.TFun(Types.intType, NativeType.TFun(Types.intType, Types.intType)))
("op_Subtraction", NativeType.TFun(Types.intType, NativeType.TFun(Types.intType, Types.intType)))

// Fixed-width variants if needed
("Int32.add", NativeType.TFun(Types.int32Type, NativeType.TFun(Types.int32Type, Types.int32Type)))
("Int64.add", NativeType.TFun(Types.int64Type, NativeType.TFun(Types.int64Type, Types.int64Type)))

// Explicit conversions
("int32_to_int64", NativeType.TFun(Types.int32Type, Types.int64Type))
("int64_to_int32", NativeType.TFun(Types.int64Type, Types.int32Type))
```

## Key Insight: `int` = Platform Word

Per native spec (fsnative-spec):
- `int` = platform word (64-bit on x86_64), NOT F#'s 32-bit
- Array indexing uses `int` (platform word)
- String.Length returns `int` (platform word)
- For loops use `int` (platform word)

```fsharp
// (greenfield implementation)
let intTyCon = nintTyCon  // int = nativeint (platform word), NOT int32TyCon
```

## Benefits of ML-Style

1. **No type confusion**: Each operation has a fixed, known type
2. **No implicit widening**: Conversions are explicit and visible
3. **Clean MLIR emission**: Type-specific ops map directly to arith dialect
4. **Compile-time safety**: Mixing types is an error, not a silent widening
5. **Zero runtime overhead**: No type tags, dispatch tables, or SRTP resolution

## Nanopass Staging for Platform Types

**Critical Insight (Jan 2026):**

The ML-style pattern must be adapted for the nanopass architecture. Type-specific operators
are correct, but SIZE resolution happens at a later stage:

```
FNCS Stage: Type IDENTITY
  - int, int64, int32 are DISTINCT types (correct)
  - Operators work on ONE type (correct)
  - BUT: Don't bake in sizes yet!
  
Alex Stage: Type SIZE Resolution
  - int (platform word) → i64 on x86_64, i32 on ARM32
  - Sizes resolved based on fidproj target
```

Use `TypeLayout.PlatformWord` instead of `TypeLayout.Inline(8, 8)` for platform-dependent types.
See memory: `fncs_platform_aware_type_resolution`

## Anti-Pattern: Implicit Widening

F# 6.0's `AdditionalTypeDirectedConversions` silently converts int32 → int64.
This is the ROOT CAUSE of the 518+ "expected int64, got int" errors.

The fix is to REMOVE this behavior and require explicit conversions.
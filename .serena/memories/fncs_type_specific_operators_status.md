# FNCS Type-Specific Operators - Implementation Status

## Changes Made (Jan 2026)

### 1. `int` = Platform Word
- `intTyCon` now = 64-bit on x86_64 (was 32-bit alias to int32TyCon)
- `int32TyCon` is now a separate fixed-width type with name "int32"
- Follows native spec: `int` = platform word, not F# BCL semantics

### 2. Type-Specific Arithmetic Operators
The following operators now work ONLY on `int` (platform word):
- `op_Addition` : int -> int -> int
- `op_Subtraction` : int -> int -> int
- `op_Multiply` : int -> int -> int
- `op_Division` : int -> int -> int
- `op_Modulus` : int -> int -> int
- `op_UnaryNegation` : int -> int
- `op_BitwiseAnd/Or/Xor` : int -> int -> int
- `op_LeftShift/RightShift` : int -> int -> int

### 3. Polymorphic Comparison Operators (Retained)
Following OCaml pattern, comparisons remain polymorphic:
- `op_Equality` : forall 'a. 'a -> 'a -> bool
- `op_Inequality` : forall 'a. 'a -> 'a -> bool
- `op_LessThan/GreaterThan` : forall 'a. 'a -> 'a -> bool
- `op_LessThanOrEqual/GreaterThanOrEqual` : forall 'a. 'a -> 'a -> bool

### 4. Explicit Conversion Functions Added
```fsharp
// Widening (safe)
int8_to_int, int16_to_int, int32_to_int, int32_to_int64, int_to_int64
uint8_to_int, uint8_to_uint, uint16_to_uint, uint32_to_uint, uint32_to_uint64, uint_to_uint64

// Narrowing (may truncate)
int_to_int8, int_to_int16, int_to_int32, int64_to_int, int64_to_int32
uint_to_uint8, uint_to_uint16, uint_to_uint32, uint64_to_uint, uint64_to_uint32

// Sign-changing (reinterpret)
int_to_uint, uint_to_int, int32_to_uint32, uint32_to_int32, int64_to_uint64, uint64_to_int64
```

## Current Error Count (Jan 2026)
- Original polymorphic operators: 592 errors
- After type-specific for `int` only: 1014 errors (broke SRTP)
- After restoring polymorphic: 592 errors (back to baseline)

**Status**: Polymorphic operators restored. SRTP mechanism functional.
The 592 errors are genuine type mismatches in Alloy source code.

## Error Pattern Analysis
Top error patterns from HelloWorldSaturated:
- `int <- uint64` (320) - using uint64 with int operators
- `int <- uint32` (152) - using uint32 with int operators
- `int <- int64` (146) - using int64 with int operators
- `int64 <- int` (118) - reverse mismatch
- `int <- float` (114) - float with int operators
- `int <- uint8` (112) - byte with int operators

## Next Steps to Reduce Errors

### Option A: Fix Alloy (Preferred - ML Approach)
1. Update Alloy to use `int` (platform word) consistently for:
   - Loop counters
   - Array indexing
   - General arithmetic
2. Use explicit conversions where specific widths are needed
3. Use `int64` only for specific 64-bit values (ticks, timestamps)

### Option B: Add Type-Specific Operator Bindings (FStar Approach)
Add separate operators per type:
```fsharp
("Int32.op_Addition", TFun(int32Type, TFun(int32Type, int32Type)))
("Int64.op_Addition", TFun(int64Type, TFun(int64Type, int64Type)))
("UInt8.op_Addition", TFun(uint8Type, TFun(uint8Type, uint8Type)))
// etc.
```

### Option C: Revert to Polymorphic (BCL Approach - Not Recommended)
Revert arithmetic operators to polymorphic. This loses the ML type safety.

## Critical Tension: Type-Specific vs SRTP

**The Problem:**
Making operators type-specific for `int` ONLY breaks the SRTP mechanism. FNCS has:
- `SRTPResolution.fs` with `numericOpWitness` that provides witnesses for ANY numeric type
- `NativeGlobals.fs` with operators fixed to `int` only

These conflict! SRTP expects polymorphic operators that get resolved via witnesses.
Type-specific operators bypass SRTP entirely.

**Two Valid Approaches:**

### Approach A: Polymorphic + SRTP (F# Style)
- Operators are polymorphic: `forall 'a. 'a -> 'a -> 'a`
- SRTP witnesses resolve to type-specific implementations
- Requires proper constraint solving and witness lookup
- Preserves F# semantics

### Approach B: Type-Specific Everywhere (ML/FStar Style)
- EACH type has its own operators: `Int64.add`, `UInt8.add`, etc.
- Standard operators (`+`, `-`) work on `int` (platform word) only
- Other types require qualified operators or explicit conversions
- Clean but requires Alloy rewrite

**Current State: Broken Hybrid**
- Operators are type-specific for `int` only
- No module operators for other types
- SRTP infrastructure exists but unused for arithmetic
- Result: 1014 errors

## Recommended Path Forward

1. **Short-term**: Restore polymorphic operators with SRTP resolution
2. **Medium-term**: Add TypeLayout.PlatformWord (see memory: fncs_platform_aware_type_resolution)
3. **Long-term**: Consider ML-style module operators if SRTP proves problematic

See memory `fncs_platform_aware_type_resolution` for the nanopass staging insight.
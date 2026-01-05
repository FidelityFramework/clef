# MLIR Arith Dialect Reference for Firefly

## Core Principle: Signedness in Operation Name, Not Type

MLIR integers are "signless" - the type `i32` doesn't encode signedness.
Signedness is determined by the **operation** (signed vs unsigned variants).

## Integer Arithmetic Operations

### Addition/Subtraction/Multiplication (Signedness-Agnostic)

```mlir
%r = arith.addi %a, %b : i32           // Addition (wraps on overflow)
%r = arith.subi %a, %b : i64           // Subtraction
%r = arith.muli %a, %b : i32           // Multiplication (low N bits)
```

With overflow flags:
```mlir
%r = arith.addi %a, %b overflow<nsw> : i32   // Signed overflow → poison
%r = arith.addi %a, %b overflow<nuw> : i32   // Unsigned overflow → poison
%r = arith.addi %a, %b overflow<nsw, nuw> : i32  // Both
```

### Division (REQUIRES Signedness)

```mlir
%r = arith.divsi %a, %b : i32          // SIGNED division
%r = arith.divui %a, %b : i32          // UNSIGNED division
%r = arith.remsi %a, %b : i32          // SIGNED remainder
%r = arith.remui %a, %b : i32          // UNSIGNED remainder
```

Floor/ceiling variants:
```mlir
%r = arith.floordivsi %a, %b : i32     // Floor division (toward -∞)
%r = arith.ceildivsi %a, %b : i32      // Ceiling division (toward +∞)
%r = arith.ceildivui %a, %b : i32      // Unsigned ceiling division
```

### Bitwise Operations (Signedness-Agnostic)

```mlir
%r = arith.andi %a, %b : i32           // Bitwise AND
%r = arith.ori %a, %b : i32            // Bitwise OR
%r = arith.xori %a, %b : i32           // Bitwise XOR
```

### Shift Operations (Right Shift REQUIRES Signedness)

```mlir
%r = arith.shli %a, %b : i32           // Left shift (zero-fill)
%r = arith.shrsi %a, %b : i32          // SIGNED right shift (sign-extend)
%r = arith.shrui %a, %b : i32          // UNSIGNED right shift (zero-fill)
```

### Min/Max (REQUIRES Signedness)

```mlir
%r = arith.minsi %a, %b : i32          // SIGNED minimum
%r = arith.maxsi %a, %b : i32          // SIGNED maximum
%r = arith.minui %a, %b : i32          // UNSIGNED minimum
%r = arith.maxui %a, %b : i32          // UNSIGNED maximum
```

## Comparison Operations

```mlir
%r = arith.cmpi eq, %a, %b : i32       // Equal (signedness-agnostic)
%r = arith.cmpi ne, %a, %b : i32       // Not equal

// SIGNED comparisons
%r = arith.cmpi slt, %a, %b : i32      // Signed less than
%r = arith.cmpi sle, %a, %b : i32      // Signed less or equal
%r = arith.cmpi sgt, %a, %b : i32      // Signed greater than
%r = arith.cmpi sge, %a, %b : i32      // Signed greater or equal

// UNSIGNED comparisons
%r = arith.cmpi ult, %a, %b : i32      // Unsigned less than
%r = arith.cmpi ule, %a, %b : i32      // Unsigned less or equal
%r = arith.cmpi ugt, %a, %b : i32      // Unsigned greater than
%r = arith.cmpi uge, %a, %b : i32      // Unsigned greater or equal
```

Result type: `i1` for scalar, `tensor<Nxi1>` for tensors.

## Type Conversion Operations

### Integer Width Conversions

```mlir
// WIDENING
%r = arith.extsi %a : i32 to i64       // Sign-extend (replicates sign bit)
%r = arith.extui %a : i32 to i64       // Zero-extend (fills with zeros)

// NARROWING
%r = arith.trunci %a : i64 to i32      // Truncate (drops high bits)
%r = arith.trunci %a overflow<nsw> : i64 to i32  // Poison if info lost
```

### Index Type Conversions

```mlir
%r = arith.index_cast %a : i32 to index    // Integer → index (sign-extends)
%r = arith.index_cast %a : index to i32    // Index → integer
%r = arith.index_castui %a : i32 to index  // Unsigned semantics (zero-extends)
```

### Float/Integer Conversions

```mlir
%r = arith.sitofp %a : i32 to f32      // Signed int → float
%r = arith.uitofp %a : i32 to f32      // Unsigned int → float
%r = arith.fptosi %a : f32 to i32      // Float → signed int (truncates)
%r = arith.fptoui %a : f32 to i32      // Float → unsigned int (truncates)
```

### Float Width Conversions

```mlir
%r = arith.extf %a : f16 to f32        // Widen float (more precision)
%r = arith.truncf %a : f32 to f16      // Narrow float (less precision)
```

## Constants

```mlir
%c = arith.constant 42 : i32           // Integer constant
%c = arith.constant 3.14 : f32         // Float constant
%c = arith.constant 0 : index          // Index constant
%c = arith.constant dense<1> : tensor<128xi32>  // Tensor constant
```

## Application to Firefly/Alex

### FNCS Type → MLIR Type Mapping

| FNCS Type | MLIR Type | Notes |
|-----------|-----------|-------|
| int (platform word) | i64 | On x86_64 |
| int32 | i32 | Fixed 32-bit |
| int64 | i64 | Fixed 64-bit |
| uint32 | i32 | Signedness in ops |
| uint64 | i64 | Signedness in ops |
| nativeint | index or i64 | Platform word |
| bool | i1 | Single bit |

### Operator → MLIR Op Mapping

| F# Operator | Signed Type | Unsigned Type |
|-------------|-------------|---------------|
| + | arith.addi | arith.addi |
| - | arith.subi | arith.subi |
| * | arith.muli | arith.muli |
| / | arith.divsi | arith.divui |
| % | arith.remsi | arith.remui |
| < | arith.cmpi slt | arith.cmpi ult |
| > | arith.cmpi sgt | arith.cmpi ugt |
| <= | arith.cmpi sle | arith.cmpi ule |
| >= | arith.cmpi sge | arith.cmpi uge |
| <<< | arith.shli | arith.shli |
| >>> | arith.shrsi | arith.shrui |

### Conversion Emission

```fsharp
// FNCS: int32_to_int64 x
// MLIR: %r = arith.extsi %x : i32 to i64

// FNCS: uint8_to_int x  (unsigned widening)
// MLIR: %r = arith.extui %x : i8 to i64

// FNCS: int64_to_int32 x  (narrowing)
// MLIR: %r = arith.trunci %x : i64 to i32
```

## Key Insight: Type Safety at Source Level

The constraint solver in FNCS should enforce:
1. Both operands of arithmetic ops have the SAME type
2. No implicit widening - require explicit conversion functions
3. Signedness is tracked in the type system (int32 vs uint32)
4. Conversion operations are explicit nodes in the PSG

This ensures that by the time Alex emits MLIR, the types are unambiguous
and the correct signed/unsigned operations can be selected.

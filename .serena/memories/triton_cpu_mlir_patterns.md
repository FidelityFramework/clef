# Triton-CPU MLIR Emission Patterns (Reference for Alex)

## Source: ~/repos/triton-cpu

## Core Pattern: Type-Specific Operations, Not Polymorphic

Triton uses **separate operation kinds** for signed vs unsigned semantics.
There is NO polymorphic dispatch based on type - the operation IS the semantics.

## Operation Mapping (arith → LLVM)

From `lib/Conversion/TritonGPUToLLVM/ElementwiseOpToLLVM.cpp`:

```cpp
// SIGNEDNESS-AGNOSTIC (same for signed/unsigned)
POPULATE_BINARY_OP(arith::AddIOp, LLVM::AddOp)     // Addition
POPULATE_BINARY_OP(arith::SubIOp, LLVM::SubOp)     // Subtraction
POPULATE_BINARY_OP(arith::MulIOp, LLVM::MulOp)     // Multiplication
POPULATE_BINARY_OP(arith::AndIOp, LLVM::AndOp)     // Bitwise AND
POPULATE_BINARY_OP(arith::OrIOp, LLVM::OrOp)       // Bitwise OR
POPULATE_BINARY_OP(arith::XOrIOp, LLVM::XOrOp)     // Bitwise XOR
POPULATE_BINARY_OP(arith::ShLIOp, LLVM::ShlOp)     // Left shift

// REQUIRE SIGNEDNESS (different ops for signed/unsigned)
POPULATE_BINARY_OP(arith::DivSIOp, LLVM::SDivOp)   // SIGNED division
POPULATE_BINARY_OP(arith::DivUIOp, LLVM::UDivOp)   // UNSIGNED division
POPULATE_BINARY_OP(arith::RemSIOp, LLVM::SRemOp)   // SIGNED remainder
POPULATE_BINARY_OP(arith::RemUIOp, LLVM::URemOp)   // UNSIGNED remainder
POPULATE_BINARY_OP(arith::ShRSIOp, LLVM::AShrOp)   // Arithmetic right shift
POPULATE_BINARY_OP(arith::ShRUIOp, LLVM::LShrOp)   // Logical right shift
POPULATE_BINARY_OP(arith::MinSIOp, LLVM::SMinOp)   // SIGNED minimum
POPULATE_BINARY_OP(arith::MaxSIOp, LLVM::SMaxOp)   // SIGNED maximum
POPULATE_BINARY_OP(arith::MinUIOp, LLVM::UMinOp)   // UNSIGNED minimum
POPULATE_BINARY_OP(arith::MaxUIOp, LLVM::UMaxOp)   // UNSIGNED maximum

// TYPE CONVERSIONS
POPULATE_UNARY_OP(arith::TruncIOp, LLVM::TruncOp)  // Truncate (narrow)
POPULATE_UNARY_OP(arith::ExtSIOp, LLVM::SExtOp)    // Sign-extend (widen signed)
POPULATE_UNARY_OP(arith::ExtUIOp, LLVM::ZExtOp)    // Zero-extend (widen unsigned)
```

## Comparison Predicate Mapping

From `CmpIOpConversion`:

```cpp
static LLVM::ICmpPredicate ArithCmpIPredicateToLLVM(arith::CmpIPredicate pred) {
  switch (predicate) {
    case arith::CmpIPredicate::eq:   return LLVM::ICmpPredicate::eq;   // Equal
    case arith::CmpIPredicate::ne:   return LLVM::ICmpPredicate::ne;   // Not equal
    case arith::CmpIPredicate::sgt:  return LLVM::ICmpPredicate::sgt;  // Signed >
    case arith::CmpIPredicate::sge:  return LLVM::ICmpPredicate::sge;  // Signed >=
    case arith::CmpIPredicate::slt:  return LLVM::ICmpPredicate::slt;  // Signed <
    case arith::CmpIPredicate::sle:  return LLVM::ICmpPredicate::sle;  // Signed <=
    case arith::CmpIPredicate::ugt:  return LLVM::ICmpPredicate::ugt;  // Unsigned >
    case arith::CmpIPredicate::uge:  return LLVM::ICmpPredicate::uge;  // Unsigned >=
    case arith::CmpIPredicate::ult:  return LLVM::ICmpPredicate::ult;  // Unsigned <
    case arith::CmpIPredicate::ule:  return LLVM::ICmpPredicate::ule;  // Unsigned <=
  }
}
```

## Type Width Utilities

From `include/triton/Conversion/TritonGPUToLLVM/Utility.h`:

```cpp
// Constant creation with specific widths
Value int_val(short bitwidth, int64_t val) {
  Type ty = builder->getIntegerType(bitwidth);
  return builder->create<LLVM::ConstantOp>(loc, ty, builder->getIntegerAttr(ty, val));
}

Value i8_val(int64_t val)  { return int_val(8, val); }
Value i16_val(int64_t val) { return int_val(16, val); }
Value i32_val(int64_t val) { return int_val(32, val); }
Value i64_val(int64_t val) { return int_val(64, val); }

// Type macros
#define i64_ty rewriter.getIntegerType(64)
#define i32_ty rewriter.getIntegerType(32)
#define i16_ty rewriter.getIntegerType(16)
#define i8_ty rewriter.getIntegerType(8)
#define i1_ty rewriter.getI1Type()
```

## Extension/Truncation Pattern

From `ConvertLayoutOpToLLVM.cpp`:

```cpp
// Sub-byte integers must be widened for shared memory operations
auto isSubByteInt = elemTy.isInteger() && elemTy.getIntOrFloatBitWidth() < 8;

for (const auto &it : llvm::enumerate(inVals)) {
  if (isSubByteInt) {
    // Zero-extend to i8 for memory operations
    inVals[it.index()] = b.zext(llvmElemTy, it.value());
  }
}

// ... operations ...

for (const auto &it : llvm::enumerate(outVals)) {
  if (isSubByteInt) {
    // Truncate back to original width
    outVals[it.index()] = b.trunc(llvmElemTyOrig, it.value());
  }
}
```

## Builder Shortcuts

```cpp
// Sign-related operations
LLVM::SExtOp sext(Args&&... args)   // Sign-extend
LLVM::ZExtOp zext(Args&&... args)   // Zero-extend
LLVM::TruncOp trunc(Args&&... args) // Truncate

// Comparisons (with signedness in predicate)
LLVM::ICmpOp icmp_slt(Args&&... args)  // Signed <
LLVM::ICmpOp icmp_sle(Args&&... args)  // Signed <=
LLVM::ICmpOp icmp_sgt(Args&&... args)  // Signed >
LLVM::ICmpOp icmp_sge(Args&&... args)  // Signed >=
LLVM::ICmpOp icmp_ult(Args&&... args)  // Unsigned <
LLVM::ICmpOp icmp_ule(Args&&... args)  // Unsigned <=
LLVM::ICmpOp icmp_ugt(Args&&... args)  // Unsigned >
LLVM::ICmpOp icmp_uge(Args&&... args)  // Unsigned >=
LLVM::ICmpOp icmp_eq(Args&&... args)   // Equal
LLVM::ICmpOp icmp_ne(Args&&... args)   // Not equal
```

## Application to Alex/Firefly

### Emission Pattern for Operators

```fsharp
// In FNCSTransfer.fs or equivalent
let emitBinaryOp (op: string) (lhsType: NativeType) (lhs: string) (rhs: string) =
    match op, lhsType with
    // Addition - same for signed/unsigned
    | "op_Addition", TApp(tc, []) when tc = int32TyCon -> $"arith.addi {lhs}, {rhs} : i32"
    | "op_Addition", TApp(tc, []) when tc = int64TyCon -> $"arith.addi {lhs}, {rhs} : i64"
    
    // Division - REQUIRES signedness
    | "op_Division", TApp(tc, []) when tc = int32TyCon -> $"arith.divsi {lhs}, {rhs} : i32"
    | "op_Division", TApp(tc, []) when tc = uint32TyCon -> $"arith.divui {lhs}, {rhs} : i32"
    
    // Comparison - REQUIRES signedness in predicate
    | "op_LessThan", TApp(tc, []) when tc = int32TyCon -> $"arith.cmpi slt, {lhs}, {rhs} : i32"
    | "op_LessThan", TApp(tc, []) when tc = uint32TyCon -> $"arith.cmpi ult, {lhs}, {rhs} : i32"
```

### Emission Pattern for Conversions

```fsharp
let emitConversion (convName: string) (arg: string) =
    match convName with
    | "int32_to_int64" -> $"arith.extsi {arg} : i32 to i64"   // Sign-extend
    | "uint8_to_int64" -> $"arith.extui {arg} : i8 to i64"    // Zero-extend
    | "int64_to_int32" -> $"arith.trunci {arg} : i64 to i32"  // Truncate
    | "int_to_index"   -> $"arith.index_cast {arg} : i64 to index"
```

## Key Takeaway

Triton demonstrates that:
1. **No central dispatch** - operations are typed at the source level
2. **Signedness is explicit** - different ops for signed/unsigned (DivSIOp vs DivUIOp)
3. **Conversions are explicit** - ExtSIOp, ExtUIOp, TruncIOp are distinct operations
4. **Type width in emission** - always include `: i32` or `: i64` suffix

This is the model Alex should follow for MLIR emission.

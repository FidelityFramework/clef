# MLIR Dialect Architecture (January 2026)

## The Principle

**MLIR provides portable dialects for portable operations. LLVM dialect is required for backend-target-intrinsic operations that have no portable equivalent.**

This is NOT about avoiding LLVM - it's about understanding which operations are fundamentally backend-specific versus which are portable across targets.

## The Flat Closure Pattern: Why LLVM is Required

F# Native uses **MLKit-style flat closures** for closures, lazy values, and sequences:

```
Closure: { code_ptr, cap₀, cap₁, ... }
Lazy:    { computed, value, code_ptr, cap₀, cap₁, ... }  
Seq:     { state, current, code_ptr, cap₀, cap₁, ... }
```

These patterns require storing a **function pointer** in a struct and calling through it later. This is fundamentally a backend-target-intrinsic operation:

1. **Taking a function's address** - `llvm.mlir.addressof` has no MLIR portable equivalent
2. **Storing in a struct** - `llvm.insertvalue` / `llvm.extractvalue` (no MLIR struct type)
3. **Indirect call through pointer** - `llvm.call` with function pointer

**There is no way to do this portably in MLIR** - it requires committing to a specific backend's representation of function pointers.

## Dialect Hierarchy

### MLIR Portable Dialects (Backend-Independent)

| Dialect | Purpose | Use For |
|---------|---------|---------|
| `func` | Function definitions and calls | Top-level functions called by name |
| `cf` | Control flow | `cf.br`, `cf.cond_br`, `cf.switch` |
| `scf` | Structured control flow | `scf.while`, `scf.for`, `scf.if` |
| `arith` | Arithmetic operations | `arith.addi`, `arith.constant`, `arith.cmpi` |

### LLVM Dialect (Backend-Target-Intrinsic)

**LLVM dialect is REQUIRED for:**

1. **Flat Closure Pattern** (closures, lazy, seq):
   - `llvm.func` - Functions whose address will be taken
   - `llvm.mlir.addressof` - Getting function addresses
   - `llvm.call` (indirect) - Calling through function pointers
   - `llvm.insertvalue` / `llvm.extractvalue` - Struct field manipulation

2. **Struct Operations** (no MLIR equivalent):
   - `llvm.undef` - Create undefined struct value
   - `llvm.getelementptr` - Struct field pointer access
   - `llvm.load` / `llvm.store` - Struct memory operations

3. **Platform-Specific Operations**:
   - Syscall wrappers
   - LLVM intrinsics
   - Coroutines (`llvm.coro.*`)

## The Correct Mixed Usage Pattern

```mlir
// Top-level entry point - func dialect (called by name)
func.func @main() -> i32 {
    // Create a lazy value - builds flat closure struct
    %lazy = call @create_lazy_value() : () -> !llvm.struct<...>
    
    // Force it - extracts code_ptr and calls indirectly
    %result = call @force_lazy(%lazy) : (!llvm.struct<...>) -> i64
    
    // Arithmetic - arith dialect (portable)
    %ret = arith.constant 0 : i32
    func.return %ret : i32
}

// Thunk function - llvm.func (address will be taken)
llvm.func @lazy_thunk(%lazy_ptr: !llvm.ptr) -> i64 {
    // Extract captures from struct - LLVM ops (necessary)
    %cap0_ptr = llvm.getelementptr %lazy_ptr[0, 3] : !llvm.ptr -> !llvm.ptr
    %cap0 = llvm.load %cap0_ptr : !llvm.ptr -> i64
    
    // Arithmetic - arith dialect (portable)  
    %result = arith.addi %cap0, %cap0 : i64
    
    // Return - llvm.return (matches llvm.func)
    llvm.return %result : i64
}

// MoveNext for Seq - llvm.func (address stored in seq struct)
llvm.func private @seq_moveNext(%seq_ptr: !llvm.ptr) -> i1 {
    // State machine implementation
    // Uses cf.switch for state dispatch (portable control flow)
    // Uses llvm.* for struct access (backend-intrinsic)
    // ...
}
```

## Why This Boundary Exists

The MLIR ecosystem is designed for **progressive lowering** through dialect conversions. The portable dialects (func, cf, scf, arith) can lower to multiple backends:
- LLVM
- SPIR-V (GPU)
- WebAssembly
- Custom hardware

But **function pointer manipulation is fundamentally backend-specific**:
- Different backends have different function pointer representations
- Different calling conventions
- Different ways to take/store/call through function addresses

The flat closure pattern commits to a specific representation. On LLVM targets, that representation uses `llvm.func` + `llvm.mlir.addressof`.

## Future Backend Targeting

When targeting a non-LLVM backend (SPIR-V, WASM, etc.), the flat closure pattern will need backend-specific implementation:
- SPIR-V: Different function pointer model
- WASM: Function tables and `call_indirect`
- Custom: Whatever the target provides

The **portable parts** (control flow, arithmetic, top-level structure) remain in MLIR portable dialects. The **backend-intrinsic parts** (function pointers, struct manipulation) will have backend-specific implementations.

This separation is already visible in the codebase:
- Platform bindings in `Fidelity.Platform` describe target capabilities
- `fidproj` platform configuration informs lowering decisions
- The dialect boundary documents WHERE backend-specific code lives

## Classification Guide

| Operation | Classification | Dialect |
|-----------|---------------|---------|
| Entry point (`main`) | Portable | `func.func` |
| Module-level functions (called by name) | Portable | `func.func` |
| Direct function calls | Portable | `func.call` |
| Thunks (lazy, closure, seq) | Backend-Intrinsic | `llvm.func` |
| Taking function address | Backend-Intrinsic | `llvm.mlir.addressof` |
| Indirect calls | Backend-Intrinsic | `llvm.call` |
| Struct manipulation | Backend-Intrinsic | `llvm.*value`, `llvm.gep` |
| Control flow | Portable | `cf.*`, `scf.*` |
| Arithmetic | Portable | `arith.*` |

## PRD Guidance

When writing PRDs for features that involve closures, lazy values, or sequences:

1. **Acknowledge the flat closure pattern** - These features build on the same foundation
2. **Expect LLVM dialect for thunks** - Functions whose address is taken
3. **Use portable dialects for logic** - Control flow, arithmetic, direct calls
4. **Document the boundary** - Be explicit about what's backend-intrinsic

## Related Memories

- `compose_from_standing_art_principle` - New features extend flat closure pattern
- `fncs_lazy_thunk_architecture` - Lazy extends flat closures
- `lazy_thunk_calling_convention` - Struct pointer passing convention
- `memory_layout_and_raii` - Struct layout principles
- `fncs_seq_generator_protocol` - Seq semantic contract

## Related fsnative-spec

- `spec/closure-representation.md` - MLKit-style flat closures, MLIR examples
- `spec/lazy-representation.md` - Lazy as extended flat closure, thunk convention
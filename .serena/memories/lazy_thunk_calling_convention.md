# Lazy Thunk Calling Convention (January 2026)

## Decision: Option B - Thunk Receives Lazy Struct Pointer

The thunk receives a pointer to the lazy struct and extracts its own captures.
This provides clean separation of concerns - the force site doesn't need to know
the internal capture structure of the lazy value.

## Calling Convention

### Thunk Signature
```mlir
// Thunk takes pointer to lazy struct, extracts captures internally
llvm.func @thunk(%lazy_ptr: ptr) -> T {
    %lazy = llvm.load %lazy_ptr : !lazy_struct_type
    %cap0 = llvm.extractvalue %lazy[3] : !lazy_struct_type
    %cap1 = llvm.extractvalue %lazy[4] : !lazy_struct_type
    // ... use captures ...
    %result = ...
    llvm.return %result : T
}
```

### Force Operation
```mlir
// Force is UNIFORM - doesn't need to know capture count
%code_ptr = llvm.extractvalue %lazy[2] : !lazy_struct_type
// Get address of lazy struct (may need alloca if by-value)
%result = llvm.call %code_ptr(%lazy_ptr) : (ptr) -> T
```

## Why Option B?

1. **Force is uniform** - Same code regardless of capture count
2. **Thunk knows its own layout** - Via LazyLayout coeffect from SSAAssignment
3. **No def-use tracking needed** - LazyForce doesn't need to trace back to LazyExpr
4. **Clean separation** - Force site handles invocation, thunk handles extraction

## FNCS Implications

- `LazyForce` does NOT need capture info - just the lazyValue NodeId
- `LazyExpr` DOES need captures computed (same pattern as Lambda)
- The captures are for the THUNK's LazyLayout coeffect, not for LazyForce

## Alex Implications

- `LazyLayout` coeffect computed for LazyExpr (not LazyForce)
- SSA cost for LazyForce is fixed: 4 (extract code_ptr, const 1, alloca, call)
  - Extract code_ptr from struct
  - Create constant 1 for alloca count
  - Alloca space for lazy struct on stack
  - Call thunk with pointer (result SSA)
- Thunk function generation uses LazyLayout to emit capture extraction
- Force must alloca + store the by-value struct to get a pointer for the thunk

## Struct Layout Reminder

```
Lazy<T> = {computed: i1, value: T, code_ptr: ptr, cap₀, cap₁, ...}
           [0]         [1]       [2]          [3]   [4]
```

## Related Memories

- `lazy_seq_flat_closure_architecture`
- `prd14_course_correction_jan2026`
- `true_flat_closures_implementation`

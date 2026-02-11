# Format Intrinsics Architecture — Number-to-String Conversion

## Status
✅ IMPLEMENTED (Feb 2026). Format.int and Format.float are F# code in Fidelity.Platform,
compiled through the full pipeline. Sample 06 (AddNumbersInteractive) uses them successfully.

## Problem Statement
Sample 05 (AddNumbers) needs `Format.int` and `Format.float` to produce console output.
These are FNCS intrinsics (`IntrinsicModule.Format`, category `Conversion`) defined in Intrinsics.fs:
- `Format.int : int → string`
- `Format.int64 : int64 → string`  
- `Format.float / float64 / double : float → string`
- `Format.bool : bool → string`

Currently unimplemented in Alex — hit catch-all error in ApplicationWitness.fs.

## User's Thesis: "There Is No BCL"
F# externalized string conversion to CLR's `ToString()` because the CLR provided it.
FNCS has no BCL/CLR. Like folding Alloy into FNCS, Format conversion should be
**compiler-generated machinery**, not delegated to a platform runtime that doesn't exist.
The question is whether this is a compiler primitive or a runtime function.

## Research Findings

### OxCaml (Reference: Compiler Primitives)
- **int↔float**: Compiler primitives (`%intoffloat`, `%floatofint`) → `Static_cast` in Lambda IR
- **int→string**: C runtime function (`caml_format_int` wraps `snprintf`)
- **Key**: Numeric casts = compiler primitives. String conversion = runtime delegation.
- Source: `asmcomp/selectgen.ml`, `runtime/ints.c`

### F* (Reference: Verified Primitives)
- `Prims.string_of_int`: Assumed primitive in Prims module (axiomatically trusted)
- Extracted to OCaml's `Z.to_string` (delegates to runtime)
- Sized int conversions (`Int32.to_string`, etc.): Library functions with verified refinements
- **Key**: Even in a verification-focused compiler, string conversion is "assumed" — not derived

### Nanopass (Scheme) (Reference: Pass Architecture)
- Type conversions are primitive operations, not pass concerns
- No dedicated conversion pass — conversions are just operations in the IR
- `number->string` is a built-in primitive in Scheme (not synthesized)

### Universal Pattern
All three models delegate number→string to a runtime/external function.
Numeric casts (int↔float) are universally compiler primitives.

## Correct Implementation Model

### ARCHITECTURAL CORRECTION (Feb 8, 2026)
The "compiler-generated MLIR helper function" model was WRONG. It's push-model (factory worker).

### Correct: Platform Library F# Code (Pull Model)
Format.int is **F# code in Fidelity.Platform**, same pattern as Console.write/Console.writeln.
Implementation uses FNCS intrinsics (MemRef, NativeStr, arithmetic, while loops).
Compiles through the full pipeline (FNCS → PSG → Baker → Alex) naturally.
Alex witnesses it like any other function — LambdaWitness wraps body in FuncDef.
At call sites, ApplicationWitness emits `func.call @Format.int`.

**No new Alex patterns, elements, or helper construction needed for the function body.**
**SSA costs still need fixing: 45/75 → 2 (func.call + result).**

See Firefly memory `format_int_implementation_plan_feb2026` for full implementation steps.

## F# Idiom Findings
- F# requires **explicit** numeric conversions: `int + float` is a type error
- Must write `float x + y` to convert int to float
- This is language-level, NOT runtime-dependent — applies to FNCS too
- Sample 05 should use idiomatic F# (explicit `float x` conversion)

## Sample 05 Design Goals
- End-to-end console output REQUIRED (user explicitly stated this)
- Process string input from console, compute with DU types, output result as string
- Use idiomatic F# (explicit conversions, pattern matching on DU)
- Format.int/Format.float are the mechanism for final output

## Open Questions (RESOLVED)
1. ✅ "Lift" = zero — F# code in Fidelity.Platform, compiled naturally through pipeline
2. ✅ Functions live in platform library, emitted as normal func.func by LambdaWitness
3. ✅ Float formatting: native F# implementation produces clean output (3.14, not 3.140000)
4. ✅ String allocation: stack memref.alloca for local buffers, escape analysis promotes if needed
5. ✅ Format.bool: not yet needed but would follow same platform library pattern
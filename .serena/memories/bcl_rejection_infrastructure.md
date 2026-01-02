# BCL Rejection Infrastructure - Critical Gap

## The Problem

FNCS encounters BCL references like `System.Text.Encoding.UTF8.GetBytes(s)` and:

1. ✅ Correctly identifies it's not in bindings
2. ✅ Emits FS0039 diagnostic
3. ❌ Creates Error node and **CONTINUES processing**
4. ❌ Error node propagates garbage downstream
5. ❌ Causes confusing failures later (unresolved TVar, missing SSA, etc.)

## Current Behavior (WRONG)

```fsharp
// CheckExpressions.fs - LongIdent case
| None ->
    // Emits diagnostic but CONTINUES with Error node
    addDiagnostic { ... Code = "FS0039" ... } env
    builder.Create(
        SemanticKind.Error $"Undefined: {name}",
        NativeType.TError $"Undefined: {name}",
        range)
```

The Error node propagates through:
- Application nodes get Error as function
- Binding nodes get Error as value → TVar left unresolved
- VarRef nodes reference bindings with garbage types
- Eventually fails in codegen with confusing "missing SSA" errors

## Required Behavior (CORRECT)

BCL references must be **HARD STOPS** with clear diagnostics:

1. Detect `System.*` namespace at earliest point
2. Emit specific FS8xxx error (not generic FS0039)
3. **Do NOT create Error node that propagates**
4. Collect all BCL violations, report them, halt compilation

## Proposed Implementation

### New Diagnostic Code

```fsharp
module DiagnosticCodes =
    // BCL rejection (FS8500-FS8599)
    let FS8500_BclReferenceNotAllowed = "FS8500"
    let FS8501_SystemNamespaceNotAllowed = "FS8501"
```

### BCL Detection Helper

```fsharp
let isBclReference (name: string) =
    name.StartsWith("System.") ||
    name.StartsWith("Microsoft.") ||
    name.StartsWith("mscorlib.") ||
    name.StartsWith("netstandard.")

let rejectBclReference (name: string) (range: SourceRange) (env: TypeEnv) =
    addNativeError DiagnosticCodes.FS8500_BclReferenceNotAllowed range
        $"BCL reference '{name}' is not available in F# Native. Use Alloy library equivalents." env
```

### Integration Points

1. **LongIdent case** - Check before tryLookupBinding
2. **DotGet case** - Check accumulated path
3. **Type references** - Check in checkSynType

## Why This Matters

From `bcl_type_validation` memory:
> "BCL types must NEVER appear in the Firefly compilation pipeline.
> BCL types cannot be 'lowered', 'converted', or 'transformed' - they simply must not exist.
> If a BCL type is detected, it indicates a BUG upstream."

The "upstream" is now FNCS. FNCS must be the gatekeeper that rejects BCL references
with clear diagnostics, not let them propagate as garbage that causes confusing
downstream failures.

## Success Criteria

- [ ] FS8500 diagnostic code defined
- [ ] `isBclReference` helper implemented
- [ ] LongIdent rejects BCL with FS8500
- [ ] DotGet rejects BCL with FS8500
- [ ] Type references reject BCL
- [ ] Diagnostics collected and reported before graph is returned
- [ ] No Error nodes with BCL references propagate downstream

## Related

- `bcl_type_validation` memory in Firefly (historical, pre-FNCS)
- `fncs_architecture` memory - "No BCL types in typed tree" success criterion
- `type_checker_anti_patterns` memory - avoiding silent failures

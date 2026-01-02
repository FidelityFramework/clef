# FNCS Control Testing Requirements

> **Created**: January 2, 2026
> **Priority**: CRITICAL - Guards the FCS/BCL balance

## Purpose

FNCS surgically preserves "good parts" of FCS while rejecting BCL dependencies. This balance requires comprehensive control testing that:
1. Verifies preserved FCS infrastructure continues working
2. Ensures BCL rejection catches all violations
3. Guards against regression as FNCS evolves

## Test Categories

### 1. FCS Infrastructure Preservation Tests

| Category | What to Test | Expected Behavior |
|----------|--------------|-------------------|
| **Symbol Resolution** | `tryLookupBinding` returns correct types | Alloy.Console.Write → `NativeStr -> unit` |
| **Range Preservation** | Source locations flow through checking | All SemanticNodes have valid ranges |
| **Open Declarations** | `open Alloy` enables unqualified access | `Console.Write` resolves to `Alloy.Console.Write` |
| **Binding Registration** | User bindings added to resolver | `let x = 5` makes `x` resolvable |
| **Error Messages** | Diagnostics include source location | Errors point to correct line/column |

### 2. BCL Rejection Tests (Negative Cases)

| Category | Input | Expected |
|----------|-------|----------|
| **System namespace** | `System.String` | FS8500: BCL reference not allowed |
| **Microsoft namespace** | `Microsoft.FSharp.Core.unit` | FS8500: BCL reference not allowed |
| **mscorlib reference** | `mscorlib.System.Int32` | FS8500: BCL reference not allowed |
| **obj type** | `let x: obj = box 5` | FS8011: obj not supported |
| **Boxing** | `box 42` | FS8012: Boxing not supported |
| **Reflection** | `typeof<int>` | Compile error (no reflection) |

### 3. Native Type Universe Tests

| Category | Input | Expected |
|----------|-------|----------|
| **String literals** | `"hello"` | Type: `NativeStr` (UTF-8 fat pointer) |
| **Option** | `Some 42` | Type: `voption<int>` (value type) |
| **Int** | `42` | Type: `int` (platform word) |
| **Array** | `[| 1; 2; 3 |]` | Type: `array<int>` (fat pointer) |
| **Function** | `fun x -> x + 1` | Type: `int -> int` |

### 4. Compositional Resolution Tests

| Category | Setup | Query | Expected |
|----------|-------|-------|----------|
| **Empty resolver** | None | `"anything"` | None |
| **Single binding** | `let x = 5` | `"x"` | Some binding |
| **Open compose** | `open Alloy` | `"Console.Write"` | Resolves to `Alloy.Console.Write` |
| **Shadowing** | `let x = 5; let x = 10` | `"x"` | Latest binding |
| **BCL impossible** | `open System` | `"String"` | None (System not in resolver) |

## Test Implementation Strategy

### Structure

```
fsnative/
├── tests/
│   └── FSharp.Native.Compiler.Tests/
│       ├── Checking.Native/
│       │   ├── NameResolutionTests.fs      # Compositional resolver tests
│       │   ├── TypeCheckingTests.fs         # Native type inference
│       │   ├── BclRejectionTests.fs         # BCL rejection (negative cases)
│       │   └── FcsPreservationTests.fs      # FCS infrastructure verification
│       └── Integration/
│           └── HelloWorldTests.fs           # End-to-end compilation
```

### Test Utilities

```fsharp
module TestHelpers =
    /// Check that source compiles with expected type
    let checkType source expectedType =
        let result = parseAndCheck source
        result.Graph.EntryPoints
        |> List.head
        |> fun id -> result.Graph.Nodes.[id].Type
        |> assertEqual expectedType
    
    /// Check that source fails with expected error code
    let expectError source errorCode =
        let result = parseAndCheck source
        result.Diagnostics
        |> List.exists (fun d -> d.Code = errorCode)
        |> assertTrue
```

### Native Type Validation

With the native type universe, static checks become authoritative:
- Type of `"hello"` MUST be `NativeStr`
- Type of `Some 42` MUST be `voption<int>`
- Any BCL type in output is a test failure

## Success Criteria

- [ ] 100% coverage of FCS infrastructure APIs used by FNCS
- [ ] All BCL namespace prefixes have rejection tests
- [ ] All native type mappings have validation tests
- [ ] Compositional resolver has property-based tests
- [ ] Integration tests for HelloWorld samples

## Guard Rails

These tests serve as guard rails:
1. **FCS preservation**: If symbol resolution breaks, tests fail
2. **BCL rejection**: If BCL leaks through, tests catch it
3. **Native types**: If type mappings change, tests detect it
4. **Compositional resolver**: If resolution logic regresses, tests catch it

## Related

- `native_type_universe_*` memories - Type definitions to validate
- `bcl_rejection_infrastructure` memory - Error codes for rejection
- `checking_native_audit` memory - What FCS infrastructure is used

# CheckExpressions.fs Restructuring Plan

## Problem Statement

`CheckExpressions.fs` is 4000 lines with three architectural violations:

1. **String prefix dispatch** - `elif name.StartsWith("NativePtr.")` for intrinsic resolution
2. **Duplicate code paths** - `SynExpr.Ident` and `SynExpr.LongIdent` both do binding/intrinsic resolution
3. **Monolithic file** - Hard to navigate, maintain, and understand

## Target Structure

```
/Checking.Native/Expressions/
├── Types.fs              # TypeEnv, environment ops, diagnostics
├── Intrinsics.fs         # Module intrinsic resolution (proper dispatch)
├── Identity.fs           # Unified Ident + LongIdent resolution
├── Literals.fs           # Const → LiteralValue
├── Applications.fs       # App, TypeApp
├── Bindings.fs           # Let, Lambda, pattern bindings
├── ControlFlow.fs        # If, Match, While, For, Try
├── Collections.fs        # Tuple, Array, List, Record
├── TypeOperations.fs     # Typed, Cast, TypeTest, AddressOf
├── Patterns.fs           # Pattern checking
├── SynTypes.fs           # SynType → NativeType
└── CheckExpressions.fs   # Thin dispatcher (imports above)
```

## Key Architectural Fixes

### Fix 1: Intrinsic Module Dispatch

**Before (string prefix matching):**
```fsharp
elif name.StartsWith("NativePtr.") then
    let intrinsicName = name.Substring("NativePtr.".Length)
    match intrinsicName with
    | "read" -> ...
    | "write" -> ...
elif name.StartsWith("Sys.") then
    let intrinsicName = name.Substring("Sys.".Length)
    match intrinsicName with
    | "write" -> ...
```

**After (proper discriminated union dispatch):**
```fsharp
// In Intrinsics.fs

/// Parse "Module.operation" into structured form
let tryParseModuleQualified (name: string) : (IntrinsicModule * string) option =
    match name.IndexOf('.') with
    | -1 -> None
    | idx ->
        let modulePart = name.Substring(0, idx)
        let opPart = name.Substring(idx + 1)
        match modulePart with
        | "NativePtr" -> Some (IntrinsicModule.NativePtr, opPart)
        | "Sys" -> Some (IntrinsicModule.Sys, opPart)
        | "String" -> Some (IntrinsicModule.String, opPart)
        | "Array" -> Some (IntrinsicModule.Array, opPart)
        | "Parse" -> Some (IntrinsicModule.Parse, opPart)
        | "Format" -> Some (IntrinsicModule.Format, opPart)
        | "Crypto" -> Some (IntrinsicModule.Crypto, opPart)
        | "Bits" -> Some (IntrinsicModule.Bits, opPart)
        | "FnPtr" -> Some (IntrinsicModule.FnPtr, opPart)
        | "Signal" -> Some (IntrinsicModule.Signal, opPart)
        | "Effect" -> Some (IntrinsicModule.Effect, opPart)
        | "Memo" -> Some (IntrinsicModule.Memo, opPart)
        | "Batch" -> Some (IntrinsicModule.Batch, opPart)
        | "NativeStr" -> Some (IntrinsicModule.NativeStr, opPart)
        | "NativeDefault" -> Some (IntrinsicModule.NativeDefault, opPart)
        | _ -> None

/// Resolve a module-qualified intrinsic to its type
let resolveModuleIntrinsic
    (modl: IntrinsicModule)
    (op: string)
    (env: TypeEnv)
    (range: SourceRange)
    : IntrinsicResolution =

    match modl with
    | IntrinsicModule.NativePtr -> resolveNativePtrOp op env range
    | IntrinsicModule.Sys -> resolveSysOp op env range
    | IntrinsicModule.String -> resolveStringOp op env range
    | IntrinsicModule.Array -> resolveArrayOp op env range
    // ... each module has its own resolver function
```

Each module gets its own focused resolver:
```fsharp
let resolveNativePtrOp (op: string) (env: TypeEnv) (range: SourceRange) : IntrinsicResolution =
    let tyParam = freshTypeParam "'T" range
    match op with
    | "read" -> Ok (mkIntrinsic NativePtr "read" Memory, TFun(TNativePtr tyParam, tyParam))
    | "write" -> Ok (mkIntrinsic NativePtr "write" Memory, TFun(TNativePtr tyParam, TFun(tyParam, UnitType)))
    | "get" -> Ok (mkIntrinsic NativePtr "get" Memory, TFun(TNativePtr tyParam, TFun(IntType, tyParam)))
    | "set" -> Ok (mkIntrinsic NativePtr "set" Memory, TFun(TNativePtr tyParam, TFun(IntType, TFun(tyParam, UnitType))))
    | "add" -> Ok (mkIntrinsic NativePtr "add" Memory, TFun(TNativePtr tyParam, TFun(IntType, TNativePtr tyParam)))
    | "stackalloc" -> Ok (mkIntrinsic NativePtr "stackalloc" Memory, TFun(IntType, TNativePtr tyParam))
    | unknown -> Error $"Unknown NativePtr operation: {unknown}"
```

### Fix 2: Unified Identity Resolution

**Before (duplicate paths):**
```fsharp
// In SynExpr.Ident case (~line 602)
| SynExpr.Ident(ident) ->
    let name = ident.idText
    let tryConversionIntrinsic = match name with | "float" -> ... | "not" -> ...
    match tryConversionIntrinsic with
    | Some (info, ty) -> builder.Create(Intrinsic info, ty, ...)
    | None ->
        match tryLookupBinding name env with
        | Some binding -> builder.Create(VarRef(name, binding.NodeId), ...)
        | None -> error

// In SynExpr.LongIdent case (~line 752)
| SynExpr.LongIdent(_, longDotId, _, _) ->
    let name = longDotId |> String.concat "."
    if isBclReference name then error
    elif name.StartsWith("NativePtr.") then ...  // DUPLICATE intrinsic handling
    elif name.StartsWith("Sys.") then ...
    // ... 15 more elif branches
    else
        match tryLookupBinding name env with  // DUPLICATE binding lookup
        | Some binding -> builder.Create(VarRef(name, binding.NodeId), ...)
        | None -> error
```

**After (single resolution path in Identity.fs):**
```fsharp
// In Identity.fs

/// Unified identifier resolution - ONE code path for both Ident and LongIdent
let resolveIdentifier
    (parts: string list)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (range: SourceRange)
    : SemanticNode =

    let fullName = String.concat "." parts

    // 1. BCL rejection (FIRST - fail fast)
    if isBclReference fullName then
        addBclError fullName range env
        builder.Create(Error $"BCL: {fullName}", TError $"BCL: {fullName}", range)

    // 2. Operator intrinsics (simple names like "not", "op_Addition")
    elif parts.Length = 1 then
        let name = parts.[0]
        match tryResolveOperator name range with
        | Some (info, ty) -> builder.Create(Intrinsic info, ty, range)
        | None ->
            match tryResolveConversion name range with
            | Some (info, ty) -> builder.Create(Intrinsic info, ty, range)
            | None -> resolveBinding name env builder range

    // 3. Module-qualified intrinsics (NativePtr.read, Sys.write, etc.)
    elif parts.Length = 2 then
        match tryParseModuleQualified fullName with
        | Some (modl, op) ->
            match resolveModuleIntrinsic modl op env range with
            | Ok (info, ty) -> builder.Create(Intrinsic info, ty, range)
            | Error msg ->
                addError range msg env
                builder.Create(Error msg, TError msg, range)
        | None -> resolveBinding fullName env builder range

    // 4. Longer paths - binding lookup only
    else
        resolveBinding fullName env builder range

/// Resolve a binding by name
let private resolveBinding (name: string) (env: TypeEnv) (builder: NodeBuilder) (range: SourceRange) : SemanticNode =
    match tryLookupBinding name env with
    | Some binding ->
        match binding.LiteralValue with
        | Some lit -> builder.Create(Literal lit, binding.Type, range)
        | None ->
            let ty = instantiateTForall binding.Type range
            builder.Create(VarRef(name, binding.NodeId), ty, range)
    | None ->
        addError range $"Undefined: {name}" env
        builder.Create(Error $"Undefined: {name}", TError $"Undefined: {name}", range)
```

Then in CheckExpressions.fs:
```fsharp
| SynExpr.Ident(ident) ->
    Identity.resolveIdentifier [ident.idText] env builder range

| SynExpr.LongIdent(_, longDotId, _, _) ->
    let parts = longDotId.LongIdent |> List.map (fun id -> id.idText)
    Identity.resolveIdentifier parts env builder range
```

### Fix 3: File Splits

**Types.fs** (~200 lines):
- `TypeEnv` type
- `addBinding`, `tryLookupBinding`, etc.
- `addDiagnostic`, `addError`, `addWarning`, etc.
- `DiagnosticCodes` module
- `instantiateTForall`

**Intrinsics.fs** (~500 lines):
- `tryParseModuleQualified`
- `resolveModuleIntrinsic`
- Per-module resolvers: `resolveNativePtrOp`, `resolveSysOp`, etc.
- `tryResolveOperator` (for `not`, `op_Addition`, etc.)
- `tryResolveConversion` (for `float`, `int`, etc.)

**Identity.fs** (~100 lines):
- `resolveIdentifier` - the unified resolution function
- `isBclReference`, `addBclError`

**Literals.fs** (~100 lines):
- `typeOfConst`
- `constToLiteral`
- Literal expression handling

**Applications.fs** (~200 lines):
- `SynExpr.App` handling
- `SynExpr.TypeApp` handling
- Function application logic

**Bindings.fs** (~400 lines):
- `checkLetOrUse`
- `checkBinding`
- `extractLambdaParams`
- `buildLambdaNode`
- Lambda expression handling

**ControlFlow.fs** (~300 lines):
- `SynExpr.IfThenElse`
- `SynExpr.Match`, `checkMatchClause`
- `SynExpr.While`, `SynExpr.For`, `SynExpr.ForEach`
- `SynExpr.TryWith`, `SynExpr.TryFinally`

**Collections.fs** (~400 lines):
- `SynExpr.Tuple`
- `SynExpr.ArrayOrList`
- `SynExpr.Record`, `SynExpr.AnonRecd`
- Record field resolution

**TypeOperations.fs** (~200 lines):
- `SynExpr.Typed`
- `SynExpr.Upcast`, `SynExpr.Downcast`
- `SynExpr.TypeTest`
- `SynExpr.AddressOf`

**Patterns.fs** (~300 lines):
- `checkPattern`
- Pattern matching helpers

**SynTypes.fs** (~300 lines):
- `checkSynType`
- `checkSynConstraint`
- `checkSynMeasure`
- Measure types

**CheckExpressions.fs** (~500 lines):
- Main `checkExpr` function
- Thin dispatcher that routes to the above modules
- `checkAndSolve` entry point

## Implementation Order

1. **Create Expressions/ folder**
2. **Types.fs** - Extract TypeEnv and environment helpers (no dependencies)
3. **Intrinsics.fs** - Extract and fix intrinsic dispatch (depends on Types.fs)
4. **Identity.fs** - Unified resolution using Intrinsics.fs (KEY FIX)
5. **Literals.fs** - Simple extraction
6. **Patterns.fs** - Pattern checking (needed by Bindings)
7. **SynTypes.fs** - Type checking (needed by several)
8. **Bindings.fs** - Binding handling
9. **ControlFlow.fs** - Control flow expressions
10. **Collections.fs** - Collection expressions
11. **TypeOperations.fs** - Type operations
12. **Applications.fs** - Application handling
13. **CheckExpressions.fs** - Final thin dispatcher

## Testing Strategy

After each step:
1. Build FNCS: `dotnet build` in fsnative
2. Build Firefly: `dotnet build` in Firefly/src
3. Compile sample 01: Should still work
4. After Identity.fs: Verify operators are intrinsics (check fncs_expr.txt)

## Dependencies

The mutually recursive `and` functions present a challenge. Options:
1. Use `rec` within modules where needed
2. Forward declare types that need to reference each other
3. Accept some circular module references via `[<AutoOpen>]`

The cleanest approach is to have CheckExpressions.fs contain the recursive core that calls into the helper modules, rather than the helpers calling back.

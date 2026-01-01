# CheckExpressions.fs Completion Plan

## Status: CRITICAL GAP

FNCS CheckExpressions.fs handles only 24 of ~55 SynExpr cases. The catch-all fallback produces `TError "unhandled"` which breaks compilation.

## Reference

FCS CheckExpressions.fs: 12,864 lines, handles ALL cases explicitly.
Location: `~/repos/fsharp/src/Compiler/Checking/Expressions/CheckExpressions.fs`

## Currently Handled (24 cases)

- App, ArrayOrList, Const, Do, DotGet, For, Ident, IfThenElse
- InterpolatedString, Lambda, LetOrUse, LongIdent, Match, Null
- Paren, Quote, Record, Sequential, Set, TryFinally, TryWith
- Tuple, Typed, While

## Missing Cases (Priority by Alloy Usage)

### Critical for Alloy (MUST IMPLEMENT FIRST)

| Case | Used For | FCS Handler |
|------|----------|-------------|
| AddressOf | `&&variable` pointer ops | mkSynPrefixPrim |
| TraitCall | SRTP resolution | TcExprTraitCall |
| TypeApp | `stackalloc<byte>` generics | DelayedTypeApp |
| ForEach | `for x in collection` | TcForEachExpr |
| DotIndexedGet | `arr.[i]` | TcIndexerThen |
| DotIndexedSet | `arr.[i] <- v` | TcIndexerThen |
| Upcast | `:>` | TcExprUpcast |
| Downcast | `:?>` | TcExprDowncast |
| InferredUpcast | implicit upcast | TcExprUpcast |
| InferredDowncast | implicit downcast | TcExprDowncast |
| TypeTest | `:?` | TcExprTypeTest |

### Secondary (Common F# Patterns)

| Case | Used For |
|------|----------|
| MatchLambda | `function` keyword |
| Lazy | `lazy expr` |
| Assert | `assert` |
| DotSet | `obj.Field <- v` |
| LongIdentSet | `Module.x <- v` |
| AnonRecd | `{| field = v |}` |
| ObjExpr | `{ new IFace with ... }` |
| New | `new Type(args)` |

### Computation Expressions (Can Defer)

| Case | Used For |
|------|----------|
| ComputationExpr | `async { }`, `seq { }` |
| YieldOrReturn | `yield`, `return` |
| YieldOrReturnFrom | `yield!`, `return!` |
| DoBang | `do!` |
| MatchBang | `match!` |
| WhileBang | `while!` |
| ImplicitZero | implicit unit return |
| SequentialOrImplicitYield | seq expr chaining |

### Error Recovery (Low Priority)

| Case | Used For |
|------|----------|
| ArbitraryAfterError | parse recovery |
| FromParseError | parse recovery |
| DiscardAfterMissingQualificationAfterDot | parse recovery |

### Specialized (Rare Usage)

| Case | Used For |
|------|----------|
| Dynamic | `?` operator |
| DotLambda | `_.Property` syntax |
| Fixed | `fixed` pointers |
| JoinIn | query join |
| IndexRange | `x.[1..5]` |
| IndexFromEnd | `x.[^1]` |
| Typar | type param in expr |
| DebugPoint | debugger hints |
| LibraryOnly* | FSharp.Core internal |

## Implementation Strategy

1. **Remove catch-all** - Replace with explicit rejection for all unhandled cases
2. **Implement Critical cases** - AddressOf, TraitCall, TypeApp, ForEach first
3. **Follow FCS patterns** - Each case has dedicated handler function
4. **No shortcuts** - Every case fully implemented or explicitly rejected with clear error

## Key FCS Patterns

### AddressOf
```fsharp
| SynExpr.AddressOf (byref, synInnerExpr, mOperator, m) ->
    TcExpr cenv overallTy env tpenv 
        (mkSynPrefixPrim mOperator m (if byref then "~&" else "~&&") synInnerExpr)
```

### TraitCall
```fsharp
| SynExpr.TraitCall (TypesForTypar tps, synMemberSig, arg, m) ->
    TcExprTraitCall cenv overallTy env tpenv (tps, synMemberSig, arg, m)
```

### TypeApp
```fsharp
| SynExpr.TypeApp (func, _, typeArgs, _, _, mTypeArgs, mFuncAndTypeArgs) ->
    TcExprThen cenv overallTy env tpenv false func 
        ((DelayedTypeApp (typeArgs, mTypeArgs, mFuncAndTypeArgs)) :: delayed)
```

### ForEach
```fsharp
| SynExpr.ForEach (spFor, spIn, SeqExprOnly seqExprOnly, isFromSource, pat, synEnumExpr, synBodyExpr, m) ->
    TcForEachExpr cenv overallTy env tpenv (seqExprOnly, isFromSource, pat, synEnumExpr, synBodyExpr, m, spFor, spIn, m)
```

## Success Criteria

- All 55 SynExpr cases explicitly handled
- No catch-all fallback
- Alloy compiles without "unhandled" errors
- HelloWorldDirect sample produces working binary

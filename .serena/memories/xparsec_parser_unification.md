# XParsec Parser Unification: Replacing FsLex/FsYacc

## ⚠️ PROJECT STATUS: POST-QC_DEMO ⚠️

**This is a deliberate, planned project scheduled AFTER the QC_Demo milestone.**

### Why Wait?

1. **QC_Demo validates current path**: The demo exercises Firefly → native compilation with existing FCS/FNCS integration
2. **Working baseline required**: Parser replacement is architectural - need proven foundation first
3. **Dedicated focus needed**: ~6 months effort requires uninterrupted attention
4. **Risk isolation**: Don't destabilize parsing during demo-critical development

### Prerequisites Before Starting

- [ ] QC_Demo complete and validated on YoshiPi
- [ ] FNCS native type checker operational
- [ ] Firefly samples 01-04 stable
- [ ] ARM64 target validated

**Do NOT begin this work until these prerequisites are met.**

---

## Executive Summary

Replace FsLex and FsYacc with XParsec-based parsing to:
1. Remove OCaml-derived tooling dependencies
2. Unify parsing infrastructure with Firefly's Alex (same XParsec library)
3. Enable self-hosting path (parser written in parseable F#)
4. Eliminate unreadable generated table code (~25K LOC)

## Current State

### The "Three Parsers" Problem

FCS has three lexer/parser pairs:

| Component | Files | Lines | Purpose |
|-----------|-------|-------|---------|
| Main F# | `lex.fsl` + `pars.fsy` | 1936 + 7195 | F# syntax |
| Preprocessor | `pplex.fsl` + `pppars.fsy` | 62 + 62 | `#if`, `#else`, etc. |
| **Generated** | `lex.fs` + `pars.fs` + ... | ~25K | Unreadable tables |

Plus the critical **LexFilter** (~2000 LOC) that:
- Implements the offside rule (indentation-sensitivity)
- Synthesizes tokens (`OLET`, `OTHEN`, `OBLOCKBEGIN`, etc.)
- Maintains context stack for nested scopes
- Is hand-written F# (not generated)

### Why This Matters for FNCS

1. **FsLex/FsYacc are OCaml-derived**: Build tooling from a different ecosystem
2. **Generated tables are opaque**: Can't modify, can't understand, can't debug
3. **Bootstrap complexity**: Must build fslex/fsyacc before building compiler
4. **No path to self-hosting**: Parser generators can't be compiled by native Firefly
5. **Duplication with Firefly**: XParsec already used in Alex for PSG traversal

## XParsec Capabilities

### Already Proven in Firefly

XParsec is already the parsing infrastructure in Firefly's Alex:
- `PSGXParsec.fs` - PSG child parsing
- `PSGZipper.fs` - Navigation with XParsec patterns
- Works with custom `IReadable` implementations

### Key Features for F# Parsing

```fsharp
// Generic over input type - can parse tokens, not just chars
type Parser<'Parsed, 'T, 'State, 'Input, 'InputSlice> =
    Reader<'T, 'State, 'Input, 'InputSlice> -> ParseResult<'Parsed, 'T, 'State>

// Pratt parsing for operator precedence (essential for F# expressions!)
let parser pExpr operators : Parser<'Expr, _, _, _, _> =
    Pratt.parseLhs pExpr operators Precedence.MinP
```

### Pratt Parsing: The F# Expression Solution

F# has ~20+ operator precedence levels. Pratt parsing handles this elegantly:

```fsharp
// Define F# operators with precedence
let fsharpOperators = Operator.create [
    // Highest precedence
    infixLeftAssoc "." P30 pDot (fun l r -> DotAccess(l, r))
    
    // Function application (left-assoc, high precedence)
    infixLeftAssoc " " P28 pWhitespace (fun f x -> App(f, x))
    
    // Arithmetic
    infixLeftAssoc "**" P20 (pstr "**") (fun l r -> Power(l, r))
    infixLeftAssoc "*" P18 (pchar '*') (fun l r -> Mul(l, r))
    infixLeftAssoc "/" P18 (pchar '/') (fun l r -> Div(l, r))
    infixLeftAssoc "+" P16 (pchar '+') (fun l r -> Add(l, r))
    infixLeftAssoc "-" P16 (pchar '-') (fun l r -> Sub(l, r))
    
    // Comparison
    infixNonAssoc "<" P14 (pchar '<') (fun l r -> LessThan(l, r))
    infixNonAssoc ">" P14 (pchar '>') (fun l r -> GreaterThan(l, r))
    infixNonAssoc "=" P14 (pchar '=') (fun l r -> Equals(l, r))
    
    // Boolean
    infixLeftAssoc "&&" P10 (pstr "&&") (fun l r -> And(l, r))
    infixLeftAssoc "||" P8 (pstr "||") (fun l r -> Or(l, r))
    
    // Pipe operators (right-assoc)
    infixRightAssoc "|>" P6 (pstr "|>") (fun l r -> PipeRight(l, r))
    infixLeftAssoc "<|" P6 (pstr "<|") (fun l r -> PipeLeft(l, r))
    
    // Sequencing
    infixRightAssoc ";" P4 (pchar ';') (fun l r -> Seq(l, r))
    
    // Prefix
    prefix "-" P22 (pchar '-') (fun x -> Negate x)
    prefix "not" P12 (pstr "not") (fun x -> Not x)
    
    // Enclosing
    enclosedBy "(" ")" P30 (pchar '(') (pchar ')') id
    enclosedBy "[" "]" P30 (pchar '[') (pchar ']') (fun x -> List x)
]
```

### Performance

XParsec benchmarks show:
- **2/3 execution time** vs FParsec
- **1/4 allocations** vs FParsec
- Uses `[<InlineIfLambda>]`, `Span<'T>`, struct unions

This is competitive with hand-written parsers.

## Architecture: Two-Phase Parsing

### Phase 1: Tokenization (Replaces FsLex)

```fsharp
/// Token stream from source
type Token =
    | IDENT of string
    | STRING of string * SynStringKind
    | INT32 of int32
    | KEYWORD of Keyword
    | OPERATOR of string
    | LPAREN | RPAREN | LBRACE | RBRACE | LBRACK | RBRACK
    | COMMA | SEMICOLON | COLON | DOT
    | NEWLINE | INDENT of int | DEDENT
    | EOF
    // ... ~80 token types

/// XParsec-based tokenizer
let tokenize : Parser<Token, char, TokenizerState, StringSlice, StringSlice> =
    choice [
        pKeyword      // match keywords first
        pIdentifier   // then identifiers
        pOperator     // operators
        pStringLit    // string literals
        pNumericLit   // numeric literals
        pPunctuation  // punctuation
        pWhitespace   // produces NEWLINE, INDENT, DEDENT
    ]
```

### Phase 2: Offside Filter (Replaces LexFilter)

The LexFilter is the key challenge. It's a stateful token transformer:

```fsharp
/// Offside context (from current LexFilter.fs)
type Context =
    | CtxtLetDecl of bool * Position
    | CtxtIf of Position
    | CtxtMatch of Position
    | CtxtSeqBlock of FirstInSequence * Position * AddBlockEnd
    // ... 20+ context types

/// Offside filter transforms token stream
let offsideFilter (tokens: Token seq) : Token seq =
    // This is the complex part - must track context stack
    // Insert synthetic tokens: OBLOCKBEGIN, OBLOCKEND, OLET, etc.
    // Key insight: this is already hand-written F#, not generated!
```

**Key Insight**: The LexFilter is already hand-written F# (~2000 lines). It doesn't use FsLex/FsYacc. We can keep it largely as-is, just adapting to new token types.

### Phase 3: Expression/Declaration Parsing (Replaces FsYacc)

```fsharp
/// Parse expressions with Pratt parsing
let rec pExpr : Parser<SynExpr, Token, ParserState, TokenSlice, TokenSlice> =
    Operator.parser pAtomicExpr fsharpOperators

/// Atomic expressions (base cases)
and pAtomicExpr : Parser<SynExpr, Token, ParserState, TokenSlice, TokenSlice> =
    choice [
        pIdent |>> SynExpr.Ident
        pConst |>> SynExpr.Const
        pParen pExpr
        pIfExpr
        pMatchExpr
        pLetExpr
        pLambdaExpr
        // ...
    ]

/// Let expression
and pLetExpr =
    parser {
        let! _ = pToken OLET  // Offside LET (from filter)
        let! pat = pPattern
        let! _ = pToken EQUALS
        let! body = pExpr
        let! _ = pToken (ODECLEND _)  // Offside end (from filter)
        let! cont = pExpr
        return SynExpr.LetOrUse(...)
    }
```

## Migration Strategy

### Phase 1: Tokenizer (Low Risk)

**What changes:**
- Replace `lex.fsl` with XParsec char parser
- Output same token types currently defined in `pars.fsy`

**Risk:** Low - tokenization is declarative, straightforward mapping

**Effort:** 2-3 weeks

### Phase 2: Offside Filter (No Change)

**What changes:**
- Minimal - adapt to new token representation
- LexFilter.fs is already hand-written F#

**Risk:** Very low - this code stays largely unchanged

**Effort:** 1 week

### Phase 3: Expression Parser (Medium Risk)

**What changes:**
- Replace `pars.fsy` expression rules with Pratt parser
- Use XParsec combinators for non-expression constructs

**Risk:** Medium - F# grammar is complex, many edge cases

**Strategy:** 
- Start with expression subset (literals, operators, application)
- Gradually add constructs (let, match, if, etc.)
- Run in parallel with FsYacc parser for validation

**Effort:** 4-6 weeks for core, 4-6 weeks for completeness

### Phase 4: Declaration Parser (Medium Risk)

**What changes:**
- Replace module/namespace/type declaration rules
- Pattern matching rules

**Risk:** Medium - declarations have complex nesting

**Effort:** 3-4 weeks

## Benefits

### Immediate

1. **No build tooling dependency**: fslex/fsyacc eliminated from build
2. **Readable parser code**: Recursive descent is maintainable
3. **Debuggable**: Can step through parsing, set breakpoints
4. **~25K LOC removed**: Generated tables gone

### For Self-Hosting

1. **Parser is parseable F#**: XParsec code can be compiled by native Firefly
2. **Unified infrastructure**: Same XParsec in parser and in Alex
3. **Quotation-compatible**: Parser combinators can be quoted for optimization

### For Native Compilation

1. **No string-based code generation**: Clean compilation path
2. **Type-safe throughout**: XParsec preserves types
3. **Performance**: Competitive with generated tables

## Challenges and Mitigations

### Challenge 1: F# Grammar Complexity

F# has ~200 grammar productions. This is substantial.

**Mitigation:**
- Pratt parsing handles operators elegantly
- Modular parser structure (one file per construct)
- Incremental migration with parallel validation

### Challenge 2: Error Recovery

FsYacc has error recovery via `%error` productions.

**Mitigation:**
- XParsec has `attempt` for backtracking
- Error accumulation via nested errors
- LexFilter already handles many recovery cases

### Challenge 3: Performance

Must match or exceed current parser performance.

**Mitigation:**
- XParsec benchmarks are promising (2/3 time, 1/4 allocations)
- `[<InlineIfLambda>]` eliminates combinator overhead
- Critical paths can use imperative optimization

### Challenge 4: Compatibility

Must parse all valid F# exactly as current parser.

**Mitigation:**
- Extensive test suite exists
- Run both parsers in parallel during migration
- Differential testing against FCS

## What NOT To Do

1. **Don't try to convert LALR tables to recursive descent**
   - The README notes this is impractical
   - Write fresh parsers using XParsec idioms

2. **Don't modify LexFilter significantly**
   - It's complex, well-tested, and already F#
   - Adapt minimally to new token representation

3. **Don't attempt all-at-once replacement**
   - Incremental migration with parallel validation
   - Expression parsing first, then declarations

## Relationship to FNCS Architecture

This parser unification supports the broader FNCS goals:

```
XParsec Tokenizer
       ↓
Offside Filter (LexFilter)
       ↓
XParsec Parser → SynExpr/SynModule
       ↓
Native Type Checker → SemanticNode (unified)
       ↓
Hard Prune
       ↓
Firefly/Alex (also uses XParsec!)
       ↓
Native Binary
```

The same XParsec library spans from source parsing to MLIR generation.

## Timeline Estimate

| Phase | Effort | Cumulative |
|-------|--------|------------|
| Tokenizer | 2-3 weeks | 3 weeks |
| Offside adapter | 1 week | 4 weeks |
| Core expressions | 4-6 weeks | 10 weeks |
| Full expressions | 4-6 weeks | 16 weeks |
| Declarations | 3-4 weeks | 20 weeks |
| Validation/polish | 4 weeks | 24 weeks |

**Total: ~6 months** for complete replacement with parallel validation.

## Self-Hosting Connection

This ties directly to F#'s metaprogramming strengths:

- **Quotations**: Parser combinator definitions can be quoted for inspection/optimization
- **Active Patterns**: XParsec uses active patterns for token matching (same pattern as Alex)
- **Computation Expressions**: XParsec's `parser { }` builder mirrors the pattern

When the parser itself is XParsec-based F#, the self-hosting compiler can compile its own parser - completing the bootstrap chain.

## Recommendation

**Proceed with XParsec unification AFTER QC_Demo.** The benefits align with FNCS goals:
- Reduces surface area (removes OCaml-derived tooling)
- Enables self-hosting (parser is compilable F#)
- Unifies infrastructure (XParsec throughout)
- Improves maintainability (readable recursive descent)

Start with tokenizer (lowest risk), then expression parser (validates Pratt approach), then complete the migration incrementally.

## References

- `/home/hhh/repos/XParsec/` - XParsec library source
- `/home/hhh/repos/fsnative/buildtools/README-fslexyacc.md` - FsLex/FsYacc notes
- `/home/hhh/repos/fsnative/src/Compiler/SyntaxTree/LexFilter.fs` - Offside rule implementation
- Firefly `Alex/Traversal/PSGXParsec.fs` - XParsec usage in compiler

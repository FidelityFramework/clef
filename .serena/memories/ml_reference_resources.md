# ML Language Reference Resources

## Primary Reference: F* (FStar)

**Location**: `~/repos/FStar`

F* is an ML-family language with dependent types and effect system. It serves as the **primary reference** for principled solutions to type-theoretic questions in FNCS because:

1. **Pure ML heritage**: F* follows ML type discipline without .NET/CLR assumptions
2. **Effect system**: Models side effects through indexed monads - informs coeffect design
3. **Proof assistant integration**: Type-level computation patterns
4. **Verified extraction**: Compiles to OCaml/F#/C - informs native codegen

**When to consult F***:
- SRTP resolution strategies (F* has refined type inference)
- Effect/coeffect typing patterns
- Dependent type encoding approaches
- Memory safety proofs at type level
- Platform-agnostic type representations

**Key areas in FStar codebase**:
- `src/typechecker/` - Type inference and constraint solving
- `src/extraction/` - Lowering typed AST to target languages
- `ulib/` - Core library with effect definitions

## Secondary Reference: F# Compiler (FCS)

**Location**: `~/repos/fsharp`

The standard F# compiler serves as a **secondary reference** for understanding:

1. **F# semantics**: When FNCS diverges, understand what FCS does and why
2. **Type checking patterns**: `TyconRef.Deref`, constraint solving, SRTP
3. **AST structures**: SynExpr, FSharpExpr - Firefly consumes these
4. **Symbol resolution**: How FCS resolves names to symbols

**When to consult FCS**:
- Understanding standard F# behavior before diverging
- Type representation questions (TType_*, FSharpType)
- Constraint solver patterns
- Module/namespace resolution

**Key areas in FCS codebase**:
- `src/Compiler/Checking/` - Type checking passes
- `src/Compiler/TypedTree/` - Typed representation
- `src/Compiler/Symbols/` - Symbol layer for tooling
- `src/Compiler/SyntaxTree/` - Parsing and syntax

## Usage Pattern

1. **Start with FStar** for principled ML solutions
2. **Consult FCS** for F#-specific behavior that must be preserved
3. **Document divergence** when FNCS chooses a different path

## Example Decision Process

**Question**: How should FNCS handle polymorphic recursion?

1. Check FStar: `~/repos/FStar/src/typechecker/TcTerm.fst` - how does F* infer types for recursive definitions?
2. Check FCS: `~/repos/fsharp/src/Compiler/Checking/CheckExpressions.fs` - what does F# do?
3. Design FNCS approach: Choose FStar-like principled solution unless F# compatibility requires FCS approach

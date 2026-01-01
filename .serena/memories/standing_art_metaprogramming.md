# Standing Art: F# Metaprogramming in Fidelity Framework

> Reference: "Standing Art: F# Metaprogramming Features in the Firefly Compiler" (SpeakEZ Blog)

## Core Principle

Three F# features form the architectural backbone of Firefly's native compilation:

| Feature | Compilation Role | Unique Capability |
|---------|-----------------|-------------------|
| **Quotations** | Semantic carriers | Encode constraints as inspectable data |
| **Active Patterns** | Structural recognition | Compositional matching without type discrimination |
| **Computation Expressions** | Control flow abstraction | Continuation capture as notation |

These are **standing art**: capabilities Don Syme designed for staged computation that now enable native compilation without runtime dependencies.

## Quotations (`Expr<'T>`)

- Encode program fragments as **compile-time data** (not runtime evaluated)
- Carry memory constraints and peripheral descriptors through PSG
- **No BCL dependencies**, no runtime support needed
- Example: Hardware binding quotations carry semantic info (volatile access, memory region)

```fsharp
let gpioQuotation: Expr<PeripheralDescriptor> = <@
    { Name = "GPIO"
      Instances = Map.ofList [("GPIOA", 0x48000000un)]
      MemoryRegion = Peripheral }
@>
```

## Active Patterns

- Enable structural recognition **without string matching or type hierarchies**
- Used in typed tree zipper and Alex traversal
- Compose with `&` and `|` operators

```fsharp
let (|PeripheralAccess|_|) (node: PSGNode) =
    match node with
    | CallToExtern name args when isPeripheralBinding name ->
        Some (extractPeripheralInfo args)
    | _ -> None
```

## Computation Expressions

- `let!` desugars to continuation capture
- Compile to DCont dialect (continuations) or Inet dialect (data flow)
- MLIR builder is itself a computation expression

| Pattern | Dialect | Strategy |
|---------|---------|----------|
| Sequential effects (async, state) | DCont | Preserve continuations |
| Parallel pure (validated, reader) | Inet | Compile to data flow |

## Tooling Implications (FSNAC)

For FsNativeAutoComplete, display these constructs properly:

1. **Quotations**: Show as "compile-time semantic carrier" not "runtime expression"
2. **Active Patterns**: Show compositional structure in hover
3. **Computation Expressions**: Format continuation bindings
4. **Native Types**: Use fsnative semantics (voption, platform words, UTF-8 fat pointers)

## Comparison to Other Languages

| Capability | OCaml | Rust | F#/Fidelity |
|------------|-------|------|-------------|
| Native compilation | Yes | Yes | Yes (via MLIR) |
| Typed quotations | No | No | **Yes** |
| Pattern-based recognition | Match only | Match only | Active patterns |
| Continuation notation | No | No | Computation expressions |
| Metaprogramming | PPX (stringly) | proc_macro (stringly) | Quotations (typed) |

## Self-Hosting Path

These features enable Firefly to compile itself:
- Quotations represent compiler AST structures
- Active patterns match on compiler IR
- Computation expressions structure the pipeline

# F# Native Compiler Services

**Native-first type resolution for F# ahead-of-time compilation.**

---

## What is fsnative?

fsnative is F# Native Compiler Services (FNCS), a specialized fork of [Microsoft's F# compiler](https://github.com/dotnet/fsharp) designed for native compilation. Where the standard F# compiler assumes a managed runtime with garbage collection and BCL types, fsnative understands native types, deterministic memory, and statically resolved operations from the ground up.

fsnative is the frontend for the [Fidelity](https://speakez.tech/blog/fidelity-framework-a-primer/) native compilation framework. It parses F# code, performs type checking, and produces a typed abstract syntax tree that flows directly into native code generation. No .NET runtime required.

## Why fsnative Exists

The standard F# Compiler Services does an excellent job for .NET development. Microsoft is making progress with ahead-of-time (AOT) compilation, but there are fundamental limitations. When you're compiling to true native binaries without a runtime or garbage collector, many .NET assumptions become obstacles:

**Strings are garbage-collected UTF-16 objects.** Native compilation needs UTF-8 strings with deterministic lifetimes. When a string goes out of scope, its memory should be freed immediately.

**Option types are heap-allocated reference types.** Native compilation needs value options that live on the stack and cost nothing when they're `None`.

**Memory has no notion of ownership or regions.** Native compilation needs to distinguish stack memory from heap memory, peripheral registers from RAM, read-only flash from writable SRAM. The type system should enforce these distinctions at compile time.

**The runtime manages all memory.** Native compilation needs explicit control. Pointers should carry lifetime information. The compiler should track whether memory is borrowed or owned, mutable or immutable.

These aren't bugs to work around. They're fundamental assumptions baked into the type system. fsnative replaces those assumptions with native-first semantics while preserving the F# developer experience.

## The Vision

fsnative makes native types *intrinsic* to the compiler:

```fsharp
// What you write
let greeting = "Hello, World!"

// Standard F#: System.String (UTF-16, GC-managed)
// fsnative:    NativeStr (UTF-8, deterministic lifetime)
```

```fsharp
// What you write
let maybeValue = Some 42

// Standard F#: int option (reference type, heap allocated)
// fsnative:    int voption (value type, stack allocated)
```

```fsharp
// What you write
let inline add a b = a + b

// Standard F#: resolves against System.Int32.op_Addition
// fsnative:    resolves against Alloy.BasicOps witness hierarchy
```

The compiler *knows* these types. It doesn't discover them by reading assembly metadata. It understands their layout, their semantics, their operations. When fsnative produces a typed tree, the types are already native, ready for direct translation to MLIR and (at least initially to) LLVM.

## The Fidelity Pipeline

fsnative is one piece of a larger native compilation story:

```
F# Source
    ↓
fsnative (FNCS)     ← You are here
    ↓
Program Semantic Graph (PSG)
    ↓
Alex → MLIR → LLVM
    ↓
Native Binary
```

**fsnative** provides parsing and native-first type checking.

**[Firefly](https://github.com/speakeztech/Firefly)** builds the Program Semantic Graph and generates MLIR.

**[Alloy](https://github.com/speakeztech/Alloy)** provides the native standard library: BCL-sympathetic APIs without BCL runtime dependencies.

**[BAREWire](https://github.com/speakeztech/BAREWire)** provides zero-copy serialization and memory region abstractions for embedded and systems programming.

**[Farscape](https://github.com/speakeztech/Farscape)** generates type-safe peripheral descriptors from header files, giving the compiler knowledge of hardware register layouts.

Together, they compile F# to efficient, standalone native binaries that run without any runtime.

## What fsnative Will Provide

- **Parsing**: Full F# syntax support via the battle-tested FCS lexer and parser
- **Native Type Resolution**: String literals, options, and arrays resolve to native types
- **Memory Region Tracking**: Pointers carry region and access-kind information through the type system, distinguishing stack from heap, peripheral registers from RAM, read-only from writable memory
- **Native SRTP**: Statically resolved type parameters resolve against the Alloy witness hierarchy
- **Typed Tree**: Complete `FSharpExpr` output for downstream code generation
- **IDE Services**: Symbol resolution, type information, and semantic classification for tooling

## What fsnative Does Not Provide

fsnative is a focused frontend, not a complete compiler:

- **No IL generation**: That's what the standard F# compiler does
- **No MSBuild integration**: Project files are handled by Firefly
- **No NuGet resolution**: Package management is external
- **No REPL**: Interactive scripting requires a managed runtime. We'll be looking into providing a REPL experience similar to Rust's model in Firefly.

fsnative stops at the typed tree. Code generation happens in Firefly via MLIR.

## Getting Started

fsnative is consumed as a library by the Firefly compiler:

```fsharp
// Firefly uses fsnative for type checking
let checker = FNCSChecker.Create()
let results = checker.ParseAndCheck(sourceFiles, config)

// Results contain the typed tree with native type resolution
let typedTree = results.TypedTree
let srtpResolutions = results.SRTPResolutions
```

For most use cases, you'll interact with fsnative through Firefly rather than directly.

## Documentation

| Document | Description |
|----------|-------------|
| [docs/fidelity/README.md](docs/fidelity/README.md) | FNCS overview and architecture |
| [docs/fidelity/FNCS_Phase1_Transformation_Plan.md](docs/fidelity/FNCS_Phase1_Transformation_Plan.md) | Detailed transformation roadmap |
| [docs/fidelity/FNCS_Pruning_Plan.md](docs/fidelity/FNCS_Pruning_Plan.md) | Component pruning strategy |

For the complete Fidelity ecosystem documentation, see the [Firefly docs](https://github.com/speakeztech/Firefly/tree/main/docs).

## Relationship to dotnet/fsharp

fsnative is a fork of Microsoft's [dotnet/fsharp](https://github.com/dotnet/fsharp) repository. We're grateful to the F# team and community for creating and maintaining an excellent compiler.

Our modifications focus on type resolution, not syntax. We aspire to match F# code that parses with the standard compiler to also parse similarly with fsnative. There will be some differences of course, such as the lack of C# interop, and no nullability (we use option exclusively). So while we're not exactly looking for a 1:1 syntactic match, we want all of the norms and conventions to be present.

We maintain the fork as a focused, surgical modification rather than a wholesale rewrite. The parsing, name resolution, and constraint solving machinery remains largely intact. What changes is the underlying type machinery those mechanisms operate against.

## Status

fsnative is under active development as part of the Fidelity framework. The current focus is:

- [ ] Phase 1: Structural pruning and namespace transformation
- [ ] Phase 2: Native type integration
- [ ] Phase 3: SRTP resolution against Alloy witnesses
- [ ] Phase 4: Memory region and access kind measures

See [FNCS_Phase1_Transformation_Plan.md](docs/fidelity/FNCS_Phase1_Transformation_Plan.md) for detailed status.

## License

This project is subject to the MIT License. Original work is copyright Microsoft Corporation. Modifications are copyright SpeakEZ Technologies.

See [LICENSE.txt](/LICENSE) for details.

## Contact

fsnative is developed by [SpeakEZ Technologies](https://speakez.tech) as part of the Fidelity native compilation framework.

For questions about fsnative and the Fidelity ecosystem, reach out through the [Firefly repository](https://github.com/speakeztech/Firefly).

---

*F# syntax you know. Native semantics you need.*

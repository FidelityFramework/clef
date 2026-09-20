# From F# to Clef: A Developer's Journey

> Historical migration essay. Composer's [completion roadmap](../../../Composer/docs/Clef_Language_Completion_Analysis.md)
> governs implementation work. Parts V–VI and §7.4 were corrected on September 19;
> other inherited examples, including measure-encoded region/access parameters,
> actor inheritance and F* integration claims, are superseded context rather than
> current Clef source or implementation contracts. See the
> [reconciliation](../../../Composer/docs/Clef_Language_Completion_Review_2026-09-19.md).

## Introduction

This document addresses the experienced .NET developer who has invested years in understanding F#, the Common Language Runtime, and the Base Class Library ecosystem. It presents Clef not as a rejection of that knowledge, but as an evolution that reclaims capabilities the language has always possessed, capabilities that the managed runtime abstracted away for convenience but that native compilation now requires us to reconsider.

The transition from F# on .NET to Clef is not merely a technical migration; it is a conceptual shift in how we think about memory, types, and the relationship between our source code and the machine that executes it. This document walks through that shift systematically, beginning with familiar ground and progressing toward the new mental model that Clef demands.

A note on how we arrived here: the Clef type system was not designed from some level of academic remove and then implemented. It emerged from engineering necessity. The initial goal was simply to compile F# to native code, and the approach involved creating "shadow types" in the Alloy library to mask BCL types during Baker type resolution. To give credit where it is due, FSharp.Core already contained some primitive types that proved invaluable in this early work: the `voption` type existed beyond the standard `option` type's null representation, and `NativeInterop.nativeptr` remained central to much of what we accomplished before making the "full break" to create Clef.

What we discovered, through iteration and experimentation, was that the types we needed bore a striking resemblance to OCaml's native types. This accidental sympathy with OCaml revealed something fundamental about ML-family languages: when you strip away the managed runtime, the natural semantics that emerge are value-oriented, UTF-8 native, and explicitly memory-aware. The sympathies to principled design are certainly part of the full picture, and those elements serve to further inform how the framework will develop as requirements grow and opportunities to target new platforms emerge. The journey described in this document reflects that discovery.

## Part I: Understanding What the CLR Has Been Doing for You

### 1.1 The Invisible Runtime

When you write F# targeting .NET, the Common Language Runtime performs substantial work that remains invisible to your source code. Consider the simplest possible expression:

```fsharp
let greeting = "Hello, World!"
```

In standard F#, this single line triggers a cascade of runtime behaviors:

1. The string literal is encoded as UTF-16 and stored in the assembly metadata
2. At runtime, the CLR allocates memory on the managed heap
3. The string object includes a header with type information and a synchronization block
4. The garbage collector tracks this allocation for potential collection
5. The string is immutable; any modification creates a new heap allocation

None of this appears in your source code. The runtime handles it transparently, and for most application development, this transparency is a feature rather than a limitation. You write `"Hello, World!"`, and the runtime ensures that a valid string object exists when you need it.

### 1.2 The Managed Heap Assumption

The .NET programming model assumes the existence of a managed heap with garbage collection. This assumption permeates the entire BCL design:

```fsharp
// Every F# option is a heap allocation (unless optimized away)
let maybeValue = Some 42

// Every array is a heap object with GC tracking
let numbers = [| 1; 2; 3 |]

// Every record without [<Struct>] lives on the heap
type Person = { Name: string; Age: int }
let alice = { Name = "Alice"; Age = 30 }
```

The garbage collector provides a powerful abstraction: you allocate freely, and the runtime reclaims memory when objects become unreachable. This abstraction has enabled productive development for decades. However, it comes with costs that become apparent only when you attempt to operate outside the managed environment:

1. **Memory overhead**: Every heap object carries metadata for the garbage collector
2. **Latency unpredictability**: Collection pauses can occur at any time
3. **Memory layout opacity**: You cannot control exactly where data resides
4. **Runtime dependency**: The program requires the CLR to execute

### 1.3 Type Erasure and Boxing

The CLR's type system differs from the type system you see in your F# source code. Generic type parameters exist at compile time, but the runtime has a more limited view. Consider:

```fsharp
let inline identity (x: ^T) = x
```

The constraint `^T` is a statically resolved type parameter (SRTP). The F# compiler resolves `^T` entirely at compile time, inlining the appropriate code for each concrete type. The CLR never sees `^T` directly; it sees only the result of that resolution.

For regular generics, the story differs. The CLR does maintain generic type information at runtime, but method dispatch often involves boxing for value types:

```fsharp
let compareValues (a: 'T) (b: 'T) when 'T :> System.IComparable<'T> =
    a.CompareTo(b)
```

When `'T` is a value type like `int`, the runtime may need to box the values to invoke the interface method, depending on how the code is compiled and optimized.

### 1.4 The BCL Type Universe

Every F# primitive type maps to a BCL type:

| F# Keyword | BCL Type | Size | Notes |
|------------|----------|------|-------|
| `int` | `System.Int32` | 4 bytes | Always 32 bits, regardless of platform |
| `int64` | `System.Int64` | 8 bytes | Always 64 bits |
| `float` | `System.Double` | 8 bytes | IEEE 754 double precision |
| `string` | `System.String` | Variable | UTF-16, immutable, heap allocated |
| `bool` | `System.Boolean` | 1 byte | But often padded for alignment |
| `unit` | `Microsoft.FSharp.Core.Unit` | 0 bytes | Singleton, reference type |

This mapping is fixed and universal across all .NET platforms. When you write `let x: int = 42`, you are working with a `System.Int32`, and the full weight of the BCL specification governs its behavior.

## Part II: What Native Compilation Changes

### 2.1 The Absence of the Runtime

Native compilation removes the CLR from the execution environment. The compiled binary runs directly on the operating system, with no intermediate runtime layer. This change has profound implications:

1. **No garbage collector**: Memory must be managed explicitly or through compile-time strategies
2. **No type metadata at runtime**: Reflection becomes impossible without embedding metadata
3. **No BCL**: The Base Class Library is unavailable; alternative implementations are required
4. **Direct hardware access**: The program can interact with memory-mapped peripherals

The question Clef answers is this: can we retain F#'s expressive type system and functional programming model while targeting this runtime-free environment? In our case, for the purposes of Clef, this is exactly our *opportunity*.

This is no small task. There are many considerations to account for, not simply for the presumed OS-based world of Windows, macOS, and Linux. There are memory mapping concerns around GPU, NPU, and other accelerators that are just as much a target for the Fidelity framework. Simply considering the constrained environment of microcontrollers, there are specific patterns that are allowed and others that would not work at all. These are all concerns that Clef has to account for and allow in order for the full range of options to be available to realize the platform's vision.

### 2.2 The OCaml Precedent

F# descends from the ML family of languages, sharing ancestry with OCaml and Standard ML. OCaml compiles natively without requiring a managed runtime, yet it offers many of the same programming constructs: algebraic data types, pattern matching, type inference, and higher-order functions.

The F* programming language, developed for verified systems programming, extracts to OCaml with high fidelity. Each F* type has a precise OCaml representation, and the extraction preserves type safety without requiring a runtime. This precedent demonstrates that ML-family languages can target native code while preserving their essential character. F* also provides the HyperStack memory model that again corresponds to what we arrived at for Clef's region system; the correspondence was discovered, not copied.

Clef found accidental sympathy in this path. Despite using F# syntax, it was found after some hand-jamming native types into Alloy that what would become Clef semantics align more closely with OCaml than with .NET F#. To give credit where it is due, FSharp.Core already contained some primitive types that proved essential: the `voption` type existed beyond the standard `option` type's null representation, and `NativeInterop.nativeptr` remained central to much of what we accomplished before making the "full break" to create Clef:

| Concept | .NET F# | OCaml | Clef |
|---------|---------|-------|-----------|
| String encoding | UTF-16 | UTF-8 | UTF-8 |
| Option representation | Reference type, None is null | Value type | Value type (voption) |
| Default record layout | Heap allocated | Value possible | Struct by default |
| Memory management | Garbage collection | GC or manual | RAII, arena, or static |
| Type metadata at runtime | Full reflection | Limited | None |

### 2.3 The Native Type Universe

Clef replaces BCL types with native equivalents from the Alloy library:

```fsharp
// In standard F#, this is System.String (UTF-16, heap-allocated)
let greeting = "Hello"

// In Clef, same syntax, native semantics (UTF-8 `memref<?xi8>` view)
let greeting = "Hello"  // Type: string (native semantics)
```

In Clef, `string` has native semantics - internally a `memref<?xi8>` view over UTF-8 bytes: a base index into the buffer and an extent, no pointer:

```fsharp
// Internal representation of string in CCS
// (Users just write "string" - this is transparent)
// string ≡ memref<?xi8>: the buffer is the string and its length is the memref's
// dimension. There is no fat-pointer struct and no raw pointer.
```

This representation differs fundamentally from `System.String`:

1. **No heap allocation required**: The data can reside on the stack, in an arena, or in static memory
2. **UTF-8 encoding**: The native string format for most operating systems and network protocols
3. **Known length**: No null terminator scanning; O(1) length access
4. **No null state**: A zero-length string is empty, not null

Similar transformations apply to other types:

| F# Syntax | Standard F# | Clef |
|-----------|-------------|-----------|
| `int option` | `option<int>` (heap, nullable) | `option<int>` with value semantics (voption) |
| `int[]` | `System.Int32[]` (heap, GC tracked) | `array<int>` with native semantics (a `memref<?xT>` view) |
| Records without `[<Struct>]` | Heap allocated | Struct by default |

### 2.4 The CCS Transformation

Clef Compiler Service (CCS) is a fork of the standard F# compiler that performs type resolution against the native type universe rather than the BCL. When CCS encounters:

```fsharp
let numbers = [| 1; 2; 3 |]
```

It resolves `array<int>` with native semantics (a `memref<?xT>` view) rather than `System.Int32[]` (heap, GC tracked). The syntax is identical; the semantics differ.

This transformation is systematic. CCS does not attempt to translate BCL code to native equivalents at runtime. Instead, it establishes a parallel type universe where native types are the primitive types, and BCL types do not exist.

The path to CCS itself illustrates the engineering-driven nature of this work. The original approach attempted to intercept type resolution at the Baker phase in Composer, substituting native types for BCL types after the fact. This proved fragile; the type system assumptions of the standard compiler leaked through in unexpected ways. The realization that a cleaner approach required modifying type resolution at its source, in the compiler services themselves, came from debugging these failures rather than from architectural foresight. Sometimes the right abstraction reveals itself only after the wrong ones have been tried.

Arriving at a generalized pattern for memory layout that adheres to the goals of the Fidelity framework while providing maximum degrees of freedom to target different processors is going to be a non-trivial challenge. We expect to start with some relatively straightforward hard-coded patterns and develop a proper abstraction pattern later. Our sense is that a plug-in system will need to be developed that will have some coupling to project-level declaration of the targeted hardware, but that story has yet to develop at this early stage. We are willing to live with some brittle implementations to help us target early wins and avoid over-engineering in the abstract.

### 2.5 Reducing the Compiler's Surface Area

The transformation from FCS to CCS involves systematic removal of .NET assembly import machinery. This work reveals an important insight about compiler architecture: what appears to be foundational infrastructure is often unnecessary indirection.

Consider `ImportMap`, a type that permeated the standard F# compiler with 268 uses across the codebase. Its stated purpose was "converting AbstractIL .NET and provided types to F# internal compiler data structures." The type held two things:

1. **`TcGlobals`**: The compiler's global type-checking context
2. **`AssemblyLoader`**: Infrastructure for loading .NET assemblies

For native compilation, the second capability is unnecessary - CCS reads F# source directly, not .NET assemblies. But the pervasive use of `ImportMap` obscured this fact. Functions throughout the compiler accepted `amap: ImportMap` as a parameter, even when they only needed access to `TcGlobals` via `amap.g`.

The principled approach is not to create a "native-friendly" `ImportMap` wrapper that preserves the interface while gutting the implementation. That would preserve unnecessary abstraction. Instead, CCS removes `ImportMap` entirely and refactors all 268 call sites to use `TcGlobals` directly:

- ~96 functions took only `amap` → now take `g: TcGlobals`
- ~172 functions took both `g` and `amap` → redundant `amap` parameter removed

This refactoring illustrates a broader principle: **when building a native type universe, question every abstraction that exists to bridge managed and native worlds**. If the bridge is no longer needed, remove it entirely rather than hollowing it out.

The same principle applies to other "IL" prefixed machinery in the compiler. Some of it (like `import.fs` - "Functions to import .NET binary metadata") is pure BCL cruft that should be deleted. But some infrastructure that happens to be named "IL*" represents useful type metadata concepts - method signatures, parameter info, type hierarchy operations - that native compilation still needs. The key distinction:

- **Does it read from .NET assemblies?** → DELETE
- **Does it represent type structure that F# source also has?** → RENAME/CONVERT for native type universe

The errors from deleting BCL import machinery serve as a roadmap. Each missing type or function points to more machinery that either needs removal (if it's pure import cruft) or conversion (if it's useful infrastructure with the wrong name).

### 2.6 The IL Dependency Cone

Following the cascade deletion to its conclusion reveals a startling fact: the IL import assumption is not a surface-level concern but permeates the entire type-checking layer of the F# compiler.

Starting from `import.fs` ("Functions to import .NET binary metadata"), the cascade removed:

| Layer | Files | Purpose |
|-------|-------|---------|
| Import | import.fs, infos.fs | IL type importing, member info unification |
| Hierarchy | TypeHierarchy.fs | Type hierarchy via ImportMap |
| Access | AccessibilityLogic.fs, InfoReader.fs | Accessibility checking on unified members |
| Relations | TypeRelations.fs, AttributeChecking.fs | Type subsumption, attribute checking |
| Display | NicePrint.fs | Pretty printing via unified members |
| Resolution | NameResolution.fs, MethodCalls.fs | Name and method resolution |
| Inference | ConstraintSolver.fs | **Core type inference** |
| Checking | CheckExpressions.fs, CheckDeclarations.fs, etc. | **Entire type-checking layer** |

**Total: 3.2MB across 59 files** - essentially the compiler's entire middle-end.

This reveals that the F# compiler was architecturally designed around the assumption that types come from two sources: F# source files and .NET assemblies. The `ImportMap` and `MethInfo`/`PropInfo`/`EventInfo` types exist to provide a unified abstraction over both sources. Every downstream consumer depends on this abstraction.

For native compilation, where types come only from F# source, this unification layer is pure indirection. But removing it doesn't leave a functioning compiler - it leaves a compiler with no type checker.

**The implication is significant**: CCS cannot be created by pruning the existing F# compiler. The type-checking layer must be rebuilt for the native type universe - a type checker that operates directly on F# types without the "types might come from IL" assumption baked into every function signature.

This is not a failure of the cascade deletion approach - it's the approach working correctly. By systematically removing indirection, we've identified exactly what needs to be rebuilt: a type checker for native F#.

## Part III: Memory as a First-Class Concern

### 3.1 The Memory Region Model

In managed environments, memory location is an implementation detail hidden from the programmer. The garbage collector may move objects during compaction, and the program remains unaware. In native compilation, memory location matters.

Clef introduces a memory region model that makes location explicit:

```fsharp
// Region type measures
[<Measure>] type peripheral   // Memory-mapped hardware registers
[<Measure>] type sram         // General-purpose RAM
[<Measure>] type flash        // Read-only storage
[<Measure>] type arena        // Compiler-managed temporary allocation
[<Measure>] type stack        // Function-scoped storage
```

These regions carry different semantics:

1. **Peripheral**: Volatile access required; reads cannot be optimized away
2. **SRAM**: Standard memory with caching
3. **Flash**: Read-only at runtime; write attempts are errors
4. **Arena**: Scoped allocation with bulk deallocation
5. **Stack**: Automatic deallocation on function return

### 3.2 Phantom Type Parameters

The region model uses F# units of measure as phantom type parameters. A phantom type parameter exists at compile time but carries no runtime representation:

```fsharp
type Ptr<'T, [<Measure>] 'region, [<Measure>] 'access> =
    struct
        val Address: unativeint
    end
```

The `'region` and `'access` parameters are measures, not concrete types. They exist purely to constrain how the pointer can be used:

```fsharp
// A pointer to a peripheral register, read-only
let statusReg: Ptr<uint32, peripheral, readOnly> = ...

// A pointer to SRAM, read-write
let buffer: Ptr<byte, sram, readWrite> = ...

// This is a compile error: cannot pass sram pointer where peripheral is expected
readPeripheral statusReg  // OK
readPeripheral buffer     // Error CCS8100: Region mismatch
```

The runtime representation of both pointers is identical: a single machine word containing an address. The type parameters carry semantic information that the compiler uses for safety checking but that vanishes in the generated code.

### 3.3 The HyperStack Pattern

The memory region model draws inspiration from F*'s HyperStack, a region-based memory model with compile-time verification. In HyperStack, memory regions form a tree structure:

```
                Static (Global)
                      |
            +---------+---------+
            |                   |
         Heap                 Stack
            |                   |
      +-----+-----+       +-----+-----+
      |           |       |           |
   Arena1     Arena2   Frame1     Frame2
```

Each region has a parent, and the key invariant is this: a pointer to a region is valid only as long as that region exists. Stack frames are automatically deallocated on function return; arenas are deallocated when their scope ends; heap regions persist until explicitly freed.

Clef adopts this pattern. Region containment is verified at compile time, not enforced at runtime. If the compiler can prove that a pointer cannot escape its region, the code is accepted. If it cannot prove this, the code is rejected.

### 3.4 Access Kind Enforcement

Beyond region, pointers carry access permissions:

```fsharp
[<Measure>] type readOnly
[<Measure>] type writeOnly
[<Measure>] type readWrite
```

These correspond to the CMSIS-standard volatile qualifiers used in embedded systems:

| CMSIS Qualifier | C Definition | Clef |
|-----------------|--------------|-----------|
| `__I` | `volatile const` | `readOnly` |
| `__O` | `volatile` | `writeOnly` |
| `__IO` | `volatile` | `readWrite` |

Access enforcement is compile-time:

```fsharp
let inputReg: Ptr<uint32, peripheral, readOnly> = ...
let outputReg: Ptr<uint32, peripheral, writeOnly> = ...

// OK: reading a read-only register
let status = Ptr.read inputReg

// Error CCS8020: Cannot write to ReadOnly pointer
Ptr.write inputReg 42u

// Error CCS8021: Cannot read from WriteOnly pointer
let value = Ptr.read outputReg

// OK: writing a write-only register
Ptr.write outputReg 42u
```

### 3.5 Zero Runtime Overhead

The critical property of this memory model is zero runtime overhead. Region parameters and access kinds exist only at compile time. The generated machine code contains no runtime checks, no metadata, and no enforcement logic. Safety is established during compilation, and the binary runs without any memory management infrastructure.

This property aligns with F*'s approach: the HyperStack model is a compile-time concept that produces flat runtime memory. The verification happens before execution; execution itself is unencumbered.

## Part IV: Rethinking Type Resolution

### 4.1 SRTP in the Native Context

Statically Resolved Type Parameters (SRTPs) are F#'s mechanism for ad-hoc polymorphism without runtime overhead. In standard F#, SRTP resolution searches .NET method tables:

```fsharp
let inline add (a: ^T) (b: ^T) : ^T
    when ^T : (static member (+) : ^T * ^T -> ^T) =
    a + b

// When called with int, resolves to System.Int32.op_Addition
let result = add 1 2
```

In Clef, there is no `System.Int32`. SRTP resolution must search elsewhere. CCS resolves against the Alloy witness hierarchy:

1. The concrete type's own members
2. `BasicOps` for primitive operations
3. `NumericOps` for numeric operations
4. `CollectionOps` for collection operations
5. `ComparableOps` for comparison operations

The same `add` function resolves differently:

```fsharp
// Clef resolution for `add 1 2`:
// 1. Look for Alloy.Int32 members - not found
// 2. Look in BasicOps - found: BasicOps.Add<int>
// 3. Resolved witness: BasicOps, method: Add
```

### 4.2 Operator Resolution

Alloy defines operators that do not exist in the BCL. The `$` operator, for example, provides efficient string operations:

```fsharp
type WritableString =
    static member inline ($) (ws: WritableString, s: string) : unit = ...

// Usage
WritableString $ "Hello"
```

CCS resolves this through SRTP:

1. Identify the trait call for `op_Dollar`
2. Search `WritableString` members
3. Find `WritableString.op_Dollar`
4. Capture resolution metadata: witness type, method, coeffects

This resolution metadata flows into the Program Semantic Graph (PSG), where subsequent compilation phases use it for code generation.

### 4.3 Resolution Metadata

Clef SRTP resolution captures richer metadata than standard F#:

```fsharp
type SRTPResolution = {
    WitnessType: FidType       // The type providing the implementation
    Method: string             // The method name
    Coeffect: Coeffect         // Effect classification (Pure, IO, etc.)
    OwnershipTransfer: bool    // Does this consume arguments?
    MemoryLayout: LayoutInfo   // Size and alignment information
}
```

This metadata enables the compiler to make informed decisions about code generation, including whether to inline, how to allocate memory, and what calling conventions to use.

## Part V: Platform Bindings Without the BCL

### 5.1 The DllImport Problem

In standard F#, platform interop uses `DllImportAttribute`:

```fsharp
[<DllImport("kernel32.dll")>]
extern bool WriteFile(nativeint hFile, byte[] buffer, uint32 numBytes, uint32& written, nativeint overlapped)
```

This approach depends on the BCL:

1. `DllImportAttribute` is in `System.Runtime.InteropServices`
2. The marshaling layer expects BCL types
3. Exception handling assumes the CLR is present

Clef uses declared platform intrinsics and generated binding contracts, as
specified below.

### 5.2 Intrinsics and Declared Bindings

The [platform-binding specification](../../../clef-lang-spec/spec/platform-bindings.md)
defines three layers: CCS intrinsics, binding libraries and application code.
`Sys` operations are recognized intrinsics. External library bindings carry
declared layout, ownership, access and calling-convention information, generated
by Farscape and read structurally by CCS. The former `Platform.Bindings` module
convention and `Unchecked.defaultof` stubs are deprecated; they do not define the
current binding contract.

Source operations use bounded arrays, width-typed `Mmio` handles and opaque
`CHandle<'T>` values where the external contract requires them. A buffer's extent
remains part of the compiler's evidence. Source code does not extract a raw
pointer from that buffer to perform a platform operation.

### 5.3 Platform-Specific Implementation

Declared platform facts participate in CCS saturation. Alex witnesses the settled
operations for the selected target pathway; it does not invent their memory or
lifetime premises. The platform-binding specification describes target
realizations such as:

| Binding | Linux x86_64 | macOS arm64 | Windows x86_64 |
|---------|--------------|-------------|----------------|
| `Sys.write` | syscall 1 (write) | `svc #0x80`, `x16=4` | WriteFile |
| `Sys.read` | syscall 0 (read) | `svc #0x80`, `x16=3` | ReadFile |

These are specified target realizations, not a claim that every target is
implemented. A target that cannot realize a reached operation requires a
diagnostic, as specified by the platform-binding contract.

### 5.4 Binding Contracts and Deterministic Memory

Platform bindings remain subject to Clef's memory, lifetime, access and extent
judgments. BAREWire supplies the structured memory and representation contracts;
Fidelity.Platform supplies declared target facts. CCS carries their relationships
and applicable proof obligations on the PSG and settles them before Alex
witnesses the operation.

Crossing a platform boundary does not suspend those judgments. External handles,
buffer views, ownership transfer and callback lifetimes must satisfy their
declared contracts. Missing evidence is an admission or implementation gap to
resolve, never a permission for a caller to waive the requirement. See
[Behavior Classification](../../../clef-lang-spec/spec/behavior-classification.md),
[FFI Boundary](../../../clef-lang-spec/spec/ffi-boundary.md) and
[Obligation Residency](../../../Composer/docs/Obligation_Residency_Design.md).

### 5.5 Native Library Integration

One of the major areas of interest is how to expand a "native library system" for the Fidelity framework that can preserve all of the advantages of its operating mechanics. Many .NET libraries that "wrap" low-level C and C++ libraries offered some insight, so we are starting with a clean approach through our "Farscape" binding generator. This requires "hooks" to integrate F# wrappers into the library system of the Fidelity framework, and that means integrating those primitives into the pipeline in a way that native F# function wrappers can provide safe harbor for their integration, either as dynamic syscall external references or as pipelined targets for static binding in the LLVM LTO layer of compilation.

C and C++ provide the low-level hardware access patterns that systems programming requires. Clef incorporates CMSIS conventions for volatile qualifiers, structure layout control through `[<Struct>]` with packing and alignment, explicit type-safe pointer operations, and reserves space for inline assembly where platform-specific optimization demands it. All of this is documented while maintaining F#'s type safety guarantees.

## Part VI: Coeffects and Proof Obligations

### 6.1 What Are Coeffects?

The PSG carries compiler-established facts, constraints and coeffects.
Dimension judgments belong to the type and group discipline; ranges propagate
as codata; region and access use their own equality sorts. Representation
choices, lifetime classification, target reachability and binding resolution
retain their corresponding judgments and provenance. Their definitions belong
to the corresponding Clef specifications, indexed by
[Program Semantic Graph §14](../../../clef-lang-spec/spec/program-semantic-graph.md).

### 6.2 Inference and Provenance

CCS derives program facts from the source graph and declared contracts. The
facts retain the identities of their participating nodes, their premises and
their declaration provenance. Platform facts come from the selected platform
description. Width, representation, lifetime and target reachability constraints
are resolved together as specified by
[Width Inference](../../../clef-lang-spec/spec/width-inference.md).

### 6.3 Composition and Preservation

Function application and elaboration retain the relationships needed to apply
the relevant judgments to the actual arguments, results, captures and storage.
For supported rules, the compiler derives and dispatches the applicable
obligations; the application does not restate them as proof annotations.

Alex reads the settled consequences. Lowering must preserve required properties
or re-check them at transformations that could change them. Evidence must remain
attached to its checked participants, premises and target context. These are the
[conformance requirements](../../../clef-lang-spec/spec/conformance.md), not
optional source annotations.

### 6.4 Obligations at Platform Operations

Coeffects record the requirements and consequences of an operation. They do not
authorize exceptions to Clef's judgments. A platform call retains the applicable
buffer bounds, access permissions, residence, lifetime and release obligations,
including when reached through a higher-order function or computation expression.

Those obligations refer to the participating program and declaration nodes in
the PSG. Their consequences are carried to witnesses as settled graph facts.
Deterministic memory management remains part of the operation's contract at
every call site.

## Part VII: Memory Management Strategies

### 7.1 Stack Allocation

The default memory strategy in Clef is stack allocation. Value types live on the stack automatically:

```fsharp
let point = { X = 1.0; Y = 2.0 }  // Stack allocated
let buffer = Array.stackalloc<byte> 1024  // Stack allocated
```

Stack allocation requires no explicit management. Memory is automatically reclaimed when the function returns. The compiler verifies that stack-allocated values do not escape their scope.

### 7.2 Arena Allocation

An arena provides region-bounded storage with bulk release. Placement and every
use must satisfy the region's lifetime and capacity contracts. The
[Memory Regions specification](../../../clef-lang-spec/spec/memory-regions.md)
marks an arena computation expression as future work; that proposed syntax is
not evidence of an available source construct.

### 7.3 Static Allocation

Program-lifetime storage is a placement class in the
[closure and lifetime contract](../../../clef-lang-spec/spec/closure-representation.md).
The selected platform declares suitable storage; CCS settles placement and its
obligations on the graph. This placement rule does not imply a separate static
computation-expression syntax.

### 7.4 Lifetime Verification

Lifetime verification is carried on the PSG. Escape classification determines a
value's placement in the lifetime lattice; region and use relationships carry
the applicable ordering obligations. The
[Memory Regions specification](../../../clef-lang-spec/spec/memory-regions.md)
defines this as coeffect and obligation discipline, with no source ownership or
borrowing annotation vocabulary planned. Deterministic release is part of that
contract.

## Part VIII: The RAII Pattern

### 8.1 Resource Acquisition Is Initialization

RAII is a pattern from C++ where resources are tied to object lifetimes. When an object is created, it acquires resources; when the object is destroyed, it releases them.

Clef extends this pattern through its use expressions and computation expressions:

```fsharp
let processFile path =
    use file = File.openRead path  // Acquire
    let content = file.ReadAll()
    process content
    // File automatically closed on scope exit (Release)
```

### 8.2 RAII and Actors

The Olivier actor model integrates with RAII at the actor level. Each actor owns an arena, and when the actor terminates, its arena is freed:

```fsharp
type DataProcessor() =
    inherit Actor<DataMessage>()

    // Actor's arena is created at spawn
    let cache = Map.empty<string, ProcessedData>

    override this.Receive message =
        match message with
        | Process data ->
            let result = performComplexProcessing data
            cache <- Map.add data.Id result cache
        | Retrieve id ->
            Map.tryFind id cache |> ReplyChannel.send

    // No disposal code needed:
    // Arena is freed when actor terminates
```

This integration eliminates the need for explicit cleanup code in most cases. The actor lifecycle defines the memory lifecycle.

### 8.3 Deterministic Cleanup

Unlike garbage collection, RAII provides deterministic cleanup. Resources are released at predictable points:

1. **Scope exit**: `use` bindings release on scope exit
2. **Arena exit**: Arena contents are freed on arena exit
3. **Actor termination**: Actor arenas are freed on actor shutdown

This predictability is essential for systems programming, where resource lifetimes affect correctness, not just performance.

## Part IX: Verification Through F*

### 9.1 The F* Connection

F* is a verification-oriented programming language that can prove properties about programs. Clef integrates with F* for design-time verification of memory properties. Key F* concepts that Clef respects and in certain cases adopts include region identifiers as phantom type parameters, containment hierarchies with tree structures of stack frames and heap regions, preorders constraining how values in regions may evolve, and witnessed predicates tracking resource availability across code boundaries.

This correspondence will continue to develop as Fidelity's continuation patterns with actors and arenas begins to become a more coherent part of the framework.

### 9.2 Decidable Properties

Certain properties of Clef types are decidable, meaning they can be verified automatically:

| Property | Verification Method |
|----------|---------------------|
| Size | Structural recursion on type definition |
| Alignment | Maximum of field alignments |
| Field offsets | Cumulative size with alignment padding |
| Region membership | Type parameter unification |
| Stack containment | Scope nesting analysis |

For these properties, the compiler can verify correctness without user intervention.

### 9.3 Proof-Carrying Types

Alloy types can carry F* specifications that the compiler verifies:

```fstar
module Alloy.String.Spec

// Layout invariants (string has native UTF-8 `memref<?xi8>` view semantics)
val sizeof_string: unit -> Lemma (sizeof string == 16)
val alignof_string: unit -> Lemma (alignof string == 8)

// Region invariant
val string_ptr_readable:
    s: string ->
    Lemma (is_readable (region_of s.ptr))

// Lifetime invariant
val string_ptr_outlives:
    s: string ->
    Lemma (lifetime s.ptr >= lifetime s)
```

These specifications are verified once, at design time. The verified properties then guide compilation without runtime overhead.

### 9.4 Proof-Aware Optimization

Proofs enable rather than hinder optimization. When the compiler knows that bounds checks always succeed, it can eliminate them. When it knows that values never alias, it can reorder operations freely.

The hypergraph representation in Composer carries proof obligations as edges, allowing the optimization passes to reason about what transformations preserve correctness.

## Part X: Migration Path

### 10.1 Recognizing BCL Dependencies

The first step in migrating to Clef is identifying BCL dependencies:

```fsharp
// BCL dependency: explicit System.String
let name: System.String = "Alice"

// BCL dependency: System.Collections.Generic
let items = System.Collections.Generic.List<int>()

// BCL dependency: System.IO
let content = System.IO.File.ReadAllText("config.json")
```

These explicit BCL references will not compile under CCS. They must be replaced with Alloy equivalents or removed.

### 10.2 Implicit BCL Usage

Many BCL dependencies are implicit:

```fsharp
// Implicit: string is System.String in standard F#
let greeting = "Hello"

// Implicit: array is System.Array
let numbers = [| 1; 2; 3 |]

// Implicit: List<T> is FSharp.Collections.FSharpList
let items = [ 1; 2; 3 ]
```

These will compile under CCS with native semantics. The `string` greeting has UTF-8 `memref<?xi8>` view semantics, the `array<int>` has native array semantics, and the `list<int>` has native list semantics - but users write standard F# type names throughout.

### 10.3 Semantic Differences to Consider

The migration requires awareness of semantic differences:

1. **String encoding**: UTF-16 to UTF-8; some characters change length
2. **Null handling**: None is no longer null; null comparisons are errors
3. **Memory location**: Data may be on stack rather than heap
4. **Thread safety**: No synchronization block; explicit synchronization required

### 10.4 Incremental Migration

For large codebases, migration can proceed incrementally:

1. **Identify leaf modules**: Modules with no BCL dependencies in their public interface
2. **Migrate leaf modules first**: These can be compiled with CCS independently
3. **Abstract boundaries**: Define interfaces that work with both type systems
4. **Migrate incrementally**: Move modules from standard F# to Clef over time

## Conclusion

The transition from F# on .NET to Clef is a conceptual shift as much as a technical one. The managed runtime has abstracted away concerns that native compilation requires us to address: memory location, resource lifetimes, and the physical representation of types.

Clef does not abandon F#'s strengths. Pattern matching, type inference, algebraic data types, and functional composition all remain. What changes is the relationship between source code and execution: the abstractions become transparent, the runtime disappears, and the programmer gains direct control over the machine.

This control comes with responsibility. Memory regions must be respected. Lifetimes must be valid. Resources must be released. But these responsibilities are not new burdens; they are the reality of native programming that the managed runtime previously hid. Clef makes them visible and verifiable.

For the .NET developer willing to make this transition, Clef offers something valuable: the expressive power of F# applied directly to the hardware, without compromise and without a runtime standing between your code and its execution.

Perhaps the most important lesson from this journey is methodological. Clef was not designed in isolation from implementation. The type system emerged from the practical demands of making code compile and run correctly. The OCaml correspondence was discovered, not decreed. The memory region model arose from the need to distinguish peripheral registers from RAM, not from theoretical considerations about memory safety. This engineering-first approach, where theory follows practice rather than preceding it, may be uncomfortable for those who prefer clean derivations from first principles. But it has the virtue of grounding every abstraction in concrete necessity. What works, works because it had to work to solve a real problem.

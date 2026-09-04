# Clef Language Specification

## Overview

This document specifies the **Clef** dialect - extensions and modifications to standard F# semantics for native compilation via the Fidelity framework. Clef is implemented by CCS (Clef Compiler Service) and compiled to native binaries by Firefly.

**Relationship to Standard F#**: Clef is a superset of F# syntax with modified type semantics. Valid Clef code parses identically to standard F#, but type resolution follows native rules.

## Companion Documents

- `docs/CCS_Pruning_Plan.md` - Implementation plan for CCS
- `Firefly/docs/CCS_Architecture.md` - Integration with Firefly
- `fslang-spec/spec/*` - Standard F# specification (reference)

---

## Part 1: Native Type Universe

> **See also**: [`native-type-universe.md`](native-type-universe.md) for complete type specification with memory layouts.
>
> **Cross-references**:
> - Primitive types: `native-type-universe.md` Part 2
> - Structural types: `native-type-universe.md` Part 3
> - String/Array: `native-type-universe.md` Part 4
> - Option/Result: `native-type-universe.md` Part 5
> - Memory regions: `native-type-universe.md` Part 8
> - OCaml provenance: `native-type-universe.md` Appendix E

### 1.1 Primitive Type Mapping

CCS resolves types to native representations at compile-time. **No Alloy shadow types required.**

| F# Syntax | Standard F# (BCL) | CCS Native | Memory |
|-----------|-------------------|-------------|--------|
| `int` | `System.Int32` | Platform word | `index` (MLIR) |
| `int32` | `System.Int32` | 32-bit signed | `i32` |
| `int64` | `System.Int64` | 64-bit signed | `i64` |
| `float` | `System.Double` | IEEE 754 double | `f64` |
| `float32` | `System.Single` | IEEE 754 single | `f32` |
| `string` | `System.String` | UTF-8 fat pointer | `{ptr, len}` |
| `char` | `System.Char` | Unicode codepoint | `i32` |
| `bool` | `System.Boolean` | 8-bit | `i8` |
| `unit` | `FSharp.Core.Unit` | Zero-sized | (elided) |
| `byte` | `System.Byte` | 8-bit unsigned | `i8` |
| `option<'T>` | `FSharp.Core.Option<'T>` | `voption<'T>` | Stack-allocated |

**Key principle**: CCS provides native type resolution at the compiler level. Alloy shadow types (e.g., `type option<'T> = voption<'T>`) are temporary workarounds that will be removed once CCS is complete.

### 1.2 String Literals

> **See**: [`native-type-universe.md` Part 4.1](native-type-universe.md#41-string) for complete string specification.

**Standard F#**: String literals have type `System.String`.

**Clef**: String literals have type `string` (UTF-8 fat pointer, resolved by CCS).

```fsharp
// Clef semantics
let greeting = "Hello"  // Type: string (UTF-8 fat pointer, not System.String)
```

CCS resolves `string` to a UTF-8 fat pointer:

```
Memory layout:
┌─────────────┬─────────────┐
│ ptr: *u8    │ len: usize  │
└─────────────┴─────────────┘
     8 bytes      8 bytes     (on 64-bit)
```

**Implications**:
- No null strings (fat pointer is always valid or zero-length)
- UTF-8 encoding (not UTF-16)
- Known length (no null terminator scanning)
- Stack or arena allocated (no GC)

### 1.3 Option Types

> **See**: [`native-type-universe.md` Part 5.1](native-type-universe.md#51-option) for complete option specification.

**Standard F#**: `option<'T>` is a reference type, `None` may be null.

**Clef**: `option<'T>` has `voption<'T>` semantics (stack-allocated value type).

```fsharp
// Clef semantics - user writes familiar syntax
let maybeValue: int option = Some 42  // Compiled as voption<int>
let nothing: int option = None        // Stack-allocated, NOT null
```

**Implications**:
- **Absolute null-freedom**: No null representation anywhere
- Stack allocated (no heap, no GC)
- Pattern matching works identically to standard F#
- CCS resolves at compile-time, no Alloy shadow required

### 1.4 Array Types

> **See**: [`native-type-universe.md` Part 4.2](native-type-universe.md#42-array) for complete array specification.

**Standard F#**: `'T[]` is `System.Array` (heap allocated, GC managed).

**Clef**: `array<'T>` is a fat pointer (pointer + length).

```fsharp
// Clef semantics - user writes familiar syntax
let numbers = [| 1; 2; 3 |]  // Type: array<int> (fat pointer)
```

```
Memory layout:
┌─────────────┬─────────────┐
│ ptr: *T     │ len: usize  │
└─────────────┴─────────────┘
```

**Implications**:
- Explicit memory management (stack, arena, or explicit allocation)
- No automatic resizing (fixed-size after creation)
- Bounds checking preserved

---

## Part 2: Null-Free Semantics

### 2.1 Null Prohibition

Clef enforces null-free semantics for ALL types:

```fsharp
// COMPILE ERROR in Clef
let s: string = null         // Error FS8010: Cannot assign null
let arr: int array = null    // Error FS8010: Cannot assign null
let opt: int option = null   // Error FS8010: Use None, not null
```

### 2.2 Interop Boundary

When interfacing with platform APIs that may return null:

```fsharp
// Platform binding returns nullable
[<PlatformBinding>]
let tryGetEnv (name: string) : string voption = ...

// Usage - must handle None case
match tryGetEnv "PATH" with
| ValueSome path -> use path
| ValueNone -> handle missing
```

### 2.3 Default Values

Native types have sensible defaults, not null:

| Type | Default |
|------|---------|
| `string` | Empty string (zero-length) |
| `array<'T>` | Empty array (zero-length) |
| `voption<'T>` | `ValueNone` |
| Numeric | `0` |
| `bool` | `false` |

---

## Part 3: SRTP Resolution

### 3.1 Witness Hierarchy

Standard F# SRTP resolves against .NET method tables. Clef SRTP resolves against the **Alloy witness hierarchy**.

**Alloy Witness Chain** (searched in order):
1. Concrete type's members
2. `BasicOps` (primitive operations)
3. `NumericOps` (numeric operations)
4. `CollectionOps` (collection operations)
5. `ComparableOps` (comparison operations)

### 3.2 Resolution Example

```fsharp
// SRTP constraint
let inline add (a: ^T) (b: ^T) : ^T
    when ^T : (static member (+) : ^T * ^T -> ^T) =
    a + b

// Standard F# resolution for `add 1 2`:
// 1. Look for System.Int32.op_Addition
// 2. Found in BCL

// Clef resolution for `add 1 2`:
// 1. CCS recognizes `int` as native platform word
// 2. Look in native BasicOps - found: Add<int>
// 3. Resolved witness: BasicOps, method: Add
```

### 3.3 Native Operator Resolution

Native operators like `$` for string operations:

```fsharp
// Alloy definition
type WritableString =
    static member inline ($) (ws: WritableString, s: string) : unit = ...

// Usage
WritableString $ "Hello"

// Clef resolution:
// 1. TraitCall for op_Dollar
// 2. Search WritableString members
// 3. Found: WritableString.op_Dollar
// 4. Resolution includes: witness type, method, coeffect
```

### 3.4 Resolution Metadata

Clef SRTP resolution captures additional metadata:

```fsharp
type SRTPResolution = {
    WitnessType: FidType       // e.g., BasicOps
    Method: string             // e.g., "Add"
    Coeffect: Coeffect         // e.g., Pure
    OwnershipTransfer: bool    // Does this consume arguments?
    MemoryLayout: LayoutInfo   // Alignment, size
}
```

This metadata flows to Firefly's PSG for code generation.

---

## Part 4: Memory Semantics

### 4.1 Stack Allocation

Clef defaults to stack allocation for value types:

```fsharp
let point = { X = 1.0; Y = 2.0 }  // Stack allocated
let numbers = [| 1; 2; 3 |]        // Stack allocated (small)
```

### 4.2 Arena Allocation (Future)

Large or dynamically-sized data uses arena allocation:

```fsharp
arena {
    let buffer = array.create 1_000_000  // Arena allocated
    let result = process buffer
    return result  // Only result escapes
}  // Arena freed here
```

### 4.3 Ownership Types (Future)

Clef will support ownership annotations:

```fsharp
// Owned value - caller receives ownership
let createBuffer () : Owned<array<byte>> = ...

// Borrowed reference - caller borrows, doesn't own
let processBuffer (buf: Borrowed<array<byte>>) : unit = ...

// Move semantics
let newOwner = move existingBuffer
```

---

## Part 5: Coeffects (Future)

### 5.1 Coeffect Annotations

Functions can declare their effects:

```fsharp
// Pure function - no side effects
let add (a: int) (b: int) : int -[Pure]-> int = a + b

// IO function - performs I/O
let readFile (path: string) : array<byte> -[IO.File]-> array<byte> = ...

// Composite coeffects
let fetchAndParse (url: string) : Data -[IO.Network, Async]-> Data = ...
```

### 5.2 Coeffect Inference

When not annotated, coeffects are inferred:

```fsharp
// Inferred: -[Pure]->
let double x = x * 2

// Inferred: -[IO.Console]->
let greet name = Console.WriteLine $"Hello, {name}"
```

### 5.3 Coeffect Compatibility

Callers must be compatible with callee coeffects:

```fsharp
let pureFunction () : int -[Pure]-> int =
    readFile "data.txt"  // ERROR: Pure cannot call IO.File
```

---

## Part 6: Platform Bindings

### 6.1 Binding Convention

Platform bindings use module convention (no DllImport):

```fsharp
module Platform.Bindings =
    let writeBytes (fd: int) (buf: array<byte, 'n, Stack>) (count: int) : int =
        Unchecked.defaultof<int>  // Placeholder - Alex provides implementation
```

### 6.2 Binding Resolution

Firefly's Alex layer provides platform-specific implementations:

| Binding | Linux x86_64 | macOS arm64 | Windows x86_64 |
|---------|--------------|-------------|----------------|
| `writeBytes` | syscall 1 (write) | syscall 0x2000004 | WriteFile |
| `readBytes` | syscall 0 (read) | syscall 0x2000003 | ReadFile |

### 6.3 Binding Safety

Platform bindings are unsafe by default:

```fsharp
// Caller must be in unsafe context or explicitly allow
let writeData (data: array<byte>) : unit -[IO, Unsafe]-> unit =
    Platform.Bindings.writeBytes 1 data.Ptr data.Length |> ignore
```

---

## Part 7: Compatibility

### 7.1 Syntax Compatibility

Clef accepts all valid F# syntax. These are identical:

```fsharp
// Valid in both F# and Clef
let rec factorial n =
    if n <= 1 then 1
    else n * factorial (n - 1)

type Person = { Name: string; Age: int }

let people =
    [ { Name = "Alice"; Age = 30 }
      { Name = "Bob"; Age = 25 } ]
    |> List.filter (fun p -> p.Age > 20)
```

### 7.2 Semantic Differences

The same syntax has different type semantics:

```fsharp
let s = "hello"
// F#: s : System.String
// Clef: s : string

let opt = Some 42
// F#: opt : int option (reference type, None = null)
// Clef: opt : int voption (value type, None = ValueNone)
```

### 7.3 Migration Path

Code targeting Clef should:
1. Avoid BCL type annotations (`System.String`, etc.)
2. Use Alloy library instead of FSharp.Core for collections
3. Handle option as value type
4. Be prepared for non-null semantics

---

## Part 8: Diagnostics

### 8.1 Native-Specific Errors

CCS produces native-specific error messages:

```
FS0001: This expression was expected to have type 'string'
        but here has type 'System.String'.

Hint: Clef uses string for string literals.
      If interoperating with .NET, use string.ofString.
```

```
FS0002: Cannot assign null to native type 'array<int>'.

Hint: Clef types are non-nullable.
      Use voption<T> for optional values.
```

### 8.2 SRTP Resolution Errors

```
FS0003: No witness found for trait constraint
        'static member (+) : MyType * MyType -> MyType'.

Searched witnesses:
  - MyType (no op_Addition member)
  - BasicOps (not applicable to MyType)

Hint: Implement op_Addition on MyType or add to witness hierarchy.
```

---

## Part 9: Memory Region Types and Semantics

> **See**: [`native-type-universe.md` Part 8](native-type-universe.md#part-8-memory-region-types-umx-absorption) for memory region type definitions and UMX absorption.

### 9.1 Memory Region Kinds

NORMATIVE: Clef defines a closed set of memory region kinds:

| Kind | Volatility | Cache Behavior | Use Case |
|------|------------|----------------|----------|
| `Peripheral` | Always volatile | No caching | Hardware registers (memory-mapped I/O) |
| `SRAM` | Non-volatile | Normal | General-purpose RAM |
| `Flash` | Non-volatile | Aggressive | Read-only storage |
| `SystemControl` | Always volatile | Special | ARM system registers |
| `Arena` | Non-volatile | Scope-bounded | Compiler-managed temporary allocation |
| `Stack` | Non-volatile | Core-local | Thread-local storage |

```fsharp
// CCS type definitions
type MemoryRegionKind =
    | Peripheral      // Memory-mapped I/O (volatile, no cache)
    | SRAM            // General RAM
    | Flash           // Read-only at runtime
    | SystemControl   // ARM system registers
    | Arena           // Compiler-managed temporary
    | Stack           // Thread-local
```

### 9.2 Region Type Parameters

NORMATIVE: Region information is carried via measure type parameters using FSharp.UMX phantom types:

```fsharp
[<Measure>] type peripheral
[<Measure>] type sram
[<Measure>] type flash
[<Measure>] type systemControl
[<Measure>] type arena
[<Measure>] type stack

type Ptr<'T, [<Measure>] 'region, [<Measure>] 'access>
```

NORMATIVE: Region parameters SHALL NOT be erased during type checking. The type checker must preserve region information through all transformations.

NORMATIVE: Region constraints propagate through function calls:

```fsharp
// Function accepting peripheral-region pointer
let readRegister (ptr: Ptr<uint32, peripheral, readOnly>) : uint32 = ...

// Attempting to pass wrong region is a type error
let sramPtr: Ptr<uint32, sram, readWrite> = ...
readRegister sramPtr  // ERROR FS8003: Memory region mismatch
```

### 9.3 Volatile Semantics

NORMATIVE: Access to `Peripheral` or `SystemControl` regions SHALL use volatile semantics.

NORMATIVE: Volatile reads SHALL NOT be reordered by the compiler or optimizer. The generated code must preserve the exact sequence of volatile operations.

NORMATIVE: Volatile reads SHALL NOT be eliminated. The compiler SHALL NOT remove "redundant" volatile reads, as hardware register values may change between reads.

NORMATIVE: Volatile writes SHALL NOT be reordered with respect to other volatile operations or memory barriers.

```fsharp
// Each read is a separate hardware access - NOT combined
let status1 = !peripheralPtr  // Volatile read
let status2 = !peripheralPtr  // Separate volatile read - NOT optimized away
```

### 9.4 Region Compatibility

NORMATIVE: Regions form a subtyping hierarchy for assignment:

```
                Stack
                  ↓
                Arena
                  ↓
                SRAM
               ↙   ↘
           Flash   Peripheral
                      ↓
                SystemControl
```

A pointer to a "higher" region can be used where a "lower" region is expected in read-only contexts, but not vice versa.

---

## Part 10: Access Kind Enforcement

### 10.1 Access Kinds

Clef enforces access kinds at the type level:

| Kind | Read | Write | Description |
|------|------|-------|-------------|
| `ReadOnly` | YES | NO | Read-only access (immutable view) |
| `WriteOnly` | NO | YES | Write-only access (output registers) |
| `ReadWrite` | YES | YES | Full access |

```fsharp
[<Measure>] type readOnly
[<Measure>] type writeOnly
[<Measure>] type readWrite
```

### 10.2 Enforcement Rules

NORMATIVE: Reading from a `WriteOnly` pointer SHALL produce error FS8001.

```fsharp
let outputPtr: Ptr<uint32, peripheral, writeOnly> = ...
let value = !outputPtr  // ERROR FS8001: Cannot read write-only pointer
```

NORMATIVE: Writing to a `ReadOnly` pointer SHALL produce error FS8002.

```fsharp
let inputPtr: Ptr<uint32, flash, readOnly> = ...
inputPtr := 42u  // ERROR FS8002: Cannot write read-only pointer
```

NORMATIVE: Access kinds are checked at compile time. No runtime overhead is incurred for access enforcement.

### 10.3 CMSIS Qualifier Mapping

Clef access kinds map directly to CMSIS-standard volatile qualifiers:

| CMSIS Qualifier | C Definition | Clef |
|-----------------|--------------|-----------|
| `__I` | `volatile const` | `readOnly` |
| `__O` | `volatile` | `writeOnly` |
| `__IO` | `volatile` | `readWrite` |

This mapping enables Farscape to generate type-safe F# bindings from CMSIS-SVD device descriptions.

### 10.4 Access Covariance and Contravariance

NORMATIVE: `ReadWrite` is a subtype of both `ReadOnly` and `WriteOnly`:

```fsharp
let rwPtr: Ptr<uint32, sram, readWrite> = ...

// OK: ReadWrite can be used where ReadOnly is expected
let readValue (p: Ptr<uint32, sram, readOnly>) = !p
readValue rwPtr  // OK

// OK: ReadWrite can be used where WriteOnly is expected
let writeValue (p: Ptr<uint32, sram, writeOnly>) v = p := v
writeValue rwPtr 42u  // OK
```

---

## Part 11: Peripheral Descriptors and Binding Markers

### 11.1 Platform Bindings Convention

NORMATIVE: Platform bindings SHALL be declared in `Platform.Bindings` modules:

```fsharp
module Platform.Bindings =
    let writeBytes (fd: int) (buffer: array<byte, 'n, Stack>) (count: int) : int =
        Unchecked.defaultof<int>
    let readBytes (fd: int) (buffer: array<byte, 'n, Stack>) (maxCount: int) : int =
        Unchecked.defaultof<int>
    let getCurrentTicks () : int64 =
        Unchecked.defaultof<int64>
    let sleep (milliseconds: int) : unit =
        ()
```

NORMATIVE: Function body SHALL be `Unchecked.defaultof<T>` (for non-unit return) or `()` (for unit return) to indicate Alex-provided implementation.

NORMATIVE: Alex SHALL recognize these binding markers and replace them with platform-specific implementations during code generation.

### 11.2 Peripheral Attributes

NORMATIVE: CCS SHALL recognize these Farscape-generated attributes on peripheral descriptor types:

```fsharp
[<AttributeUsage(AttributeTargets.Class ||| AttributeTargets.Struct)>]
type PeripheralDescriptorAttribute(family: string, baseAddress: uint64) =
    inherit Attribute()
    member _.Family = family
    member _.BaseAddress = baseAddress

[<AttributeUsage(AttributeTargets.Field ||| AttributeTargets.Property)>]
type RegisterAttribute(name: string, offset: uint32, access: string) =
    inherit Attribute()
    member _.Name = name
    member _.Offset = offset
    member _.Access = access  // "r", "w", "rw"

[<AttributeUsage(AttributeTargets.Field ||| AttributeTargets.Property)>]
type PeripheralAttribute(instance: string, address: uint64) =
    inherit Attribute()
    member _.Instance = instance
    member _.Address = address
```

**Example Farscape-generated peripheral:**

```fsharp
[<PeripheralDescriptor("GPIO", 0x48000000UL)>]
type GPIO_TypeDef = {
    [<Register("MODER", 0x00u, "rw")>]
    MODER: Ptr<uint32, peripheral, readWrite>

    [<Register("IDR", 0x10u, "r")>]
    IDR: Ptr<uint32, peripheral, readOnly>

    [<Register("ODR", 0x14u, "rw")>]
    ODR: Ptr<uint32, peripheral, readWrite>

    [<Register("BSRR", 0x18u, "w")>]
    BSRR: Ptr<uint32, peripheral, writeOnly>
}

[<Peripheral("GPIOA", 0x48000000UL)>]
let GPIOA: GPIO_TypeDef = Unchecked.defaultof<GPIO_TypeDef>

[<Peripheral("GPIOB", 0x48000400UL)>]
let GPIOB: GPIO_TypeDef = Unchecked.defaultof<GPIO_TypeDef>
```

### 11.3 Units of Measure Preservation

NORMATIVE: Units of measure SHALL be preserved through memory operations:

```fsharp
[<Measure>] type bytes
[<Measure>] type offset
[<Measure>] type address

let bufferSize: int<bytes> = 1024<bytes>
let registerOffset: int<offset> = 0x10<offset>

// Type error - cannot add incompatible units
let invalid = bufferSize + registerOffset  // ERROR: int<bytes> + int<offset>

// Explicit conversion required
let total = bufferSize + int<bytes> registerOffset  // OK with explicit cast
```

NORMATIVE: Measure types integrate with memory region types:

```fsharp
type SizedPtr<'T, [<Measure>] 'region, [<Measure>] 'access, [<Measure>] 'unit> =
    Ptr<'T, 'region, 'access>

let buffer: SizedPtr<byte, sram, readWrite, bytes> = ...
```

### 11.4 BAREWire Schema Integration

NORMATIVE: BAREWire memory layouts integrate with Clef types through struct layout attributes:

```fsharp
[<Struct; StructLayout(LayoutKind.Sequential, Pack = 1)>]
type MessageHeader = {
    Version: uint8
    Type: uint8
    Length: uint16<bytes>
    Sequence: uint32
}

// BAREWire-compatible zero-copy deserialization
let parseHeader (ptr: Ptr<byte, sram, readOnly>) : MessageHeader =
    BAREWire.view<MessageHeader> ptr   // zero-copy: a typed view over the declared layout; access kind preserved
```

---

## Part 12: Ownership and Coeffects (FUTURE)

*This section reserves syntax and semantics for future implementation.*

### 12.1 Reserved Ownership Syntax

The following syntax is reserved for ownership semantics:

```fsharp
// Ownership wrappers
Owned<'T>      // Caller receives exclusive ownership
Borrowed<'T>   // Caller borrows, does not own
Shared<'T>     // Shared ownership (reference counted)

// Ownership expressions
move expr      // Transfer ownership
&expr          // Borrow immutably
&mut expr      // Borrow mutably
drop expr      // Explicit drop

// Arena expressions
arena { expr } // Arena-scoped allocation
```

### 12.2 Reserved Coeffect Syntax

The following syntax is reserved for coeffect annotations:

```fsharp
// Coeffect arrow
type -> type                    // Current syntax (no coeffect)
type -[coeffect]-> type         // Future: explicit coeffect

// Built-in coeffects
Pure           // No side effects
IO             // General I/O
IO.File        // File I/O specifically
IO.Network     // Network I/O specifically
IO.Console     // Console I/O specifically
Async          // Asynchronous operation
Unsafe         // Requires unsafe context
Alloc          // Performs allocation
```

### 12.3 Future Integration Points

The ownership and coeffect systems are designed to integrate with:

1. **Memory regions** - Ownership transfers preserve region information
2. **Access kinds** - Mutable borrows require `readWrite` access
3. **BAREWire** - Zero-copy IPC uses ownership transfer across process boundaries
4. **Farscape** - Peripheral access requires explicit coeffect declarations

---

## Part 12: SemanticGraph Traversal and SCF Regions

### 12.1 Overview

The SemanticGraph provides a traversal API that supports control flow construct compilation. For MLIR SCF (Structured Control Flow) dialect emission, downstream compilers need to capture operations within distinct regions (guard, body, then, else branches) of control flow constructs.

### 12.2 SCF Region Kinds

The `RegionKind` discriminated union identifies regions within control flow constructs:

```fsharp
type RegionKind =
    | GuardRegion      // Loop guard/condition
    | BodyRegion       // Loop body
    | ThenRegion       // If-then branch
    | ElseRegion       // If-else branch
    | StartExprRegion  // ForLoop start expression
    | EndExprRegion    // ForLoop end expression
```

### 12.3 SCF Region Hooks

The `SCFRegionHook<'State>` record provides callbacks for region boundary events:

```fsharp
type SCFRegionHook<'State> = {
    /// Called before entering a region's subtree
    /// Parameters: state, parentNodeId, regionKind
    BeforeRegion: 'State -> NodeId -> RegionKind -> 'State

    /// Called after exiting a region's subtree
    /// Parameters: state, parentNodeId, regionKind
    AfterRegion: 'State -> NodeId -> RegionKind -> 'State
}
```

**Design rationale**: Both `BeforeRegion` and `AfterRegion` receive the *parent* NodeId (e.g., the WhileLoop node), not the region's child NodeId. This enables the hook to look up the parent's structure to extract region-specific information (guard NodeId, body NodeId, etc.).

### 12.4 Extended Fold

The `foldWithSCFRegions` function extends the standard fold with SCF hooks:

```fsharp
let foldWithSCFRegions
    (preBind: 'State -> SemanticNode -> 'State)
    (scfHook: SCFRegionHook<'State> option)
    (folder: 'State -> SemanticNode -> 'State)
    (state: 'State)
    (graph: SemanticGraph) : 'State
```

For control flow nodes, the traversal calls hooks between child regions:

**WhileLoop (guardId, bodyId)**:
1. `BeforeRegion(state, parentId, GuardRegion)`
2. Walk guard subtree
3. `AfterRegion(state, parentId, GuardRegion)`
4. `BeforeRegion(state, parentId, BodyRegion)`
5. Walk body subtree
6. `AfterRegion(state, parentId, BodyRegion)`
7. Call `folder` on WhileLoop node (post-order)

**ForLoop (var, startId, endId, isUp, bodyId)**:
1. StartExprRegion hooks → walk start
2. EndExprRegion hooks → walk end
3. BodyRegion hooks → walk body
4. Call `folder` on ForLoop node

**IfThenElse (guardId, thenId, elseIdOpt)**:
1. Walk guard (no hooks - guard is just a boolean SSA value)
2. ThenRegion hooks → walk then
3. ElseRegion hooks → walk else (if present)
4. Call `folder` on IfThenElse node

### 12.5 MLIR SCF Dialect Integration

**Context**: The SCF dialect is a well-established MLIR dialect for structured control flow. Using SCF provides an interim solution while DCont (Delimited Continuations) and Inet (Interaction Nets) dialects are developed for the full Fidelity computation expression compilation strategy.

**SCF Operations**:
- `scf.while` - While loops with iter_args for mutable state
- `scf.for` - For loops with loop variable and optional iter_args
- `scf.if` - Conditionals with optional else branch and yield values

**iter_args Pattern**: Mutable variables modified within a loop must be passed as `iter_args` to maintain SSA form:

```mlir
// F# source:
let mutable count = 0
while count < 10 do
    count <- count + 1

// MLIR output:
%c0 = arith.constant 0 : i32
%result = scf.while (%count_arg = %c0) : (i32) -> (i32) {
    %c10 = arith.constant 10 : i32
    %cond = arith.cmpi slt, %count_arg, %c10 : i32
    scf.condition(%cond) %count_arg : i32
} do {
    %c1 = arith.constant 1 : i32
    %next = arith.addi %count_arg, %c1 : i32
    scf.yield %next : i32
}
```

**Analyze Then Witness Pattern**: The `BeforeRegion` hook for a loop's GuardRegion analyzes the body subtree to find Set nodes (mutable assignments), then pre-binds iter_args before body traversal. This ensures operations in both guard and body naturally use the rebound SSA names.

### 12.6 Suspension and Nets on the PSG

The SCF dialect is not a stepping stone; it is the witnessed form. Both halves of the compilation strategy are hypergraph structure settled by Baker at saturation:

1. **Delimited continuations** — for sequential effects (async, state, actor receive). The suspension recipe splits a computation-expression region at its cuts into segments, enumerates each cut's live-across set into a frame, and records a delimiter edge from every cut to its builder extent. Witnessed as a discriminant, a byte frame, and `scf.index_switch`.

2. **Interaction nets** — for parallel pure computation (queries, comprehensions). The net's rule system is hyperedge structure over enumerated source sets; its parallelism is a consequence of that structure and is witnessed as data flow.

The computation-expression builder's extent determines the region; saturation determines which structure applies and where the effect boundary splits them. No continuation or net dialect exists above the witness boundary (spec: `program-hypergraph.md`, `dcont-representation.md`; Composer: `Thin_Middle_End_Design.md`).

---

## Part 13: Pattern Matching Semantics

Pattern matching is foundational to ML-family languages. This section specifies how pattern variables flow from discriminated union scrutinee to bound variables in case bodies.

### 13.1 MatchCase Structure

A `MatchCase` represents one arm of a match expression:

```fsharp
type MatchCase = {
    /// The pattern to match (Const, Var, UnionCase, etc.)
    Pattern: Pattern
    /// PatternBinding NodeIds for variables bound by this pattern
    PatternBindings: NodeId list
    /// Optional guard expression (when clause)
    Guard: NodeId option
    /// The body to execute if matched
    Body: NodeId
}
```

**Key principle**: `PatternBindings` contains NodeIds that are part of the traversal path, ensuring SSA assignment visits them.

### 13.2 PatternBinding Lifecycle

A `PatternBinding` represents a variable introduced by a pattern:

```fsharp
// Pattern: IntVal x
//         ↓
// PatternBinding node with name = "x", type = int
```

**Lifecycle phases:**

1. **Creation** (CCS pattern checking): When CCS processes a pattern like `IntVal x`, it creates a PatternBinding node with the variable name and inferred type.

2. **SSA Assignment** (traversal): The `foldWithSCFRegions` traversal visits PatternBinding nodes as children of Match, assigning them SSA values.

3. **VarBindings Population** (BeforeRegion hook): Before traversing the case body, the pattern variable name must be bound to its SSA in the VarBindings map.

4. **Usage** (case body): VarRef nodes in the case body look up the pattern variable in VarBindings.

### 13.3 Match Traversal Semantics

The traversal order for Match expressions ensures pattern variables are bound before use:

```
Match (scrutineeId, cases)
    │
    ├─→ Walk scrutinee (produces scrutinee SSA)
    │
    └─→ For each case:
        │
        ├─→ BeforeRegion(MatchCaseRegion idx)
        │       │
        │       └─→ Extract payload from scrutinee
        │       └─→ Bind PatternBindings to VarBindings
        │
        ├─→ Walk PatternBinding nodes (assigns SSAs)
        ├─→ Walk optional guard
        ├─→ Walk case body (can reference pattern variables)
        │
        └─→ AfterRegion(MatchCaseRegion idx)
```

**The Lambda Parallel**: Just as Lambda `preBindParams` binds parameters to VarBindings before body traversal, the Match `BeforeRegion` hook must bind pattern variables before case body traversal.

### 13.4 DU Payload Extraction

When entering a match case, the payload must be extracted from the scrutinee:

**DU Memory Layout** (from native-type-universe.md):
```
┌──────────┬─────────┬───────────────────────┐
│ Tag (i8) │ padding │ Payload (variant data) │
└──────────┴─────────┴───────────────────────┘
```

**Extraction sequence:**
```mlir
; Scrutinee: !llvm.struct<(i8, payload_type)>
%tag = llvm.extractvalue %scrutinee[0] : !llvm.struct<...> -> i8
%payload = llvm.extractvalue %scrutinee[1] : !llvm.struct<...> -> payload_type

; For multi-field payload, further extraction:
%field0 = llvm.extractvalue %payload[0] : payload_type -> field0_type
%field1 = llvm.extractvalue %payload[1] : payload_type -> field1_type
```

**Single-field optimization**: For DU cases with a single field (e.g., `IntVal of int`), the payload IS the bound value - no additional extraction needed.

### 13.5 VarBindings Population

The `BeforeRegion` hook for `MatchCaseRegion` must:

1. **Look up the Match node** using `parentId`
2. **Get the case** at index `idx`
3. **Get scrutinee SSA** from prior traversal results
4. **Extract payload** from scrutinee for this case's tag
5. **For each PatternBinding** in `case.PatternBindings`:
   - Get the binding's name and type from the node
   - Get the appropriate payload field (single-field: entire payload; multi-field: indexed extraction)
   - Add to VarBindings: `name → (payloadSSA, payloadType)`

```fsharp
// Pseudo-code for BeforeRegion(MatchCaseRegion idx):
let matchNode = graph.Nodes.[parentId]
let case = matchNode.Cases.[idx]
let scrutineeSSA = recallNodeResult scrutineeId
let payloadSSA = extractPayload scrutineeSSA case.Pattern.Tag

for binding in case.PatternBindings do
    let node = graph.Nodes.[binding]
    match node.Kind with
    | SemanticKind.PatternBinding name ->
        let bindingType = mapType node.Type
        VarBindings.add name (payloadSSA, bindingType)
```

### 13.6 Pattern Matching Compilation Summary

| Phase | Responsibility | Output |
|-------|----------------|--------|
| **CCS Checking** | Create PatternBinding nodes | PSG with pattern structure |
| **SSA Assignment** | Assign SSAs to PatternBindings | Coeffect map |
| **BeforeRegion Hook** | Extract payload, bind to VarBindings | State update |
| **Case Body Traversal** | VarRefs resolve pattern variables | MLIR ops |
| **witnessMatch** | Generate scf.if chain with extractions | MLIR module |

### 13.7 Tuple Pattern Matching

When the scrutinee is a tuple of discriminated unions, pattern extraction requires a **two-step process** for each tuple element.

**Example:**

```fsharp
type Number = IntVal of int | FloatVal of float

let add (a: Number) (b: Number) : Number =
    match a, b with
    | IntVal x, IntVal y -> IntVal (x + y)
    | FloatVal x, FloatVal y -> FloatVal (x + y)
    | _ -> IntVal 0
```

**Scrutinee Memory Layout:**

The scrutinee `(a, b)` is a tuple of two DUs:

```
Tuple scrutinee: struct<(Number, Number)>
┌─────────────────────────────┬─────────────────────────────┐
│ Number (tag + payload)      │ Number (tag + payload)      │
└─────────────────────────────┴─────────────────────────────┘
       element 0                      element 1
```

Each `Number` has the standard DU layout:

```
Number: struct<(i8, i64)>
┌──────────┬─────────────────────┐
│ Tag (i8) │ Payload (i64/f64)   │
└──────────┴─────────────────────┘
```

**Two-Step Extraction Sequence:**

For a pattern like `IntVal x, IntVal y`, each binding requires:

1. **Extract tuple element** at index `i` → yields the DU struct
2. **Extract DU payload** from field `[1]` → yields the bound value

```mlir
; Step 1: Extract tuple element 0 (first Number)
%du0 = llvm.extractvalue %scrutinee[0] : !llvm.struct<(struct<(i8, i64)>, struct<(i8, i64)>)> -> !llvm.struct<(i8, i64)>

; Step 2: Extract payload from DU (field 1)
%payload0 = llvm.extractvalue %du0[1] : !llvm.struct<(i8, i64)> -> i64

; Step 3: Convert if needed (e.g., i64 to index for int)
%x = arith.index_cast %payload0 : i64 to index

; Repeat for element 1 → %y
```

**Tag Comparison for Tuple Patterns:**

Each element's tag must be checked independently:

```mlir
; Extract tags from both tuple elements
%tag0 = llvm.extractvalue %du0[0] : !llvm.struct<(i8, i64)> -> i8
%tag1 = llvm.extractvalue %du1[0] : !llvm.struct<(i8, i64)> -> i8

; Check if both are IntVal (tag 0)
%isInt0 = arith.cmpi eq, %tag0, %c0 : i8
%isInt1 = arith.cmpi eq, %tag1, %c0 : i8

; Combine with AND for the case guard
%bothInt = arith.andi %isInt0, %isInt1 : i1
```

**Pattern.Tuple Structure:**

CCS represents tuple patterns with `Pattern.Tuple`:

```fsharp
type Pattern =
    | Const of obj * FidType
    | Var of string * FidType
    | Union of caseName: string * tagIndex: int * payload: Pattern option * unionType: FidType
    | Tuple of elements: Pattern list  // Tuple pattern
    | Wild of FidType
```

When processing `Pattern.Tuple elements`:

1. Iterate over `elements` with index `i`
2. For each element pattern (typically `Pattern.Union`):
   - Extract tuple element at index `i`
   - Apply single-DU extraction logic to get payload
   - Bind pattern variables to VarBindings

**Compilation Flow:**

| Step | Single DU | Tuple of DUs |
|------|-----------|--------------|
| **Scrutinee** | `DU struct` | `struct<(DU1, DU2, ...)>` |
| **Tag extraction** | `extractvalue %s[0]` | `extractvalue %s[i][0]` per element |
| **Payload extraction** | `extractvalue %s[1]` | `extractvalue %s[i]` then `extractvalue %du[1]` |
| **Guard condition** | Single tag check | AND of all element tag checks |

---

## Appendix A: Type Mapping Reference

### Primitive Types

| F# Keyword | Clef Type | Size | Alignment |
|------------|----------------|------|-----------|
| `sbyte` | `Int8` | 1 | 1 |
| `byte` | `UInt8` | 1 | 1 |
| `int16` | `Int16` | 2 | 2 |
| `uint16` | `UInt16` | 2 | 2 |
| `int` | `NativeInt` | ptr | ptr |
| `int32` | `Int32` | 4 | 4 |
| `uint` | `NativeUInt` | ptr | ptr |
| `uint32` | `UInt32` | 4 | 4 |
| `int64` | `Int64` | 8 | 8 |
| `uint64` | `UInt64` | 8 | 8 |
| `nativeint` | `NativeInt` | ptr | ptr |
| `unativeint` | `NativeUInt` | ptr | ptr |
| `float32` | `Float32` | 4 | 4 |
| `float` | `Float64` | 8 | 8 |
| `bool` | `Bool` | 1 | 1 |
| `char` | `Char` | 4 | 4 |
| `unit` | `Unit` | 0 | 1 |

### Compound Types

| F# Syntax | CCS Native Semantics | Notes |
|-----------|----------------------|-------|
| `string` | UTF-8 fat pointer | `{ptr, len}` |
| `option<'T>` | `voption<'T>` | Stack-allocated, non-null |
| `array<'T>` | Fat pointer | `{ptr, len}` |
| `list<'T>` | Cons cells | Arena or stack allocated |
| `Map<'K,'V>` | Balanced tree | Arena allocated |
| `Set<'T>` | Balanced tree | Arena allocated |

---

## Appendix B: Grammar Extensions (Future)

Reserved syntax for future Clef features:

```
// Ownership expressions
move <expr>
&<expr>
&mut <expr>
drop <expr>
arena { <expr> }

// Coeffect annotations
<type> -[<coeffect>]-> <type>

// Lifetime annotations
'<ident>
'static
'_

// Alignment annotations
@Align1, @Align2, @Align4, @Align8, @Packed
```

These parse as standard F# (attributes, operators) but have special semantics in Clef.

---

## Appendix C: Specification Status

| Section | Status | Implementation |
|---------|--------|----------------|
| Part 1: Native Type Universe | **Specified** | Pending in CCS |
| Part 2: Null-Free Semantics | **Specified** | Pending in CCS |
| Part 3: SRTP Resolution | **Specified** | Pending in CCS |
| Part 4: Memory Semantics | Draft | Future |
| Part 5: Coeffects | Draft | Future |
| Part 6: Platform Bindings | **Specified** | Implemented in Firefly |
| Part 7: Compatibility | **Specified** | Reference |
| Part 8: Diagnostics | **Specified** | Partial in CCS |
| Part 9: Memory Region Types | **Specified** | Pending in CCS |
| Part 10: Access Kind Enforcement | **Specified** | Pending in CCS |
| Part 11: Peripheral Descriptors | **Specified** | Pending (Farscape integration) |
| Part 12: Ownership/Coeffects | Reserved | Future |
| Part 12: SCF Regions | **Specified** | Implemented in Firefly |
| Part 13: Pattern Matching | **Specified** | Implemented in Firefly |
| Part 14: Collection HOF Decomposition | **Specified** | Design phase |

---

## Appendix D: Native-Specific Diagnostics

### D.1 Error Code Ranges

Clef reserves the FS8xxx range for native-specific diagnostics:

| Range | Category |
|-------|----------|
| FS8001-FS8009 | Memory access violations |
| FS8010-FS8019 | BCL/native type conflicts |
| FS8020-FS8029 | SRTP resolution failures |
| FS8030-FS8039 | Region constraint violations |
| FS8040-FS8049 | Ownership violations (future) |
| FS8050-FS8059 | Coeffect violations (future) |

### D.2 Memory Access Errors

**FS8001: Cannot read write-only pointer**

```
error FS8001: Cannot read write-only pointer.
  The pointer 'outputReg' has access kind 'writeOnly' which does not permit read operations.

  let value = !outputReg
              ^~~~~~~~~~

Hint: Write-only pointers (CMSIS __O) are used for output-only hardware registers.
      Reading from such registers is undefined behavior on most hardware.
```

**FS8002: Cannot write read-only pointer**

```
error FS8002: Cannot write read-only pointer.
  The pointer 'flashData' has access kind 'readOnly' which does not permit write operations.

  flashData := newValue
  ^~~~~~~~~~~~~~~~~~~~

Hint: Read-only pointers (CMSIS __I) represent hardware inputs or flash memory.
      To modify the value, you need a pointer with 'readWrite' access.
```

**FS8003: Memory region mismatch**

```
error FS8003: Memory region mismatch.
  Expected pointer with region 'peripheral' but received region 'sram'.

  readPeripheralRegister(sramPtr)
                         ^~~~~~~

Hint: Peripheral-region pointers require volatile access semantics.
      SRAM pointers cannot be substituted for peripheral pointers.
```

**FS8004: Volatile constraint violation**

```
error FS8004: Volatile constraint violation.
  The operation on 'statusReg' was optimized or reordered in a context
  requiring volatile semantics.

Hint: Peripheral and SystemControl regions require volatile semantics.
      Ensure all accesses use the correct pointer type.
```

**FS8005: Null assignment to native type**

```
error FS8005: Cannot assign null to native type 'array<int>'.
  Clef types are non-nullable by design.

  let arr: array<int> = null
                              ^~~~

Hint: Use 'voption<array<int>>' for optional values,
      or 'array.empty' for an empty array.
```

### D.3 BCL/Native Type Conflicts

**FS8010: BCL type in native compilation**

```
error FS8010: BCL type 'System.String' is not available in native compilation.
  Clef uses 'string' for string values.

  let s: System.String = "hello"
         ^~~~~~~~~~~~~

Hint: Remove explicit BCL type annotations. String literals automatically
      have type 'string' in Clef.
```

**FS8011: BCL collection in native compilation**

```
error FS8011: BCL collection 'System.Collections.Generic.List<T>' is not available.
  Clef uses native collection types.

Hint: Use 'list<T>', 'array<T>', or 'Map<K,V>' with native semantics.
```

### D.4 SRTP Resolution Errors

**FS8020: No native witness found**

```
error FS8020: No witness found for trait constraint on type 'MyCustomType'.
  Searched witnesses:
    - MyCustomType members (not found)
    - BasicOps (not applicable)
    - NumericOps (not applicable)

  let result = a + b  // where a, b: MyCustomType
               ^~~~~

Hint: Implement 'static member (+) : MyCustomType * MyCustomType -> MyCustomType'
      on type 'MyCustomType', or add it to the Alloy witness hierarchy.
```

**FS8021: Ambiguous witness resolution**

```
error FS8021: Ambiguous witness resolution for operator '+' on type 'Number'.
  Multiple witnesses found:
    - BasicOps.Add<Number>
    - Number.op_Addition

Hint: Use explicit type annotation or disambiguate with module qualification.
```

### D.5 Diagnostic Format

NORMATIVE: All native-specific diagnostics SHALL follow this format:

```
error FS<code>: <Brief description>
  <Detailed explanation of the error>

  <Source code snippet with marker>
  <Caret indicating error location>

Hint: <Actionable guidance for resolution>
```

NORMATIVE: Hints SHALL provide actionable guidance. Generic "see documentation" hints are insufficient.

---

---

## Part 14: Collection HOF Decomposition (Baker)

### 14.1 Overview

Collection higher-order functions (HOFs) like `List.map`, `List.fold`, `Seq.collect`, etc. must be decomposed into primitive operations that the code generator (Alex) can witness directly. This decomposition occurs in the **Baker** component of CCS.

**Architectural Principle**: PSGSaturation (Baker) decomposes; Alex witnesses. Alex never implements collection algorithms—it sees only primitives.

```
CCS Type Checking
        ↓
PSGSaturation (Baker Decomposition)
        ↓
PSG Graph (contains full algorithmic structure)
        ↓
Alex (witnesses primitives → MLIR)
```

### 14.2 Primitive vs HOF Operations

**Primitive Operations** (Alex witnesses directly):

| Collection | Primitives |
|------------|------------|
| `List<'T>` | `empty`, `isEmpty`, `head`, `tail`, `cons` |
| `Map<'K,'V>` | `empty`, `isEmpty`, `node`, `left`, `right`, `key`, `value` |
| `Set<'T>` | `empty`, `isEmpty`, `node`, `left`, `right`, `element` |
| `Option<'T>` | `some`, `none`, `isSome`, `isNone`, `get` |
| `Seq<'T>` | `moveNext`, `current`, `dispose` (iterator protocol) |

**HOF Operations** (Baker decomposes):

| Collection | HOFs |
|------------|------|
| `List<'T>` | `map`, `fold`, `filter`, `exists`, `forall`, `length`, `rev`, `append`, `collect` |
| `Map<'K,'V>` | `add`, `tryFind`, `containsKey`, `toList`, `keys`, `values`, `forall` |
| `Set<'T>` | `add`, `contains`, `remove`, `union`, `intersect`, `difference` |
| `Option<'T>` | `map`, `bind`, `filter`, `defaultValue` |
| `Seq<'T>` | `map`, `filter`, `collect`, `take`, `skip`, `fold`, `iter` |

### 14.3 Decomposition Model

When Baker encounters a HOF application in the PSG, it expands it into a structure using only primitive operations.

**Example: List.map**

```fsharp
// Source
List.map f xs

// Baker decomposes to (conceptually):
let rec loop xs =
    if List.isEmpty xs then List.empty
    else List.cons (f (List.head xs)) (loop (List.tail xs))
loop xs
```

**Example: Seq.collect (state machine)**

```fsharp
// Source
Seq.collect f xs

// Baker decomposes to an iterator state machine with:
// - State enum: Initial | InOuter | InInner | Done
// - MoveNext with state transitions
// - Current property
// - Multiple iterator fields
```

### 14.4 Two-Level Shadow AST Model

PSG nodes created by Baker have no corresponding source syntax. To provide **editing transparency** for developers (distinguishing "code I wrote" from "compiler-saturated code"), Baker maintains a **two-level shadow model**:

#### Level 1: Semantic Shadow (Developer-Facing)

Captures the **meaning** of the expansion, not every PSG node. This is what tooling displays.

```fsharp
/// For simple recursive patterns (List operations)
type RecursivePatternShadow = {
    Operation: string           // "List.map"
    BaseCase: string            // "empty list → empty list"
    RecursiveCase: string       // "cons(f(head), recurse(tail))"
    SourceRefs: Map<string, NodeId>  // Links to real source nodes
}

/// For state machines (Seq operations)
type StateMachineShadow = {
    States: string list
    OuterSource: ShadowRef
    InnerMapper: ShadowRef option
    YieldPoints: YieldPoint list
    Transitions: Transition list
}

/// Reference to real source vs synthesized
type ShadowRef =
    | Real of NodeId           // Points to source-derived PSG node
    | Synthetic of ShadowId    // Points to synthesized shadow node
```

#### Level 2: PSG Nodes (Compiler-Facing)

The full PSG structure with all `SemanticNode` records. This is what Alex witnesses. The shadow doesn't mirror this 1:1.

### 14.5 XParsec Template Integration

Baker decomposition uses XParsec-style templates that produce **both** PSG nodes and semantic shadow simultaneously:

```fsharp
type Expanded<'a> = {
    Value: 'a                    // The PSG node(s)
    Shadow: ShadowExpr           // Semantic description
    Provenance: Provenance       // Link to inspiring source
}
```

The template IS the documentation—when you read the template, you understand both what PSG is built AND what the semantic shadow captures.

**Key principle**: No separate construction pass. Shadow is built alongside PSG in a single traversal.

### 14.6 Provenance Tracking

Every shadow node tracks its origin:

```fsharp
type Provenance = {
    /// The source PSG node that triggered expansion
    InspiringNode: NodeId
    /// Original source range (for IDE navigation)
    SourceRange: SourceRange
    /// What HOF was expanded (e.g., "Seq.collect")
    ExpandedOperation: string
    /// Nesting depth (for nested expansions)
    Depth: int
}
```

### 14.7 Tooling Integration

The shadow AST enables design-time tooling:

**IDE Expansion View:**
```
// Expanded from List.map at MyFile.fs:42:5
// Pattern: Recursive
//   Base case: empty list → empty list
//   Recursive: cons(f(head), recurse(tail))
//   Source refs: f → line 42, xs → line 42

[Expand to see full PSG structure...]
```

**State Machine View:**
```
// Expanded from Seq.collect at MyFile.fs:58:9
// State Machine: Initial → InOuter → InInner → Done
//   Outer source: «xs» (line 58)
//   Inner mapper: «f» (line 58)
//   Yields: innerEnum.Current when in InInner state

[View state transition diagram...]
```

### 14.8 Implementation Files

| File | Purpose |
|------|---------|
| `Baker/ShadowAST.fs` | Shadow types, rendering, provenance |
| `Baker/Recipes/Decomposition.fs` | Context, Result types, helpers |
| `Baker/Recipes/ListRecipes.fs` | List HOF templates |
| `Baker/Recipes/MapRecipes.fs` | Map HOF templates |
| `Baker/Recipes/SetRecipes.fs` | Set HOF templates |
| `Baker/Recipes/OptionRecipes.fs` | Option HOF templates |
| `Baker/Recipes/SeqRecipes.fs` | Seq state machine templates |
| `Baker/HOFDecomposition.fs` | Orchestration, shadow registry |

### 14.9 Anti-Patterns

1. **Alex implementing algorithms** — Wrong layer. Decomposition belongs in Baker.
2. **1:1 shadow-to-PSG mapping** — Shadow is semantic, not syntactic.
3. **Separate shadow construction pass** — Shadow must be built alongside PSG.
4. **Ad-hoc patterns per operation** — All decompositions use same infrastructure.
5. **Forgetting provenance** — Every shadow node must link back to source.

### 14.10 Specification Status

| Component | Status |
|-----------|--------|
| Primitive witnesses (Alex) | **Implemented** |
| List decomposition | Placeholder |
| Map decomposition | Placeholder |
| Set decomposition | Placeholder |
| Option decomposition | Draft |
| Seq state machines | Design |
| Shadow AST infrastructure | Design |
| Tooling integration | Future |

---

*This specification is maintained alongside the clef-lang-spec repository and evolves with the Fidelity framework.*

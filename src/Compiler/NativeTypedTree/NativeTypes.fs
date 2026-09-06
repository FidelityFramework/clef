// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Core type representation for the native type checker.
/// These types are used throughout the type checking process and in the output semantic graph.
module Clef.Compiler.NativeTypedTree.NativeTypes

open System.Collections.Generic

//-------------------------------------------------------------------------
// Source Location
//-------------------------------------------------------------------------

/// A position in source code (line, column)
[<Struct>]
type Position = { Line: int; Column: int }

/// A range in source code
[<Struct>]
type SourceRange = {
    File: string
    Start: Position
    End: Position
}

let dummyRange = { File = ""; Start = { Line = 0; Column = 0 }; End = { Line = 0; Column = 0 } }

//-------------------------------------------------------------------------
// Module Path
//-------------------------------------------------------------------------

/// A path to a module (e.g., ["Alloy"; "Core"; "Memory"])
type ModulePath = string list

/// Format a module path as a dot-separated string
let formatModulePath (path: ModulePath) =
    match path with
    | [] -> "<root>"
    | _ -> String.concat "." path

//-------------------------------------------------------------------------
// Node Identity (PSG)
//-------------------------------------------------------------------------

/// Unique identifier for semantic nodes in the PSG.
/// Moved here from SemanticGraph.fs to break circular dependencies.
[<Struct>]
type NodeId = NodeId of int

module NodeId =
    let mutable private counter = 0

    let fresh () =
        let id = counter
        counter <- counter + 1
        NodeId id

    let reset () = counter <- 0

    let value (NodeId id) = id

//-------------------------------------------------------------------------
// Type Layout (Memory Representation)
//-------------------------------------------------------------------------


//-------------------------------------------------------------------------
// NTU (Native Type Universe) Kind System
// Following F* pattern: type identity is separate from type width.
// Width is a first-class dimension, not baked into discrete variants.
// Width is erased metadata resolved by Alex via platform quotations.
//-------------------------------------------------------------------------

/// Platform-resolved width dimensions — NTU-native vocabulary.
/// These are NOT named after C types. Farscape maps C types to these dimensions;
/// the NTU doesn't know or care about C.
[<RequireQualifiedAccess>]
type WidthDimension =
    /// Address width — pointer-sized (64-bit on x86_64, 32-bit on ARM32)
    | Pointer
    /// Machine register / natural computational word width
    | Register

/// How the width of a numeric type is determined.
[<RequireQualifiedAccess>]
type NTUWidth =
    /// Known at all times: 8, 16, 32, 64, 128 bits
    | Fixed of bits: int
    /// Platform-dependent, resolved by Alex via PlatformContext
    | Resolved of WidthDimension

/// NTU (Native Type Universe) type kinds.
/// Numeric types are parameterized by width — 3 kinds replace 16 discrete variants.
/// Type identity: NTUint(Fixed 32) ≠ NTUint(Resolved Register) even if same width on LP64.
[<RequireQualifiedAccess>]
type NTUKind =
    //-----------------------------------------------------------------------
    // Parameterized numeric types (width as dimension)
    //-----------------------------------------------------------------------

    /// Signed integer of any width
    /// Fixed 8/16/32/64 or Resolved Register/Pointer
    | NTUint of NTUWidth

    /// Unsigned integer of any width
    /// Fixed 8/16/32/64 or Resolved Register/Pointer
    | NTUuint of NTUWidth

    /// IEEE floating point of any width
    /// Fixed 32 or Fixed 64 (extensible to Fixed 128 for long double)
    | NTUfloat of NTUWidth

    //-----------------------------------------------------------------------
    // Pointer types (width = Pointer, implicit)
    //-----------------------------------------------------------------------

    /// Native pointer type (pointer-sized)
    | NTUptr

    /// Function pointer type (pointer-sized)
    /// Used for callbacks to top-level functions (no closures)
    | NTUfnptr

    /// Size type (unsigned, pointer-width) — array lengths, memory sizes
    | NTUsize

    /// Pointer difference type (signed, pointer-width)
    | NTUdiff

    //-----------------------------------------------------------------------
    // Special types
    //-----------------------------------------------------------------------

    /// UTF-8 encoded string (fat pointer: ptr + length)
    | NTUstring

    /// Boolean (1 byte)
    | NTUbool

    /// Unicode code point (UTF-32, 4 bytes)
    | NTUchar

    /// Unit type (zero-sized)
    | NTUunit

    /// Decimal (128-bit)
    | NTUdecimal

    /// Lazy computation (thunk with memoization)
    /// PRD-14: Foundation of the Lazy Stack
    | NTUlazy

    /// Sequence/generator (resumable computation producing values on demand)
    /// PRD-15: Simple Sequence Expressions
    | NTUseq

    //-----------------------------------------------------------------------
    // Collection types (PRD-13a: Core Collections)
    //-----------------------------------------------------------------------

    /// Mutable contiguous array (fat pointer: ptr + length)
    /// C-04: Type constructor arity = 1
    | NTUarray

    /// Immutable singly-linked list
    /// PRD-13a: Core Collections
    | NTUlist

    /// Immutable key-value map (balanced BST)
    /// PRD-13a: Core Collections
    | NTUmap

    /// Immutable set (balanced BST)
    /// PRD-13a: Core Collections
    | NTUset

    //-----------------------------------------------------------------------
    // Compound value types (platform-independent fixed size)
    //-----------------------------------------------------------------------

    /// UUID (128-bit, RFC 4122)
    /// Platform entropy source for generation (getrandom/BCryptGenRandom)
    | NTUuuid

    /// DateTime - ticks since epoch (64-bit)
    /// Platform clock resolution via quotations
    | NTUdatetime

    /// TimeSpan - duration in ticks (64-bit)
    | NTUtimespan

    //-----------------------------------------------------------------------
    // Posit numeric types (Gustafson Type III Unum)
    //-----------------------------------------------------------------------

    /// Posit number: tapered-precision floating point.
    /// Width determines storage size (8/16/32/64 bits).
    /// es = exponent field size (0-3), determines dynamic range vs precision tradeoff.
    /// Type identity: NTUposit(Fixed 32, 2) ≠ NTUfloat(Fixed 32) — different numeric semantics.
    /// CPU: software decode/encode or AVX-512 vectorized.
    /// FPGA: dedicated hardware pipeline via CIRCT (PACoGen-style).
    | NTUposit of NTUWidth * es: int

//-------------------------------------------------------------------------
// NTU Dimensional Qualifiers (Multi-Substrate Compilation)
//-------------------------------------------------------------------------

/// Memory space qualifier for substrate-aware type placement.
/// These do NOT affect type identity — `int @Global` and `int @Shared`
/// are the same NTU type with different placement. Qualifiers inform
/// code generation and BAREWire inter-substrate transfer strategy.
[<RequireQualifiedAccess>]
type NTUMemorySpace =
    /// Substrate chooses (escape analysis on CPU, compiler on GPU)
    | Default
    /// Function-local (universal concept across substrates)
    | Stack
    /// Main memory / VRAM / HBM
    | Global
    /// Explicitly managed cache (GPU shared mem, NPU tile mem)
    | Shared
    /// Per-thread/per-PE (GPU registers, NPU private mem)
    | Private
    /// HSA unified (CPU↔GPU↔NPU on Strix Halo — zero-copy)
    | Coherent
    /// Cross-device (FPGA BRAM from CPU perspective)
    | External
    /// MMIO (volatile access from BAREWire patterns)
    | Peripheral

/// Access pattern qualifier for cache-aware compilation.
/// Informs cache bypass strategy on CPU, coalescing on GPU,
/// and AXI stream vs memory-mapped on FPGA.
[<RequireQualifiedAccess>]
type NTUAccessPattern =
    /// Regular read/write
    | Normal
    /// Sequential, don't cache (non-temporal on CPU, coalesced on GPU)
    | Streaming
    /// MMIO / peripheral
    | Volatile
    /// Immutable view (enables sharing without coherency cost)
    | ReadOnly
    /// Producer-only (enables GPU write-combine)
    | WriteOnly

/// Bundle of placement qualifiers for substrate-aware compilation.
/// Attached to TypeLayout, not type identity.
type NTUQualifiers = {
    MemorySpace: NTUMemorySpace option
    AccessPattern: NTUAccessPattern option
}

/// NTUQualifiers helpers
module NTUQualifiers =
    /// Empty qualifiers (no explicit placement)
    let empty = { MemorySpace = None; AccessPattern = None }

    /// Create qualifiers with only a memory space
    let withMemorySpace space = { MemorySpace = Some space; AccessPattern = None }

    /// Create qualifiers with only an access pattern
    let withAccessPattern pattern = { MemorySpace = None; AccessPattern = Some pattern }

/// Platform predicate types (abstract, erased at runtime).
/// F*-inspired propositions for conditional compilation without runtime checks.
/// These flow through CCS unchanged and are resolved by Alex using platform quotations.
[<RequireQualifiedAccess>]
type PlatformPredicate =
    /// Platform supports 32-bit word operations
    | FitsU32
    /// Platform supports 64-bit word operations
    | FitsU64
    /// Platform has AVX-512 vector support
    | HasAVX512
    /// Platform has ARM NEON vector support
    | HasNEON
    /// Platform has 64-bit atomic operations
    | HasAtomics64
    /// Platform supports unaligned memory access
    | HasUnalignedAccess
    /// Platform has hardware floating point
    | HasHardwareFloat
    /// Custom predicate (for extensibility)
    | Custom of name: string

//-------------------------------------------------------------------------
// Freestanding Startup Data (Platform Entry Point)
//-------------------------------------------------------------------------

/// Freestanding startup configuration for platforms without libc.
/// This is DATA only - contains offsets, syscall numbers, register names.
/// Baker provides the BEHAVIOR through ingredients and recipes.
///
/// Platform bindings flow: Fidelity.Platform → PlatformContext → RecipeContext → Baker
[<NoComparison; NoEquality>]
type FreestandingStartup = {
    /// Entry point symbol name (typically "_start" for freestanding)
    EntrySymbol: string

    /// Main function name (what _start calls)
    MainFunction: string

    /// Offset from stack pointer to argc on entry (bytes)
    /// Linux x86_64: argc is at [rsp]
    ArgcOffset: int

    /// Offset from stack pointer to argv pointer array (bytes)
    /// Linux x86_64: argv is at [rsp + 8]
    ArgvOffset: int

    /// Exit syscall number
    /// Linux x86_64: 60 (sys_exit)
    ExitSyscall: int

    /// Register for syscall number
    /// Linux x86_64: "rax"
    SyscallRegister: string

    /// Register for first syscall argument (exit code)
    /// Linux x86_64: "rdi"
    Arg0Register: string
}

module FreestandingStartup =
    /// Default freestanding startup for Linux x86_64
    let defaultLinux_x86_64 = {
        EntrySymbol = "_start"
        MainFunction = "main"
        ArgcOffset = 0      // argc at [rsp]
        ArgvOffset = 8      // argv at [rsp + 8]
        ExitSyscall = 60    // sys_exit
        SyscallRegister = "rax"
        Arg0Register = "rdi"
    }

    /// Look up freestanding startup config for a platform
    let forPlatform (platformId: string) : FreestandingStartup option =
        match platformId with
        | "Linux_x86_64" -> Some defaultLinux_x86_64
        | "Linux_aarch64" ->
            Some {
                EntrySymbol = "_start"
                MainFunction = "main"
                ArgcOffset = 0
                ArgvOffset = 8
                ExitSyscall = 93    // sys_exit on aarch64
                SyscallRegister = "x8"
                Arg0Register = "x0"
            }
        | _ -> None

//-------------------------------------------------------------------------
// Substrate and Platform Context (NTU Resolution)
//-------------------------------------------------------------------------

/// Runtime model — what execution environment services are available.
/// This is a capability coeffect: what the computation requires from
/// its environment. Comes from the platform binding's [platform] section.
/// See DTS+DMM paper Section 3.1.
[<RequireQualifiedAccess>]
type RuntimeModel =
    /// C library available (CPU console apps)
    | Libc
    /// Direct syscalls only, no libc (CPU standalone)
    | Freestanding
    /// No OS, hardware target (FPGA, MCU)
    | Bare
    /// AMD GPU runtime
    | ROCm
    /// AMD NPU runtime
    | XDNA

/// Compute substrate kind for multi-substrate compilation.
/// Each fidproj targets a single substrate; the fidsln orchestrates across them.
[<RequireQualifiedAccess>]
type SubstrateKind =
    /// CPU target (Zen 5, ARM, RISC-V) → MLIR → LLVM → native
    | CPU
    /// GPU target (RDNA 3.5, etc.) → MLIR → GPU/AMDGPU → ROCm
    | GPU
    /// NPU target (XDNA 2, etc.) → MLIR → MLIR-AIE → AI Engine runtime
    | NPU
    /// FPGA target (Xilinx, etc.) → MLIR → CIRCT → handshake → hw/comb/seq → SV
    | FPGA

/// Platform context for NTU type resolution.
/// Carries quotation-resolved platform information used to
/// resolve platform-dependent types (NTUint, NTUptr, etc.) to concrete widths.
/// Extended with substrate-awareness for multi-target compilation.
[<NoComparison; NoEquality>]
type PlatformContext = {
    /// Platform identifier (e.g., "Linux_x86_64", "Windows_ARM64")
    PlatformId: string

    /// Width dimension resolutions (bits).
    /// Maps WidthDimension → concrete bit width.
    /// e.g., Pointer → 64, Register → 64 on x86_64
    Dimensions: Map<WidthDimension, int>

    /// Pointer alignment in bytes
    PointerAlign: int

    /// Path to the Fidelity.Platform library
    PlatformLibraryPath: string option

    /// Evaluated platform predicates (from quotations)
    Predicates: Map<PlatformPredicate, bool>

    /// Freestanding startup configuration (populated for freestanding builds)
    FreestandingStartup: FreestandingStartup option

    /// Substrate kind (None = CPU for backward compat with single-substrate builds)
    SubstrateKind: SubstrateKind option

    /// Runtime model from platform binding — capability coeffect.
    /// What execution environment services are available.
    RuntimeModel: RuntimeModel option

    /// Memory spaces available on this substrate.
    /// Empty = all spaces available (for backward compat).
    AvailableMemorySpaces: NTUMemorySpace list

    /// Default memory space for allocation on this substrate.
    /// None = substrate default (Stack/heap via escape analysis on CPU, Global on GPU, etc.)
    DefaultMemorySpace: NTUMemorySpace option

    /// Clock frequency in MHz from platform binding (FPGA/MCU).
    /// Used to compute combinational depth threshold.
    ClockFrequencyMhz: int option

    /// Fabric-specific ns per weighted depth unit (from binding, calibrated against Vivado).
    /// threshold = floor(clock_period_ns / ns_per_weight_unit)
    NsPerWeightUnit: float option
}

/// SubstrateContext is PlatformContext with substrate-aware fields populated.
/// Type alias for documentation and gradual migration — not a separate type.
type SubstrateContext = PlatformContext

/// Platform context operations for NTU type resolution
module PlatformContext =
    /// Resolve an NTUWidth to concrete bits using the platform dimensions.
    let resolveWidth (ctx: PlatformContext) (width: NTUWidth) : int =
        match width with
        | NTUWidth.Fixed bits -> bits
        | NTUWidth.Resolved dim -> ctx.Dimensions.[dim]

    /// Convenience: pointer size in bytes for this platform
    let pointerSize (ctx: PlatformContext) : int =
        ctx.Dimensions.[WidthDimension.Pointer] / 8

    /// Convenience: word size in bits for this platform
    let wordSize (ctx: PlatformContext) : int =
        ctx.Dimensions.[WidthDimension.Register]

    /// Default platform context for x86_64 Linux (most common development target)
    let defaultLinux_x86_64 = {
        PlatformId = "Linux_x86_64"
        Dimensions = Map.ofList [
            (WidthDimension.Pointer, 64)
            (WidthDimension.Register, 64)
        ]
        PointerAlign = 8
        PlatformLibraryPath = None
        Predicates = Map.ofList [
            (PlatformPredicate.FitsU32, true)
            (PlatformPredicate.FitsU64, true)
            (PlatformPredicate.HasAtomics64, true)
            (PlatformPredicate.HasUnalignedAccess, true)
            (PlatformPredicate.HasHardwareFloat, true)
        ]
        FreestandingStartup = None  // Set when building freestanding binaries
        SubstrateKind = None  // None = CPU (backward compat)
        RuntimeModel = None  // None = inferred from DeploymentMode (backward compat)
        AvailableMemorySpaces = []  // Empty = all (backward compat)
        DefaultMemorySpace = None  // None = substrate default
        ClockFrequencyMhz = None  // None = no timing analysis
        NsPerWeightUnit = None  // None = use default threshold
    }

    /// Create a platform context from a platform library path
    let fromPlatformPath (path: string) : PlatformContext =
        // Extract platform ID from path (e.g., "Linux_x86_64" from ".../Fidelity.Platform/Linux_x86_64")
        let platformId =
            let parts = path.Replace("\\", "/").Split('/')
            parts |> Array.tryLast |> Option.defaultValue "Unknown"

        // Default to x86_64 assumptions, will be refined by quotation evaluation
        { defaultLinux_x86_64 with
            PlatformId = platformId
            PlatformLibraryPath = Some path }

    /// Resolve the byte size for an NTU kind on this platform
    let resolveSize (ctx: PlatformContext) (kind: NTUKind) : int =
        match kind with
        // Parameterized numeric types — resolve width dimension
        | NTUKind.NTUint w | NTUKind.NTUuint w | NTUKind.NTUfloat w
        | NTUKind.NTUposit (w, _) ->
            resolveWidth ctx w / 8
        // Pointer types — pointer-sized
        | NTUKind.NTUptr | NTUKind.NTUfnptr | NTUKind.NTUsize | NTUKind.NTUdiff ->
            pointerSize ctx
        // Special types
        | NTUKind.NTUstring -> 16  // Fat pointer: ptr + length
        | NTUKind.NTUbool -> 1
        | NTUKind.NTUchar -> 4  // UTF-32
        | NTUKind.NTUunit -> 0
        | NTUKind.NTUdecimal -> 16
        // Temporal and identity types
        | NTUKind.NTUuuid -> 16  // 128-bit UUID
        | NTUKind.NTUdatetime -> 8  // 64-bit ticks
        | NTUKind.NTUtimespan -> 8  // 64-bit duration
        | NTUKind.NTUlazy -> -1  // Size depends on element type (PRD-14)
        | NTUKind.NTUseq -> -1  // Size depends on element type (PRD-15)
        | NTUKind.NTUarray -> 16  // Fat pointer: ptr + length (C-04)
        | NTUKind.NTUlist -> pointerSize ctx  // Pointer to cons cell (PRD-13a)
        | NTUKind.NTUmap -> pointerSize ctx  // Pointer to tree root (PRD-13a)
        | NTUKind.NTUset -> pointerSize ctx  // Pointer to tree root (PRD-13a)

    /// Resolve the alignment for an NTU kind on this platform
    let resolveAlign (ctx: PlatformContext) (kind: NTUKind) : int =
        match kind with
        // Parameterized numeric types — align to width
        | NTUKind.NTUint w | NTUKind.NTUuint w | NTUKind.NTUfloat w
        | NTUKind.NTUposit (w, _) ->
            resolveWidth ctx w / 8
        // Pointer types — pointer alignment
        | NTUKind.NTUptr | NTUKind.NTUfnptr | NTUKind.NTUsize | NTUKind.NTUdiff ->
            ctx.PointerAlign
        // Special types
        | NTUKind.NTUstring -> 8  // Pointer alignment for fat pointer
        | NTUKind.NTUbool -> 1
        | NTUKind.NTUchar -> 4
        | NTUKind.NTUunit -> 1
        | NTUKind.NTUdecimal -> 8
        // Temporal and identity types
        | NTUKind.NTUuuid -> 8  // 64-bit aligned (two i64s)
        | NTUKind.NTUdatetime -> 8  // 64-bit aligned
        | NTUKind.NTUtimespan -> 8  // 64-bit aligned
        | NTUKind.NTUlazy -> 8  // Pointer-aligned (PRD-14)
        | NTUKind.NTUseq -> 8  // Pointer-aligned (PRD-15)
        | NTUKind.NTUarray -> 8  // Pointer-aligned (C-04)
        | NTUKind.NTUlist -> ctx.PointerAlign  // Pointer-aligned (PRD-13a)
        | NTUKind.NTUmap -> ctx.PointerAlign  // Pointer-aligned (PRD-13a)
        | NTUKind.NTUset -> ctx.PointerAlign  // Pointer-aligned (PRD-13a)

    /// Get the substrate kind (defaults to CPU for backward compatibility)
    let substrateKind (ctx: PlatformContext) : SubstrateKind =
        ctx.SubstrateKind |> Option.defaultValue SubstrateKind.CPU

    /// Check if a memory space is available on this substrate
    let isMemorySpaceAvailable (ctx: PlatformContext) (space: NTUMemorySpace) : bool =
        match ctx.AvailableMemorySpaces with
        | [] -> true  // Empty = all available (backward compat)
        | spaces -> List.contains space spaces

    /// Get the default memory space for this substrate
    let defaultMemorySpace (ctx: PlatformContext) : NTUMemorySpace =
        ctx.DefaultMemorySpace |> Option.defaultValue NTUMemorySpace.Default

/// Helpers for NTUKind
module NTUKind =
    /// Check if an NTUKind is platform-dependent (requires quotation resolution)
    let isPlatformDependent = function
        | NTUKind.NTUint (NTUWidth.Resolved _)
        | NTUKind.NTUuint (NTUWidth.Resolved _)
        | NTUKind.NTUfloat (NTUWidth.Resolved _)
        | NTUKind.NTUposit (NTUWidth.Resolved _, _) -> true
        | NTUKind.NTUptr | NTUKind.NTUfnptr | NTUKind.NTUsize | NTUKind.NTUdiff -> true
        | _ -> false

    /// Check if an NTUKind is a fixed-width integer
    let isFixedWidthInteger = function
        | NTUKind.NTUint (NTUWidth.Fixed _) -> true
        | NTUKind.NTUuint (NTUWidth.Fixed _) -> true
        | _ -> false

    /// Check if an NTUKind is any integer type (signed or unsigned, any width)
    let isInteger = function
        | NTUKind.NTUint _ | NTUKind.NTUuint _ -> true
        | NTUKind.NTUsize | NTUKind.NTUdiff -> true
        | _ -> false

    /// Check if an NTUKind is a signed integer
    let isSigned = function
        | NTUKind.NTUint _ -> true
        | NTUKind.NTUdiff -> true
        | _ -> false

    /// Check if an NTUKind is floating point
    let isFloatingPoint = function
        | NTUKind.NTUfloat _ -> true
        | _ -> false

    /// Check if an NTUKind is a posit (Gustafson Type III Unum)
    let isPosit = function
        | NTUKind.NTUposit _ -> true
        | _ -> false

    /// Check if an NTUKind is numeric (integer, floating point, or posit)
    let isNumeric kind = isInteger kind || isFloatingPoint kind || isPosit kind

    /// Get the human-readable name for an NTUKind
    let name = function
        | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register) -> "int"
        | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register) -> "uint"
        | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer) -> "nativeint"
        | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer) -> "unativeint"
        | NTUKind.NTUint (NTUWidth.Fixed 8) -> "int8"
        | NTUKind.NTUint (NTUWidth.Fixed 16) -> "int16"
        | NTUKind.NTUint (NTUWidth.Fixed 32) -> "int32"
        | NTUKind.NTUint (NTUWidth.Fixed 64) -> "int64"
        | NTUKind.NTUuint (NTUWidth.Fixed 8) -> "uint8"
        | NTUKind.NTUuint (NTUWidth.Fixed 16) -> "uint16"
        | NTUKind.NTUuint (NTUWidth.Fixed 32) -> "uint32"
        | NTUKind.NTUuint (NTUWidth.Fixed 64) -> "uint64"
        | NTUKind.NTUfloat (NTUWidth.Fixed 32) -> "float32"
        | NTUKind.NTUfloat (NTUWidth.Fixed 64) -> "float"
        | NTUKind.NTUint w -> $"int({w})"
        | NTUKind.NTUuint w -> $"uint({w})"
        | NTUKind.NTUfloat w -> $"float({w})"
        | NTUKind.NTUposit (NTUWidth.Fixed 8, _) -> "posit8"
        | NTUKind.NTUposit (NTUWidth.Fixed 16, _) -> "posit16"
        | NTUKind.NTUposit (NTUWidth.Fixed 32, _) -> "posit32"
        | NTUKind.NTUposit (NTUWidth.Fixed 64, _) -> "posit64"
        | NTUKind.NTUposit (w, es) -> $"posit({w},es={es})"
        | NTUKind.NTUptr -> "nativeptr"
        | NTUKind.NTUfnptr -> "fnptr"
        | NTUKind.NTUsize -> "size"
        | NTUKind.NTUdiff -> "diff"
        | NTUKind.NTUstring -> "string"
        | NTUKind.NTUbool -> "bool"
        | NTUKind.NTUchar -> "char"
        | NTUKind.NTUunit -> "unit"
        | NTUKind.NTUdecimal -> "decimal"
        | NTUKind.NTUlazy -> "Lazy"
        | NTUKind.NTUseq -> "Seq"
        | NTUKind.NTUarray -> "array"
        | NTUKind.NTUlist -> "List"
        | NTUKind.NTUmap -> "Map"
        | NTUKind.NTUset -> "Set"
        | NTUKind.NTUuuid -> "Uuid"
        | NTUKind.NTUdatetime -> "DateTime"
        | NTUKind.NTUtimespan -> "TimeSpan"

/// Type layout determines memory representation
[<RequireQualifiedAccess>]
type TypeLayout =
    /// Stack-allocated, known size and alignment
    | Inline of size: int * align: int
    /// Arena-allocated (heap-like but deterministic)
    | Reference of arena: ArenaAffinity
    /// Platform-specific, size determined at codegen
    | Opaque
    /// Platform word size - size/alignment depend on target architecture
    /// CCS preserves type identity; Alex resolves to concrete size
    | PlatformWord
    /// Fat pointer: pointer + length (both platform word sized)
    /// Used for arrays, strings, spans - compound of two NTU components.
    /// On x86_64: 16 bytes (8 + 8), on ARM32: 8 bytes (4 + 4)
    /// Alex resolves to concrete size via platform quotations.
    | FatPointer
    /// NTU compound: struct of multiple NTU-sized components
    /// Size = sum of component sizes (all platform-dependent)
    /// Used for types like NativeSlice (ptr + length + flags)
    | NTUCompound of componentCount: int
    /// Substrate-qualified layout: same type, different placement.
    /// Qualifiers do NOT affect type identity — only inform codegen
    /// and BAREWire inter-substrate transfer strategy.
    | Qualified of inner: TypeLayout * qualifiers: NTUQualifiers

/// Arena affinity for memory management
and [<RequireQualifiedAccess>] ArenaAffinity =
    /// Default: current actor's arena
    | CurrentActor
    /// Named arena (explicit allocation context)
    | Explicit of name: string
    /// Stack allocation (no arena, scope-bound)
    | Stack

/// TypeLayout helpers
module TypeLayout =
    /// Strip qualifiers to get the underlying layout (for size/align calculations).
    /// Most code should use this when computing layout properties.
    let rec baseLayout = function
        | TypeLayout.Qualified (inner, _) -> baseLayout inner
        | layout -> layout

    /// Get qualifiers from a layout, if present
    let qualifiers = function
        | TypeLayout.Qualified (_, q) -> Some q
        | _ -> None

//-------------------------------------------------------------------------
// Type Parameter Kind
//-------------------------------------------------------------------------

/// Distinguishes type parameters from measure parameters.
/// In Clef, measures work on ANY type (not just numerics like in .NET F#).
[<RequireQualifiedAccess>]
type TypeParamKind =
    /// Regular type parameter: 'T
    | Type
    /// Measure parameter: [<Measure>] 'u
    /// Measures on non-numeric types enable memory region tracking, access control, etc.
    | Measure

//-------------------------------------------------------------------------
// Type Constructor Reference
//-------------------------------------------------------------------------

/// Unique identifier for type parameters
type TypeParamId = int

/// Reference to a type constructor (not IL-based)
/// Note: For record types, field info is accessed via SemanticGraph.Types lookup
/// (not embedded here due to F# forward reference constraints)
[<NoComparison>]
type TypeConRef = {
    /// The name of the type constructor (e.g., "string", "option", "Ptr")
    Name: string
    /// The module where this type is defined
    Module: ModulePath
    /// Parameter kinds - which are types vs measures
    /// e.g., Ptr<'T, 'region, 'access> = [Type; Measure; Measure]
    ParamKinds: TypeParamKind list
    /// Memory layout hint (may be refined during checking)
    Layout: TypeLayout
    /// NTU kind for primitive/native types.
    /// Some(kind) for native primitives, None for user-defined/compound types.
    /// Used for type identity: NTUint ≠ NTUint64 even if same width on some platforms.
    NTUKind: NTUKind option
    /// Number of record fields (if this is a record type).
    /// 0 for non-record types. >0 for record types.
    /// Actual field types are looked up via SemanticGraph.Types.
    FieldCount: int
    /// Number of union cases (if this is a DU type).
    /// 0 for non-DU types. >0 for discriminated unions.
    /// Platform elision decides concrete tag representation from case count.
    CaseCount: int
    /// Placement qualifiers for substrate-aware compilation.
    /// None = no explicit placement (substrate default).
    /// These do NOT affect type identity — types with different
    /// qualifiers unify as the same type.
    Qualifiers: NTUQualifiers option
    /// Pin attributes on record fields: Map<fieldName, pinLogicalNames>
    /// Populated from [<Pin("name")>] and [<Pins("a","b","c")>] attributes on SynField.
    /// Empty for non-record types and records without pin attributes.
    FieldPinAttributes: Map<string, string list>
}

/// Total arity (type + measure parameters)
let arity (tc: TypeConRef) = List.length tc.ParamKinds

/// Create a simple type constructor with only type parameters (non-NTU kind)
let mkTypeConRef name typeArity layout =
    { Name = name; Module = []; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = None; FieldCount = 0; CaseCount = 0; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a type constructor with explicit parameter kinds (non-NTU kind)
let mkTypeConRefWithMeasures name paramKinds layout =
    { Name = name; Module = []; ParamKinds = paramKinds; Layout = layout; NTUKind = None; FieldCount = 0; CaseCount = 0; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a type constructor with an NTU kind (for native primitives)
let mkNTUTypeConRef name ntuKind layout =
    { Name = name; Module = []; ParamKinds = []; Layout = layout; NTUKind = Some ntuKind; FieldCount = 0; CaseCount = 0; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a parameterized type constructor with an NTU kind
let mkNTUTypeConRefWithArity name ntuKind typeArity layout =
    { Name = name; Module = []; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = Some ntuKind; FieldCount = 0; CaseCount = 0; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a type constructor for a record type
/// Field info is accessed via SemanticGraph.Types lookup (not embedded in TypeConRef)
let mkRecordTypeConRef name modulePath typeArity layout fieldCount =
    { Name = name; Module = modulePath; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = None; FieldCount = fieldCount; CaseCount = 0; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a type constructor for a record type with pin attributes
let mkRecordTypeConRefWithPins name modulePath typeArity layout fieldCount (pinAttrs: Map<string, string list>) =
    { Name = name; Module = modulePath; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = None; FieldCount = fieldCount; CaseCount = 0; Qualifiers = None; FieldPinAttributes = pinAttrs }

/// Create a type constructor for a discriminated union type
let mkUnionTypeConRef name typeArity layout caseCount =
    { Name = name; Module = []; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = None; FieldCount = 0; CaseCount = caseCount; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a qualified type constructor (same type, different placement)
let withQualifiers (qualifiers: NTUQualifiers) (tycon: TypeConRef) : TypeConRef =
    { tycon with Qualifiers = Some qualifiers }

//-------------------------------------------------------------------------
// Code Labels (for state machine compilation)
//-------------------------------------------------------------------------

/// Code label for state machine compilation (async, task, resumable code).
/// Used in Goto/Label operations.
type CodeLabel = int

//-------------------------------------------------------------------------
// Method and Function References
//-------------------------------------------------------------------------

/// Reference to a method or function in native compilation.
/// Replaces IL method references with native semantics.
[<NoComparison>]
type MethodRef = {
    /// The name of the method
    Name: string
    /// The type that declares this method (None for module-level functions)
    DeclaringType: TypeConRef option
    /// The module path for module-level functions
    DeclaringModule: ModulePath
    /// Generic arity (number of type parameters on the method itself)
    GenericArity: int
    /// Is this an instance method?
    IsInstance: bool
}

/// Create a simple method reference
let mkMethodRef name declaringType isInstance =
    { Name = name; DeclaringType = declaringType; DeclaringModule = []; GenericArity = 0; IsInstance = isInstance }

/// Create a module function reference
let mkFunctionRef name modulePath =
    { Name = name; DeclaringType = None; DeclaringModule = modulePath; GenericArity = 0; IsInstance = false }


//-------------------------------------------------------------------------
// Scope References
//-------------------------------------------------------------------------

/// Reference to a scope/compilation unit in native compilation.
/// Replaces IL scope references with native semantics.
[<RequireQualifiedAccess>]
type ScopeRef =
    /// The current compilation unit
    | Local
    /// Reference to an external module
    | Module of name: string
    /// Reference to an external assembly/library
    | Assembly of name: string
    /// Reference to the primary runtime library (Alloy core)
    | Primary

    member x.Name =
        match x with
        | Local -> "<local>"
        | Module name -> name
        | Assembly name -> name
        | Primary -> "<primary>"

    member x.QualifiedName = x.Name

//-------------------------------------------------------------------------
// Access Modifiers
//-------------------------------------------------------------------------

/// Access modifier for type members in native compilation.
[<RequireQualifiedAccess>]
type MemberAccess =
    | Public
    | Private
    | Internal
    | Assembly
    | Protected
    | FamilyOrAssembly
    | FamilyAndAssembly

/// Access modifier for type definitions in native compilation.
[<RequireQualifiedAccess>]
type TypeAccess =
    | Public
    | Private
    | Nested of MemberAccess

//-------------------------------------------------------------------------
// Type Parameter (with Union-Find support)
//-------------------------------------------------------------------------

/// State of a type parameter in the Union-Find structure
[<RequireQualifiedAccess>]
type TypeParamState =
    /// Not yet bound to anything
    | Unbound
    /// Bound to a type (or another type parameter)
    | Bound of NativeType

/// Type parameter with constraints and Union-Find parent pointer
and [<NoComparison; ReferenceEquality>] TypeParam = {
    /// Unique identifier for this type parameter
    Id: TypeParamId
    /// User-visible name (e.g., "'a", "'T", "'region")
    Name: string
    /// Is this a type parameter or a measure parameter?
    Kind: TypeParamKind
    /// Constraints on this type parameter (populated during checking)
    mutable Constraints: Constraint list
    /// Union-Find parent pointer for efficient substitution
    mutable Parent: TypeParamState
    /// Where this type parameter was introduced
    Range: SourceRange
}

//-------------------------------------------------------------------------
// Constraints
//-------------------------------------------------------------------------

/// Constraints generated during type checking
and [<RequireQualifiedAccess>] Constraint =
    /// Two types must be equal
    | Equals of NativeType * NativeType * SourceRange
    /// Type must have a member with given name and signature (SRTP)
    | HasMember of ty: NativeType * name: string * signature: NativeType * SourceRange
    /// Type must support given measure
    | HasMeasure of NativeType * Measure * SourceRange
    /// Subtype relationship (minimal, for inheritance)
    | Subtype of sub: NativeType * super: NativeType * SourceRange
    /// Type must have compatible memory layout
    | LayoutCompatible of NativeType * TypeLayout * SourceRange
    /// Type application: forall type must instantiate with given args to yield result
    | HasTypeArgs of forallTy: NativeType * args: NativeType list * resultTy: NativeType * SourceRange

//-------------------------------------------------------------------------
// Native Type Representation
//-------------------------------------------------------------------------

/// The core type representation for native compilation.
/// No IL types, no BCL - these are native-first types.
and [<RequireQualifiedAccess; NoComparison>] NativeType =
    /// Polymorphic type: forall 'a 'b. body
    | TForall of typars: TypeParam list * body: NativeType
    
    /// Type application: tycon<arg1, arg2, ...>
    | TApp of tycon: TypeConRef * args: NativeType list
    
    /// Tuple type: T1 * T2 * ... (struct or reference)
    | TTuple of elements: NativeType list * isStruct: bool
    
    /// Function type: domain -> range
    | TFun of domain: NativeType * range: NativeType
    
    /// Type variable (reference to a TypeParam)
    | TVar of typar: TypeParam
    
    /// Unit of measure
    | TMeasure of measure: Measure
    
    /// Anonymous record type: {| field1: T1; field2: T2 |}
    /// isStruct: true for struct anonymous records (value type), false for reference type
    | TAnon of fields: (string * NativeType) list * isStruct: bool

    // Named records are TApp(tyconRef, []) where tyconRef.FieldCount > 0
    // Fields accessed via tryGetRecordFields lookup (ML-family pattern)

    /// Discriminated union type
    | TUnion of tycon: TypeConRef * cases: UnionCase list
    
    /// Byref type: byref<T> or inref<T> or outref<T>
    | TByref of element: NativeType * kind: ByrefKind
    
    /// Native pointer: nativeptr<T>
    | TNativePtr of element: NativeType
    
    /// Lazy computation: Lazy<T>
    /// PRD-14: Deferred computation with memoization
    | TLazy of element: NativeType
    
    /// Sequence type: Seq<T>
    /// PRD-15: Resumable computation producing values on demand
    | TSeq of element: NativeType

    /// Sequence enumerator type: SeqEnumerator<T>
    /// PRD-15/16: State machine for iterating over a seq
    /// This is the mutable iteration state returned by Seq.getEnumerator
    | TSeqEnumerator of element: NativeType

    /// List type: List<T>
    /// PRD-13a: Immutable singly-linked list
    | TList of element: NativeType

    /// Map type: Map<K, V>
    /// PRD-13a: Immutable key-value map (balanced BST)
    | TMap of keyType: NativeType * valueType: NativeType

    /// Set type: Set<T>
    /// PRD-13a: Immutable set (balanced BST)
    | TSet of element: NativeType

    /// Error type (used during recovery from type errors)
    | TError of message: string

//-------------------------------------------------------------------------
// Supporting Types
//-------------------------------------------------------------------------

/// Unit of measure (for dimensional analysis)
and Measure =
    | MOne                                    // Dimensionless
    | MVar of TypeParam                       // Measure variable
    | MProd of Measure * Measure              // Product m1 * m2
    | MInv of Measure                         // Inverse 1/m
    | MCon of name: string * ModulePath       // Named measure (e.g., Meters, Seconds)

/// A case in a discriminated union
and UnionCase = {
    Name: string
    Fields: (string option * NativeType) list  // Optional field names
    Index: int
}

/// Kind of byref
and [<RequireQualifiedAccess>] ByrefKind =
    | In      // inref<T> - read-only
    | Out     // outref<T> - write-only
    | InOut   // byref<T> - read-write

//-------------------------------------------------------------------------
// Literal Values (NTU-typed)
//-------------------------------------------------------------------------

/// Literal value representation, typed by NTU.
/// Consolidates literal representation with the Native Type Universe.
/// The NTUKind specifies which numeric type (int8, int32, float64, etc.).
[<RequireQualifiedAccess>]
type NativeLiteral =
    /// Integer literal with NTU kind specifying width/signedness
    /// Covers: int8, uint8, int16, uint16, int32, uint32, int64, uint64, nativeint, unativeint
    | Int of value: int64 * kind: NTUKind
    /// Unsigned integer literal (for values > int64.MaxValue)
    | UInt of value: uint64 * kind: NTUKind
    /// Floating point literal with NTU kind (float32 or float64)
    | Float of value: float * kind: NTUKind
    /// String literal (UTF-8)
    | String of string
    /// Boolean literal
    | Bool of bool
    /// Character literal (UTF-32 code point)
    | Char of char
    /// Unit literal
    | Unit
    /// Decimal literal (128-bit)
    | Decimal of decimal
    /// Embedded byte array
    | ByteArray of byte[]
    /// Embedded uint16 array (for some string encodings)
    | UInt16Array of uint16[]
    /// Big integer (stored as string for arbitrary precision)
    | BigInt of string

module NativeLiteral =
    /// Get the NTUKind for a literal.
    /// Returns None for compound literals (ByteArray, UInt16Array, BigInt)
    /// that decompose to NTUarray or user-defined composite types.
    let tryKind = function
        | NativeLiteral.Int (_, k) -> Some k
        | NativeLiteral.UInt (_, k) -> Some k
        | NativeLiteral.Float (_, k) -> Some k
        | NativeLiteral.String _ -> Some NTUKind.NTUstring
        | NativeLiteral.Bool _ -> Some NTUKind.NTUbool
        | NativeLiteral.Char _ -> Some NTUKind.NTUchar
        | NativeLiteral.Unit -> Some NTUKind.NTUunit
        | NativeLiteral.Decimal _ -> Some NTUKind.NTUdecimal
        | NativeLiteral.ByteArray _ -> Some NTUKind.NTUarray   // array<uint8>
        | NativeLiteral.UInt16Array _ -> Some NTUKind.NTUarray  // array<uint16>
        | NativeLiteral.BigInt _ -> Some (NTUKind.NTUint (NTUWidth.Fixed 64))  // Maps to int64

    /// Get the NTUKind for a literal (backward-compat; use tryKind for new code)
    let kind lit =
        match tryKind lit with
        | Some k -> k
        | None -> failwith "NativeLiteral.kind: no NTUKind for this literal"

//-------------------------------------------------------------------------
// Closure Capture Information
//-------------------------------------------------------------------------

/// Information about a variable captured by a lambda (closure).
/// Capture analysis is performed during CCS type checking as part of scope resolution.
/// MLKit-style flat closures: immutable bindings captured by value, mutable by reference.
type CaptureInfo = {
    /// Name of the captured variable
    Name: string
    /// Type of the captured variable
    Type: NativeType
    /// Whether the captured variable is mutable (determines ByRef vs ByValue capture)
    IsMutable: bool
    /// NodeId of the binding that defines this variable (for SSA lookup in Alex)
    SourceNodeId: NodeId option
}

//-------------------------------------------------------------------------
// Record Type Infrastructure (for Field Label Resolution)
// Per clef-lang-spec inference-procedures.md: "Field order determines memory layout"
//-------------------------------------------------------------------------

/// A reference to a field in a specific record type.
/// Used in the FieldLabels table for field label resolution.
[<NoComparison>]
type FieldRef = {
    /// The record type this field belongs to
    RecordType: TypeConRef
    /// The field name
    FieldName: string
    /// The field's type
    FieldType: NativeType
    /// Position in declaration order (= memory order), 0-based
    FieldIndex: int
}

/// Complete record type information.
/// Stores fields in declaration order, which determines memory layout.
/// Per spec: "Fidelity makes ALL memory layout decisions - MLIR/LLVM never determine layout."
[<NoComparison; NoEquality>]
type RecordTypeInfo = {
    /// The type constructor (with computed layout)
    TypeCon: TypeConRef
    /// Fields in declaration order (= memory order)
    Fields: (string * NativeType) list
    /// Module path where this record type is defined
    Module: ModulePath
    /// Whether type has [<RequireQualifiedAccess>] attribute
    /// If true, field labels are NOT added to FieldLabels table
    RequireQualifiedAccess: bool
}

//-------------------------------------------------------------------------
// Type Utilities
//-------------------------------------------------------------------------

/// Get the layout of a type (may need refinement after solving)
let rec layoutOf (ty: NativeType) : TypeLayout =
    match ty with
    | NativeType.TApp(tycon, args) ->
        match tycon.Name, tycon.Layout, args with
        // Option<T>: tag (1 byte) + T - compute from type argument
        | "option", TypeLayout.Inline(-1, -1), [innerTy] ->
            let innerLayout = layoutOf innerTy
            match innerLayout with
            | TypeLayout.Inline(innerSize, innerAlign) when innerSize >= 0 ->
                // tag (1 byte) + padding + payload
                let align = max 1 innerAlign
                let tagPadding = if innerAlign > 1 then innerAlign - 1 else 0
                TypeLayout.Inline(1 + tagPadding + innerSize, align)
            | TypeLayout.PlatformWord ->
                // tag + padding + word (8 bytes on 64-bit)
                TypeLayout.Inline(16, 8)
            | TypeLayout.FatPointer ->
                // tag + padding + fat ptr (16 bytes)
                TypeLayout.Inline(24, 8)
            | _ -> tycon.Layout
        // Result<T, E>: tag (1 byte) + max(T, E) - compute from type arguments
        | "result", TypeLayout.Inline(-1, -1), [okTy; errorTy] ->
            let okLayout = layoutOf okTy
            let errorLayout = layoutOf errorTy
            match okLayout, errorLayout with
            | TypeLayout.Inline(okSize, okAlign), TypeLayout.Inline(errSize, errAlign) when okSize >= 0 && errSize >= 0 ->
                let maxPayloadSize = max okSize errSize
                let maxAlign = max okAlign errAlign
                let align = max 1 maxAlign
                let tagPadding = if align > 1 then align - 1 else 0
                TypeLayout.Inline(1 + tagPadding + maxPayloadSize, align)
            | TypeLayout.PlatformWord, _ | _, TypeLayout.PlatformWord ->
                TypeLayout.Inline(16, 8)  // tag + padding + word
            | TypeLayout.FatPointer, _ | _, TypeLayout.FatPointer ->
                TypeLayout.Inline(24, 8)  // tag + padding + fat ptr
            | _ -> tycon.Layout
        | _ -> tycon.Layout
    | NativeType.TTuple(_, isStruct) when isStruct -> TypeLayout.Inline(-1, -1) // Size depends on elements
    | NativeType.TTuple(_, _) -> TypeLayout.Reference ArenaAffinity.CurrentActor
    | NativeType.TFun _ -> TypeLayout.Inline(16, 8)  // Function pointer + closure env
    | NativeType.TVar _ -> TypeLayout.Opaque  // Not yet known
    | NativeType.TNativePtr _ -> TypeLayout.PlatformWord  // Pointer size is platform-dependent
    | NativeType.TByref _ -> TypeLayout.PlatformWord  // Byref size is platform-dependent
    | NativeType.TForall(_, body) -> layoutOf body
    | NativeType.TMeasure _ -> TypeLayout.Inline(0, 1)  // Phantom type
    | NativeType.TAnon(_, isStruct) when isStruct -> TypeLayout.Inline(-1, -1) // Size depends on fields
    | NativeType.TAnon(_, _) -> TypeLayout.Reference ArenaAffinity.CurrentActor
    // Named records use TApp - layout comes from tycon.Layout (handled above)
    | NativeType.TUnion(tycon, _) -> tycon.Layout
    | NativeType.TLazy _ -> TypeLayout.Inline(-1, -1)  // Size depends on element type (PRD-14)
    | NativeType.TSeq _ -> TypeLayout.Inline(-1, -1)  // Size depends on element type (PRD-15)
    | NativeType.TSeqEnumerator _ -> TypeLayout.Inline(-1, -1)  // Size depends on seq state machine (PRD-15/16)
    | NativeType.TList _ -> TypeLayout.PlatformWord  // Pointer to cons cell (PRD-13a)
    | NativeType.TMap _ -> TypeLayout.PlatformWord  // Pointer to tree root (PRD-13a)
    | NativeType.TSet _ -> TypeLayout.PlatformWord  // Pointer to tree root (PRD-13a)
    | NativeType.TError _ -> TypeLayout.Opaque

/// Compute memory layout for a record from its fields.
/// Per clef-lang-spec: "Field order determines memory layout" and
/// "Fidelity makes ALL memory layout decisions - MLIR/LLVM never determine layout."
///
/// Algorithm (from spec inference-procedures.md Step 4):
/// 1. For each field in declaration order, compute offset with padding for alignment
/// 2. Total layout = (sum of sizes + padding, max alignment)
/// Compute record layout from field types.
/// Uses 64-bit (8-byte word size) as the compilation target.
/// ARCHITECTURAL NOTE: Fidelity targets 64-bit platforms exclusively.
/// This is a deliberate design choice, not a limitation to be worked around.
let computeRecordLayout (fields: (string * NativeType) list) : TypeLayout =
    // 64-bit platform constants
    let wordSize = 8
    let wordAlign = 8

    let folder (offset, maxAlign) (_, fieldType) =
        let fieldLayout = TypeLayout.baseLayout (layoutOf fieldType)
        match fieldLayout with
        | TypeLayout.Inline(size, align) when size >= 0 && align > 0 ->
            // Known inline size - add padding for alignment
            let pad =
                let remainder = offset % align
                if remainder = 0 then 0 else align - remainder
            let paddedOffset = offset + pad
            (paddedOffset + size, max maxAlign align)
        | TypeLayout.Inline _ ->
            // Size or alignment is unknown (-1), propagate unknown
            (-1, -1)
        | TypeLayout.Opaque ->
            // Truly unknown at compile time - can't compute exact layout
            (-1, -1)
        | TypeLayout.PlatformWord ->
            // nativeint, nativeptr - word-sized on 64-bit platform
            let pad =
                let remainder = offset % wordAlign
                if remainder = 0 then 0 else wordAlign - remainder
            let paddedOffset = offset + pad
            (paddedOffset + wordSize, max maxAlign wordAlign)
        | TypeLayout.FatPointer ->
            // Fat pointer = {ptr, len} = 2 words on 64-bit
            let fatPtrSize = 2 * wordSize
            let pad =
                let remainder = offset % wordAlign
                if remainder = 0 then 0 else wordAlign - remainder
            let paddedOffset = offset + pad
            (paddedOffset + fatPtrSize, max maxAlign wordAlign)
        | TypeLayout.NTUCompound count ->
            // NTU compound = n words on 64-bit (e.g., tuple of nativeints)
            let compoundSize = count * wordSize
            let pad =
                let remainder = offset % wordAlign
                if remainder = 0 then 0 else wordAlign - remainder
            let paddedOffset = offset + pad
            (paddedOffset + compoundSize, max maxAlign wordAlign)
        | TypeLayout.Reference _ ->
            // Reference types are pointer-sized (8 bytes on 64-bit)
            let pad =
                let remainder = offset % wordAlign
                if remainder = 0 then 0 else wordAlign - remainder
            let paddedOffset = offset + pad
            (paddedOffset + wordSize, max maxAlign wordAlign)
        | TypeLayout.Qualified _ ->
            // Defensive: baseLayout should have stripped this, but handle for exhaustiveness
            failwith "computeRecordLayout: Qualified layout should have been unwrapped by baseLayout"

    let (totalSize, maxAlign) = List.fold folder (0, 1) fields

    if totalSize < 0 || maxAlign < 0 then
        // Some field has unknown size - layout is opaque
        TypeLayout.Opaque
    else
        // Final padding for struct alignment
        let finalPad =
            if maxAlign > 0 then
                let remainder = totalSize % maxAlign
                if remainder = 0 then 0 else maxAlign - remainder
            else 0
        TypeLayout.Inline(totalSize + finalPad, maxAlign)

/// Check if a type is a function type
let isFunctionType = function
    | NativeType.TFun _ -> true
    | _ -> false

/// Check if a type is a type variable
let isTypeVar = function
    | NativeType.TVar _ -> true
    | _ -> false

/// Create a simple type (no type arguments)
let mkSimpleType tycon = NativeType.TApp(tycon, [])

/// Create a function type with multiple arguments
let rec mkFunctionType args result =
    match args with
    | [] -> result
    | [arg] -> NativeType.TFun(arg, result)
    | arg :: rest -> NativeType.TFun(arg, mkFunctionType rest result)


/// Integer powers use a shared product tree, avoiding expansion proportional to the exponent.
let rec measurePower (measure: Measure) (exponent: bigint) : Measure =
    if exponent < 0I then MInv(measurePower measure -exponent)
    elif exponent = 0I then MOne
    elif exponent = 1I then measure
    else
        let half = measurePower measure (exponent / 2I)
        let square = MProd(half, half)
        if exponent % 2I = 0I then square else MProd(measure, square)

/// Abelian-group normal form: named atoms (including their module) and variables
/// have signed integer exponents. Substitutions are followed before cancellation.
let measureFactors (measure: Measure) =
    let rec collect exponent factors measure =
        let add key atom =
            let previous = Map.tryFind key factors |> Option.map snd |> Option.defaultValue 0I
            let total = previous + exponent
            if total = 0I then Map.remove key factors else Map.add key (atom, total) factors
        match measure with
        | MOne -> factors
        | MCon(name, path) -> add (Choice1Of2(path, name)) measure
        | MVar tp ->
            match tp.Parent with
            | TypeParamState.Unbound -> add (Choice2Of2 tp.Id) measure
            | TypeParamState.Bound(NativeType.TMeasure bound) -> collect exponent factors bound
            | TypeParamState.Bound(NativeType.TVar other) -> collect exponent factors (MVar other)
            | _ -> invalidOp "A measure parameter is bound to an ordinary type"
        | MInv inner -> collect -exponent factors inner
        | MProd(left, right) ->
            if obj.ReferenceEquals(left, right) then collect (2I * exponent) factors left
            else collect exponent (collect exponent factors left) right
    collect 1I Map.empty measure

let measureFromFactors factors =
    factors |> Map.fold (fun product _ (atom, exponent) ->
        let factor = measurePower atom exponent
        match product with MOne -> factor | _ -> MProd(product, factor)) MOne

let normalizeMeasure measure = measure |> measureFactors |> measureFromFactors

/// Numeric kind identity is unchanged when a measure is attached. Representation
/// selection is separate; no width or representation is introduced by this operation.
let withMeasure (ty: NativeType) (measure: Measure) =
    match ty with
    | NativeType.TApp(tc, []) when tc.Name = "int" || tc.Name = "float" ->
        NativeType.TApp({ tc with ParamKinds = [TypeParamKind.Measure] }, [NativeType.TMeasure(normalizeMeasure measure)])
    | _ -> NativeType.TError "Expected an integer or real kind for a measured value"

/// Substitute type arguments into a forall type
let instantiate (typars: TypeParam list) (args: NativeType list) (body: NativeType) : NativeType =
    if List.length typars <> List.length args then
        failwith $"instantiate: arity mismatch - expected {List.length typars} args, got {List.length args}"
    
    let subst = List.zip typars args |> dict
    
    let rec go ty =
        match ty with
        | NativeType.TVar tp when subst.ContainsKey tp -> subst.[tp]
        | NativeType.TVar _ -> ty
        | NativeType.TApp(tc, args) -> NativeType.TApp(tc, List.map go args)
        | NativeType.TFun(d, r) -> NativeType.TFun(go d, go r)
        | NativeType.TTuple(elems, isStruct) -> NativeType.TTuple(List.map go elems, isStruct)
        | NativeType.TForall(tps, body) -> NativeType.TForall(tps, go body)  // Capture-avoiding?
        | NativeType.TByref(elem, kind) -> NativeType.TByref(go elem, kind)
        | NativeType.TNativePtr elem -> NativeType.TNativePtr(go elem)
        | NativeType.TAnon(fields, isStruct) -> NativeType.TAnon(fields |> List.map (fun (n, t) -> (n, go t)), isStruct)
        // Named records use TApp - handled above (type args substituted)
        | NativeType.TUnion(tc, cases) ->
            NativeType.TUnion(tc, cases |> List.map (fun c ->
                { c with Fields = c.Fields |> List.map (fun (n, t) -> (n, go t)) }))
        | NativeType.TLazy elem -> NativeType.TLazy(go elem)  // PRD-14
        | NativeType.TSeq elem -> NativeType.TSeq(go elem)  // PRD-15
        | NativeType.TSeqEnumerator elem -> NativeType.TSeqEnumerator(go elem)  // PRD-15/16
        | NativeType.TList elem -> NativeType.TList(go elem)  // PRD-13a
        | NativeType.TMap(k, v) -> NativeType.TMap(go k, go v)  // PRD-13a
        | NativeType.TSet elem -> NativeType.TSet(go elem)  // PRD-13a
        | NativeType.TMeasure measure -> NativeType.TMeasure(goMeasure measure)
        | NativeType.TError _ -> ty

    and goMeasure measure =
        measureFactors measure |> Map.fold (fun product _ (atom, exponent) ->
            let replacement =
                match atom with
                | MVar tp when subst.ContainsKey tp ->
                    match subst.[tp] with
                    | NativeType.TMeasure replacement -> replacement
                    | NativeType.TVar replacement when replacement.Kind = TypeParamKind.Measure -> MVar replacement
                    | _ -> invalidArg "args" "Expected a measure argument"
                | _ -> atom
            MProd(product, measurePower replacement exponent)) MOne |> normalizeMeasure
    
    go body

//-------------------------------------------------------------------------
// Pretty Printing
//-------------------------------------------------------------------------

/// Format a type for display
let rec formatType (ty: NativeType) : string =
    match ty with
    | NativeType.TVar tp -> tp.Name
    | NativeType.TApp(tc, []) -> tc.Name
    | NativeType.TApp(tc, [NativeType.TMeasure measure]) -> $"{tc.Name}<{formatMeasure measure}>"
    | NativeType.TApp(tc, [arg]) -> $"{formatType arg} {tc.Name}"
    | NativeType.TApp(tc, args) -> 
        let argsStr = args |> List.map formatType |> String.concat ", "
        $"{tc.Name}<{argsStr}>"
    | NativeType.TFun(d, r) -> 
        let dStr = match d with NativeType.TFun _ -> $"({formatType d})" | _ -> formatType d
        $"{dStr} -> {formatType r}"
    | NativeType.TTuple(elems, true) -> 
        "struct (" + (elems |> List.map formatType |> String.concat " * ") + ")"
    | NativeType.TTuple(elems, false) -> 
        elems |> List.map formatType |> String.concat " * "
    | NativeType.TForall(tps, body) ->
        let tpsStr = tps |> List.map (fun tp -> tp.Name) |> String.concat " "
        $"forall {tpsStr}. {formatType body}"
    | NativeType.TByref(elem, ByrefKind.In) -> $"inref<{formatType elem}>"
    | NativeType.TByref(elem, ByrefKind.Out) -> $"outref<{formatType elem}>"
    | NativeType.TByref(elem, ByrefKind.InOut) -> $"byref<{formatType elem}>"
    | NativeType.TNativePtr elem -> $"nativeptr<{formatType elem}>"
    | NativeType.TMeasure m -> formatMeasure m
    | NativeType.TAnon(fields, isStruct) ->
        let fieldsStr = fields |> List.map (fun (n, t) -> $"{n}: {formatType t}") |> String.concat "; "
        if isStruct then $"struct {{| {fieldsStr} |}}" else $"{{| {fieldsStr} |}}"
    // Named records use TApp - formatted above (just shows type name)
    | NativeType.TUnion(tc, _) -> tc.Name
    | NativeType.TLazy elem -> $"Lazy<{formatType elem}>"  // PRD-14
    | NativeType.TSeq elem -> $"seq<{formatType elem}>"  // PRD-15
    | NativeType.TSeqEnumerator elem -> $"SeqEnumerator<{formatType elem}>"  // PRD-15/16
    | NativeType.TList elem -> $"List<{formatType elem}>"  // PRD-13a
    | NativeType.TMap(k, v) -> $"Map<{formatType k}, {formatType v}>"  // PRD-13a
    | NativeType.TSet elem -> $"Set<{formatType elem}>"  // PRD-13a
    | NativeType.TError msg -> $"<error: {msg}>"

and formatMeasure (m: Measure) : string =
    let factors = measureFactors m |> Map.toList |> List.map (fun (_, (atom, exponent)) ->
        let order, name =
            match atom with
            | MVar tp -> 0, tp.Name
            | MCon(name, path) -> 1, String.concat "." (path @ [name])
            | _ -> invalidOp "Expected an atomic measure in normal form"
        order, name, exponent) |> List.sortBy (fun (order, name, _) -> order, name)
    let render factors =
        factors |> List.map (fun (_, name, exponent) ->
            let power = abs exponent
            if power = 1I then name else $"{name}^{power}") |> String.concat " "
    let positive, negative = factors |> List.partition (fun (_, _, exponent) -> exponent > 0I)
    let numerator = if positive.IsEmpty then "1" else render positive
    if negative.IsEmpty then numerator else $"{numerator}/({render negative})"

//-------------------------------------------------------------------------
// Standard Types Module (NTU-based type definitions)
//-------------------------------------------------------------------------

/// Standard type definitions for native compilation.
/// These are the canonical type values used throughout the compiler.
module Types =
    // Type constructors for primitive types (NTU kinds)
    // Platform-dependent types use PlatformWord layout (size resolved by Alex)
    let intTyCon = mkNTUTypeConRef "int" (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)) TypeLayout.PlatformWord
    // Fixed-width types use Inline layout with known sizes
    let int8TyCon = mkNTUTypeConRef "int8" (NTUKind.NTUint (NTUWidth.Fixed 8)) (TypeLayout.Inline(1, 1))
    let int16TyCon = mkNTUTypeConRef "int16" (NTUKind.NTUint (NTUWidth.Fixed 16)) (TypeLayout.Inline(2, 2))
    let int32TyCon = mkNTUTypeConRef "int32" (NTUKind.NTUint (NTUWidth.Fixed 32)) (TypeLayout.Inline(4, 4))
    let int64TyCon = mkNTUTypeConRef "int64" (NTUKind.NTUint (NTUWidth.Fixed 64)) (TypeLayout.Inline(8, 8))
    // Platform-dependent unsigned
    let uintTyCon = mkNTUTypeConRef "uint" (NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register)) TypeLayout.PlatformWord
    // Fixed-width unsigned
    let uint8TyCon = mkNTUTypeConRef "uint8" (NTUKind.NTUuint (NTUWidth.Fixed 8)) (TypeLayout.Inline(1, 1))
    let uint16TyCon = mkNTUTypeConRef "uint16" (NTUKind.NTUuint (NTUWidth.Fixed 16)) (TypeLayout.Inline(2, 2))
    let uint32TyCon = mkNTUTypeConRef "uint32" (NTUKind.NTUuint (NTUWidth.Fixed 32)) (TypeLayout.Inline(4, 4))
    let uint64TyCon = mkNTUTypeConRef "uint64" (NTUKind.NTUuint (NTUWidth.Fixed 64)) (TypeLayout.Inline(8, 8))
    // Native pointer-sized integers (always platform-dependent)
    let nintTyCon = mkNTUTypeConRef "nativeint" (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer)) TypeLayout.PlatformWord
    let unintTyCon = mkNTUTypeConRef "unativeint" (NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer)) TypeLayout.PlatformWord
    let float32TyCon = mkNTUTypeConRef "float32" (NTUKind.NTUfloat (NTUWidth.Fixed 32)) (TypeLayout.Inline(4, 4))
    let floatTyCon = mkNTUTypeConRef "float" (NTUKind.NTUfloat (NTUWidth.Fixed 64)) (TypeLayout.Inline(8, 8))

    // Posit numeric types (Gustafson Type III Unum)
    // es = exponent field size: determines dynamic range vs precision tradeoff
    let posit8TyCon = mkNTUTypeConRef "posit8" (NTUKind.NTUposit (NTUWidth.Fixed 8, 0)) (TypeLayout.Inline(1, 1))
    let posit16TyCon = mkNTUTypeConRef "posit16" (NTUKind.NTUposit (NTUWidth.Fixed 16, 1)) (TypeLayout.Inline(2, 2))
    let posit32TyCon = mkNTUTypeConRef "posit32" (NTUKind.NTUposit (NTUWidth.Fixed 32, 2)) (TypeLayout.Inline(4, 4))
    let posit64TyCon = mkNTUTypeConRef "posit64" (NTUKind.NTUposit (NTUWidth.Fixed 64, 3)) (TypeLayout.Inline(8, 8))

    let boolTyCon = mkNTUTypeConRef "bool" NTUKind.NTUbool (TypeLayout.Inline(1, 1))
    let charTyCon = mkNTUTypeConRef "char" NTUKind.NTUchar (TypeLayout.Inline(4, 4))
    let unitTyCon = mkNTUTypeConRef "unit" NTUKind.NTUunit (TypeLayout.Inline(0, 1))
    let stringTyCon = mkNTUTypeConRef "string" NTUKind.NTUstring TypeLayout.Opaque
    let decimalTyCon = mkNTUTypeConRef "decimal" NTUKind.NTUdecimal (TypeLayout.Inline(16, 8))
    let voidptrTyCon = mkNTUTypeConRef "voidptr" NTUKind.NTUptr (TypeLayout.Inline(8, 8))
    
    // Array type constructor (arity 1, fat pointer layout)
    // C-04: No helper function - use TApp(arrayTyCon, [elemType]) directly
    let arrayTyCon = mkNTUTypeConRefWithArity "array" NTUKind.NTUarray 1 TypeLayout.FatPointer

    // Option type constructor (arity 1) - no specialized DU case, uses TApp
    // Usage: NativeType.TApp(Types.optionTyCon, [elemType])
    let optionTyCon = mkTypeConRef "option" 1 (TypeLayout.Inline(-1, -1))

    // Standard type values
    let intType = mkSimpleType intTyCon
    let int8Type = mkSimpleType int8TyCon
    let int16Type = mkSimpleType int16TyCon
    let int32Type = mkSimpleType int32TyCon
    let int64Type = mkSimpleType int64TyCon
    let uintType = mkSimpleType uintTyCon
    let uint8Type = mkSimpleType uint8TyCon
    let uint16Type = mkSimpleType uint16TyCon
    let uint32Type = mkSimpleType uint32TyCon
    let uint64Type = mkSimpleType uint64TyCon
    let nintType = mkSimpleType nintTyCon
    let unintType = mkSimpleType unintTyCon
    let float32Type = mkSimpleType float32TyCon
    let floatType = mkSimpleType floatTyCon
    let posit8Type = mkSimpleType posit8TyCon
    let posit16Type = mkSimpleType posit16TyCon
    let posit32Type = mkSimpleType posit32TyCon
    let posit64Type = mkSimpleType posit64TyCon
    let boolType = mkSimpleType boolTyCon
    let charType = mkSimpleType charTyCon
    let unitType = mkSimpleType unitTyCon
    let stringType = mkSimpleType stringTyCon
    let decimalType = mkSimpleType decimalTyCon

    // ValueOption type constructor (arity 1)
    // Usage: NativeType.TApp(Types.voptionTyCon, [elemType])
    let voptionTyCon = mkTypeConRef "ValueOption" 1 (TypeLayout.Inline(-1, -1))

    // FnPtr type constructor (arity 1)
    // Usage: NativeType.TApp(Types.fnPtrTyCon, [funcType])
    let fnPtrTyCon = mkNTUTypeConRefWithArity "FnPtr" NTUKind.NTUfnptr 1 (TypeLayout.Inline(8, 8))

    // Arena type constructor (arity 1 - lifetime measure parameter)
    // Usage: NativeType.TApp(Types.arenaTyCon, [lifetimeMeasure])
    // Layout: fat pointer (ptr to memory region + remaining size)
    let arenaTyCon = mkTypeConRef "Arena" 1 TypeLayout.FatPointer

    // Expr type constructor (arity 1 - for quoted expressions)
    // Usage: NativeType.TApp(Types.exprTyCon, [innerType])
    let exprTyCon = mkTypeConRef "Expr" 1 (TypeLayout.Inline(-1, -1))

    /// Construct array<'T> type
    let mkArrayType elemType =
        NativeType.TApp(arrayTyCon, [elemType])

    /// Construct Lazy<'T> type
    let mkLazyType elemType =
        NativeType.TLazy elemType

    /// Construct seq<'T> type
    let mkSeqType elemType =
        NativeType.TSeq elemType

    /// Construct Expr<'T> type (quotation)
    let mkExprType exprType =
        NativeType.TApp(exprTyCon, [exprType])

    /// Try to extract NTUKind from a NativeType (for use with NTUKind predicates)
    let tryGetNTUKind (ty: NativeType) : NTUKind option =
        match ty with
        | NativeType.TApp(tycon, _) -> tycon.NTUKind
        | _ -> None

    /// Check if a type is numeric (integer or float)
    let isNumericType (ty: NativeType) : bool =
        match tryGetNTUKind ty with
        | Some kind -> NTUKind.isNumeric kind
        | None -> false

    /// Check if a type is an integer (signed or unsigned)
    let isIntegerType (ty: NativeType) : bool =
        match tryGetNTUKind ty with
        | Some kind -> NTUKind.isInteger kind
        | None -> false

    /// Check if a type is a floating point type
    let isFloatType (ty: NativeType) : bool =
        match tryGetNTUKind ty with
        | Some kind -> NTUKind.isFloatingPoint kind
        | None -> false

    /// Check if a type is the string type
    let isStringType (ty: NativeType) : bool =
        match tryGetNTUKind ty with
        | Some NTUKind.NTUstring -> true
        | _ -> false

// Re-export for convenience
let voidptrTyCon = Types.voidptrTyCon

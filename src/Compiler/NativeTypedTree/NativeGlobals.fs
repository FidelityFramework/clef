// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Built-in types with native semantics.
/// These define the type universe for native F# compilation.
///
/// KEY DESIGN: Units of measure work on ANY type in fsnative (not just numerics).
/// This enables memory region tracking, access control, and type-safe hardware access.
module FSharp.Native.Compiler.NativeTypedTree.NativeGlobals

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes

//-------------------------------------------------------------------------
// Memory Region Measures
//-------------------------------------------------------------------------

/// Memory region measures - track where data lives.
/// These are measure types that can be applied to pointers and references.
module MemoryRegions =
    /// Stack memory - automatically freed on scope exit
    let stack = MCon("stack", ["Fidelity"; "Memory"])

    /// Arena/heap memory - managed by allocator
    let arena = MCon("arena", ["Fidelity"; "Memory"])

    /// SRAM - fast on-chip RAM (embedded)
    let sram = MCon("sram", ["Fidelity"; "Memory"])

    /// Flash memory - persistent storage (embedded)
    let flash = MCon("flash", ["Fidelity"; "Memory"])

    /// Peripheral memory - memory-mapped I/O registers
    let peripheral = MCon("peripheral", ["Fidelity"; "Memory"])

    /// DMA memory - accessible by DMA controller
    let dma = MCon("dma", ["Fidelity"; "Memory"])

    /// External memory (e.g., off-chip SDRAM)
    let external' = MCon("external", ["Fidelity"; "Memory"])

//-------------------------------------------------------------------------
// Access Mode Measures
//-------------------------------------------------------------------------

/// Access mode measures - track read/write permissions.
/// Applied to pointers to enforce access control at compile time.
module AccessModes =
    /// Read-only access
    let readOnly = MCon("ro", ["Fidelity"; "Access"])

    /// Write-only access
    let writeOnly = MCon("wo", ["Fidelity"; "Access"])

    /// Read-write access
    let readWrite = MCon("rw", ["Fidelity"; "Access"])

//-------------------------------------------------------------------------
// Built-in Type Constructors
//-------------------------------------------------------------------------

/// Primitive type constructors (arity 0)
/// 
/// KEY DESIGN: Following ML/Rust/Triton patterns, not BCL/F#
/// - `int` = platform word (64-bit on x86_64), NOT 32-bit like F#
/// - `int32` = fixed 32-bit integer
/// - See memory: ml_integer_type_patterns
///
/// NTU INTEGRATION: Each primitive now carries its NTUKind for type identity.
/// Type identity: NTUint ≠ NTUint64 even if same width on some platforms.
/// Width is resolved by Alex via platform quotations.
module Primitives =
    /// UTF-8 string: fat pointer (ptr + length, both platform-word sized)
    /// Resolved by Alex: 16 bytes on x86_64, 8 bytes on ARM32
    let stringTyCon = mkNTUTypeConRef "string" NTUKind.NTUstring TypeLayout.FatPointer
    
    /// Platform word signed integer - native `int` type
    /// NOTE: Fidelity uses `int` = platform word (ML/Rust semantics)
    /// This is 64-bit on x86_64, unlike F#'s 32-bit `int`
    /// For fixed 32-bit, use `int32`
    let intTyCon = mkNTUTypeConRef "int" NTUKind.NTUint TypeLayout.PlatformWord

    /// 32-bit signed integer - fixed width
    /// Use this when you need exactly 32 bits (interop, serialization)
    let int32TyCon = mkNTUTypeConRef "int32" NTUKind.NTUint32 (TypeLayout.Inline(4, 4))

    /// 64-bit signed integer (fixed size, not platform-dependent)
    let int64TyCon = mkNTUTypeConRef "int64" NTUKind.NTUint64 (TypeLayout.Inline(8, 8))

    /// Platform word unsigned integer - native `uint` type
    /// This is 64-bit on x86_64, unlike F#'s 32-bit `uint`
    let uintTyCon = mkNTUTypeConRef "uint" NTUKind.NTUuint TypeLayout.PlatformWord

    /// 32-bit unsigned integer - fixed width
    /// Use this when you need exactly 32 bits (interop, serialization)
    let uint32TyCon = mkNTUTypeConRef "uint32" NTUKind.NTUuint32 (TypeLayout.Inline(4, 4))
    
    /// 64-bit unsigned integer (fixed size, not platform-dependent)
    let uint64TyCon = mkNTUTypeConRef "uint64" NTUKind.NTUuint64 (TypeLayout.Inline(8, 8))
    
    /// 8-bit signed integer
    let int8TyCon = mkNTUTypeConRef "int8" NTUKind.NTUint8 (TypeLayout.Inline(1, 1))
    
    /// 8-bit unsigned integer
    let uint8TyCon = mkNTUTypeConRef "uint8" NTUKind.NTUuint8 (TypeLayout.Inline(1, 1))
    
    /// 16-bit signed integer
    let int16TyCon = mkNTUTypeConRef "int16" NTUKind.NTUint16 (TypeLayout.Inline(2, 2))
    
    /// 16-bit unsigned integer
    let uint16TyCon = mkNTUTypeConRef "uint16" NTUKind.NTUuint16 (TypeLayout.Inline(2, 2))
    
    /// Native-size signed integer (explicit `nativeint` in source)
    /// NOTE: Semantically equivalent to `int` (both = platform word)
    /// Kept separate for explicit nativeint references in F# source
    let nintTyCon = mkNTUTypeConRef "nativeint" NTUKind.NTUnint TypeLayout.PlatformWord
    
    /// Native-size unsigned integer (explicit `unativeint` in source)
    /// NOTE: Semantically equivalent to `uint` (both = platform word)
    let unintTyCon = mkNTUTypeConRef "unativeint" NTUKind.NTUunint TypeLayout.PlatformWord
    
    /// 64-bit floating point (IEEE 754 double)
    let floatTyCon = mkNTUTypeConRef "float" NTUKind.NTUfloat64 (TypeLayout.Inline(8, 8))
    
    /// 32-bit floating point (IEEE 754 single)
    let float32TyCon = mkNTUTypeConRef "float32" NTUKind.NTUfloat32 (TypeLayout.Inline(4, 4))
    
    /// Boolean: 1 byte
    let boolTyCon = mkNTUTypeConRef "bool" NTUKind.NTUbool (TypeLayout.Inline(1, 1))
    
    /// Unicode code point (UTF-32): 4 bytes
    let charTyCon = mkNTUTypeConRef "char" NTUKind.NTUchar (TypeLayout.Inline(4, 4))
    
    /// Unit type: zero-sized type
    let unitTyCon = mkNTUTypeConRef "unit" NTUKind.NTUunit (TypeLayout.Inline(0, 1))
    
    /// Decimal: 16 bytes
    let decimalTyCon = mkNTUTypeConRef "decimal" NTUKind.NTUdecimal (TypeLayout.Inline(16, 8))
    
    /// UUID: 128-bit identifier (RFC 4122)
    /// Platform entropy source for generation (getrandom/BCryptGenRandom)
    let uuidTyCon = mkNTUTypeConRef "Uuid" NTUKind.NTUuuid (TypeLayout.Inline(16, 8))
    
    /// DateTime: 64-bit ticks since epoch
    /// Platform clock resolution via quotations
    let dateTimeTyCon = mkNTUTypeConRef "DateTime" NTUKind.NTUdatetime (TypeLayout.Inline(8, 8))
    
    /// TimeSpan: 64-bit duration in ticks
    let timeSpanTyCon = mkNTUTypeConRef "TimeSpan" NTUKind.NTUtimespan (TypeLayout.Inline(8, 8))

    /// Exception type: native exception representation
    /// Layout: tagged union with string message + optional data
    /// NTUKind.NTUother since exn is not a primitive NTU kind
    let exnTyCon = mkTypeConRef "exn" 0 (TypeLayout.Reference ArenaAffinity.CurrentActor)

    /// NTUKind type: the native type universe kind tags
    /// This is exposed to user code so BAREWire etc. can reference type kinds
    /// Layout: single byte tag (enum-like)
    let ntuKindTyCon = mkTypeConRef "NTUKind" 0 (TypeLayout.Inline(1, 1))

    /// PlatformContext type: compiler platform configuration
    /// This is exposed to user code for platform-specific type resolution.
    /// Layout: opaque record (treated as reference for simplicity)
    let platformContextTyCon = mkTypeConRef "PlatformContext" 0 (TypeLayout.Reference ArenaAffinity.CurrentActor)

/// Parameterized type constructors (arity > 0)
module Parameterized =
    /// Option type: VALUE TYPE (not reference!)
    /// Layout: tag (1 byte) + padding + value
    /// Size depends on 'T
    let optionTyCon = mkTypeConRef "option" 1 (TypeLayout.Inline(-1, -1))

    /// Value option type: explicitly value-typed option
    let voptionTyCon = mkTypeConRef "voption" 1 (TypeLayout.Inline(-1, -1))

    /// Result type: VALUE TYPE
    /// Either Ok of 'T or Error of 'TError
    let resultTyCon = mkTypeConRef "result" 2 (TypeLayout.Inline(-1, -1))

    /// Array type: fat pointer (ptr + length, both platform-word sized)
    /// Resolved by Alex: 16 bytes on x86_64, 8 bytes on ARM32
    let arrayTyCon = mkTypeConRef "array" 1 TypeLayout.FatPointer

    /// List type: linked list (arena-allocated nodes)
    let listTyCon = mkTypeConRef "list" 1 (TypeLayout.Reference ArenaAffinity.CurrentActor)

    /// Sequence type: lazy enumeration
    let seqTyCon = mkTypeConRef "seq" 1 (TypeLayout.Reference ArenaAffinity.CurrentActor)

    /// Reference cell type: mutable reference
    let refTyCon = mkTypeConRef "ref" 1 (TypeLayout.Reference ArenaAffinity.CurrentActor)

    /// Lazy type: deferred computation
    let lazyTyCon = mkTypeConRef "lazy" 1 (TypeLayout.Reference ArenaAffinity.CurrentActor)

    /// Quotation type: Expr<'T> (code-as-data)
    let exprTyCon = mkTypeConRef "Expr" 1 (TypeLayout.Reference ArenaAffinity.CurrentActor)

    //-------------------------------------------------------------------------
    // Pointer Types with Memory Region and Access Measures
    //-------------------------------------------------------------------------

    /// Native pointer with region and access measures: Ptr<'T, 'region, 'access>
    /// This is the core abstraction for type-safe memory access.
    /// 'region: where the memory lives (stack, arena, peripheral, etc.)
    /// 'access: what operations are allowed (ro, wo, rw)
    let ptrTyCon =
        mkTypeConRefWithMeasures "Ptr"
            [TypeParamKind.Type; TypeParamKind.Measure; TypeParamKind.Measure]
            (TypeLayout.Inline(8, 8))

    /// Read-only reference with region measure: Ref<'T, 'region>
    /// Like byref but with region tracking
    let refWithRegionTyCon =
        mkTypeConRefWithMeasures "Ref"
            [TypeParamKind.Type; TypeParamKind.Measure]
            (TypeLayout.Inline(8, 8))

    /// Span with region and access measures: Span<'T, 'region, 'access>
    /// Fat pointer (ptr + length, both platform-word sized) with memory safety
    /// Resolved by Alex: 16 bytes on x86_64, 8 bytes on ARM32
    let spanTyCon =
        mkTypeConRefWithMeasures "Span"
            [TypeParamKind.Type; TypeParamKind.Measure; TypeParamKind.Measure]
            TypeLayout.FatPointer

    /// ReadOnlySpan with region measure: ReadOnlySpan<'T, 'region>
    /// Immutable view - fat pointer (ptr + length, both platform-word sized)
    /// Resolved by Alex: 16 bytes on x86_64, 8 bytes on ARM32
    let readOnlySpanTyCon =
        mkTypeConRefWithMeasures "ReadOnlySpan"
            [TypeParamKind.Type; TypeParamKind.Measure]
            TypeLayout.FatPointer

//-------------------------------------------------------------------------
// Built-in Types (pre-constructed)
//-------------------------------------------------------------------------

/// Pre-constructed types for common use
/// Following ML/Rust patterns: int = platform word, int32 = fixed 32-bit
module Types =
    let stringType = mkSimpleType Primitives.stringTyCon
    let intType = mkSimpleType Primitives.intTyCon     // int = platform word (64-bit on x86_64)
    let int32Type = mkSimpleType Primitives.int32TyCon // Fixed 32-bit
    let int64Type = mkSimpleType Primitives.int64TyCon // Fixed 64-bit
    let uintType = mkSimpleType Primitives.uintTyCon   // uint = platform word (64-bit on x86_64)
    let uint32Type = mkSimpleType Primitives.uint32TyCon // Fixed 32-bit
    let uint64Type = mkSimpleType Primitives.uint64TyCon // Fixed 64-bit
    let int8Type = mkSimpleType Primitives.int8TyCon
    let uint8Type = mkSimpleType Primitives.uint8TyCon
    let int16Type = mkSimpleType Primitives.int16TyCon
    let uint16Type = mkSimpleType Primitives.uint16TyCon
    let nintType = mkSimpleType Primitives.nintTyCon   // nativeint = int (platform word), separate for explicit references
    let unintType = mkSimpleType Primitives.unintTyCon // unativeint = uint (platform word), separate for explicit references
    let floatType = mkSimpleType Primitives.floatTyCon
    let float32Type = mkSimpleType Primitives.float32TyCon
    let boolType = mkSimpleType Primitives.boolTyCon
    let charType = mkSimpleType Primitives.charTyCon
    let unitType = mkSimpleType Primitives.unitTyCon
    let decimalType = mkSimpleType Primitives.decimalTyCon
    let uuidType = mkSimpleType Primitives.uuidTyCon
    let dateTimeType = mkSimpleType Primitives.dateTimeTyCon
    let timeSpanType = mkSimpleType Primitives.timeSpanTyCon
    let exnType = mkSimpleType Primitives.exnTyCon
    let ntuKindType = mkSimpleType Primitives.ntuKindTyCon  // NTUKind type for type universe tags
    let platformContextType = mkSimpleType Primitives.platformContextTyCon  // PlatformContext for platform-specific resolution

//-------------------------------------------------------------------------
// Type Constructor Lookup
//-------------------------------------------------------------------------

/// Map from type names to their constructors
let private primitiveTyConsByName =
    [ ("string", Primitives.stringTyCon)
      ("int", Primitives.intTyCon)       // Platform word (isize)
      ("int32", Primitives.int32TyCon)   // Fixed 32-bit (distinct from int!)
      ("int64", Primitives.int64TyCon)   // Fixed 64-bit
      ("uint", Primitives.uintTyCon)     // Platform word (usize)
      ("uint32", Primitives.uint32TyCon) // Fixed 32-bit (distinct from uint!)
      ("uint64", Primitives.uint64TyCon) // Fixed 64-bit
      ("int8", Primitives.int8TyCon)
      ("sbyte", Primitives.int8TyCon)  // Alias
      ("uint8", Primitives.uint8TyCon)
      ("byte", Primitives.uint8TyCon)  // Alias
      ("int16", Primitives.int16TyCon)
      ("uint16", Primitives.uint16TyCon)
      ("nativeint", Primitives.nintTyCon)
      ("unativeint", Primitives.unintTyCon)
      ("float", Primitives.floatTyCon)
      ("double", Primitives.floatTyCon)  // Alias
      ("float32", Primitives.float32TyCon)
      ("single", Primitives.float32TyCon)  // Alias
      ("bool", Primitives.boolTyCon)
      ("char", Primitives.charTyCon)
      ("unit", Primitives.unitTyCon)
      ("decimal", Primitives.decimalTyCon)
      ("Uuid", Primitives.uuidTyCon)
      ("DateTime", Primitives.dateTimeTyCon)
      ("TimeSpan", Primitives.timeSpanTyCon)
      ("exn", Primitives.exnTyCon)
      ("Exception", Primitives.exnTyCon)  // Alias
      ("NTUKind", Primitives.ntuKindTyCon)  // Native type universe kind tags
      ("PlatformContext", Primitives.platformContextTyCon) ]  // Platform configuration for type resolution
    |> Map.ofList

/// Native pointer type: nativeptr<'T>
/// Uses NTUptr kind - pointer-sized on all platforms
let nativeptrTyCon = mkNTUTypeConRefWithArity "nativeptr" NTUKind.NTUptr 1 TypeLayout.PlatformWord

/// Void pointer type: voidptr
/// Uses NTUptr kind - pointer-sized on all platforms
let voidptrTyCon = mkNTUTypeConRef "voidptr" NTUKind.NTUptr TypeLayout.PlatformWord

/// Byref type: byref<'T> - managed reference, maps to pointer in native
/// Uses NTUptr kind - pointer-sized on all platforms
let byrefTyCon = mkNTUTypeConRefWithArity "byref" NTUKind.NTUptr 1 TypeLayout.PlatformWord

/// Inref type: inref<'T> - read-only byref
/// Uses NTUptr kind - pointer-sized on all platforms
let inrefTyCon = mkNTUTypeConRefWithArity "inref" NTUKind.NTUptr 1 TypeLayout.PlatformWord

/// Outref type: outref<'T> - write-only byref
/// Uses NTUptr kind - pointer-sized on all platforms
let outrefTyCon = mkNTUTypeConRefWithArity "outref" NTUKind.NTUptr 1 TypeLayout.PlatformWord

/// Function pointer type: FnPtr<'F>
/// Used for FFI calls and callbacks to top-level functions (no closures)
/// Single type parameter 'F is the full function type, e.g., FnPtr<int -> unit>
/// See fsnative-spec/spec/ffi-boundary.md for complete semantics
let fnptrTyCon = mkNTUTypeConRefWithArity "FnPtr" NTUKind.NTUfnptr 1 TypeLayout.PlatformWord

/// Reactive signal type: Signal<'T>
/// Signal handle type: Signal<'T>
/// Platform word slot index into runtime signal table
/// Part of SolidJS-inspired native reactive signals
let signalTyCon = mkTypeConRef "Signal" 1 TypeLayout.PlatformWord

/// Effect handle type: Effect
/// Platform word handle to a registered effect in the runtime
/// Effects re-run when their signal dependencies change
let effectTyCon = mkTypeConRef "Effect" 0 TypeLayout.PlatformWord

/// Memoized value type: Memo<'T>
/// Platform word handle to a cached derived value
/// Memos recompute when their signal dependencies change
let memoTyCon = mkTypeConRef "Memo" 1 TypeLayout.PlatformWord

/// Arena type: Arena<'lifetime>
/// Bump allocator for deterministic memory management.
/// Measure parameter tracks lifetime scope.
/// Layout: { Base: nativeint, Capacity: int, Position: int } = 3 platform words
let arenaTyCon =
    mkTypeConRefWithMeasures "Arena"
        [TypeParamKind.Measure]  // 'lifetime is a measure parameter
        (TypeLayout.NTUCompound 3)  // 3 platform-word fields

let private parameterizedTyConsByName =
    [ ("option", Parameterized.optionTyCon)
      ("voption", Parameterized.voptionTyCon)
      ("ValueOption", Parameterized.voptionTyCon)  // Alias
      ("result", Parameterized.resultTyCon)
      ("Result", Parameterized.resultTyCon)  // Alias
      ("array", Parameterized.arrayTyCon)
      ("list", Parameterized.listTyCon)
      ("seq", Parameterized.seqTyCon)
      ("ref", Parameterized.refTyCon)
      ("Lazy", Parameterized.lazyTyCon)
      ("Expr", Parameterized.exprTyCon)
      ("nativeptr", nativeptrTyCon)
      ("voidptr", voidptrTyCon)
      ("byref", byrefTyCon)
      ("inref", inrefTyCon)
      ("outref", outrefTyCon)
      ("FnPtr", fnptrTyCon)
      // Reactive signals (SolidJS-inspired)
      ("Signal", signalTyCon)
      ("Effect", effectTyCon)
      ("Memo", memoTyCon)
      // Memory management
      ("Arena", arenaTyCon) ]
    |> Map.ofList

/// Try to find a primitive type constructor by name
let tryFindPrimitiveTyCon name = Map.tryFind name primitiveTyConsByName

/// Try to find a parameterized type constructor by name
let tryFindParameterizedTyCon name = Map.tryFind name parameterizedTyConsByName

/// Try to find any built-in type constructor by name
let tryFindBuiltinTyCon name =
    match tryFindPrimitiveTyCon name with
    | Some tc -> Some tc
    | None -> tryFindParameterizedTyCon name

//-------------------------------------------------------------------------
// Type Construction Helpers
//-------------------------------------------------------------------------

/// Create an option type: 'T option
let mkOptionType elemType = NativeType.TApp(Parameterized.optionTyCon, [elemType])

/// Create a value option type: 'T voption
let mkValueOptionType elemType = NativeType.TApp(Parameterized.voptionTyCon, [elemType])

/// Create a result type: Result<'T, 'TError>
let mkResultType okType errorType = NativeType.TApp(Parameterized.resultTyCon, [okType; errorType])

/// Create an array type: 'T array
let mkArrayType elemType = NativeType.TApp(Parameterized.arrayTyCon, [elemType])

/// Create a list type: 'T list
/// PRD-13a: Use TList directly for proper pointer layout (not TApp with Reference layout)
let mkListType elemType = NativeType.TList elemType

/// Create a map type: Map<'K, 'V>
/// PRD-13a: Immutable key-value map (balanced BST)
let mkMapType keyType valueType = NativeType.TMap(keyType, valueType)

/// Create a set type: Set<'T>
/// PRD-13a: Immutable set (balanced BST)
let mkSetType elemType = NativeType.TSet elemType

/// Create a ref type: 'T ref
let mkRefType elemType = NativeType.TApp(Parameterized.refTyCon, [elemType])

/// Create a quotation type: Expr<'T>
let mkExprType elemType = NativeType.TApp(Parameterized.exprTyCon, [elemType])

/// Create a lazy type: Lazy<'T>
/// PRD-14: Use TLazy directly for proper struct layout (not TApp with Reference layout)
let mkLazyType elemType = NativeType.TLazy elemType

/// Create a seq type: seq<'T>
/// PRD-15: Use TSeq directly for proper struct layout (not TApp with Reference layout)
let mkSeqType elemType = NativeType.TSeq elemType

/// Create a function pointer type: FnPtr<'F>
/// 'F must be a function type (TFun), e.g., int -> unit or nativeptr<byte> -> int -> int
/// Used for FFI calls and callbacks to top-level functions (no closures)
let mkFnPtrType funcType = NativeType.TApp(fnptrTyCon, [funcType])

/// Create a reactive signal type: Signal<'T>
/// Signals are reactive values that notify effects when they change
let mkSignalType elemType = NativeType.TApp(signalTyCon, [elemType])

/// Get the Effect type (non-parameterized handle)
/// Effects are side-effect functions that re-run when dependencies change
let effectType = NativeType.TApp(effectTyCon, [])

/// Create a memoized value type: Memo<'T>
/// Memos cache derived values that recompute when dependencies change
let mkMemoType elemType = NativeType.TApp(memoTyCon, [elemType])

/// Create an arena type: Arena<'lifetime>
/// Arenas provide deterministic bump allocation with lifetime tracking
let mkArenaType lifetimeMeasure = NativeType.TApp(arenaTyCon, [lifetimeMeasure])

//-------------------------------------------------------------------------
// Built-in F# Intrinsic Functions
//-------------------------------------------------------------------------

/// Built-in F# language functions that must be provided by the type checker.
/// These are the functions that are normally in FSharp.Core's Operators module.
module BuiltInFunctions =

    let private builtinRange = { File = "<builtin>"; Start = { Line = 0; Column = 0 }; End = { Line = 0; Column = 0 } }
    let mutable private tyVarCounter = 0

    // Create type variables for polymorphic functions
    // IMPORTANT: Each call creates a NEW type parameter with unique ID
    let private freshTyVar name =
        tyVarCounter <- tyVarCounter - 1
        let tyParam = {
            Id = tyVarCounter
            Name = name
            Kind = TypeParamKind.Type
            Constraints = []
            Parent = TypeParamState.Unbound
            Range = builtinRange
        }
        NativeType.TVar tyParam

    // Create a proper polymorphic type wrapped in TForall
    // This ensures each use site gets fresh type variables via instantiation
    let private freshTypeParam name =
        tyVarCounter <- tyVarCounter - 1
        {
            Id = tyVarCounter
            Name = name
            Kind = TypeParamKind.Type
            Constraints = []
            Parent = TypeParamState.Unbound
            Range = builtinRange
        }

    /// Create a polymorphic binary operator type: forall 'a. 'a -> 'a -> 'a
    let private mkPolymorphicBinaryOp () =
        let tyParam = freshTypeParam "'a"
        let tyVar = NativeType.TVar tyParam
        NativeType.TForall([tyParam], NativeType.TFun(tyVar, NativeType.TFun(tyVar, tyVar)))

    /// Create a polymorphic comparison operator type: forall 'a. 'a -> 'a -> bool
    let private mkPolymorphicComparisonOp () =
        let tyParam = freshTypeParam "'a"
        let tyVar = NativeType.TVar tyParam
        NativeType.TForall([tyParam], NativeType.TFun(tyVar, NativeType.TFun(tyVar, Types.boolType)))

    /// Create a polymorphic shift operator type: forall 'a. 'a -> int -> 'a
    let private mkPolymorphicShiftOp () =
        let tyParam = freshTypeParam "'a"
        let tyVar = NativeType.TVar tyParam
        NativeType.TForall([tyParam], NativeType.TFun(tyVar, NativeType.TFun(Types.intType, tyVar)))

    /// Create a polymorphic unary operator type: forall 'a. 'a -> 'a
    let private mkPolymorphicUnaryOp () =
        let tyParam = freshTypeParam "'a"
        let tyVar = NativeType.TVar tyParam
        NativeType.TForall([tyParam], NativeType.TFun(tyVar, tyVar))

    /// Create a polymorphic pipe operator type: forall 'a 'b. 'a -> ('a -> 'b) -> 'b
    let private mkPipeRightOp () =
        let aParam = freshTypeParam "'a"
        let bParam = freshTypeParam "'b"
        let aVar = NativeType.TVar aParam
        let bVar = NativeType.TVar bParam
        let funcType = NativeType.TFun(aVar, bVar)
        NativeType.TForall([aParam; bParam], NativeType.TFun(aVar, NativeType.TFun(funcType, bVar)))

    /// Create a polymorphic pipe left operator type: forall 'a 'b. ('a -> 'b) -> 'a -> 'b
    let private mkPipeLeftOp () =
        let aParam = freshTypeParam "'a"
        let bParam = freshTypeParam "'b"
        let aVar = NativeType.TVar aParam
        let bVar = NativeType.TVar bParam
        let funcType = NativeType.TFun(aVar, bVar)
        NativeType.TForall([aParam; bParam], NativeType.TFun(funcType, NativeType.TFun(aVar, bVar)))

    /// Create polymorphic compose right: forall 'a 'b 'c. ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
    let private mkComposeRightOp () =
        let aParam = freshTypeParam "'a"
        let bParam = freshTypeParam "'b"
        let cParam = freshTypeParam "'c"
        let aVar = NativeType.TVar aParam
        let bVar = NativeType.TVar bParam
        let cVar = NativeType.TVar cParam
        NativeType.TForall([aParam; bParam; cParam],
            NativeType.TFun(NativeType.TFun(aVar, bVar),
                NativeType.TFun(NativeType.TFun(bVar, cVar), NativeType.TFun(aVar, cVar))))

    /// Create polymorphic compose left: forall 'a 'b 'c. ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c
    let private mkComposeLeftOp () =
        let aParam = freshTypeParam "'a"
        let bParam = freshTypeParam "'b"
        let cParam = freshTypeParam "'c"
        let aVar = NativeType.TVar aParam
        let bVar = NativeType.TVar bParam
        let cVar = NativeType.TVar cParam
        NativeType.TForall([aParam; bParam; cParam],
            NativeType.TFun(NativeType.TFun(bVar, cVar),
                NativeType.TFun(NativeType.TFun(aVar, bVar), NativeType.TFun(aVar, cVar))))

    /// Conversion function type: forall 'a. 'a -> targetType
    /// These use SRTP internally but for type checking we model them as simple conversions.
    /// Must be wrapped in TForall so each usage gets fresh type variables!
    let mkConversionType targetType =
        let inputParam = freshTypeParam "'a"
        let inputVar = NativeType.TVar inputParam
        NativeType.TForall([inputParam], NativeType.TFun(inputVar, targetType))
    
    /// Create all built-in function bindings as (name, type) pairs
    let getBuiltInBindings () : (string * NativeType) list =
        [
            // Integer conversion functions
            ("int", mkConversionType Types.intType)
            ("int8", mkConversionType Types.int8Type)
            ("sbyte", mkConversionType Types.int8Type)  // Alias
            ("int16", mkConversionType Types.int16Type)
            ("int32", mkConversionType Types.int32Type)
            ("int64", mkConversionType Types.int64Type)
            ("nativeint", mkConversionType Types.nintType)
            
            // Unsigned integer conversion functions
            ("byte", mkConversionType Types.uint8Type)
            ("uint8", mkConversionType Types.uint8Type)
            ("uint16", mkConversionType Types.uint16Type)
            ("uint32", mkConversionType Types.uint32Type)
            ("uint64", mkConversionType Types.uint64Type)
            ("unativeint", mkConversionType Types.unintType)
            
            // Floating point conversion functions
            ("float", mkConversionType Types.floatType)
            ("double", mkConversionType Types.floatType)  // Alias
            ("float32", mkConversionType Types.float32Type)
            ("single", mkConversionType Types.float32Type)  // Alias
            ("decimal", mkConversionType Types.decimalType)
            
            // Other conversion functions
            ("char", mkConversionType Types.charType)
            ("string", mkConversionType Types.stringType)
            
            // ==========================================================================
            // EXPLICIT TYPE-SPECIFIC CONVERSIONS (ML/Rust pattern)
            // These are the preferred way to convert between integer types
            // See memory: ml_integer_type_patterns
            // ==========================================================================
            
            // Widening conversions (safe, no data loss)
            ("int8_to_int", NativeType.TFun(Types.int8Type, Types.intType))
            ("int16_to_int", NativeType.TFun(Types.int16Type, Types.intType))
            ("int32_to_int", NativeType.TFun(Types.int32Type, Types.intType))
            ("int32_to_int64", NativeType.TFun(Types.int32Type, Types.int64Type))
            ("int_to_int64", NativeType.TFun(Types.intType, Types.int64Type))
            ("uint8_to_int", NativeType.TFun(Types.uint8Type, Types.intType))
            ("uint8_to_uint", NativeType.TFun(Types.uint8Type, Types.uintType))
            ("uint16_to_uint", NativeType.TFun(Types.uint16Type, Types.uintType))
            ("uint32_to_uint", NativeType.TFun(Types.uint32Type, Types.uintType))
            ("uint32_to_uint64", NativeType.TFun(Types.uint32Type, Types.uint64Type))
            ("uint_to_uint64", NativeType.TFun(Types.uintType, Types.uint64Type))
            
            // Narrowing conversions (may truncate - use with care)
            ("int_to_int8", NativeType.TFun(Types.intType, Types.int8Type))
            ("int_to_int16", NativeType.TFun(Types.intType, Types.int16Type))
            ("int_to_int32", NativeType.TFun(Types.intType, Types.int32Type))
            ("int64_to_int", NativeType.TFun(Types.int64Type, Types.intType))
            ("int64_to_int32", NativeType.TFun(Types.int64Type, Types.int32Type))
            ("uint_to_uint8", NativeType.TFun(Types.uintType, Types.uint8Type))
            ("uint_to_uint16", NativeType.TFun(Types.uintType, Types.uint16Type))
            ("uint_to_uint32", NativeType.TFun(Types.uintType, Types.uint32Type))
            ("uint64_to_uint", NativeType.TFun(Types.uint64Type, Types.uintType))
            ("uint64_to_uint32", NativeType.TFun(Types.uint64Type, Types.uint32Type))
            
            // Sign-changing conversions (reinterpret bits)
            ("int_to_uint", NativeType.TFun(Types.intType, Types.uintType))
            ("uint_to_int", NativeType.TFun(Types.uintType, Types.intType))
            ("int32_to_uint32", NativeType.TFun(Types.int32Type, Types.uint32Type))
            ("uint32_to_int32", NativeType.TFun(Types.uint32Type, Types.int32Type))
            ("int64_to_uint64", NativeType.TFun(Types.int64Type, Types.uint64Type))
            ("uint64_to_int64", NativeType.TFun(Types.uint64Type, Types.int64Type))
            
            // Utility functions - wrapped in TForall for proper polymorphism
            // ignore : forall 'a. 'a -> unit
            let ignoreParam = freshTypeParam "'a"
            ("ignore", NativeType.TForall([ignoreParam], NativeType.TFun(NativeType.TVar ignoreParam, Types.unitType)))
            
            // abs : forall 'a. 'a -> 'a (SRTP-based, returns same type)
            let absParam = freshTypeParam "'a"
            let absVar = NativeType.TVar absParam
            ("abs", NativeType.TForall([absParam], NativeType.TFun(absVar, absVar)))
            
            // sizeof<'T> : int (type-level function, returns int)
            // Polymorphic: forall 'T. unit -> int
            // Alex resolves the type 'T to compute size based on target architecture
            let sizeofParam = freshTypeParam "'T"
            ("sizeof", NativeType.TForall([sizeofParam], NativeType.TFun(Types.unitType, Types.intType)))
            
            // Floating point special values
            ("nan", Types.floatType)   // Not a function, a value
            ("nanf", Types.float32Type)
            ("infinity", Types.floatType)
            ("infinityf", Types.float32Type)
            
            // ValueOption union case constructors - wrapped in TForall
            // ValueNone : forall 'a. voption<'a>
            let vnoneParam = freshTypeParam "'a"
            ("ValueNone", NativeType.TForall([vnoneParam], mkValueOptionType (NativeType.TVar vnoneParam)))
            // ValueSome : forall 'a. 'a -> voption<'a>
            let vsomeParam = freshTypeParam "'a"
            let vsomeVar = NativeType.TVar vsomeParam
            ("ValueSome", NativeType.TForall([vsomeParam], NativeType.TFun(vsomeVar, mkValueOptionType vsomeVar)))
            
            // Result union case constructors - wrapped in TForall
            // Ok : forall 'T 'Error. 'T -> Result<'T, 'Error>
            let okTParam = freshTypeParam "'T"
            let okErrParam = freshTypeParam "'Error"
            let okTVar = NativeType.TVar okTParam
            let okErrVar = NativeType.TVar okErrParam
            ("Ok", NativeType.TForall([okTParam; okErrParam], NativeType.TFun(okTVar, mkResultType okTVar okErrVar)))
            // Error : forall 'T 'Error. 'Error -> Result<'T, 'Error>
            let errTParam = freshTypeParam "'T"
            let errErrParam = freshTypeParam "'Error"
            let errTVar = NativeType.TVar errTParam
            let errErrVar = NativeType.TVar errErrParam
            ("Error", NativeType.TForall([errTParam; errErrParam], NativeType.TFun(errErrVar, mkResultType errTVar errErrVar)))
            
            // Option union case constructors (for compatibility) - wrapped in TForall
            // None : forall 'a. option<'a>
            let noneParam = freshTypeParam "'a"
            ("None", NativeType.TForall([noneParam], mkOptionType (NativeType.TVar noneParam)))
            // Some : forall 'a. 'a -> option<'a>
            let someParam = freshTypeParam "'a"
            let someVar = NativeType.TVar someParam
            ("Some", NativeType.TForall([someParam], NativeType.TFun(someVar, mkOptionType someVar)))

            // ==========================================================================
            // NTUKind UNION CASE CONSTRUCTORS
            // These expose the native type universe kind tags to user code.
            // BAREWire uses these for schema type definitions.
            // No open statement needed - these are primitive like int, string, etc.
            // ==========================================================================

            // Platform-dependent types
            ("NTUKind.NTUint", Types.ntuKindType)
            ("NTUKind.NTUuint", Types.ntuKindType)
            ("NTUKind.NTUnint", Types.ntuKindType)
            ("NTUKind.NTUunint", Types.ntuKindType)
            ("NTUKind.NTUptr", Types.ntuKindType)
            ("NTUKind.NTUfnptr", Types.ntuKindType)
            ("NTUKind.NTUsize", Types.ntuKindType)
            ("NTUKind.NTUdiff", Types.ntuKindType)

            // Fixed-width integer types
            ("NTUKind.NTUint8", Types.ntuKindType)
            ("NTUKind.NTUint16", Types.ntuKindType)
            ("NTUKind.NTUint32", Types.ntuKindType)
            ("NTUKind.NTUint64", Types.ntuKindType)
            ("NTUKind.NTUuint8", Types.ntuKindType)
            ("NTUKind.NTUuint16", Types.ntuKindType)
            ("NTUKind.NTUuint32", Types.ntuKindType)
            ("NTUKind.NTUuint64", Types.ntuKindType)

            // Floating point types
            ("NTUKind.NTUfloat32", Types.ntuKindType)
            ("NTUKind.NTUfloat64", Types.ntuKindType)

            // Special types
            ("NTUKind.NTUstring", Types.ntuKindType)
            ("NTUKind.NTUbool", Types.ntuKindType)
            ("NTUKind.NTUchar", Types.ntuKindType)
            ("NTUKind.NTUunit", Types.ntuKindType)
            ("NTUKind.NTUdecimal", Types.ntuKindType)
            ("NTUKind.NTUlazy", Types.ntuKindType)
            ("NTUKind.NTUseq", Types.ntuKindType)

            // Collection types (PRD-13a)
            ("NTUKind.NTUlist", Types.ntuKindType)
            ("NTUKind.NTUmap", Types.ntuKindType)
            ("NTUKind.NTUset", Types.ntuKindType)

            // Compound value types
            ("NTUKind.NTUuuid", Types.ntuKindType)
            ("NTUKind.NTUdatetime", Types.ntuKindType)
            ("NTUKind.NTUtimespan", Types.ntuKindType)
            ("NTUKind.NTUother", Types.ntuKindType)

            // printf family - format string functions
            // For now, model as string -> unit (simplified)
            ("printf", NativeType.TFun(Types.stringType, Types.unitType))
            ("printfn", NativeType.TFun(Types.stringType, Types.unitType))
            ("sprintf", NativeType.TFun(Types.stringType, Types.stringType))
            // failwith : forall 'a. string -> 'a (polymorphic return type for any context)
            let failwithParam = freshTypeParam "'a"
            ("failwith", NativeType.TForall([failwithParam], NativeType.TFun(Types.stringType, NativeType.TVar failwithParam)))
            // failwithf : forall 'a. string -> 'a (simplified - format string handling TBD)
            let failwithfParam = freshTypeParam "'a"
            ("failwithf", NativeType.TForall([failwithfParam], NativeType.TFun(Types.stringType, NativeType.TVar failwithfParam)))
            
            // ==========================================================================
            // POLYMORPHIC ARITHMETIC OPERATORS
            // These work on any numeric type via SRTP resolution.
            // See memory: srtp_operator_architecture, fncs_platform_aware_type_resolution
            // ==========================================================================
            
            // Arithmetic operators - polymorphic with SRTP resolution
            ("op_Addition", mkPolymorphicBinaryOp())
            ("op_Subtraction", mkPolymorphicBinaryOp())
            ("op_Multiply", mkPolymorphicBinaryOp())
            ("op_Division", mkPolymorphicBinaryOp())
            ("op_Modulus", mkPolymorphicBinaryOp())
            
            // ==========================================================================
            // MODULE-QUALIFIED TYPE-SPECIFIC OPERATORS (FStar pattern)
            // Use these for arithmetic on non-int types: Int64.add, Int32.mul, etc.
            // ==========================================================================
            
            // Int64 operators
            ("Int64.add", NativeType.TFun(Types.int64Type, NativeType.TFun(Types.int64Type, Types.int64Type)))
            ("Int64.sub", NativeType.TFun(Types.int64Type, NativeType.TFun(Types.int64Type, Types.int64Type)))
            ("Int64.mul", NativeType.TFun(Types.int64Type, NativeType.TFun(Types.int64Type, Types.int64Type)))
            ("Int64.div", NativeType.TFun(Types.int64Type, NativeType.TFun(Types.int64Type, Types.int64Type)))
            ("Int64.rem", NativeType.TFun(Types.int64Type, NativeType.TFun(Types.int64Type, Types.int64Type)))
            ("Int64.neg", NativeType.TFun(Types.int64Type, Types.int64Type))
            
            // Int32 operators
            ("Int32.add", NativeType.TFun(Types.int32Type, NativeType.TFun(Types.int32Type, Types.int32Type)))
            ("Int32.sub", NativeType.TFun(Types.int32Type, NativeType.TFun(Types.int32Type, Types.int32Type)))
            ("Int32.mul", NativeType.TFun(Types.int32Type, NativeType.TFun(Types.int32Type, Types.int32Type)))
            ("Int32.div", NativeType.TFun(Types.int32Type, NativeType.TFun(Types.int32Type, Types.int32Type)))
            ("Int32.rem", NativeType.TFun(Types.int32Type, NativeType.TFun(Types.int32Type, Types.int32Type)))
            ("Int32.neg", NativeType.TFun(Types.int32Type, Types.int32Type))
            
            // UInt64 operators
            ("UInt64.add", NativeType.TFun(Types.uint64Type, NativeType.TFun(Types.uint64Type, Types.uint64Type)))
            ("UInt64.sub", NativeType.TFun(Types.uint64Type, NativeType.TFun(Types.uint64Type, Types.uint64Type)))
            ("UInt64.mul", NativeType.TFun(Types.uint64Type, NativeType.TFun(Types.uint64Type, Types.uint64Type)))
            ("UInt64.div", NativeType.TFun(Types.uint64Type, NativeType.TFun(Types.uint64Type, Types.uint64Type)))
            ("UInt64.rem", NativeType.TFun(Types.uint64Type, NativeType.TFun(Types.uint64Type, Types.uint64Type)))
            
            // UInt32 operators
            ("UInt32.add", NativeType.TFun(Types.uint32Type, NativeType.TFun(Types.uint32Type, Types.uint32Type)))
            ("UInt32.sub", NativeType.TFun(Types.uint32Type, NativeType.TFun(Types.uint32Type, Types.uint32Type)))
            ("UInt32.mul", NativeType.TFun(Types.uint32Type, NativeType.TFun(Types.uint32Type, Types.uint32Type)))
            ("UInt32.div", NativeType.TFun(Types.uint32Type, NativeType.TFun(Types.uint32Type, Types.uint32Type)))
            ("UInt32.rem", NativeType.TFun(Types.uint32Type, NativeType.TFun(Types.uint32Type, Types.uint32Type)))
            
            // UInt8 (byte) operators
            ("UInt8.add", NativeType.TFun(Types.uint8Type, NativeType.TFun(Types.uint8Type, Types.uint8Type)))
            ("UInt8.sub", NativeType.TFun(Types.uint8Type, NativeType.TFun(Types.uint8Type, Types.uint8Type)))
            ("UInt8.mul", NativeType.TFun(Types.uint8Type, NativeType.TFun(Types.uint8Type, Types.uint8Type)))
            ("UInt8.div", NativeType.TFun(Types.uint8Type, NativeType.TFun(Types.uint8Type, Types.uint8Type)))
            ("UInt8.rem", NativeType.TFun(Types.uint8Type, NativeType.TFun(Types.uint8Type, Types.uint8Type)))
            
            // Float operators
            ("Float.add", NativeType.TFun(Types.floatType, NativeType.TFun(Types.floatType, Types.floatType)))
            ("Float.sub", NativeType.TFun(Types.floatType, NativeType.TFun(Types.floatType, Types.floatType)))
            ("Float.mul", NativeType.TFun(Types.floatType, NativeType.TFun(Types.floatType, Types.floatType)))
            ("Float.div", NativeType.TFun(Types.floatType, NativeType.TFun(Types.floatType, Types.floatType)))
            ("Float.neg", NativeType.TFun(Types.floatType, Types.floatType))
            
            // Float32 operators
            ("Float32.add", NativeType.TFun(Types.float32Type, NativeType.TFun(Types.float32Type, Types.float32Type)))
            ("Float32.sub", NativeType.TFun(Types.float32Type, NativeType.TFun(Types.float32Type, Types.float32Type)))
            ("Float32.mul", NativeType.TFun(Types.float32Type, NativeType.TFun(Types.float32Type, Types.float32Type)))
            ("Float32.div", NativeType.TFun(Types.float32Type, NativeType.TFun(Types.float32Type, Types.float32Type)))
            ("Float32.neg", NativeType.TFun(Types.float32Type, Types.float32Type))

            // compare : forall 'a. 'a -> 'a -> int (OCaml-style polymorphic compare)
            let compareParam = freshTypeParam "'a"
            let compareVar = NativeType.TVar compareParam
            ("compare", NativeType.TForall([compareParam], NativeType.TFun(compareVar, NativeType.TFun(compareVar, Types.intType))))

            // Comparison operators - polymorphic (ML/OCaml pattern)
            // Unlike arithmetic, comparison works on any type: 'a -> 'a -> bool
            // This is consistent with OCaml where (=), (<), etc. are polymorphic
            ("op_Equality", mkPolymorphicComparisonOp())
            ("op_Inequality", mkPolymorphicComparisonOp())
            ("op_LessThan", mkPolymorphicComparisonOp())
            ("op_GreaterThan", mkPolymorphicComparisonOp())
            ("op_LessThanOrEqual", mkPolymorphicComparisonOp())
            ("op_GreaterThanOrEqual", mkPolymorphicComparisonOp())

            // Bitwise operators - polymorphic for integer types
            // SRTP resolves to type-specific implementations
            ("op_BitwiseAnd", mkPolymorphicBinaryOp())
            ("op_BitwiseOr", mkPolymorphicBinaryOp())
            ("op_ExclusiveOr", mkPolymorphicBinaryOp())
            ("op_LeftShift", mkPolymorphicShiftOp())
            ("op_RightShift", mkPolymorphicShiftOp())

            // Logical operators (monomorphic bool -> bool -> bool)
            ("op_BooleanAnd", NativeType.TFun(Types.boolType, NativeType.TFun(Types.boolType, Types.boolType)))
            ("op_BooleanOr", NativeType.TFun(Types.boolType, NativeType.TFun(Types.boolType, Types.boolType)))
            ("not", NativeType.TFun(Types.boolType, Types.boolType))

            // Unary operators - polymorphic
            ("op_UnaryNegation", mkPolymorphicUnaryOp())
            ("op_LogicalNot", NativeType.TFun(Types.boolType, Types.boolType))

            // Pipe operators (polymorphic with TForall for proper instantiation)
            ("op_PipeRight", mkPipeRightOp())  // |>
            ("op_PipeLeft", mkPipeLeftOp())    // <|

            // Composition operators (polymorphic with TForall)
            ("op_ComposeRight", mkComposeRightOp())  // >>
            ("op_ComposeLeft", mkComposeLeftOp())    // <<

            // ==========================================================================
            // PLATFORM CONTEXT (for BAREWire and other systems libraries)
            // PlatformContext provides platform-specific type resolution at compile time.
            // ==========================================================================

            // PlatformContext.resolveSize : PlatformContext -> NTUKind -> int
            ("PlatformContext.resolveSize", NativeType.TFun(Types.platformContextType, NativeType.TFun(Types.ntuKindType, Types.intType)))

            // PlatformContext.resolveAlign : PlatformContext -> NTUKind -> int
            ("PlatformContext.resolveAlign", NativeType.TFun(Types.platformContextType, NativeType.TFun(Types.ntuKindType, Types.intType)))

            // PlatformContext.defaultLinux_x86_64 : PlatformContext
            ("PlatformContext.defaultLinux_x86_64", Types.platformContextType)

            // ==========================================================================
            // PRD-13a: COLLECTION MODULE FUNCTIONS
            // Map, List, Set operations as built-in functions
            // ==========================================================================

            // --- Map module ---
            // Map.empty : forall 'K 'V. Map<'K, 'V>
            let mapKParam = freshTypeParam "'K"
            let mapVParam = freshTypeParam "'V"
            let mapKVar = NativeType.TVar mapKParam
            let mapVVar = NativeType.TVar mapVParam
            let mapType = NativeType.TMap(mapKVar, mapVVar)
            ("Map.empty", NativeType.TForall([mapKParam; mapVParam], mapType))

            // Map.add : forall 'K 'V. 'K -> 'V -> Map<'K, 'V> -> Map<'K, 'V>
            let addKParam = freshTypeParam "'K"
            let addVParam = freshTypeParam "'V"
            let addKVar = NativeType.TVar addKParam
            let addVVar = NativeType.TVar addVParam
            let addMapType = NativeType.TMap(addKVar, addVVar)
            ("Map.add", NativeType.TForall([addKParam; addVParam],
                NativeType.TFun(addKVar, NativeType.TFun(addVVar, NativeType.TFun(addMapType, addMapType)))))

            // Map.find : forall 'K 'V. 'K -> Map<'K, 'V> -> 'V
            let findKParam = freshTypeParam "'K"
            let findVParam = freshTypeParam "'V"
            let findKVar = NativeType.TVar findKParam
            let findVVar = NativeType.TVar findVParam
            let findMapType = NativeType.TMap(findKVar, findVVar)
            ("Map.find", NativeType.TForall([findKParam; findVParam],
                NativeType.TFun(findKVar, NativeType.TFun(findMapType, findVVar))))

            // Map.tryFind : forall 'K 'V. 'K -> Map<'K, 'V> -> 'V option
            let tryFindKParam = freshTypeParam "'K"
            let tryFindVParam = freshTypeParam "'V"
            let tryFindKVar = NativeType.TVar tryFindKParam
            let tryFindVVar = NativeType.TVar tryFindVParam
            let tryFindMapType = NativeType.TMap(tryFindKVar, tryFindVVar)
            let tryFindResultType = mkOptionType tryFindVVar
            ("Map.tryFind", NativeType.TForall([tryFindKParam; tryFindVParam],
                NativeType.TFun(tryFindKVar, NativeType.TFun(tryFindMapType, tryFindResultType))))

            // Map.containsKey : forall 'K 'V. 'K -> Map<'K, 'V> -> bool
            let containsKParam = freshTypeParam "'K"
            let containsVParam = freshTypeParam "'V"
            let containsKVar = NativeType.TVar containsKParam
            let containsVVar = NativeType.TVar containsVParam
            let containsMapType = NativeType.TMap(containsKVar, containsVVar)
            ("Map.containsKey", NativeType.TForall([containsKParam; containsVParam],
                NativeType.TFun(containsKVar, NativeType.TFun(containsMapType, Types.boolType))))

            // Map.remove : forall 'K 'V. 'K -> Map<'K, 'V> -> Map<'K, 'V>
            let removeKParam = freshTypeParam "'K"
            let removeVParam = freshTypeParam "'V"
            let removeKVar = NativeType.TVar removeKParam
            let removeVVar = NativeType.TVar removeVParam
            let removeMapType = NativeType.TMap(removeKVar, removeVVar)
            ("Map.remove", NativeType.TForall([removeKParam; removeVParam],
                NativeType.TFun(removeKVar, NativeType.TFun(removeMapType, removeMapType))))

            // Map.keys : forall 'K 'V. Map<'K, 'V> -> seq<'K>
            // PRD-16: Returns lazy sequence for in-order traversal of keys
            let keysKParam = freshTypeParam "'K"
            let keysVParam = freshTypeParam "'V"
            let keysKVar = NativeType.TVar keysKParam
            let keysVVar = NativeType.TVar keysVParam
            let keysMapType = NativeType.TMap(keysKVar, keysVVar)
            let keysResultType = NativeType.TSeq(keysKVar)
            ("Map.keys", NativeType.TForall([keysKParam; keysVParam],
                NativeType.TFun(keysMapType, keysResultType)))

            // Map.values : forall 'K 'V. Map<'K, 'V> -> seq<'V>
            // PRD-16: Returns lazy sequence for in-order traversal of values
            let valuesKParam = freshTypeParam "'K"
            let valuesVParam = freshTypeParam "'V"
            let valuesKVar = NativeType.TVar valuesKParam
            let valuesVVar = NativeType.TVar valuesVParam
            let valuesMapType = NativeType.TMap(valuesKVar, valuesVVar)
            let valuesResultType = NativeType.TSeq(valuesVVar)
            ("Map.values", NativeType.TForall([valuesKParam; valuesVParam],
                NativeType.TFun(valuesMapType, valuesResultType)))

            // Map.toList : forall 'K 'V. Map<'K, 'V> -> ('K * 'V) list
            let toListKParam = freshTypeParam "'K"
            let toListVParam = freshTypeParam "'V"
            let toListKVar = NativeType.TVar toListKParam
            let toListVVar = NativeType.TVar toListVParam
            let toListMapType = NativeType.TMap(toListKVar, toListVVar)
            let toListPairType = NativeType.TTuple([toListKVar; toListVVar], true)  // struct tuple
            let toListResultType = NativeType.TList(toListPairType)
            ("Map.toList", NativeType.TForall([toListKParam; toListVParam],
                NativeType.TFun(toListMapType, toListResultType)))

            // Map.toSeq : forall 'K 'V. Map<'K, 'V> -> seq<'K * 'V>
            // PRD-16: Lazy enumeration over map key-value pairs
            let toSeqKParam = freshTypeParam "'K"
            let toSeqVParam = freshTypeParam "'V"
            let toSeqKVar = NativeType.TVar toSeqKParam
            let toSeqVVar = NativeType.TVar toSeqVParam
            let toSeqMapType = NativeType.TMap(toSeqKVar, toSeqVVar)
            let toSeqPairType = NativeType.TTuple([toSeqKVar; toSeqVVar], true)  // struct tuple
            let toSeqResultType = NativeType.TSeq(toSeqPairType)
            ("Map.toSeq", NativeType.TForall([toSeqKParam; toSeqVParam],
                NativeType.TFun(toSeqMapType, toSeqResultType)))

            // Map.forall : forall 'K 'V. ('K -> 'V -> bool) -> Map<'K, 'V> -> bool
            let forallKParam = freshTypeParam "'K"
            let forallVParam = freshTypeParam "'V"
            let forallKVar = NativeType.TVar forallKParam
            let forallVVar = NativeType.TVar forallVParam
            let forallMapType = NativeType.TMap(forallKVar, forallVVar)
            let forallPredType = NativeType.TFun(forallKVar, NativeType.TFun(forallVVar, Types.boolType))
            ("Map.forall", NativeType.TForall([forallKParam; forallVParam],
                NativeType.TFun(forallPredType, NativeType.TFun(forallMapType, Types.boolType))))

            // Map.fold : forall 'K 'V 'State. ('State -> 'K -> 'V -> 'State) -> 'State -> Map<'K, 'V> -> 'State
            let foldKParam = freshTypeParam "'K"
            let foldVParam = freshTypeParam "'V"
            let foldSParam = freshTypeParam "'State"
            let foldKVar = NativeType.TVar foldKParam
            let foldVVar = NativeType.TVar foldVParam
            let foldSVar = NativeType.TVar foldSParam
            let foldMapType = NativeType.TMap(foldKVar, foldVVar)
            let foldFuncType = NativeType.TFun(foldSVar, NativeType.TFun(foldKVar, NativeType.TFun(foldVVar, foldSVar)))
            ("Map.fold", NativeType.TForall([foldKParam; foldVParam; foldSParam],
                NativeType.TFun(foldFuncType, NativeType.TFun(foldSVar, NativeType.TFun(foldMapType, foldSVar)))))

            // --- Set module ---
            // Set.empty : forall 'T. Set<'T>
            let setTParam = freshTypeParam "'T"
            let setTVar = NativeType.TVar setTParam
            let setType = NativeType.TSet(setTVar)
            ("Set.empty", NativeType.TForall([setTParam], setType))

            // Set.add : forall 'T. 'T -> Set<'T> -> Set<'T>
            let setAddTParam = freshTypeParam "'T"
            let setAddTVar = NativeType.TVar setAddTParam
            let setAddType = NativeType.TSet(setAddTVar)
            ("Set.add", NativeType.TForall([setAddTParam],
                NativeType.TFun(setAddTVar, NativeType.TFun(setAddType, setAddType))))

            // Set.contains : forall 'T. 'T -> Set<'T> -> bool
            let setContainsTParam = freshTypeParam "'T"
            let setContainsTVar = NativeType.TVar setContainsTParam
            let setContainsType = NativeType.TSet(setContainsTVar)
            ("Set.contains", NativeType.TForall([setContainsTParam],
                NativeType.TFun(setContainsTVar, NativeType.TFun(setContainsType, Types.boolType))))

            // Set.remove : forall 'T. 'T -> Set<'T> -> Set<'T>
            let setRemoveTParam = freshTypeParam "'T"
            let setRemoveTVar = NativeType.TVar setRemoveTParam
            let setRemoveType = NativeType.TSet(setRemoveTVar)
            ("Set.remove", NativeType.TForall([setRemoveTParam],
                NativeType.TFun(setRemoveTVar, NativeType.TFun(setRemoveType, setRemoveType))))

            // Set.toList : forall 'T. Set<'T> -> 'T list
            let setToListTParam = freshTypeParam "'T"
            let setToListTVar = NativeType.TVar setToListTParam
            let setToListSetType = NativeType.TSet(setToListTVar)
            let setToListResultType = NativeType.TList(setToListTVar)
            ("Set.toList", NativeType.TForall([setToListTParam],
                NativeType.TFun(setToListSetType, setToListResultType)))

            // --- List module ---
            // List.empty : forall 'T. 'T list
            let listTParam = freshTypeParam "'T"
            let listTVar = NativeType.TVar listTParam
            let listType = NativeType.TList(listTVar)
            ("List.empty", NativeType.TForall([listTParam], listType))

            // List.head : forall 'T. 'T list -> 'T
            let headTParam = freshTypeParam "'T"
            let headTVar = NativeType.TVar headTParam
            let headListType = NativeType.TList(headTVar)
            ("List.head", NativeType.TForall([headTParam],
                NativeType.TFun(headListType, headTVar)))

            // List.tail : forall 'T. 'T list -> 'T list
            let tailTParam = freshTypeParam "'T"
            let tailTVar = NativeType.TVar tailTParam
            let tailListType = NativeType.TList(tailTVar)
            ("List.tail", NativeType.TForall([tailTParam],
                NativeType.TFun(tailListType, tailListType)))

            // List.isEmpty : forall 'T. 'T list -> bool
            let isEmptyTParam = freshTypeParam "'T"
            let isEmptyTVar = NativeType.TVar isEmptyTParam
            let isEmptyListType = NativeType.TList(isEmptyTVar)
            ("List.isEmpty", NativeType.TForall([isEmptyTParam],
                NativeType.TFun(isEmptyListType, Types.boolType)))

            // List.length : forall 'T. 'T list -> int
            let lengthTParam = freshTypeParam "'T"
            let lengthTVar = NativeType.TVar lengthTParam
            let lengthListType = NativeType.TList(lengthTVar)
            ("List.length", NativeType.TForall([lengthTParam],
                NativeType.TFun(lengthListType, Types.intType)))

            // List.map : forall 'T 'U. ('T -> 'U) -> 'T list -> 'U list
            let mapTParam = freshTypeParam "'T"
            let mapUParam = freshTypeParam "'U"
            let mapTVar = NativeType.TVar mapTParam
            let mapUVar = NativeType.TVar mapUParam
            let mapInputListType = NativeType.TList(mapTVar)
            let mapOutputListType = NativeType.TList(mapUVar)
            let mapFuncType = NativeType.TFun(mapTVar, mapUVar)
            ("List.map", NativeType.TForall([mapTParam; mapUParam],
                NativeType.TFun(mapFuncType, NativeType.TFun(mapInputListType, mapOutputListType))))

            // List.filter : forall 'T. ('T -> bool) -> 'T list -> 'T list
            let filterTParam = freshTypeParam "'T"
            let filterTVar = NativeType.TVar filterTParam
            let filterListType = NativeType.TList(filterTVar)
            let filterPredType = NativeType.TFun(filterTVar, Types.boolType)
            ("List.filter", NativeType.TForall([filterTParam],
                NativeType.TFun(filterPredType, NativeType.TFun(filterListType, filterListType))))

            // List.fold : forall 'T 'State. ('State -> 'T -> 'State) -> 'State -> 'T list -> 'State
            let listFoldTParam = freshTypeParam "'T"
            let listFoldSParam = freshTypeParam "'State"
            let listFoldTVar = NativeType.TVar listFoldTParam
            let listFoldSVar = NativeType.TVar listFoldSParam
            let listFoldListType = NativeType.TList(listFoldTVar)
            let listFoldFuncType = NativeType.TFun(listFoldSVar, NativeType.TFun(listFoldTVar, listFoldSVar))
            ("List.fold", NativeType.TForall([listFoldTParam; listFoldSParam],
                NativeType.TFun(listFoldFuncType, NativeType.TFun(listFoldSVar, NativeType.TFun(listFoldListType, listFoldSVar)))))

            // List.append : forall 'T. 'T list -> 'T list -> 'T list
            let appendTParam = freshTypeParam "'T"
            let appendTVar = NativeType.TVar appendTParam
            let appendListType = NativeType.TList(appendTVar)
            ("List.append", NativeType.TForall([appendTParam],
                NativeType.TFun(appendListType, NativeType.TFun(appendListType, appendListType))))

            // List.collect : forall 'T 'U. ('T -> 'U list) -> 'T list -> 'U list
            let collectTParam = freshTypeParam "'T"
            let collectUParam = freshTypeParam "'U"
            let collectTVar = NativeType.TVar collectTParam
            let collectUVar = NativeType.TVar collectUParam
            let collectInputListType = NativeType.TList(collectTVar)
            let collectOutputListType = NativeType.TList(collectUVar)
            let collectFuncType = NativeType.TFun(collectTVar, collectOutputListType)
            ("List.collect", NativeType.TForall([collectTParam; collectUParam],
                NativeType.TFun(collectFuncType, NativeType.TFun(collectInputListType, collectOutputListType))))

            // List.forall : forall 'T. ('T -> bool) -> 'T list -> bool
            let listForallTParam = freshTypeParam "'T"
            let listForallTVar = NativeType.TVar listForallTParam
            let listForallListType = NativeType.TList(listForallTVar)
            let listForallPredType = NativeType.TFun(listForallTVar, Types.boolType)
            ("List.forall", NativeType.TForall([listForallTParam],
                NativeType.TFun(listForallPredType, NativeType.TFun(listForallListType, Types.boolType))))

            // List.exists : forall 'T. ('T -> bool) -> 'T list -> bool
            let listExistsTParam = freshTypeParam "'T"
            let listExistsTVar = NativeType.TVar listExistsTParam
            let listExistsListType = NativeType.TList(listExistsTVar)
            let listExistsPredType = NativeType.TFun(listExistsTVar, Types.boolType)
            ("List.exists", NativeType.TForall([listExistsTParam],
                NativeType.TFun(listExistsPredType, NativeType.TFun(listExistsListType, Types.boolType))))

            // List.sumBy : forall 'T. ('T -> int) -> 'T list -> int
            let sumByTParam = freshTypeParam "'T"
            let sumByTVar = NativeType.TVar sumByTParam
            let sumByListType = NativeType.TList(sumByTVar)
            let sumByFuncType = NativeType.TFun(sumByTVar, Types.intType)
            ("List.sumBy", NativeType.TForall([sumByTParam],
                NativeType.TFun(sumByFuncType, NativeType.TFun(sumByListType, Types.intType))))

            // List.rev : forall 'T. 'T list -> 'T list
            let listRevTParam = freshTypeParam "'T"
            let listRevTVar = NativeType.TVar listRevTParam
            let listRevListType = NativeType.TList(listRevTVar)
            ("List.rev", NativeType.TForall([listRevTParam],
                NativeType.TFun(listRevListType, listRevListType)))

            // List.contains : forall 'T. 'T -> 'T list -> bool
            let listContainsTParam = freshTypeParam "'T"
            let listContainsTVar = NativeType.TVar listContainsTParam
            let listContainsListType = NativeType.TList(listContainsTVar)
            ("List.contains", NativeType.TForall([listContainsTParam],
                NativeType.TFun(listContainsTVar, NativeType.TFun(listContainsListType, Types.boolType))))

            // List.tryPick : forall 'T 'U. ('T -> 'U option) -> 'T list -> 'U option
            let listTryPickTParam = freshTypeParam "'T"
            let listTryPickUParam = freshTypeParam "'U"
            let listTryPickTVar = NativeType.TVar listTryPickTParam
            let listTryPickUVar = NativeType.TVar listTryPickUParam
            let listTryPickListType = NativeType.TList(listTryPickTVar)
            let listTryPickResultType = mkOptionType listTryPickUVar
            let listTryPickFn = NativeType.TFun(listTryPickTVar, listTryPickResultType)
            ("List.tryPick", NativeType.TForall([listTryPickTParam; listTryPickUParam],
                NativeType.TFun(listTryPickFn, NativeType.TFun(listTryPickListType, listTryPickResultType))))

            // List.max : forall 'T. 'T list -> 'T
            let listMaxTParam = freshTypeParam "'T"
            let listMaxTVar = NativeType.TVar listMaxTParam
            let listMaxListType = NativeType.TList(listMaxTVar)
            ("List.max", NativeType.TForall([listMaxTParam],
                NativeType.TFun(listMaxListType, listMaxTVar)))

            // List.forall2 : forall 'T 'U. ('T -> 'U -> bool) -> 'T list -> 'U list -> bool
            let listForall2TParam = freshTypeParam "'T"
            let listForall2UParam = freshTypeParam "'U"
            let listForall2TVar = NativeType.TVar listForall2TParam
            let listForall2UVar = NativeType.TVar listForall2UParam
            let listForall2List1Type = NativeType.TList(listForall2TVar)
            let listForall2List2Type = NativeType.TList(listForall2UVar)
            let listForall2PredType = NativeType.TFun(listForall2TVar, NativeType.TFun(listForall2UVar, Types.boolType))
            ("List.forall2", NativeType.TForall([listForall2TParam; listForall2UParam],
                NativeType.TFun(listForall2PredType, NativeType.TFun(listForall2List1Type, NativeType.TFun(listForall2List2Type, Types.boolType)))))

            // List.ofSeq : forall 'T. seq<'T> -> 'T list
            // Alias for Seq.toList - same decomposition via Baker
            let listOfSeqTParam = freshTypeParam "'T"
            let listOfSeqTVar = NativeType.TVar listOfSeqTParam
            let listOfSeqSeqType = NativeType.TSeq(listOfSeqTVar)
            let listOfSeqResultType = NativeType.TList(listOfSeqTVar)
            ("List.ofSeq", NativeType.TForall([listOfSeqTParam],
                NativeType.TFun(listOfSeqSeqType, listOfSeqResultType)))

            //
            // Map module - additional functions
            //

            // Map.isEmpty : forall 'K 'V. Map<'K, 'V> -> bool
            let mapIsEmptyKParam = freshTypeParam "'K"
            let mapIsEmptyVParam = freshTypeParam "'V"
            let mapIsEmptyKVar = NativeType.TVar mapIsEmptyKParam
            let mapIsEmptyVVar = NativeType.TVar mapIsEmptyVParam
            let mapIsEmptyMapType = NativeType.TMap(mapIsEmptyKVar, mapIsEmptyVVar)
            ("Map.isEmpty", NativeType.TForall([mapIsEmptyKParam; mapIsEmptyVParam],
                NativeType.TFun(mapIsEmptyMapType, Types.boolType)))

            // Map.ofList : forall 'K 'V. ('K * 'V) list -> Map<'K, 'V>
            let mapOfListKParam = freshTypeParam "'K"
            let mapOfListVParam = freshTypeParam "'V"
            let mapOfListKVar = NativeType.TVar mapOfListKParam
            let mapOfListVVar = NativeType.TVar mapOfListVParam
            let mapOfListPairType = NativeType.TTuple([mapOfListKVar; mapOfListVVar], true)
            let mapOfListListType = NativeType.TList(mapOfListPairType)
            let mapOfListResultType = NativeType.TMap(mapOfListKVar, mapOfListVVar)
            ("Map.ofList", NativeType.TForall([mapOfListKParam; mapOfListVParam],
                NativeType.TFun(mapOfListListType, mapOfListResultType)))

            // Map.count : forall 'K 'V. Map<'K, 'V> -> int
            let mapCountKParam = freshTypeParam "'K"
            let mapCountVParam = freshTypeParam "'V"
            let mapCountKVar = NativeType.TVar mapCountKParam
            let mapCountVVar = NativeType.TVar mapCountVParam
            let mapCountMapType = NativeType.TMap(mapCountKVar, mapCountVVar)
            ("Map.count", NativeType.TForall([mapCountKParam; mapCountVParam],
                NativeType.TFun(mapCountMapType, Types.intType)))

            // Map.map : forall 'K 'V 'U. ('K -> 'V -> 'U) -> Map<'K, 'V> -> Map<'K, 'U>
            let mapMapKParam = freshTypeParam "'K"
            let mapMapVParam = freshTypeParam "'V"
            let mapMapUParam = freshTypeParam "'U"
            let mapMapKVar = NativeType.TVar mapMapKParam
            let mapMapVVar = NativeType.TVar mapMapVParam
            let mapMapUVar = NativeType.TVar mapMapUParam
            let mapMapInputType = NativeType.TMap(mapMapKVar, mapMapVVar)
            let mapMapResultType = NativeType.TMap(mapMapKVar, mapMapUVar)
            let mapMapFn = NativeType.TFun(mapMapKVar, NativeType.TFun(mapMapVVar, mapMapUVar))
            ("Map.map", NativeType.TForall([mapMapKParam; mapMapVParam; mapMapUParam],
                NativeType.TFun(mapMapFn, NativeType.TFun(mapMapInputType, mapMapResultType))))

            // Map.filter : forall 'K 'V. ('K -> 'V -> bool) -> Map<'K, 'V> -> Map<'K, 'V>
            let mapFilterKParam = freshTypeParam "'K"
            let mapFilterVParam = freshTypeParam "'V"
            let mapFilterKVar = NativeType.TVar mapFilterKParam
            let mapFilterVVar = NativeType.TVar mapFilterVParam
            let mapFilterMapType = NativeType.TMap(mapFilterKVar, mapFilterVVar)
            let mapFilterPredType = NativeType.TFun(mapFilterKVar, NativeType.TFun(mapFilterVVar, Types.boolType))
            ("Map.filter", NativeType.TForall([mapFilterKParam; mapFilterVParam],
                NativeType.TFun(mapFilterPredType, NativeType.TFun(mapFilterMapType, mapFilterMapType))))

            // Map.exists : forall 'K 'V. ('K -> 'V -> bool) -> Map<'K, 'V> -> bool
            let mapExistsKParam = freshTypeParam "'K"
            let mapExistsVParam = freshTypeParam "'V"
            let mapExistsKVar = NativeType.TVar mapExistsKParam
            let mapExistsVVar = NativeType.TVar mapExistsVParam
            let mapExistsMapType = NativeType.TMap(mapExistsKVar, mapExistsVVar)
            let mapExistsPredType = NativeType.TFun(mapExistsKVar, NativeType.TFun(mapExistsVVar, Types.boolType))
            ("Map.exists", NativeType.TForall([mapExistsKParam; mapExistsVParam],
                NativeType.TFun(mapExistsPredType, NativeType.TFun(mapExistsMapType, Types.boolType))))

            // Map.tryPick : forall 'K 'V 'U. ('K -> 'V -> 'U option) -> Map<'K, 'V> -> 'U option
            let mapTryPickKParam = freshTypeParam "'K"
            let mapTryPickVParam = freshTypeParam "'V"
            let mapTryPickUParam = freshTypeParam "'U"
            let mapTryPickKVar = NativeType.TVar mapTryPickKParam
            let mapTryPickVVar = NativeType.TVar mapTryPickVParam
            let mapTryPickUVar = NativeType.TVar mapTryPickUParam
            let mapTryPickMapType = NativeType.TMap(mapTryPickKVar, mapTryPickVVar)
            let mapTryPickResultType = mkOptionType mapTryPickUVar
            let mapTryPickFn = NativeType.TFun(mapTryPickKVar, NativeType.TFun(mapTryPickVVar, mapTryPickResultType))
            ("Map.tryPick", NativeType.TForall([mapTryPickKParam; mapTryPickVParam; mapTryPickUParam],
                NativeType.TFun(mapTryPickFn, NativeType.TFun(mapTryPickMapType, mapTryPickResultType))))

            //
            // Set module - additional functions
            //

            // Set.ofList : forall 'T. 'T list -> Set<'T>
            let setOfListTParam = freshTypeParam "'T"
            let setOfListTVar = NativeType.TVar setOfListTParam
            let setOfListListType = NativeType.TList(setOfListTVar)
            let setOfListSetType = NativeType.TSet(setOfListTVar)
            ("Set.ofList", NativeType.TForall([setOfListTParam],
                NativeType.TFun(setOfListListType, setOfListSetType)))

            // Set.count : forall 'T. Set<'T> -> int
            let setCountTParam = freshTypeParam "'T"
            let setCountTVar = NativeType.TVar setCountTParam
            let setCountSetType = NativeType.TSet(setCountTVar)
            ("Set.count", NativeType.TForall([setCountTParam],
                NativeType.TFun(setCountSetType, Types.intType)))

            // Set.isEmpty : forall 'T. Set<'T> -> bool
            let setIsEmptyTParam = freshTypeParam "'T"
            let setIsEmptyTVar = NativeType.TVar setIsEmptyTParam
            let setIsEmptySetType = NativeType.TSet(setIsEmptyTVar)
            ("Set.isEmpty", NativeType.TForall([setIsEmptyTParam],
                NativeType.TFun(setIsEmptySetType, Types.boolType)))

            // Set.map : forall 'T 'U. ('T -> 'U) -> Set<'T> -> Set<'U>
            let setMapTParam = freshTypeParam "'T"
            let setMapUParam = freshTypeParam "'U"
            let setMapTVar = NativeType.TVar setMapTParam
            let setMapUVar = NativeType.TVar setMapUParam
            let setMapInputType = NativeType.TSet(setMapTVar)
            let setMapResultType = NativeType.TSet(setMapUVar)
            let setMapFn = NativeType.TFun(setMapTVar, setMapUVar)
            ("Set.map", NativeType.TForall([setMapTParam; setMapUParam],
                NativeType.TFun(setMapFn, NativeType.TFun(setMapInputType, setMapResultType))))

            // Set.filter : forall 'T. ('T -> bool) -> Set<'T> -> Set<'T>
            let setFilterTParam = freshTypeParam "'T"
            let setFilterTVar = NativeType.TVar setFilterTParam
            let setFilterSetType = NativeType.TSet(setFilterTVar)
            let setFilterPredType = NativeType.TFun(setFilterTVar, Types.boolType)
            ("Set.filter", NativeType.TForall([setFilterTParam],
                NativeType.TFun(setFilterPredType, NativeType.TFun(setFilterSetType, setFilterSetType))))

            // Set.fold : forall 'T 'State. ('State -> 'T -> 'State) -> 'State -> Set<'T> -> 'State
            let setFoldTParam = freshTypeParam "'T"
            let setFoldSParam = freshTypeParam "'State"
            let setFoldTVar = NativeType.TVar setFoldTParam
            let setFoldSVar = NativeType.TVar setFoldSParam
            let setFoldSetType = NativeType.TSet(setFoldTVar)
            let setFoldFn = NativeType.TFun(setFoldSVar, NativeType.TFun(setFoldTVar, setFoldSVar))
            ("Set.fold", NativeType.TForall([setFoldTParam; setFoldSParam],
                NativeType.TFun(setFoldFn, NativeType.TFun(setFoldSVar, NativeType.TFun(setFoldSetType, setFoldSVar)))))

            // Set.forall : forall 'T. ('T -> bool) -> Set<'T> -> bool
            let setForallTParam = freshTypeParam "'T"
            let setForallTVar = NativeType.TVar setForallTParam
            let setForallSetType = NativeType.TSet(setForallTVar)
            let setForallPredType = NativeType.TFun(setForallTVar, Types.boolType)
            ("Set.forall", NativeType.TForall([setForallTParam],
                NativeType.TFun(setForallPredType, NativeType.TFun(setForallSetType, Types.boolType))))

            // Set.exists : forall 'T. ('T -> bool) -> Set<'T> -> bool
            let setExistsTParam = freshTypeParam "'T"
            let setExistsTVar = NativeType.TVar setExistsTParam
            let setExistsSetType = NativeType.TSet(setExistsTVar)
            let setExistsPredType = NativeType.TFun(setExistsTVar, Types.boolType)
            ("Set.exists", NativeType.TForall([setExistsTParam],
                NativeType.TFun(setExistsPredType, NativeType.TFun(setExistsSetType, Types.boolType))))

            // Set.union : forall 'T. Set<'T> -> Set<'T> -> Set<'T>
            let setUnionTParam = freshTypeParam "'T"
            let setUnionTVar = NativeType.TVar setUnionTParam
            let setUnionSetType = NativeType.TSet(setUnionTVar)
            ("Set.union", NativeType.TForall([setUnionTParam],
                NativeType.TFun(setUnionSetType, NativeType.TFun(setUnionSetType, setUnionSetType))))

            // Set.intersect : forall 'T. Set<'T> -> Set<'T> -> Set<'T>
            let setIntersectTParam = freshTypeParam "'T"
            let setIntersectTVar = NativeType.TVar setIntersectTParam
            let setIntersectSetType = NativeType.TSet(setIntersectTVar)
            ("Set.intersect", NativeType.TForall([setIntersectTParam],
                NativeType.TFun(setIntersectSetType, NativeType.TFun(setIntersectSetType, setIntersectSetType))))

            // Set.difference : forall 'T. Set<'T> -> Set<'T> -> Set<'T>
            let setDiffTParam = freshTypeParam "'T"
            let setDiffTVar = NativeType.TVar setDiffTParam
            let setDiffSetType = NativeType.TSet(setDiffTVar)
            ("Set.difference", NativeType.TForall([setDiffTParam],
                NativeType.TFun(setDiffSetType, NativeType.TFun(setDiffSetType, setDiffSetType))))

            // Set.isSubset : forall 'T. Set<'T> -> Set<'T> -> bool
            let setIsSubsetTParam = freshTypeParam "'T"
            let setIsSubsetTVar = NativeType.TVar setIsSubsetTParam
            let setIsSubsetSetType = NativeType.TSet(setIsSubsetTVar)
            ("Set.isSubset", NativeType.TForall([setIsSubsetTParam],
                NativeType.TFun(setIsSubsetSetType, NativeType.TFun(setIsSubsetSetType, Types.boolType))))

            // Set.isSuperset : forall 'T. Set<'T> -> Set<'T> -> bool
            let setIsSupersetTParam = freshTypeParam "'T"
            let setIsSupersetTVar = NativeType.TVar setIsSupersetTParam
            let setIsSupersetSetType = NativeType.TSet(setIsSupersetTVar)
            ("Set.isSuperset", NativeType.TForall([setIsSupersetTParam],
                NativeType.TFun(setIsSupersetSetType, NativeType.TFun(setIsSupersetSetType, Types.boolType))))

            // Set.minElement : forall 'T. Set<'T> -> 'T
            let setMinTParam = freshTypeParam "'T"
            let setMinTVar = NativeType.TVar setMinTParam
            let setMinSetType = NativeType.TSet(setMinTVar)
            ("Set.minElement", NativeType.TForall([setMinTParam],
                NativeType.TFun(setMinSetType, setMinTVar)))

            // Set.maxElement : forall 'T. Set<'T> -> 'T
            let setMaxTParam = freshTypeParam "'T"
            let setMaxTVar = NativeType.TVar setMaxTParam
            let setMaxSetType = NativeType.TSet(setMaxTVar)
            ("Set.maxElement", NativeType.TForall([setMaxTParam],
                NativeType.TFun(setMaxSetType, setMaxTVar)))

            //
            // Seq module - lazy sequence operations (PRD-15/16)
            //
            // PRIMITIVES (Alex witnesses directly):
            //   - Seq.empty, Seq.getEnumerator
            //   - SeqEnumerator.moveNext, SeqEnumerator.current
            //
            // HOFs (Baker decomposes using primitives):
            //   - Producers: map, filter, collect, append
            //   - Consumers: toList, toArray, fold, tryPick, max, minBy
            //

            // Seq.empty : forall 'T. seq<'T>
            // PRIMITIVE: Returns empty sequence (no-op state machine)
            let seqEmptyTParam = freshTypeParam "'T"
            let seqEmptyTVar = NativeType.TVar seqEmptyTParam
            let seqEmptyType = NativeType.TSeq(seqEmptyTVar)
            ("Seq.empty", NativeType.TForall([seqEmptyTParam], seqEmptyType))

            // Seq.toList : forall 'T. seq<'T> -> 'T list
            // HOF: Decomposes to iteration loop using enumerator primitives
            let seqToListTParam = freshTypeParam "'T"
            let seqToListTVar = NativeType.TVar seqToListTParam
            let seqToListSeqType = NativeType.TSeq(seqToListTVar)
            let seqToListResultType = NativeType.TList(seqToListTVar)
            ("Seq.toList", NativeType.TForall([seqToListTParam],
                NativeType.TFun(seqToListSeqType, seqToListResultType)))

            // Seq.toArray : forall 'T. seq<'T> -> 'T[]
            // HOF: Decomposes to iteration loop, builds array
            let seqToArrayTParam = freshTypeParam "'T"
            let seqToArrayTVar = NativeType.TVar seqToArrayTParam
            let seqToArraySeqType = NativeType.TSeq(seqToArrayTVar)
            let seqToArrayResultType = mkArrayType seqToArrayTVar
            ("Seq.toArray", NativeType.TForall([seqToArrayTParam],
                NativeType.TFun(seqToArraySeqType, seqToArrayResultType)))

            // Seq.map : forall 'T 'U. ('T -> 'U) -> seq<'T> -> seq<'U>
            // HOF: Decomposes to seq { for x in xs do yield f x }
            let seqMapTParam = freshTypeParam "'T"
            let seqMapUParam = freshTypeParam "'U"
            let seqMapTVar = NativeType.TVar seqMapTParam
            let seqMapUVar = NativeType.TVar seqMapUParam
            let seqMapInputType = NativeType.TSeq(seqMapTVar)
            let seqMapResultType = NativeType.TSeq(seqMapUVar)
            let seqMapFnType = NativeType.TFun(seqMapTVar, seqMapUVar)
            ("Seq.map", NativeType.TForall([seqMapTParam; seqMapUParam],
                NativeType.TFun(seqMapFnType, NativeType.TFun(seqMapInputType, seqMapResultType))))

            // Seq.filter : forall 'T. ('T -> bool) -> seq<'T> -> seq<'T>
            // HOF: Decomposes to seq { for x in xs do if p x then yield x }
            let seqFilterTParam = freshTypeParam "'T"
            let seqFilterTVar = NativeType.TVar seqFilterTParam
            let seqFilterSeqType = NativeType.TSeq(seqFilterTVar)
            let seqFilterPredType = NativeType.TFun(seqFilterTVar, Types.boolType)
            ("Seq.filter", NativeType.TForall([seqFilterTParam],
                NativeType.TFun(seqFilterPredType, NativeType.TFun(seqFilterSeqType, seqFilterSeqType))))

            // Seq.collect : forall 'T 'U. ('T -> seq<'U>) -> seq<'T> -> seq<'U>
            // HOF: Decomposes to seq { for x in xs do yield! f x }
            let seqCollectTParam = freshTypeParam "'T"
            let seqCollectUParam = freshTypeParam "'U"
            let seqCollectTVar = NativeType.TVar seqCollectTParam
            let seqCollectUVar = NativeType.TVar seqCollectUParam
            let seqCollectInputType = NativeType.TSeq(seqCollectTVar)
            let seqCollectResultType = NativeType.TSeq(seqCollectUVar)
            let seqCollectFnType = NativeType.TFun(seqCollectTVar, seqCollectResultType)
            ("Seq.collect", NativeType.TForall([seqCollectTParam; seqCollectUParam],
                NativeType.TFun(seqCollectFnType, NativeType.TFun(seqCollectInputType, seqCollectResultType))))

            // Seq.append : forall 'T. seq<'T> -> seq<'T> -> seq<'T>
            // HOF: Decomposes to seq { yield! xs; yield! ys }
            let seqAppendTParam = freshTypeParam "'T"
            let seqAppendTVar = NativeType.TVar seqAppendTParam
            let seqAppendSeqType = NativeType.TSeq(seqAppendTVar)
            ("Seq.append", NativeType.TForall([seqAppendTParam],
                NativeType.TFun(seqAppendSeqType, NativeType.TFun(seqAppendSeqType, seqAppendSeqType))))

            // Seq.fold : forall 'T 'State. ('State -> 'T -> 'State) -> 'State -> seq<'T> -> 'State
            // HOF: Decomposes to iteration loop with accumulator
            let seqFoldTParam = freshTypeParam "'T"
            let seqFoldSParam = freshTypeParam "'State"
            let seqFoldTVar = NativeType.TVar seqFoldTParam
            let seqFoldSVar = NativeType.TVar seqFoldSParam
            let seqFoldSeqType = NativeType.TSeq(seqFoldTVar)
            let seqFoldFnType = NativeType.TFun(seqFoldSVar, NativeType.TFun(seqFoldTVar, seqFoldSVar))
            ("Seq.fold", NativeType.TForall([seqFoldTParam; seqFoldSParam],
                NativeType.TFun(seqFoldFnType, NativeType.TFun(seqFoldSVar, NativeType.TFun(seqFoldSeqType, seqFoldSVar)))))

            // Seq.tryPick : forall 'T 'U. ('T -> 'U option) -> seq<'T> -> 'U option
            // HOF: Decomposes to iteration loop until Some
            let seqTryPickTParam = freshTypeParam "'T"
            let seqTryPickUParam = freshTypeParam "'U"
            let seqTryPickTVar = NativeType.TVar seqTryPickTParam
            let seqTryPickUVar = NativeType.TVar seqTryPickUParam
            let seqTryPickSeqType = NativeType.TSeq(seqTryPickTVar)
            let seqTryPickResultType = mkOptionType seqTryPickUVar
            let seqTryPickFnType = NativeType.TFun(seqTryPickTVar, seqTryPickResultType)
            ("Seq.tryPick", NativeType.TForall([seqTryPickTParam; seqTryPickUParam],
                NativeType.TFun(seqTryPickFnType, NativeType.TFun(seqTryPickSeqType, seqTryPickResultType))))

            // Seq.max : forall 'T. seq<'T> -> 'T (requires comparison)
            // HOF: Decomposes to iteration loop tracking max
            let seqMaxTParam = freshTypeParam "'T"
            let seqMaxTVar = NativeType.TVar seqMaxTParam
            let seqMaxSeqType = NativeType.TSeq(seqMaxTVar)
            ("Seq.max", NativeType.TForall([seqMaxTParam],
                NativeType.TFun(seqMaxSeqType, seqMaxTVar)))

            // Seq.min : forall 'T. seq<'T> -> 'T (requires comparison)
            // HOF: Decomposes to iteration loop tracking min
            let seqMinTParam = freshTypeParam "'T"
            let seqMinTVar = NativeType.TVar seqMinTParam
            let seqMinSeqType = NativeType.TSeq(seqMinTVar)
            ("Seq.min", NativeType.TForall([seqMinTParam],
                NativeType.TFun(seqMinSeqType, seqMinTVar)))

            // Seq.minBy : forall 'T 'U. ('T -> 'U) -> seq<'T> -> 'T (requires comparison on 'U)
            // HOF: Decomposes to iteration loop tracking min by projection
            let seqMinByTParam = freshTypeParam "'T"
            let seqMinByUParam = freshTypeParam "'U"
            let seqMinByTVar = NativeType.TVar seqMinByTParam
            let seqMinByUVar = NativeType.TVar seqMinByUParam
            let seqMinBySeqType = NativeType.TSeq(seqMinByTVar)
            let seqMinByFnType = NativeType.TFun(seqMinByTVar, seqMinByUVar)
            ("Seq.minBy", NativeType.TForall([seqMinByTParam; seqMinByUParam],
                NativeType.TFun(seqMinByFnType, NativeType.TFun(seqMinBySeqType, seqMinByTVar))))

            // Seq.maxBy : forall 'T 'U. ('T -> 'U) -> seq<'T> -> 'T (requires comparison on 'U)
            // HOF: Decomposes to iteration loop tracking max by projection
            let seqMaxByTParam = freshTypeParam "'T"
            let seqMaxByUParam = freshTypeParam "'U"
            let seqMaxByTVar = NativeType.TVar seqMaxByTParam
            let seqMaxByUVar = NativeType.TVar seqMaxByUParam
            let seqMaxBySeqType = NativeType.TSeq(seqMaxByTVar)
            let seqMaxByFnType = NativeType.TFun(seqMaxByTVar, seqMaxByUVar)
            ("Seq.maxBy", NativeType.TForall([seqMaxByTParam; seqMaxByUParam],
                NativeType.TFun(seqMaxByFnType, NativeType.TFun(seqMaxBySeqType, seqMaxByTVar))))

            // Seq.exists : forall 'T. ('T -> bool) -> seq<'T> -> bool
            // HOF: Decomposes to iteration with short-circuit
            let seqExistsTParam = freshTypeParam "'T"
            let seqExistsTVar = NativeType.TVar seqExistsTParam
            let seqExistsSeqType = NativeType.TSeq(seqExistsTVar)
            let seqExistsPredType = NativeType.TFun(seqExistsTVar, Types.boolType)
            ("Seq.exists", NativeType.TForall([seqExistsTParam],
                NativeType.TFun(seqExistsPredType, NativeType.TFun(seqExistsSeqType, Types.boolType))))

            // Seq.forall : forall 'T. ('T -> bool) -> seq<'T> -> bool
            // HOF: Decomposes to iteration with short-circuit
            let seqForallTParam = freshTypeParam "'T"
            let seqForallTVar = NativeType.TVar seqForallTParam
            let seqForallSeqType = NativeType.TSeq(seqForallTVar)
            let seqForallPredType = NativeType.TFun(seqForallTVar, Types.boolType)
            ("Seq.forall", NativeType.TForall([seqForallTParam],
                NativeType.TFun(seqForallPredType, NativeType.TFun(seqForallSeqType, Types.boolType))))

            // Seq.length : forall 'T. seq<'T> -> int
            // HOF: Decomposes to iteration counting elements
            let seqLengthTParam = freshTypeParam "'T"
            let seqLengthTVar = NativeType.TVar seqLengthTParam
            let seqLengthSeqType = NativeType.TSeq(seqLengthTVar)
            ("Seq.length", NativeType.TForall([seqLengthTParam],
                NativeType.TFun(seqLengthSeqType, Types.intType)))

            // Seq.isEmpty : forall 'T. seq<'T> -> bool
            // HOF: Decomposes to single moveNext check
            let seqIsEmptyTParam = freshTypeParam "'T"
            let seqIsEmptyTVar = NativeType.TVar seqIsEmptyTParam
            let seqIsEmptySeqType = NativeType.TSeq(seqIsEmptyTVar)
            ("Seq.isEmpty", NativeType.TForall([seqIsEmptyTParam],
                NativeType.TFun(seqIsEmptySeqType, Types.boolType)))

            // Seq.head : forall 'T. seq<'T> -> 'T
            // HOF: Decomposes to single iteration step
            let seqHeadTParam = freshTypeParam "'T"
            let seqHeadTVar = NativeType.TVar seqHeadTParam
            let seqHeadSeqType = NativeType.TSeq(seqHeadTVar)
            ("Seq.head", NativeType.TForall([seqHeadTParam],
                NativeType.TFun(seqHeadSeqType, seqHeadTVar)))

            // Seq.tryHead : forall 'T. seq<'T> -> 'T option
            // HOF: Decomposes to single iteration step returning option
            let seqTryHeadTParam = freshTypeParam "'T"
            let seqTryHeadTVar = NativeType.TVar seqTryHeadTParam
            let seqTryHeadSeqType = NativeType.TSeq(seqTryHeadTVar)
            let seqTryHeadResultType = mkOptionType seqTryHeadTVar
            ("Seq.tryHead", NativeType.TForall([seqTryHeadTParam],
                NativeType.TFun(seqTryHeadSeqType, seqTryHeadResultType)))

            //
            // Seq enumerator primitives (for iteration - Alex witnesses directly)
            //

            // Seq.getEnumerator : forall 'T. seq<'T> -> SeqEnumerator<'T>
            // PRIMITIVE: Initialize state machine for iteration
            let seqGetEnumTParam = freshTypeParam "'T"
            let seqGetEnumTVar = NativeType.TVar seqGetEnumTParam
            let seqGetEnumSeqType = NativeType.TSeq(seqGetEnumTVar)
            let seqGetEnumResultType = NativeType.TSeqEnumerator(seqGetEnumTVar)
            ("Seq.getEnumerator", NativeType.TForall([seqGetEnumTParam],
                NativeType.TFun(seqGetEnumSeqType, seqGetEnumResultType)))

            // SeqEnumerator.moveNext : forall 'T. SeqEnumerator<'T> -> bool
            // PRIMITIVE: Advance state machine, return whether value available
            let seqMoveNextTParam = freshTypeParam "'T"
            let seqMoveNextTVar = NativeType.TVar seqMoveNextTParam
            let seqMoveNextEnumType = NativeType.TSeqEnumerator(seqMoveNextTVar)
            ("SeqEnumerator.moveNext", NativeType.TForall([seqMoveNextTParam],
                NativeType.TFun(seqMoveNextEnumType, Types.boolType)))

            // SeqEnumerator.current : forall 'T. SeqEnumerator<'T> -> 'T
            // PRIMITIVE: Get current value from state machine
            let seqCurrentTParam = freshTypeParam "'T"
            let seqCurrentTVar = NativeType.TVar seqCurrentTParam
            let seqCurrentEnumType = NativeType.TSeqEnumerator(seqCurrentTVar)
            ("SeqEnumerator.current", NativeType.TForall([seqCurrentTParam],
                NativeType.TFun(seqCurrentEnumType, seqCurrentTVar)))

            //
            // List module - additional functions
            //

            // List.tryFind : forall 'T. ('T -> bool) -> 'T list -> 'T option
            let listTryFindTParam = freshTypeParam "'T"
            let listTryFindTVar = NativeType.TVar listTryFindTParam
            let listTryFindListType = NativeType.TList(listTryFindTVar)
            let listTryFindResultType = mkOptionType listTryFindTVar
            let listTryFindPredType = NativeType.TFun(listTryFindTVar, Types.boolType)
            ("List.tryFind", NativeType.TForall([listTryFindTParam],
                NativeType.TFun(listTryFindPredType, NativeType.TFun(listTryFindListType, listTryFindResultType))))

            // List.find : forall 'T. ('T -> bool) -> 'T list -> 'T
            let listFindTParam = freshTypeParam "'T"
            let listFindTVar = NativeType.TVar listFindTParam
            let listFindListType = NativeType.TList(listFindTVar)
            let listFindPredType = NativeType.TFun(listFindTVar, Types.boolType)
            ("List.find", NativeType.TForall([listFindTParam],
                NativeType.TFun(listFindPredType, NativeType.TFun(listFindListType, listFindTVar))))

            // List.choose : forall 'T 'U. ('T -> 'U option) -> 'T list -> 'U list
            let listChooseTParam = freshTypeParam "'T"
            let listChooseUParam = freshTypeParam "'U"
            let listChooseTVar = NativeType.TVar listChooseTParam
            let listChooseUVar = NativeType.TVar listChooseUParam
            let listChooseInputType = NativeType.TList(listChooseTVar)
            let listChooseResultType = NativeType.TList(listChooseUVar)
            let listChooseOptionType = mkOptionType listChooseUVar
            let listChooseFn = NativeType.TFun(listChooseTVar, listChooseOptionType)
            ("List.choose", NativeType.TForall([listChooseTParam; listChooseUParam],
                NativeType.TFun(listChooseFn, NativeType.TFun(listChooseInputType, listChooseResultType))))

            // List.concat : forall 'T. 'T list list -> 'T list
            let listConcatTParam = freshTypeParam "'T"
            let listConcatTVar = NativeType.TVar listConcatTParam
            let listConcatElemType = NativeType.TList(listConcatTVar)
            let listConcatInputType = NativeType.TList(listConcatElemType)
            ("List.concat", NativeType.TForall([listConcatTParam],
                NativeType.TFun(listConcatInputType, listConcatElemType)))

            // List.distinct : forall 'T. 'T list -> 'T list
            let listDistinctTParam = freshTypeParam "'T"
            let listDistinctTVar = NativeType.TVar listDistinctTParam
            let listDistinctListType = NativeType.TList(listDistinctTVar)
            ("List.distinct", NativeType.TForall([listDistinctTParam],
                NativeType.TFun(listDistinctListType, listDistinctListType)))

            // List.distinctBy : forall 'T 'K. ('T -> 'K) -> 'T list -> 'T list
            let listDistinctByTParam = freshTypeParam "'T"
            let listDistinctByKParam = freshTypeParam "'K"
            let listDistinctByTVar = NativeType.TVar listDistinctByTParam
            let listDistinctByKVar = NativeType.TVar listDistinctByKParam
            let listDistinctByListType = NativeType.TList(listDistinctByTVar)
            let listDistinctByFn = NativeType.TFun(listDistinctByTVar, listDistinctByKVar)
            ("List.distinctBy", NativeType.TForall([listDistinctByTParam; listDistinctByKParam],
                NativeType.TFun(listDistinctByFn, NativeType.TFun(listDistinctByListType, listDistinctByListType))))

            // List.sort : forall 'T. 'T list -> 'T list
            let listSortTParam = freshTypeParam "'T"
            let listSortTVar = NativeType.TVar listSortTParam
            let listSortListType = NativeType.TList(listSortTVar)
            ("List.sort", NativeType.TForall([listSortTParam],
                NativeType.TFun(listSortListType, listSortListType)))

            // List.sortBy : forall 'T 'K. ('T -> 'K) -> 'T list -> 'T list
            let listSortByTParam = freshTypeParam "'T"
            let listSortByKParam = freshTypeParam "'K"
            let listSortByTVar = NativeType.TVar listSortByTParam
            let listSortByKVar = NativeType.TVar listSortByKParam
            let listSortByListType = NativeType.TList(listSortByTVar)
            let listSortByFn = NativeType.TFun(listSortByTVar, listSortByKVar)
            ("List.sortBy", NativeType.TForall([listSortByTParam; listSortByKParam],
                NativeType.TFun(listSortByFn, NativeType.TFun(listSortByListType, listSortByListType))))

            // List.sortDescending : forall 'T. 'T list -> 'T list
            let listSortDescTParam = freshTypeParam "'T"
            let listSortDescTVar = NativeType.TVar listSortDescTParam
            let listSortDescListType = NativeType.TList(listSortDescTVar)
            ("List.sortDescending", NativeType.TForall([listSortDescTParam],
                NativeType.TFun(listSortDescListType, listSortDescListType)))

            // List.min : forall 'T. 'T list -> 'T
            let listMinTParam = freshTypeParam "'T"
            let listMinTVar = NativeType.TVar listMinTParam
            let listMinListType = NativeType.TList(listMinTVar)
            ("List.min", NativeType.TForall([listMinTParam],
                NativeType.TFun(listMinListType, listMinTVar)))

            // List.minBy : forall 'T 'K. ('T -> 'K) -> 'T list -> 'T
            let listMinByTParam = freshTypeParam "'T"
            let listMinByKParam = freshTypeParam "'K"
            let listMinByTVar = NativeType.TVar listMinByTParam
            let listMinByKVar = NativeType.TVar listMinByKParam
            let listMinByListType = NativeType.TList(listMinByTVar)
            let listMinByFn = NativeType.TFun(listMinByTVar, listMinByKVar)
            ("List.minBy", NativeType.TForall([listMinByTParam; listMinByKParam],
                NativeType.TFun(listMinByFn, NativeType.TFun(listMinByListType, listMinByTVar))))

            // List.maxBy : forall 'T 'K. ('T -> 'K) -> 'T list -> 'T
            let listMaxByTParam = freshTypeParam "'T"
            let listMaxByKParam = freshTypeParam "'K"
            let listMaxByTVar = NativeType.TVar listMaxByTParam
            let listMaxByKVar = NativeType.TVar listMaxByKParam
            let listMaxByListType = NativeType.TList(listMaxByTVar)
            let listMaxByFn = NativeType.TFun(listMaxByTVar, listMaxByKVar)
            ("List.maxBy", NativeType.TForall([listMaxByTParam; listMaxByKParam],
                NativeType.TFun(listMaxByFn, NativeType.TFun(listMaxByListType, listMaxByTVar))))

            // List.sum : forall 'T. 'T list -> 'T (polymorphic, will be constrained by SRTP)
            let listSumTParam = freshTypeParam "'T"
            let listSumTVar = NativeType.TVar listSumTParam
            let listSumListType = NativeType.TList(listSumTVar)
            ("List.sum", NativeType.TForall([listSumTParam],
                NativeType.TFun(listSumListType, listSumTVar)))

            // List.average : forall 'T. 'T list -> 'T
            let listAvgTParam = freshTypeParam "'T"
            let listAvgTVar = NativeType.TVar listAvgTParam
            let listAvgListType = NativeType.TList(listAvgTVar)
            ("List.average", NativeType.TForall([listAvgTParam],
                NativeType.TFun(listAvgListType, listAvgTVar)))

            // List.item : forall 'T. int -> 'T list -> 'T (List.item is same as List.nth)
            let listItemTParam = freshTypeParam "'T"
            let listItemTVar = NativeType.TVar listItemTParam
            let listItemListType = NativeType.TList(listItemTVar)
            ("List.item", NativeType.TForall([listItemTParam],
                NativeType.TFun(Types.intType, NativeType.TFun(listItemListType, listItemTVar))))

            // List.nth : forall 'T. 'T list -> int -> 'T (deprecated, but commonly used)
            let listNthTParam = freshTypeParam "'T"
            let listNthTVar = NativeType.TVar listNthTParam
            let listNthListType = NativeType.TList(listNthTVar)
            ("List.nth", NativeType.TForall([listNthTParam],
                NativeType.TFun(listNthListType, NativeType.TFun(Types.intType, listNthTVar))))

            // List.take : forall 'T. int -> 'T list -> 'T list
            let listTakeTParam = freshTypeParam "'T"
            let listTakeTVar = NativeType.TVar listTakeTParam
            let listTakeListType = NativeType.TList(listTakeTVar)
            ("List.take", NativeType.TForall([listTakeTParam],
                NativeType.TFun(Types.intType, NativeType.TFun(listTakeListType, listTakeListType))))

            // List.skip : forall 'T. int -> 'T list -> 'T list
            let listSkipTParam = freshTypeParam "'T"
            let listSkipTVar = NativeType.TVar listSkipTParam
            let listSkipListType = NativeType.TList(listSkipTVar)
            ("List.skip", NativeType.TForall([listSkipTParam],
                NativeType.TFun(Types.intType, NativeType.TFun(listSkipListType, listSkipListType))))

            // List.truncate : forall 'T. int -> 'T list -> 'T list
            let listTruncTParam = freshTypeParam "'T"
            let listTruncTVar = NativeType.TVar listTruncTParam
            let listTruncListType = NativeType.TList(listTruncTVar)
            ("List.truncate", NativeType.TForall([listTruncTParam],
                NativeType.TFun(Types.intType, NativeType.TFun(listTruncListType, listTruncListType))))

            // List.zip : forall 'T 'U. 'T list -> 'U list -> ('T * 'U) list
            let listZipTParam = freshTypeParam "'T"
            let listZipUParam = freshTypeParam "'U"
            let listZipTVar = NativeType.TVar listZipTParam
            let listZipUVar = NativeType.TVar listZipUParam
            let listZipList1Type = NativeType.TList(listZipTVar)
            let listZipList2Type = NativeType.TList(listZipUVar)
            let listZipPairType = NativeType.TTuple([listZipTVar; listZipUVar], true)
            let listZipResultType = NativeType.TList(listZipPairType)
            ("List.zip", NativeType.TForall([listZipTParam; listZipUParam],
                NativeType.TFun(listZipList1Type, NativeType.TFun(listZipList2Type, listZipResultType))))

            // List.unzip : forall 'T 'U. ('T * 'U) list -> ('T list * 'U list)
            let listUnzipTParam = freshTypeParam "'T"
            let listUnzipUParam = freshTypeParam "'U"
            let listUnzipTVar = NativeType.TVar listUnzipTParam
            let listUnzipUVar = NativeType.TVar listUnzipUParam
            let listUnzipPairType = NativeType.TTuple([listUnzipTVar; listUnzipUVar], true)
            let listUnzipInputType = NativeType.TList(listUnzipPairType)
            let listUnzipList1Type = NativeType.TList(listUnzipTVar)
            let listUnzipList2Type = NativeType.TList(listUnzipUVar)
            let listUnzipResultType = NativeType.TTuple([listUnzipList1Type; listUnzipList2Type], true)
            ("List.unzip", NativeType.TForall([listUnzipTParam; listUnzipUParam],
                NativeType.TFun(listUnzipInputType, listUnzipResultType)))

            // List.mapi : forall 'T 'U. (int -> 'T -> 'U) -> 'T list -> 'U list
            let listMapiTParam = freshTypeParam "'T"
            let listMapiUParam = freshTypeParam "'U"
            let listMapiTVar = NativeType.TVar listMapiTParam
            let listMapiUVar = NativeType.TVar listMapiUParam
            let listMapiInputType = NativeType.TList(listMapiTVar)
            let listMapiResultType = NativeType.TList(listMapiUVar)
            let listMapiFn = NativeType.TFun(Types.intType, NativeType.TFun(listMapiTVar, listMapiUVar))
            ("List.mapi", NativeType.TForall([listMapiTParam; listMapiUParam],
                NativeType.TFun(listMapiFn, NativeType.TFun(listMapiInputType, listMapiResultType))))

            // List.iter : forall 'T. ('T -> unit) -> 'T list -> unit
            let listIterTParam = freshTypeParam "'T"
            let listIterTVar = NativeType.TVar listIterTParam
            let listIterListType = NativeType.TList(listIterTVar)
            let listIterFn = NativeType.TFun(listIterTVar, Types.unitType)
            ("List.iter", NativeType.TForall([listIterTParam],
                NativeType.TFun(listIterFn, NativeType.TFun(listIterListType, Types.unitType))))

            // List.iteri : forall 'T. (int -> 'T -> unit) -> 'T list -> unit
            let listIteriTParam = freshTypeParam "'T"
            let listIteriTVar = NativeType.TVar listIteriTParam
            let listIteriListType = NativeType.TList(listIteriTVar)
            let listIteriFn = NativeType.TFun(Types.intType, NativeType.TFun(listIteriTVar, Types.unitType))
            ("List.iteri", NativeType.TForall([listIteriTParam],
                NativeType.TFun(listIteriFn, NativeType.TFun(listIteriListType, Types.unitType))))

            // List.reduce : forall 'T. ('T -> 'T -> 'T) -> 'T list -> 'T
            let listReduceTParam = freshTypeParam "'T"
            let listReduceTVar = NativeType.TVar listReduceTParam
            let listReduceListType = NativeType.TList(listReduceTVar)
            let listReduceFn = NativeType.TFun(listReduceTVar, NativeType.TFun(listReduceTVar, listReduceTVar))
            ("List.reduce", NativeType.TForall([listReduceTParam],
                NativeType.TFun(listReduceFn, NativeType.TFun(listReduceListType, listReduceTVar))))

            // List.foldBack : forall 'T 'State. ('T -> 'State -> 'State) -> 'T list -> 'State -> 'State
            let listFoldBackTParam = freshTypeParam "'T"
            let listFoldBackSParam = freshTypeParam "'State"
            let listFoldBackTVar = NativeType.TVar listFoldBackTParam
            let listFoldBackSVar = NativeType.TVar listFoldBackSParam
            let listFoldBackListType = NativeType.TList(listFoldBackTVar)
            let listFoldBackFn = NativeType.TFun(listFoldBackTVar, NativeType.TFun(listFoldBackSVar, listFoldBackSVar))
            ("List.foldBack", NativeType.TForall([listFoldBackTParam; listFoldBackSParam],
                NativeType.TFun(listFoldBackFn, NativeType.TFun(listFoldBackListType, NativeType.TFun(listFoldBackSVar, listFoldBackSVar)))))

            // List.exists2 : forall 'T 'U. ('T -> 'U -> bool) -> 'T list -> 'U list -> bool
            let listExists2TParam = freshTypeParam "'T"
            let listExists2UParam = freshTypeParam "'U"
            let listExists2TVar = NativeType.TVar listExists2TParam
            let listExists2UVar = NativeType.TVar listExists2UParam
            let listExists2List1Type = NativeType.TList(listExists2TVar)
            let listExists2List2Type = NativeType.TList(listExists2UVar)
            let listExists2PredType = NativeType.TFun(listExists2TVar, NativeType.TFun(listExists2UVar, Types.boolType))
            ("List.exists2", NativeType.TForall([listExists2TParam; listExists2UParam],
                NativeType.TFun(listExists2PredType, NativeType.TFun(listExists2List1Type, NativeType.TFun(listExists2List2Type, Types.boolType)))))

            // List.partition : forall 'T. ('T -> bool) -> 'T list -> ('T list * 'T list)
            let listPartTParam = freshTypeParam "'T"
            let listPartTVar = NativeType.TVar listPartTParam
            let listPartListType = NativeType.TList(listPartTVar)
            let listPartPredType = NativeType.TFun(listPartTVar, Types.boolType)
            let listPartResultType = NativeType.TTuple([listPartListType; listPartListType], true)
            ("List.partition", NativeType.TForall([listPartTParam],
                NativeType.TFun(listPartPredType, NativeType.TFun(listPartListType, listPartResultType))))

            // List.splitAt : forall 'T. int -> 'T list -> ('T list * 'T list)
            let listSplitAtTParam = freshTypeParam "'T"
            let listSplitAtTVar = NativeType.TVar listSplitAtTParam
            let listSplitAtListType = NativeType.TList(listSplitAtTVar)
            let listSplitAtResultType = NativeType.TTuple([listSplitAtListType; listSplitAtListType], true)
            ("List.splitAt", NativeType.TForall([listSplitAtTParam],
                NativeType.TFun(Types.intType, NativeType.TFun(listSplitAtListType, listSplitAtResultType))))

            // List.groupBy : forall 'T 'K. ('T -> 'K) -> 'T list -> ('K * 'T list) list
            let listGroupByTParam = freshTypeParam "'T"
            let listGroupByKParam = freshTypeParam "'K"
            let listGroupByTVar = NativeType.TVar listGroupByTParam
            let listGroupByKVar = NativeType.TVar listGroupByKParam
            let listGroupByInputType = NativeType.TList(listGroupByTVar)
            let listGroupByElemListType = NativeType.TList(listGroupByTVar)
            let listGroupByPairType = NativeType.TTuple([listGroupByKVar; listGroupByElemListType], true)
            let listGroupByResultType = NativeType.TList(listGroupByPairType)
            let listGroupByFn = NativeType.TFun(listGroupByTVar, listGroupByKVar)
            ("List.groupBy", NativeType.TForall([listGroupByTParam; listGroupByKParam],
                NativeType.TFun(listGroupByFn, NativeType.TFun(listGroupByInputType, listGroupByResultType))))

            //
            // Option module functions
            //

            // Option.map : forall 'T 'U. ('T -> 'U) -> 'T option -> 'U option
            let optMapTParam = freshTypeParam "'T"
            let optMapUParam = freshTypeParam "'U"
            let optMapTVar = NativeType.TVar optMapTParam
            let optMapUVar = NativeType.TVar optMapUParam
            let optMapInputType = mkOptionType optMapTVar
            let optMapResultType = mkOptionType optMapUVar
            let optMapFn = NativeType.TFun(optMapTVar, optMapUVar)
            ("Option.map", NativeType.TForall([optMapTParam; optMapUParam],
                NativeType.TFun(optMapFn, NativeType.TFun(optMapInputType, optMapResultType))))

            // Option.bind : forall 'T 'U. ('T -> 'U option) -> 'T option -> 'U option
            let optBindTParam = freshTypeParam "'T"
            let optBindUParam = freshTypeParam "'U"
            let optBindTVar = NativeType.TVar optBindTParam
            let optBindUVar = NativeType.TVar optBindUParam
            let optBindInputType = mkOptionType optBindTVar
            let optBindResultType = mkOptionType optBindUVar
            let optBindFn = NativeType.TFun(optBindTVar, optBindResultType)
            ("Option.bind", NativeType.TForall([optBindTParam; optBindUParam],
                NativeType.TFun(optBindFn, NativeType.TFun(optBindInputType, optBindResultType))))

            // Option.defaultValue : forall 'T. 'T -> 'T option -> 'T
            let optDefValTParam = freshTypeParam "'T"
            let optDefValTVar = NativeType.TVar optDefValTParam
            let optDefValOptionType = mkOptionType optDefValTVar
            ("Option.defaultValue", NativeType.TForall([optDefValTParam],
                NativeType.TFun(optDefValTVar, NativeType.TFun(optDefValOptionType, optDefValTVar))))

            // Option.isSome : forall 'T. 'T option -> bool
            let optIsSomeTParam = freshTypeParam "'T"
            let optIsSomeTVar = NativeType.TVar optIsSomeTParam
            let optIsSomeOptionType = mkOptionType optIsSomeTVar
            ("Option.isSome", NativeType.TForall([optIsSomeTParam],
                NativeType.TFun(optIsSomeOptionType, Types.boolType)))

            // Option.isNone : forall 'T. 'T option -> bool
            let optIsNoneTParam = freshTypeParam "'T"
            let optIsNoneTVar = NativeType.TVar optIsNoneTParam
            let optIsNoneOptionType = mkOptionType optIsNoneTVar
            ("Option.isNone", NativeType.TForall([optIsNoneTParam],
                NativeType.TFun(optIsNoneOptionType, Types.boolType)))

            // Option.get : forall 'T. 'T option -> 'T
            let optGetTParam = freshTypeParam "'T"
            let optGetTVar = NativeType.TVar optGetTParam
            let optGetOptionType = mkOptionType optGetTVar
            ("Option.get", NativeType.TForall([optGetTParam],
                NativeType.TFun(optGetOptionType, optGetTVar)))

            // =====================================================================
            // Result Module - Error handling operations
            // =====================================================================

            // Result.map : forall 'T 'U 'E. ('T -> 'U) -> Result<'T, 'E> -> Result<'U, 'E>
            let resMapTParam = freshTypeParam "'T"
            let resMapUParam = freshTypeParam "'U"
            let resMapEParam = freshTypeParam "'E"
            let resMapTVar = NativeType.TVar resMapTParam
            let resMapUVar = NativeType.TVar resMapUParam
            let resMapEVar = NativeType.TVar resMapEParam
            let resMapInputType = mkResultType resMapTVar resMapEVar
            let resMapResultType = mkResultType resMapUVar resMapEVar
            let resMapFn = NativeType.TFun(resMapTVar, resMapUVar)
            ("Result.map", NativeType.TForall([resMapTParam; resMapUParam; resMapEParam],
                NativeType.TFun(resMapFn, NativeType.TFun(resMapInputType, resMapResultType))))

            // Result.bind : forall 'T 'U 'E. ('T -> Result<'U, 'E>) -> Result<'T, 'E> -> Result<'U, 'E>
            let resBindTParam = freshTypeParam "'T"
            let resBindUParam = freshTypeParam "'U"
            let resBindEParam = freshTypeParam "'E"
            let resBindTVar = NativeType.TVar resBindTParam
            let resBindUVar = NativeType.TVar resBindUParam
            let resBindEVar = NativeType.TVar resBindEParam
            let resBindInputType = mkResultType resBindTVar resBindEVar
            let resBindResultType = mkResultType resBindUVar resBindEVar
            let resBindFn = NativeType.TFun(resBindTVar, resBindResultType)
            ("Result.bind", NativeType.TForall([resBindTParam; resBindUParam; resBindEParam],
                NativeType.TFun(resBindFn, NativeType.TFun(resBindInputType, resBindResultType))))

            // Result.mapError : forall 'T 'E 'F. ('E -> 'F) -> Result<'T, 'E> -> Result<'T, 'F>
            let resMapErrTParam = freshTypeParam "'T"
            let resMapErrEParam = freshTypeParam "'E"
            let resMapErrFParam = freshTypeParam "'F"
            let resMapErrTVar = NativeType.TVar resMapErrTParam
            let resMapErrEVar = NativeType.TVar resMapErrEParam
            let resMapErrFVar = NativeType.TVar resMapErrFParam
            let resMapErrInputType = mkResultType resMapErrTVar resMapErrEVar
            let resMapErrResultType = mkResultType resMapErrTVar resMapErrFVar
            let resMapErrFn = NativeType.TFun(resMapErrEVar, resMapErrFVar)
            ("Result.mapError", NativeType.TForall([resMapErrTParam; resMapErrEParam; resMapErrFParam],
                NativeType.TFun(resMapErrFn, NativeType.TFun(resMapErrInputType, resMapErrResultType))))

            // Result.isOk : forall 'T 'E. Result<'T, 'E> -> bool
            let resIsOkTParam = freshTypeParam "'T"
            let resIsOkEParam = freshTypeParam "'E"
            let resIsOkTVar = NativeType.TVar resIsOkTParam
            let resIsOkEVar = NativeType.TVar resIsOkEParam
            let resIsOkType = mkResultType resIsOkTVar resIsOkEVar
            ("Result.isOk", NativeType.TForall([resIsOkTParam; resIsOkEParam],
                NativeType.TFun(resIsOkType, Types.boolType)))

            // Result.isError : forall 'T 'E. Result<'T, 'E> -> bool
            let resIsErrTParam = freshTypeParam "'T"
            let resIsErrEParam = freshTypeParam "'E"
            let resIsErrTVar = NativeType.TVar resIsErrTParam
            let resIsErrEVar = NativeType.TVar resIsErrEParam
            let resIsErrType = mkResultType resIsErrTVar resIsErrEVar
            ("Result.isError", NativeType.TForall([resIsErrTParam; resIsErrEParam],
                NativeType.TFun(resIsErrType, Types.boolType)))

            // Result.defaultValue : forall 'T 'E. 'T -> Result<'T, 'E> -> 'T
            let resDefValTParam = freshTypeParam "'T"
            let resDefValEParam = freshTypeParam "'E"
            let resDefValTVar = NativeType.TVar resDefValTParam
            let resDefValEVar = NativeType.TVar resDefValEParam
            let resDefValType = mkResultType resDefValTVar resDefValEVar
            ("Result.defaultValue", NativeType.TForall([resDefValTParam; resDefValEParam],
                NativeType.TFun(resDefValTVar, NativeType.TFun(resDefValType, resDefValTVar))))

            // =====================================================================
            // Bits Module - Byte manipulation and bit reinterpretation
            // =====================================================================

            // Bits.toUInt16 : byte[] -> int -> uint16 (little-endian read)
            ("Bits.toUInt16", NativeType.TFun(mkArrayType Types.uint8Type,
                NativeType.TFun(Types.intType, Types.uint16Type)))

            // Bits.toUInt32 : byte[] -> int -> uint32 (little-endian read)
            ("Bits.toUInt32", NativeType.TFun(mkArrayType Types.uint8Type,
                NativeType.TFun(Types.intType, Types.uint32Type)))

            // Bits.toUInt64 : byte[] -> int -> uint64 (little-endian read)
            ("Bits.toUInt64", NativeType.TFun(mkArrayType Types.uint8Type,
                NativeType.TFun(Types.intType, Types.uint64Type)))

            // Bits.toInt16 : byte[] -> int -> int16 (little-endian read)
            ("Bits.toInt16", NativeType.TFun(mkArrayType Types.uint8Type,
                NativeType.TFun(Types.intType, Types.int16Type)))

            // Bits.toInt32 : byte[] -> int -> int32 (little-endian read)
            ("Bits.toInt32", NativeType.TFun(mkArrayType Types.uint8Type,
                NativeType.TFun(Types.intType, Types.int32Type)))

            // Bits.toInt64 : byte[] -> int -> int64 (little-endian read)
            ("Bits.toInt64", NativeType.TFun(mkArrayType Types.uint8Type,
                NativeType.TFun(Types.intType, Types.int64Type)))

            // Network byte order conversion
            // Bits.htons : uint16 -> uint16
            ("Bits.htons", NativeType.TFun(Types.uint16Type, Types.uint16Type))
            // Bits.ntohs : uint16 -> uint16
            ("Bits.ntohs", NativeType.TFun(Types.uint16Type, Types.uint16Type))
            // Bits.htonl : uint32 -> uint32
            ("Bits.htonl", NativeType.TFun(Types.uint32Type, Types.uint32Type))
            // Bits.ntohl : uint32 -> uint32
            ("Bits.ntohl", NativeType.TFun(Types.uint32Type, Types.uint32Type))

            // Bit reinterpretation (type punning)
            // Bits.float32ToInt32Bits : float32 -> int32
            ("Bits.float32ToInt32Bits", NativeType.TFun(Types.float32Type, Types.int32Type))
            // Bits.int32BitsToFloat32 : int32 -> float32
            ("Bits.int32BitsToFloat32", NativeType.TFun(Types.int32Type, Types.float32Type))
            // Bits.float64ToInt64Bits : float -> int64
            ("Bits.float64ToInt64Bits", NativeType.TFun(Types.floatType, Types.int64Type))
            // Bits.int64BitsToFloat64 : int64 -> float
            ("Bits.int64BitsToFloat64", NativeType.TFun(Types.int64Type, Types.floatType))

            // =====================================================================
            // String Module - UTF-8 byte operations
            // =====================================================================

            // String.toBytes : string -> byte[] (UTF-8 encoding)
            ("String.toBytes", NativeType.TFun(Types.stringType, mkArrayType Types.uint8Type))

            // String.fromBytes : byte[] -> string (UTF-8 decoding)
            ("String.fromBytes", NativeType.TFun(mkArrayType Types.uint8Type, Types.stringType))
        ]

//-------------------------------------------------------------------------
// Native Globals Container
//-------------------------------------------------------------------------

/// Container for all native global type information.
/// This is passed through the type checker as the environment.
[<NoComparison; NoEquality>]
type NativeGlobals = {
    /// Primitive type constructors
    Primitives: Map<string, TypeConRef>
    
    /// Parameterized type constructors
    Parameterized: Map<string, TypeConRef>
    
    /// Built-in F# function bindings (name -> type)
    BuiltInBindings: Map<string, NativeType>
    
    /// Pre-constructed common types
    StringType: NativeType
    IntType: NativeType
    Int64Type: NativeType
    FloatType: NativeType
    BoolType: NativeType
    CharType: NativeType
    UnitType: NativeType
    ExnType: NativeType
}

/// Create the native globals environment
let createNativeGlobals() : NativeGlobals = {
    Primitives = primitiveTyConsByName
    Parameterized = parameterizedTyConsByName
    BuiltInBindings = BuiltInFunctions.getBuiltInBindings() |> Map.ofList
    StringType = Types.stringType
    IntType = Types.intType
    Int64Type = Types.int64Type
    FloatType = Types.floatType
    BoolType = Types.boolType
    CharType = Types.charType
    UnitType = Types.unitType
    ExnType = Types.exnType
}

//-------------------------------------------------------------------------
// Type Checking Helpers
//-------------------------------------------------------------------------

/// Check if a type is the unit type (using NTUKind for robust checking)
let isUnitType ty =
    match ty with
    | NativeType.TApp(tc, []) ->
        match tc.NTUKind with
        | Some NTUKind.NTUunit -> true
        | _ -> false
    | _ -> false

/// Check if a type is a numeric type (using NTUKind for robust checking)
let isNumericType ty =
    match ty with
    | NativeType.TApp(tc, []) ->
        match tc.NTUKind with
        | Some kind -> NTUKind.isNumeric kind || kind = NTUKind.NTUdecimal
        | None -> false
    | _ -> false

/// Check if a type is an integer type (using NTUKind for robust checking)
let isIntegerType ty =
    match ty with
    | NativeType.TApp(tc, []) ->
        match tc.NTUKind with
        | Some kind -> NTUKind.isInteger kind
        | None -> false
    | _ -> false

/// Check if a type is a floating point type (using NTUKind for robust checking)
let isFloatType ty =
    match ty with
    | NativeType.TApp(tc, []) ->
        match tc.NTUKind with
        | Some kind -> NTUKind.isFloatingPoint kind || kind = NTUKind.NTUdecimal
        | None -> false
    | _ -> false

/// Check if a type is platform-dependent (using NTUKind)
let isPlatformDependentType ty =
    match ty with
    | NativeType.TApp(tc, _) ->
        match tc.NTUKind with
        | Some kind -> NTUKind.isPlatformDependent kind
        | None -> tc.Layout = TypeLayout.PlatformWord
    | NativeType.TNativePtr _ -> true
    | NativeType.TByref _ -> true
    | _ -> false

/// Get the NTUKind of a type, if it has one
let getNTUKind ty =
    match ty with
    | NativeType.TApp(tc, _) -> tc.NTUKind
    | NativeType.TNativePtr _ -> Some NTUKind.NTUptr
    | NativeType.TByref _ -> Some NTUKind.NTUptr
    | _ -> None

/// Check if a type is a value type (stack-allocated)
let rec isValueType ty =
    match ty with
    | NativeType.TApp(tc, _) ->
        match tc.Layout with
        | TypeLayout.Inline _ -> true
        | TypeLayout.PlatformWord -> true  // Platform word types are value types
        | TypeLayout.FatPointer -> true    // Fat pointers are value types (structs)
        | TypeLayout.NTUCompound _ -> true // NTU compounds are value types
        | TypeLayout.Reference _ -> false
        | TypeLayout.Opaque -> false  // Conservative
    | NativeType.TTuple(_, isStruct) -> isStruct
    | NativeType.TFun _ -> false  // Functions are closures
    | NativeType.TVar _ -> false  // Unknown until solved
    | NativeType.TByref _ -> true  // Byrefs are value types
    | NativeType.TNativePtr _ -> true  // Pointers are value types
    | NativeType.TForall(_, body) -> isValueType body
    | NativeType.TMeasure _ -> true  // Phantom type
    | NativeType.TAnon(_, isStruct) -> isStruct  // Struct anon records are value types
    // Named records use TApp - handled above via tc.Layout check
    | NativeType.TUnion(tc, _) ->
        match tc.Layout with
        | TypeLayout.Inline _ -> true
        | TypeLayout.PlatformWord -> true
        | TypeLayout.FatPointer -> true
        | TypeLayout.NTUCompound _ -> true
        | _ -> false
    | NativeType.TLazy _ -> true  // Lazy<'T> is a value type struct (PRD-14)
    | NativeType.TSeq _ -> true  // seq<'T> is a value type struct (PRD-15)
    | NativeType.TSeqEnumerator _ -> true  // SeqEnumerator<'T> is a value type struct (PRD-15/16)
    // PRD-13a: Immutable collection types (reference types - pointer to nodes)
    | NativeType.TList _ -> false  // list<'T> is a reference type (linked list nodes)
    | NativeType.TMap _ -> false  // Map<'K,'V> is a reference type (tree nodes)
    | NativeType.TSet _ -> false  // Set<'T> is a reference type (tree nodes)
    // Note: option<'T> is handled via TUnion - it's a discriminated union, not a special type
    | NativeType.TError _ -> false

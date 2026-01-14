// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Built-in types with native semantics.
/// These define the type universe for native F# compilation.
///
/// KEY DESIGN: Units of measure work on ANY type in fsnative (not just numerics).
/// This enables memory region tracking, access control, and type-safe hardware access.
module FSharp.Native.Compiler.Checking.Native.NativeGlobals

open FSharp.Native.Compiler.Checking.Native.NativeTypes

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
      ("Exception", Primitives.exnTyCon) ]  // Alias
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
      ("Memo", memoTyCon) ]
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
let mkListType elemType = NativeType.TApp(Parameterized.listTyCon, [elemType])

/// Create a sequence type: seq<'T>
let mkSeqType elemType = NativeType.TApp(Parameterized.seqTyCon, [elemType])

/// Create a ref type: 'T ref
let mkRefType elemType = NativeType.TApp(Parameterized.refTyCon, [elemType])

/// Create a quotation type: Expr<'T>
let mkExprType elemType = NativeType.TApp(Parameterized.exprTyCon, [elemType])

/// Create a lazy type: Lazy<'T>
let mkLazyType elemType = NativeType.TApp(Parameterized.lazyTyCon, [elemType])

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
            // Note: This is a type function, not a value function
            // For now, model as unit -> int (will be specialized)
            ("sizeof", NativeType.TFun(Types.unitType, Types.intType))
            
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
            
            // box/unbox - these are BCL-dependent and will emit errors in codegen
            // but we provide types so code type-checks before failing
            // box : forall 'a 'b. 'a -> 'b (erased in native, types don't actually match)
            let boxAParam = freshTypeParam "'a"
            let boxBParam = freshTypeParam "'b"
            ("box", NativeType.TForall([boxAParam; boxBParam], NativeType.TFun(NativeType.TVar boxAParam, NativeType.TVar boxBParam)))
            // unbox : forall 'a 'b. 'a -> 'b (erased in native)
            let unboxAParam = freshTypeParam "'a"
            let unboxBParam = freshTypeParam "'b"
            ("unbox", NativeType.TForall([unboxAParam; unboxBParam], NativeType.TFun(NativeType.TVar unboxAParam, NativeType.TVar unboxBParam)))
            
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
    | NativeType.TRecord(tc, _) -> 
        match tc.Layout with
        | TypeLayout.Inline _ -> true
        | TypeLayout.PlatformWord -> true
        | TypeLayout.FatPointer -> true
        | TypeLayout.NTUCompound _ -> true
        | _ -> false
    | NativeType.TUnion(tc, _) ->
        match tc.Layout with
        | TypeLayout.Inline _ -> true
        | TypeLayout.PlatformWord -> true
        | TypeLayout.FatPointer -> true
        | TypeLayout.NTUCompound _ -> true
        | _ -> false
    | NativeType.TError _ -> false

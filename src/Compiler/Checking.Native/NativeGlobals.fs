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
module Primitives =
    /// UTF-8 string: fat pointer (ptr: 8 bytes, length: 8 bytes)
    let stringTyCon = mkTypeConRef "string" 0 (TypeLayout.Inline(16, 8))
    
    /// Platform word signed integer: size determined by target platform
    /// On 32-bit: 4 bytes, on 64-bit: 8 bytes
    /// This matches Rust's isize / C's intptr_t
    /// NOTE: -1 indicates platform-dependent layout, resolved at code generation
    let intTyCon = mkTypeConRef "int" 0 (TypeLayout.Inline(-1, -1))
    
    /// 64-bit signed integer (fixed size, not platform-dependent)
    let int64TyCon = mkTypeConRef "int64" 0 (TypeLayout.Inline(8, 8))
    
    /// Platform word unsigned integer: size determined by target platform
    /// On 32-bit: 4 bytes, on 64-bit: 8 bytes
    /// This matches Rust's usize / C's uintptr_t
    /// NOTE: -1 indicates platform-dependent layout, resolved at code generation
    let uintTyCon = mkTypeConRef "uint" 0 (TypeLayout.Inline(-1, -1))
    
    /// 32-bit signed integer (fixed size)
    /// Use this when you need exactly 32 bits, regardless of platform
    let int32TyCon = mkTypeConRef "int32" 0 (TypeLayout.Inline(4, 4))
    
    /// 32-bit unsigned integer (fixed size)
    /// Use this when you need exactly 32 bits, regardless of platform
    let uint32TyCon = mkTypeConRef "uint32" 0 (TypeLayout.Inline(4, 4))
    
    /// 64-bit unsigned integer (fixed size, not platform-dependent)
    let uint64TyCon = mkTypeConRef "uint64" 0 (TypeLayout.Inline(8, 8))
    
    /// 8-bit signed integer
    let int8TyCon = mkTypeConRef "int8" 0 (TypeLayout.Inline(1, 1))
    
    /// 8-bit unsigned integer
    let uint8TyCon = mkTypeConRef "uint8" 0 (TypeLayout.Inline(1, 1))
    
    /// 16-bit signed integer
    let int16TyCon = mkTypeConRef "int16" 0 (TypeLayout.Inline(2, 2))
    
    /// 16-bit unsigned integer
    let uint16TyCon = mkTypeConRef "uint16" 0 (TypeLayout.Inline(2, 2))
    
    /// Native-size signed integer
    let nintTyCon = mkTypeConRef "nativeint" 0 (TypeLayout.Inline(8, 8))
    
    /// Native-size unsigned integer
    let unintTyCon = mkTypeConRef "unativeint" 0 (TypeLayout.Inline(8, 8))
    
    /// 64-bit floating point (IEEE 754 double)
    let floatTyCon = mkTypeConRef "float" 0 (TypeLayout.Inline(8, 8))
    
    /// 32-bit floating point (IEEE 754 single)
    let float32TyCon = mkTypeConRef "float32" 0 (TypeLayout.Inline(4, 4))
    
    /// Boolean: 1 byte
    let boolTyCon = mkTypeConRef "bool" 0 (TypeLayout.Inline(1, 1))
    
    /// Unicode code point (UTF-32): 4 bytes
    let charTyCon = mkTypeConRef "char" 0 (TypeLayout.Inline(4, 4))
    
    /// Unit type: zero-sized type
    let unitTyCon = mkTypeConRef "unit" 0 (TypeLayout.Inline(0, 1))
    
    /// Decimal: 16 bytes
    let decimalTyCon = mkTypeConRef "decimal" 0 (TypeLayout.Inline(16, 8))

    /// Exception type: native exception representation
    /// Layout: tagged union with string message + optional data
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

    /// Array type: fat pointer (ptr: 8 bytes, length: 8 bytes)
    let arrayTyCon = mkTypeConRef "array" 1 (TypeLayout.Inline(16, 8))

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
    /// Fat pointer (ptr + length) with memory safety
    let spanTyCon =
        mkTypeConRefWithMeasures "Span"
            [TypeParamKind.Type; TypeParamKind.Measure; TypeParamKind.Measure]
            (TypeLayout.Inline(16, 8))

//-------------------------------------------------------------------------
// Built-in Types (pre-constructed)
//-------------------------------------------------------------------------

/// Pre-constructed types for common use
module Types =
    let stringType = mkSimpleType Primitives.stringTyCon
    let intType = mkSimpleType Primitives.intTyCon     // Platform word
    let int32Type = mkSimpleType Primitives.int32TyCon // Fixed 32-bit
    let int64Type = mkSimpleType Primitives.int64TyCon // Fixed 64-bit
    let uintType = mkSimpleType Primitives.uintTyCon   // Platform word
    let uint32Type = mkSimpleType Primitives.uint32TyCon // Fixed 32-bit
    let uint64Type = mkSimpleType Primitives.uint64TyCon // Fixed 64-bit
    let int8Type = mkSimpleType Primitives.int8TyCon
    let uint8Type = mkSimpleType Primitives.uint8TyCon
    let int16Type = mkSimpleType Primitives.int16TyCon
    let uint16Type = mkSimpleType Primitives.uint16TyCon
    let nintType = mkSimpleType Primitives.nintTyCon
    let unintType = mkSimpleType Primitives.unintTyCon
    let floatType = mkSimpleType Primitives.floatTyCon
    let float32Type = mkSimpleType Primitives.float32TyCon
    let boolType = mkSimpleType Primitives.boolTyCon
    let charType = mkSimpleType Primitives.charTyCon
    let unitType = mkSimpleType Primitives.unitTyCon
    let decimalType = mkSimpleType Primitives.decimalTyCon
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
      ("exn", Primitives.exnTyCon)
      ("Exception", Primitives.exnTyCon) ]  // Alias
    |> Map.ofList

/// Native pointer type: nativeptr<'T>
let nativeptrTyCon = mkTypeConRef "nativeptr" 1 (TypeLayout.Inline(8, 8))

/// Void pointer type: voidptr
let voidptrTyCon = mkTypeConRef "voidptr" 0 (TypeLayout.Inline(8, 8))

/// Byref type: byref<'T> - managed reference, maps to pointer in native
let byrefTyCon = mkTypeConRef "byref" 1 (TypeLayout.Inline(8, 8))

/// Inref type: inref<'T> - read-only byref
let inrefTyCon = mkTypeConRef "inref" 1 (TypeLayout.Inline(8, 8))

/// Outref type: outref<'T> - write-only byref  
let outrefTyCon = mkTypeConRef "outref" 1 (TypeLayout.Inline(8, 8))

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
      ("outref", outrefTyCon) ]
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

//-------------------------------------------------------------------------
// Built-in F# Intrinsic Functions
//-------------------------------------------------------------------------

/// Built-in F# language functions that must be provided by the type checker.
/// These are the functions that are normally in FSharp.Core's Operators module.
module BuiltInFunctions =
    
    // Create type variables for polymorphic functions
    let private freshTyVar name =
        let tyParam = {
            Id = -(name.GetHashCode())
            Name = name
            Kind = TypeParamKind.Type
            Constraints = []
            Parent = TypeParamState.Unbound
            Range = { File = "<builtin>"; Start = { Line = 0; Column = 0 }; End = { Line = 0; Column = 0 } }
        }
        NativeType.TVar tyParam

    /// Conversion function type: 'T -> targetType
    /// These use SRTP internally but for type checking we model them as simple conversions
    let mkConversionType targetType =
        let inputVar = freshTyVar "'a"
        NativeType.TFun(inputVar, targetType)
    
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
            
            // Utility functions
            ("ignore", NativeType.TFun(freshTyVar "'a", Types.unitType))  // 'a -> unit
            
            // abs : 'a -> 'a (SRTP-based, returns same type)
            let absVar = freshTyVar "'a"
            ("abs", NativeType.TFun(absVar, absVar))
            
            // sizeof<'T> : int (type-level function, returns int)
            // Note: This is a type function, not a value function
            // For now, model as unit -> int (will be specialized)
            ("sizeof", NativeType.TFun(Types.unitType, Types.intType))
            
            // Floating point special values
            ("nan", Types.floatType)   // Not a function, a value
            ("nanf", Types.float32Type)
            ("infinity", Types.floatType)
            ("infinityf", Types.float32Type)
            
            // ValueOption union case constructors
            // ValueNone : voption<'a>
            ("ValueNone", mkValueOptionType (freshTyVar "'a"))
            // ValueSome : 'a -> voption<'a>
            let vosomeVar = freshTyVar "'a"
            ("ValueSome", NativeType.TFun(vosomeVar, mkValueOptionType vosomeVar))
            
            // Result union case constructors
            // Ok : 'T -> Result<'T, 'Error>
            let okVar = freshTyVar "'T"
            let okErrVar = freshTyVar "'Error"
            ("Ok", NativeType.TFun(okVar, mkResultType okVar okErrVar))
            // Error : 'Error -> Result<'T, 'Error>
            let errVar = freshTyVar "'T"
            let errErrVar = freshTyVar "'Error"
            ("Error", NativeType.TFun(errErrVar, mkResultType errVar errErrVar))
            
            // Option union case constructors (for compatibility)
            // None : option<'a>
            ("None", mkOptionType (freshTyVar "'a"))
            // Some : 'a -> option<'a>
            let someVar = freshTyVar "'a"
            ("Some", NativeType.TFun(someVar, mkOptionType someVar))
            
            // box/unbox - these are BCL-dependent and will emit errors
            // but we provide types so code type-checks before failing
            ("box", NativeType.TFun(freshTyVar "'a", freshTyVar "'obj"))
            ("unbox", NativeType.TFun(freshTyVar "'obj", freshTyVar "'a"))
            
            // printf family - format string functions
            // For now, model as string -> unit (simplified)
            ("printf", NativeType.TFun(Types.stringType, Types.unitType))
            ("printfn", NativeType.TFun(Types.stringType, Types.unitType))
            ("sprintf", NativeType.TFun(Types.stringType, Types.stringType))
            ("failwith", NativeType.TFun(Types.stringType, freshTyVar "'a"))
            ("failwithf", NativeType.TFun(Types.stringType, freshTyVar "'a"))
            
            // Arithmetic operators (SRTP-based)
            // op_Addition : 'a -> 'a -> 'a
            let addVar = freshTyVar "'a"
            ("op_Addition", NativeType.TFun(addVar, NativeType.TFun(addVar, addVar)))
            let subVar = freshTyVar "'a"
            ("op_Subtraction", NativeType.TFun(subVar, NativeType.TFun(subVar, subVar)))
            let mulVar = freshTyVar "'a"
            ("op_Multiply", NativeType.TFun(mulVar, NativeType.TFun(mulVar, mulVar)))
            let divVar = freshTyVar "'a"
            ("op_Division", NativeType.TFun(divVar, NativeType.TFun(divVar, divVar)))
            let modVar = freshTyVar "'a"
            ("op_Modulus", NativeType.TFun(modVar, NativeType.TFun(modVar, modVar)))
            
            // Comparison operators
            let eqVar = freshTyVar "'a"
            ("op_Equality", NativeType.TFun(eqVar, NativeType.TFun(eqVar, Types.boolType)))
            let neqVar = freshTyVar "'a"
            ("op_Inequality", NativeType.TFun(neqVar, NativeType.TFun(neqVar, Types.boolType)))
            let ltVar = freshTyVar "'a"
            ("op_LessThan", NativeType.TFun(ltVar, NativeType.TFun(ltVar, Types.boolType)))
            let gtVar = freshTyVar "'a"
            ("op_GreaterThan", NativeType.TFun(gtVar, NativeType.TFun(gtVar, Types.boolType)))
            let leVar = freshTyVar "'a"
            ("op_LessThanOrEqual", NativeType.TFun(leVar, NativeType.TFun(leVar, Types.boolType)))
            let geVar = freshTyVar "'a"
            ("op_GreaterThanOrEqual", NativeType.TFun(geVar, NativeType.TFun(geVar, Types.boolType)))
            
            // Bitwise operators
            let bandVar = freshTyVar "'a"
            ("op_BitwiseAnd", NativeType.TFun(bandVar, NativeType.TFun(bandVar, bandVar)))
            let borVar = freshTyVar "'a"
            ("op_BitwiseOr", NativeType.TFun(borVar, NativeType.TFun(borVar, borVar)))
            let bxorVar = freshTyVar "'a"
            ("op_ExclusiveOr", NativeType.TFun(bxorVar, NativeType.TFun(bxorVar, bxorVar)))
            let shlVar = freshTyVar "'a"
            ("op_LeftShift", NativeType.TFun(shlVar, NativeType.TFun(Types.intType, shlVar)))
            let shrVar = freshTyVar "'a"
            ("op_RightShift", NativeType.TFun(shrVar, NativeType.TFun(Types.intType, shrVar)))
            
            // Logical operators
            ("op_BooleanAnd", NativeType.TFun(Types.boolType, NativeType.TFun(Types.boolType, Types.boolType)))
            ("op_BooleanOr", NativeType.TFun(Types.boolType, NativeType.TFun(Types.boolType, Types.boolType)))
            ("not", NativeType.TFun(Types.boolType, Types.boolType))
            
            // Unary operators
            let negVar = freshTyVar "'a"
            ("op_UnaryNegation", NativeType.TFun(negVar, negVar))
            ("op_LogicalNot", NativeType.TFun(Types.boolType, Types.boolType))
            
            // Pipe operators: 'a -> ('a -> 'b) -> 'b and ('a -> 'b) -> 'a -> 'b
            let pipeAVar = freshTyVar "'a"
            let pipeBVar = freshTyVar "'b"
            let pipeFunc = NativeType.TFun(pipeAVar, pipeBVar)
            ("op_PipeRight", NativeType.TFun(pipeAVar, NativeType.TFun(pipeFunc, pipeBVar)))  // |>
            ("op_PipeLeft", NativeType.TFun(pipeFunc, NativeType.TFun(pipeAVar, pipeBVar)))   // <|
            
            // Composition operators: ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c
            let compAVar = freshTyVar "'a"
            let compBVar = freshTyVar "'b"
            let compCVar = freshTyVar "'c"
            ("op_ComposeRight", NativeType.TFun(NativeType.TFun(compAVar, compBVar), 
                NativeType.TFun(NativeType.TFun(compBVar, compCVar), NativeType.TFun(compAVar, compCVar))))  // >>
            ("op_ComposeLeft", NativeType.TFun(NativeType.TFun(compBVar, compCVar), 
                NativeType.TFun(NativeType.TFun(compAVar, compBVar), NativeType.TFun(compAVar, compCVar))))  // <<
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

/// Check if a type is the unit type
let isUnitType ty =
    match ty with
    | NativeType.TApp(tc, []) when tc.Name = "unit" -> true
    | _ -> false

/// Check if a type is a numeric type
let isNumericType ty =
    match ty with
    | NativeType.TApp(tc, []) ->
        match tc.Name with
        | "int" | "int8" | "int16" | "int64"
        | "uint" | "uint8" | "uint16" | "uint64"
        | "nativeint" | "unativeint"
        | "float" | "float32" | "decimal" -> true
        | _ -> false
    | _ -> false

/// Check if a type is an integer type
let isIntegerType ty =
    match ty with
    | NativeType.TApp(tc, []) ->
        match tc.Name with
        | "int" | "int8" | "int16" | "int64"
        | "uint" | "uint8" | "uint16" | "uint64"
        | "nativeint" | "unativeint" -> true
        | _ -> false
    | _ -> false

/// Check if a type is a floating point type
let isFloatType ty =
    match ty with
    | NativeType.TApp(tc, []) ->
        match tc.Name with
        | "float" | "float32" | "decimal" -> true
        | _ -> false
    | _ -> false

/// Check if a type is a value type (stack-allocated)
let rec isValueType ty =
    match ty with
    | NativeType.TApp(tc, _) ->
        match tc.Layout with
        | TypeLayout.Inline _ -> true
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
        | _ -> false
    | NativeType.TUnion(tc, _) ->
        match tc.Layout with
        | TypeLayout.Inline _ -> true
        | _ -> false
    | NativeType.TError _ -> false

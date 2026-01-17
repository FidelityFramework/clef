// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Core type representation for the native type checker.
/// These types are used throughout the type checking process and in the output semantic graph.
module FSharp.Native.Compiler.Checking.Native.NativeTypes

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
// Type Layout (Memory Representation)
//-------------------------------------------------------------------------


//-------------------------------------------------------------------------
// NTU (Native Type Universe) Kind System
// Following F* pattern: type identity is separate from type width.
// Width is erased metadata resolved by Alex via platform quotations.
//-------------------------------------------------------------------------

/// NTU (Native Type Universe) type kinds.
/// These categorize native types semantically, independent of platform width.
/// Type identity: NTUint ≠ NTUint64 (different types even if same width on some platforms)
[<RequireQualifiedAccess>]
type NTUKind =
    //-----------------------------------------------------------------------
    // Platform-dependent types (resolved via quotations at codegen)
    //-----------------------------------------------------------------------
    
    /// Platform word, signed (F# `int` in Fidelity semantics)
    /// 64-bit on x86_64, 32-bit on ARM32, etc.
    | NTUint
    
    /// Platform word, unsigned (F# `uint` in Fidelity semantics)
    | NTUuint
    
    /// Native int, pointer-sized signed (explicit `nativeint`)
    /// Semantically equivalent to NTUint but kept separate for source fidelity
    | NTUnint
    
    /// Native uint, pointer-sized unsigned (explicit `unativeint`)
    /// Semantically equivalent to NTUuint but kept separate for source fidelity
    | NTUunint
    
    /// Native pointer type (pointer-sized)
    | NTUptr

    /// Function pointer type (pointer-sized)
    /// Used for callbacks to top-level functions (no closures)
    | NTUfnptr

    /// Size type (like C `size_t`) - used for array lengths, memory sizes
    | NTUsize
    
    /// Pointer difference type (like C `ptrdiff_t`)
    | NTUdiff
    
    //-----------------------------------------------------------------------
    // Fixed width types (platform-independent)
    //-----------------------------------------------------------------------
    
    /// 8-bit signed integer
    | NTUint8
    /// 16-bit signed integer
    | NTUint16
    /// 32-bit signed integer
    | NTUint32
    /// 64-bit signed integer
    | NTUint64
    
    /// 8-bit unsigned integer
    | NTUuint8
    /// 16-bit unsigned integer
    | NTUuint16
    /// 32-bit unsigned integer
    | NTUuint32
    /// 64-bit unsigned integer
    | NTUuint64
    
    /// 32-bit IEEE 754 floating point
    | NTUfloat32
    /// 64-bit IEEE 754 floating point
    | NTUfloat64
    
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
    
    /// Not a primitive NTU kind (user-defined types, parameterized types, etc.)
    | NTUother

/// Platform predicate types (abstract, erased at runtime).
/// F*-inspired propositions for conditional compilation without runtime checks.
/// These flow through FNCS unchanged and are resolved by Alex using platform quotations.
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

/// Helpers for NTUKind
module NTUKind =
    /// Check if an NTUKind is platform-dependent (requires quotation resolution)
    let isPlatformDependent = function
        | NTUKind.NTUint | NTUKind.NTUuint
        | NTUKind.NTUnint | NTUKind.NTUunint
        | NTUKind.NTUptr | NTUKind.NTUfnptr | NTUKind.NTUsize | NTUKind.NTUdiff -> true
        | _ -> false
    
    /// Check if an NTUKind is a fixed-width integer
    let isFixedWidthInteger = function
        | NTUKind.NTUint8 | NTUKind.NTUint16 | NTUKind.NTUint32 | NTUKind.NTUint64
        | NTUKind.NTUuint8 | NTUKind.NTUuint16 | NTUKind.NTUuint32 | NTUKind.NTUuint64 -> true
        | _ -> false
    
    /// Check if an NTUKind is any integer type
    let isInteger = function
        | NTUKind.NTUint | NTUKind.NTUuint | NTUKind.NTUnint | NTUKind.NTUunint
        | NTUKind.NTUint8 | NTUKind.NTUint16 | NTUKind.NTUint32 | NTUKind.NTUint64
        | NTUKind.NTUuint8 | NTUKind.NTUuint16 | NTUKind.NTUuint32 | NTUKind.NTUuint64
        | NTUKind.NTUsize | NTUKind.NTUdiff -> true
        | _ -> false
    
    /// Check if an NTUKind is a signed integer
    let isSigned = function
        | NTUKind.NTUint | NTUKind.NTUnint
        | NTUKind.NTUint8 | NTUKind.NTUint16 | NTUKind.NTUint32 | NTUKind.NTUint64
        | NTUKind.NTUdiff -> true
        | _ -> false
    
    /// Check if an NTUKind is floating point
    let isFloatingPoint = function
        | NTUKind.NTUfloat32 | NTUKind.NTUfloat64 -> true
        | _ -> false
    
    /// Check if an NTUKind is numeric (integer or floating point)
    let isNumeric kind = isInteger kind || isFloatingPoint kind
    
    /// Get the human-readable name for an NTUKind
    let name = function
        | NTUKind.NTUint -> "int"
        | NTUKind.NTUuint -> "uint"
        | NTUKind.NTUnint -> "nativeint"
        | NTUKind.NTUunint -> "unativeint"
        | NTUKind.NTUptr -> "nativeptr"
        | NTUKind.NTUfnptr -> "fnptr"
        | NTUKind.NTUsize -> "size"
        | NTUKind.NTUdiff -> "diff"
        | NTUKind.NTUint8 -> "int8"
        | NTUKind.NTUint16 -> "int16"
        | NTUKind.NTUint32 -> "int32"
        | NTUKind.NTUint64 -> "int64"
        | NTUKind.NTUuint8 -> "uint8"
        | NTUKind.NTUuint16 -> "uint16"
        | NTUKind.NTUuint32 -> "uint32"
        | NTUKind.NTUuint64 -> "uint64"
        | NTUKind.NTUfloat32 -> "float32"
        | NTUKind.NTUfloat64 -> "float"
        | NTUKind.NTUstring -> "string"
        | NTUKind.NTUbool -> "bool"
        | NTUKind.NTUchar -> "char"
        | NTUKind.NTUunit -> "unit"
        | NTUKind.NTUdecimal -> "decimal"
        | NTUKind.NTUlazy -> "Lazy"
        | NTUKind.NTUuuid -> "Uuid"
        | NTUKind.NTUdatetime -> "DateTime"
        | NTUKind.NTUtimespan -> "TimeSpan"
        | NTUKind.NTUother -> "<other>"

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
    /// FNCS preserves type identity; Alex resolves to concrete size
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

/// Arena affinity for memory management
and [<RequireQualifiedAccess>] ArenaAffinity =
    /// Default: current actor's arena
    | CurrentActor
    /// Named arena (explicit allocation context)
    | Explicit of name: string
    /// Stack allocation (no arena, scope-bound)
    | Stack

//-------------------------------------------------------------------------
// Type Parameter Kind
//-------------------------------------------------------------------------

/// Distinguishes type parameters from measure parameters.
/// In fsnative, measures work on ANY type (not just numerics like in .NET F#).
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
}

/// Total arity (type + measure parameters)
let arity (tc: TypeConRef) = List.length tc.ParamKinds

/// Create a simple type constructor with only type parameters (non-NTU kind)
let mkTypeConRef name typeArity layout =
    { Name = name; Module = []; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = None; FieldCount = 0 }

/// Create a type constructor with explicit parameter kinds (non-NTU kind)
let mkTypeConRefWithMeasures name paramKinds layout =
    { Name = name; Module = []; ParamKinds = paramKinds; Layout = layout; NTUKind = None; FieldCount = 0 }

/// Create a type constructor with an NTU kind (for native primitives)
let mkNTUTypeConRef name ntuKind layout =
    { Name = name; Module = []; ParamKinds = []; Layout = layout; NTUKind = Some ntuKind; FieldCount = 0 }

/// Create a parameterized type constructor with an NTU kind
let mkNTUTypeConRefWithArity name ntuKind typeArity layout =
    { Name = name; Module = []; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = Some ntuKind; FieldCount = 0 }

/// Create a type constructor for a record type
/// Field info is accessed via SemanticGraph.Types lookup (not embedded in TypeConRef)
let mkRecordTypeConRef name modulePath layout fieldCount =
    { Name = name; Module = modulePath; ParamKinds = []; Layout = layout; NTUKind = None; FieldCount = fieldCount }

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
// Record Type Infrastructure (for Field Label Resolution)
// Per fsnative-spec inference-procedures.md: "Field order determines memory layout"
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
    | NativeType.TApp(tycon, _) -> tycon.Layout
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
    | NativeType.TError _ -> TypeLayout.Opaque

/// Compute memory layout for a record from its fields.
/// Per fsnative-spec: "Field order determines memory layout" and
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
        let fieldLayout = layoutOf fieldType
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
        | NativeType.TMeasure _ -> ty
        | NativeType.TError _ -> ty
    
    go body

//-------------------------------------------------------------------------
// Pretty Printing
//-------------------------------------------------------------------------

/// Format a type for display
let rec formatType (ty: NativeType) : string =
    match ty with
    | NativeType.TVar tp -> tp.Name
    | NativeType.TApp(tc, []) -> tc.Name
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
    | NativeType.TError msg -> $"<error: {msg}>"

and formatMeasure (m: Measure) : string =
    match m with
    | MOne -> "1"
    | MVar tp -> tp.Name
    | MProd(m1, m2) -> $"{formatMeasure m1}*{formatMeasure m2}"
    | MInv m -> $"1/{formatMeasure m}"
    | MCon(name, _) -> name

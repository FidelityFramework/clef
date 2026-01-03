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

/// Type layout determines memory representation
[<RequireQualifiedAccess>]
type TypeLayout =
    /// Stack-allocated, known size and alignment
    | Inline of size: int * align: int
    /// Arena-allocated (heap-like but deterministic)
    | Reference of arena: ArenaAffinity
    /// Platform-specific, size determined at codegen
    | Opaque

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
}

/// Total arity (type + measure parameters)
let arity (tc: TypeConRef) = List.length tc.ParamKinds

/// Create a simple type constructor with only type parameters
let mkTypeConRef name typeArity layout =
    { Name = name; Module = []; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout }

/// Create a type constructor with explicit parameter kinds
let mkTypeConRefWithMeasures name paramKinds layout =
    { Name = name; Module = []; ParamKinds = paramKinds; Layout = layout }

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
    
    /// Record type with named fields
    | TRecord of tycon: TypeConRef * fields: (string * NativeType) list
    
    /// Discriminated union type
    | TUnion of tycon: TypeConRef * cases: UnionCase list
    
    /// Byref type: byref<T> or inref<T> or outref<T>
    | TByref of element: NativeType * kind: ByrefKind
    
    /// Native pointer: nativeptr<T>
    | TNativePtr of element: NativeType
    
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
    | NativeType.TNativePtr _ -> TypeLayout.Inline(8, 8)  // Pointer size
    | NativeType.TByref _ -> TypeLayout.Inline(8, 8)  // Pointer size
    | NativeType.TForall(_, body) -> layoutOf body
    | NativeType.TMeasure _ -> TypeLayout.Inline(0, 1)  // Phantom type
    | NativeType.TAnon(_, isStruct) when isStruct -> TypeLayout.Inline(-1, -1) // Size depends on fields
    | NativeType.TAnon(_, _) -> TypeLayout.Reference ArenaAffinity.CurrentActor
    | NativeType.TRecord(tycon, _) -> tycon.Layout
    | NativeType.TUnion(tycon, _) -> tycon.Layout
    | NativeType.TError _ -> TypeLayout.Opaque

/// Compute memory layout for a record from its fields.
/// Per fsnative-spec: "Field order determines memory layout" and
/// "Fidelity makes ALL memory layout decisions - MLIR/LLVM never determine layout."
///
/// Algorithm (from spec inference-procedures.md Step 4):
/// 1. For each field in declaration order, compute offset with padding for alignment
/// 2. Total layout = (sum of sizes + padding, max alignment)
let computeRecordLayout (fields: (string * NativeType) list) : TypeLayout =
    let folder (offset, maxAlign) (_, fieldType) =
        let fieldLayout = layoutOf fieldType
        match fieldLayout with
        | TypeLayout.Inline(size, align) when size >= 0 && align > 0 ->
            // Add padding for alignment
            let pad =
                let remainder = offset % align
                if remainder = 0 then 0 else align - remainder
            let paddedOffset = offset + pad
            (paddedOffset + size, max maxAlign align)
        | TypeLayout.Inline _ ->
            // Size or alignment is unknown (-1), propagate unknown
            (-1, -1)
        | TypeLayout.Opaque ->
            // Unknown at compile time - can't compute exact layout
            (-1, -1)
        | TypeLayout.Reference _ ->
            // Reference types are pointer-sized (8 bytes on 64-bit)
            let pad =
                let remainder = offset % 8
                if remainder = 0 then 0 else 8 - remainder
            let paddedOffset = offset + pad
            (paddedOffset + 8, max maxAlign 8)

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
        | NativeType.TRecord(tc, fields) -> NativeType.TRecord(tc, fields |> List.map (fun (n, t) -> (n, go t)))
        | NativeType.TUnion(tc, cases) -> 
            NativeType.TUnion(tc, cases |> List.map (fun c -> 
                { c with Fields = c.Fields |> List.map (fun (n, t) -> (n, go t)) }))
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
    | NativeType.TRecord(tc, fields) ->
        let fieldsStr = fields |> List.map (fun (n, t) -> $"{n}: {formatType t}") |> String.concat "; "
        $"{tc.Name} {{ {fieldsStr} }}"
    | NativeType.TUnion(tc, _) -> tc.Name
    | NativeType.TError msg -> $"<error: {msg}>"

and formatMeasure (m: Measure) : string =
    match m with
    | MOne -> "1"
    | MVar tp -> tp.Name
    | MProd(m1, m2) -> $"{formatMeasure m1}*{formatMeasure m2}"
    | MInv m -> $"1/{formatMeasure m}"
    | MCon(name, _) -> name

// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// SynType to NativeType conversion for F# Native.
/// Handles: SynType.LongIdent, App, Fun, Tuple, Var, Array, Paren, etc.
module FSharp.Native.Compiler.NativeTypedTree.Expressions.SynTypes

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.UnionFind
open FSharp.Native.Compiler.NativeTypedTree.Expressions.Types

//-------------------------------------------------------------------------
// SynType Conversion
//-------------------------------------------------------------------------

/// Convert a SynType to NativeType
let rec checkSynType (env: TypeEnv) (synType: SynType) : NativeType =
    let r = synType.Range  // FCS range for error reporting
    let sr = rangeToSourceRange r  // SourceRange for constraints
    
    match synType with
    //---------------------------------------------------------------------
    // Named types: int, string, MyType, etc.
    //---------------------------------------------------------------------
    | SynType.LongIdent(SynLongIdent(idents, _, _)) ->
        let name = idents |> List.map (fun id -> id.idText) |> String.concat "."
        resolveTypeName env name r sr
    
    //---------------------------------------------------------------------
    // Generic type application: list<int>, option<string>, etc.
    //---------------------------------------------------------------------
    | SynType.App(typeName, _, typeArgs, _, _, _, _) ->
        let baseType = checkSynType env typeName
        let argTypes = typeArgs |> List.map (checkSynType env)
        applyTypeArgs baseType argTypes sr
    
    //---------------------------------------------------------------------
    // Long identifier with type application: Foo.Bar<int>
    //---------------------------------------------------------------------
    | SynType.LongIdentApp(typeName, SynLongIdent(idents, _, _), _, typeArgs, _, _, _) ->
        let baseType = checkSynType env typeName
        let suffix = idents |> List.map (fun id -> id.idText) |> String.concat "."
        let argTypes = typeArgs |> List.map (checkSynType env)
        // For now, treat as qualified type with args
        let qualifiedName = 
            match baseType with
            | NativeType.TApp(tc, []) -> tc.Name + "." + suffix
            | _ -> suffix
        let resolvedBase = resolveTypeName env qualifiedName r sr
        applyTypeArgs resolvedBase argTypes sr
    
    //---------------------------------------------------------------------
    // Function type: int -> string
    //---------------------------------------------------------------------
    | SynType.Fun(argType, returnType, _, _) ->
        let argTy = checkSynType env argType
        let retTy = checkSynType env returnType
        NativeType.TFun(argTy, retTy)
    
    //---------------------------------------------------------------------
    // Tuple type: int * string
    //---------------------------------------------------------------------
    | SynType.Tuple(isStruct, segments, _) ->
        let elemTypes = 
            segments 
            |> List.choose (function
                | SynTupleTypeSegment.Type synTy -> Some (checkSynType env synTy)
                | SynTupleTypeSegment.Star _ -> None
                | SynTupleTypeSegment.Slash _ -> None)
        NativeType.TTuple(elemTypes, isStruct)
    
    //---------------------------------------------------------------------
    // Type variable: 'a, 'T
    //---------------------------------------------------------------------
    | SynType.Var(SynTypar(ident, _, _), _) ->
        let _name = ident.idText
        // Check if we have this type parameter in scope, otherwise create fresh
        freshTypeVar sr  // TODO: Look up in type parameter environment
    
    //---------------------------------------------------------------------
    // Anonymous type: _ (infer)
    //---------------------------------------------------------------------
    | SynType.Anon _ ->
        freshTypeVar sr
    
    //---------------------------------------------------------------------
    // Array type: int[]
    //---------------------------------------------------------------------
    | SynType.Array(rank, elementType, _) ->
        let elemTy = checkSynType env elementType
        if rank = 1 then
            Types.mkArrayType elemTy
        else
            // Multi-dimensional arrays - use a fresh type for now
            addWarning r $"Multi-dimensional array (rank {rank}) treated as 1D" env
            Types.mkArrayType elemTy
    
    //---------------------------------------------------------------------
    // Parenthesized type: (int)
    //---------------------------------------------------------------------
    | SynType.Paren(innerType, _) ->
        checkSynType env innerType
    
    //---------------------------------------------------------------------
    // Anonymous record: {| Name: string; Age: int |}
    //---------------------------------------------------------------------
    | SynType.AnonRecd(isStruct, fields, _) ->
        let fieldTypes = 
            fields 
            |> List.map (fun (ident, synTy) -> 
                (ident.idText, checkSynType env synTy))
        NativeType.TAnon(fieldTypes, isStruct)
    
    //---------------------------------------------------------------------
    // With constraints: int when ...
    //---------------------------------------------------------------------
    | SynType.WithGlobalConstraints(typeName, constraints, _) ->
        let baseTy = checkSynType env typeName
        // Process constraints - add to constraint environment
        for c in constraints do
            checkSynConstraint env c
        baseTy
    
    //---------------------------------------------------------------------
    // Hash constraint: #IDisposable (flexible type)
    //---------------------------------------------------------------------
    | SynType.HashConstraint(innerType, _) ->
        let baseTy = checkSynType env innerType
        // #T means the type is a subtype of T - create a fresh var with constraint
        let tv = freshTypeVar sr
        addConstraint (Constraint.Subtype(tv, baseTy, sr)) env
        tv
    
    //---------------------------------------------------------------------
    // Nullable type: int | null
    //---------------------------------------------------------------------
    | SynType.WithNull(innerType, _, _, _) ->
        // F# Native doesn't support null - warn and return inner type
        addNullWarning r env
        checkSynType env innerType
    
    //---------------------------------------------------------------------
    // Measure types (not yet supported)
    //---------------------------------------------------------------------
    | SynType.MeasurePower(baseMeasure, _, _) ->
        addWarning r "Measure types not yet supported" env
        checkSynType env baseMeasure
    
    //---------------------------------------------------------------------
    // Static constants in types (compile-time values)
    //---------------------------------------------------------------------
    | SynType.StaticConstant(_, _) ->
        // Used in type-level computation - return a placeholder
        addWarning r "Static constant in type position" env
        freshTypeVar sr
    
    | SynType.StaticConstantNull _ ->
        addNullWarning r env
        freshTypeVar sr
    
    | SynType.StaticConstantExpr(_, _) ->
        addWarning r "Static constant expression in type position" env
        freshTypeVar sr
    
    | SynType.StaticConstantNamed(_, value, _) ->
        checkSynType env value
    
    //---------------------------------------------------------------------
    // Signal end (compiler internal)
    //---------------------------------------------------------------------
    | SynType.SignatureParameter(_, _, _, synType, _) ->
        checkSynType env synType
    
    //---------------------------------------------------------------------
    // Or type: A | B (union constraint)
    //---------------------------------------------------------------------
    | SynType.Or(lhs, rhs, _, _) ->
        // Create a fresh type variable - Or constraints not yet supported
        let _lhsTy = checkSynType env lhs
        let _rhsTy = checkSynType env rhs
        addWarning r "Or type constraint not yet supported" env
        freshTypeVar sr
    
    //---------------------------------------------------------------------
    // Intersection type: A & B
    //---------------------------------------------------------------------
    | SynType.Intersection(_, types, _, _) ->
        // Create constraints that the type satisfies all intersected types
        let tv = freshTypeVar sr
        for synTy in types do
            let ty = checkSynType env synTy
            addConstraint (Constraint.Subtype(tv, ty, sr)) env
        tv
    
    //---------------------------------------------------------------------
    // From parse error (recovery)
    //---------------------------------------------------------------------
    | SynType.FromParseError _ ->
        NativeType.TError "Parse error in type"

//-------------------------------------------------------------------------
// Helper: Resolve type name to NativeType
//-------------------------------------------------------------------------

/// Resolve a type name like "int", "string", "MyModule.MyType" to NativeType
and resolveTypeName (env: TypeEnv) (name: string) (r: range) (sr: SourceRange) : NativeType =
    // Check primitive types first
    match name with
    | "int" | "int32" | "Int32" -> Types.intType
    | "int8" | "sbyte" | "SByte" -> Types.int8Type
    | "int16" | "Int16" -> Types.int16Type
    | "int64" | "Int64" -> Types.int64Type
    | "uint" | "uint32" | "UInt32" -> Types.uintType
    | "uint8" | "byte" | "Byte" -> Types.uint8Type
    | "uint16" | "UInt16" -> Types.uint16Type
    | "uint64" | "UInt64" -> Types.uint64Type
    | "float" | "float64" | "double" | "Double" -> Types.floatType
    | "float32" | "single" | "Single" -> Types.float32Type
    | "bool" | "Boolean" -> Types.boolType
    | "char" | "Char" -> Types.charType
    | "string" | "String" -> Types.stringType
    | "unit" | "Unit" -> Types.unitType
    | "nativeint" | "IntPtr" -> Types.nintType
    | "unativeint" | "UIntPtr" -> Types.unintType
    | "decimal" | "Decimal" -> Types.decimalType
    | "obj" | "Object" | "object" ->
        addObjError r env
        NativeType.TError "obj/Object not supported"
    // Parameterized type constructors (used in App)
    | "array" | "[]" ->
        // Return the type constructor - args applied in App case
        NativeType.TApp(Types.arrayTyCon, [])
    | "list" | "List" ->
        // F# list not yet supported in native
        addWarning r "F# list type not yet supported in native compilation" env
        NativeType.TError "list not supported"
    | "option" | "Option" ->
        NativeType.TApp(Types.optionTyCon, [])
    | "voption" | "ValueOption" ->
        NativeType.TApp(Types.voptionTyCon, [])
    | "nativeptr" ->
        // nativeptr<'T> - return constructor, args applied in App
        NativeType.TNativePtr(freshTypeVar sr)
    | "byref" | "inref" | "outref" ->
        // byref types - return constructor
        NativeType.TByref(freshTypeVar sr, ByrefKind.InOut)
    | "Lazy" ->
        NativeType.TLazy(freshTypeVar sr)
    | "seq" | "IEnumerable" ->
        NativeType.TSeq(freshTypeVar sr)
    | "Expr" ->
        NativeType.TApp(Types.exprTyCon, [])
    | "Map" ->
        // Map<'K, 'V> - return placeholder that will get args in App case
        // TMap is the canonical form but we need to handle unapplied case
        NativeType.TMap(freshTypeVar sr, freshTypeVar sr)
    | "Set" ->
        // Set<'T> - return placeholder that will get arg in App case
        NativeType.TSet(freshTypeVar sr)
    | "Arena" ->
        // Arena<'lifetime> - uses TApp with arenaTyCon
        NativeType.TApp(Types.arenaTyCon, [])
    | "Result" ->
        // Result<'T, 'E> - represented as tagged union
        // Use TApp approach since Result isn't a DU case in NativeType
        let resultTyCon = mkTypeConRef "Result" 2 (TypeLayout.Inline(-1, -1))
        NativeType.TApp(resultTyCon, [])
    | "FnPtr" ->
        // FnPtr<'T> - function pointer
        NativeType.TApp(Types.fnPtrTyCon, [])
    | _ ->
        // Check for user-defined types
        match tryLookupTypeDef name env with
        | Some typeCon ->
            // Found a user-defined type - wrap in TApp
            NativeType.TApp(typeCon, [])
        | None ->
            // Check for type abbreviations
            match tryLookupTypeAbbrev name env with
            | Some abbrevTy ->
                abbrevTy
            | None ->
                // Check for record definitions
                match tryLookupRecordDef name env with
                | Some recordInfo ->
                    NativeType.TApp(recordInfo.TypeCon, [])
                | None ->
                    // Unknown type - create error
                    addError r $"Unknown type: {name}" env
                    NativeType.TError $"Unknown type: {name}"

//-------------------------------------------------------------------------
// Helper: Apply type arguments to a base type
//-------------------------------------------------------------------------

/// Apply type arguments to a parameterized type
and applyTypeArgs (baseType: NativeType) (argTypes: NativeType list) (_sr: SourceRange) : NativeType =
    match baseType, argTypes with
    | _, [] -> baseType  // No args to apply
    | NativeType.TApp(tc, []), args ->
        // Apply args to type constructor
        NativeType.TApp(tc, args)
    | NativeType.TNativePtr _, [arg] ->
        NativeType.TNativePtr arg
    | NativeType.TByref(_, kind), [arg] ->
        NativeType.TByref(arg, kind)
    | NativeType.TLazy _, [arg] ->
        NativeType.TLazy arg
    | NativeType.TSeq _, [arg] ->
        NativeType.TSeq arg
    | NativeType.TMap(_, _), [keyArg; valueArg] ->
        // Map<'K, 'V> with explicit type args
        NativeType.TMap(keyArg, valueArg)
    | NativeType.TSet _, [arg] ->
        // Set<'T> with explicit type arg
        NativeType.TSet arg
    | NativeType.TVar _, _ ->
        // Type variable with args - need to unify later
        baseType  // TODO: Handle properly
    | _ ->
        // Unexpected - can't apply args to this type
        baseType

//-------------------------------------------------------------------------
// SynTypeConstraint Processing
//-------------------------------------------------------------------------

/// Process a SynTypeConstraint and add to environment
and checkSynConstraint (env: TypeEnv) (synConstraint: SynTypeConstraint) : unit =
    match synConstraint with
    | SynTypeConstraint.WhereTyparIsValueType(SynTypar(ident, _, _), _) ->
        // struct constraint - warn as not directly supported
        addWarning ident.idRange "struct constraint not yet supported" env
    
    | SynTypeConstraint.WhereTyparIsReferenceType(SynTypar(ident, _, _), _) ->
        // not struct constraint - warn as not directly supported
        addWarning ident.idRange "not struct constraint not yet supported" env
    
    | SynTypeConstraint.WhereTyparIsUnmanaged(SynTypar(ident, _, _), _) ->
        // unmanaged constraint - warn as not directly supported
        addWarning ident.idRange "unmanaged constraint not yet supported" env
    
    | SynTypeConstraint.WhereTyparSupportsNull(SynTypar(ident, _, _), _) ->
        // null constraint - warn as F# Native doesn't support null
        addNullWarning ident.idRange env
    
    | SynTypeConstraint.WhereTyparNotSupportsNull(SynTypar(_ident, _, _), _, _) ->
        // not null constraint - this is the default in native, so just accept
        ()
    
    | SynTypeConstraint.WhereTyparIsComparable(SynTypar(ident, _, _), _) ->
        // comparison constraint - warn as not directly supported
        addWarning ident.idRange "comparison constraint not yet supported" env
    
    | SynTypeConstraint.WhereTyparIsEquatable(SynTypar(ident, _, _), _) ->
        // equality constraint - warn as not directly supported
        addWarning ident.idRange "equality constraint not yet supported" env
    
    | SynTypeConstraint.WhereTyparDefaultsToType(SynTypar(ident, _, _), synType, _) ->
        // default type constraint - just check the type
        let _defaultTy = checkSynType env synType
        addWarning ident.idRange "defaults to type constraint not yet supported" env
    
    | SynTypeConstraint.WhereTyparSubtypeOfType(SynTypar(ident, _, _), synType, _) ->
        // subtype constraint: 'T :> SomeType
        let sr = rangeToSourceRange ident.idRange
        let superTy = checkSynType env synType
        let tv = freshTypeVar sr
        addConstraint (Constraint.Subtype(tv, superTy, sr)) env
    
    | SynTypeConstraint.WhereTyparSupportsMember(_, _, _) ->
        // SRTP member constraint - handled separately via HasMember
        ()
    
    | SynTypeConstraint.WhereTyparIsEnum(SynTypar(ident, _, _), _, _) ->
        // enum constraint - warn as not directly supported
        addWarning ident.idRange "enum constraint not yet supported" env
    
    | SynTypeConstraint.WhereTyparIsDelegate(SynTypar(ident, _, _), _, _) ->
        // delegate constraint - not supported in native
        addWarning ident.idRange "delegate constraint not supported in native compilation" env
    
    | SynTypeConstraint.WhereSelfConstrained(synType, _) ->
        // Self-constrained - the type constrains itself
        let _ = checkSynType env synType
        ()

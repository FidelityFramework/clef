// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// SynType checking for F# Native.
/// Converts syntax tree types (SynType) to native types (NativeType).
/// Also handles: SynTypar, SynMeasure, SynTypeConstraint
module FSharp.Native.Compiler.Checking.Native.Expressions.SynTypes

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.Expressions.Types

//-------------------------------------------------------------------------
// SynTypar → TypeParam
//-------------------------------------------------------------------------

/// Convert a SynTypar to a TypeParam
/// Creates a named type parameter from the syntax tree representation
/// Note: Currently creates fresh type parameters; scope tracking not yet implemented
let checkSynTypar (_env: TypeEnv) (synTypar: SynTypar) : TypeParam =
    let (SynTypar(ident, _typarStaticReq, _isCompGen)) = synTypar
    let name = "'" + ident.idText
    let range = rangeToSourceRange ident.idRange
    // Create a new named type parameter using the UnionFind helper
    // TODO: Track type parameters in scope for proper sharing
    freshTypeParam name TypeParamKind.Type range

//-------------------------------------------------------------------------
// Measure Helpers
//-------------------------------------------------------------------------

/// Evaluate a SynRationalConst to an integer exponent
/// For simplicity, we only support integer exponents (not rational)
let rec evalRationalConst (synRat: SynRationalConst) : int =
    match synRat with
    | SynRationalConst.Integer(value, _) -> value
    | SynRationalConst.Negate(inner, _) -> -(evalRationalConst inner)
    | SynRationalConst.Paren(inner, _) -> evalRationalConst inner
    | SynRationalConst.Rational(num, _, _, denom, _, _range) ->
        // Rational exponents not fully supported in native compilation
        // Use the nearest integer (num / denom rounded)
        if denom <> 0 then num / denom else 1

/// Expand a measure power: m^n = m * m * ... * m (n times)
/// For negative powers: m^-n = 1 / (m^n)
let rec expandMeasurePower (baseMeasure: Measure) (exponent: int) : Measure =
    if exponent = 0 then MOne
    elif exponent = 1 then baseMeasure
    elif exponent = -1 then MInv baseMeasure
    elif exponent > 0 then
        // m^n = m * m * ... * m
        List.replicate exponent baseMeasure
        |> List.reduce (fun a b -> MProd(a, b))
    else
        // m^-n = 1 / m^n
        MInv (expandMeasurePower baseMeasure (-exponent))

//-------------------------------------------------------------------------
// SynMeasure → Measure
//-------------------------------------------------------------------------

/// Convert a SynMeasure to our native Measure representation
/// Per fsnative-spec units-of-measure.md: measures support product, quotient, power, and named units
let rec checkSynMeasure (env: TypeEnv) (synMeasure: SynMeasure) : Measure =
    match synMeasure with
    | SynMeasure.One _ ->
        // The dimensionless unit: 1
        MOne

    | SynMeasure.Named(longId, _) ->
        // Named measure: kg, m, s, or module-qualified like Physics.Meters
        let parts = longId |> List.map (fun id -> id.idText)
        let name = parts |> List.last
        let modulePath = parts |> List.rev |> List.tail |> List.rev
        MCon(name, modulePath)

    | SynMeasure.Product(m1, _, m2, _) ->
        // Product of measures: m1 * m2
        let measure1 = checkSynMeasure env m1
        let measure2 = checkSynMeasure env m2
        MProd(measure1, measure2)

    | SynMeasure.Divide(Some m1, _, m2, _) ->
        // Division: m1 / m2 = m1 * (1/m2)
        let measure1 = checkSynMeasure env m1
        let measure2 = checkSynMeasure env m2
        MProd(measure1, MInv measure2)

    | SynMeasure.Divide(None, _, m2, _) ->
        // Division with no numerator: /m2 = 1/m2
        let measure2 = checkSynMeasure env m2
        MInv measure2

    | SynMeasure.Power(baseMeasure, _, power, _) ->
        // Power: m^n
        let measure = checkSynMeasure env baseMeasure
        let exp = evalRationalConst power
        expandMeasurePower measure exp

    | SynMeasure.Var(synTypar, _) ->
        // Measure type variable: 'u
        let tp = checkSynTypar env synTypar
        // Ensure it's marked as a measure parameter
        let measureTp = { tp with Kind = TypeParamKind.Measure }
        MVar measureTp

    | SynMeasure.Seq(measures, _) ->
        // Sequence of measures: m1 m2 m3 (implicit product)
        measures
        |> List.map (checkSynMeasure env)
        |> List.reduce (fun a b -> MProd(a, b))

    | SynMeasure.Anon _ ->
        // Anonymous measure: _ (fresh measure variable)
        let range = dummyRange
        MVar (freshMeasureVar range)

    | SynMeasure.Paren(inner, _) ->
        // Parenthesized measure
        checkSynMeasure env inner

//-------------------------------------------------------------------------
// SynTypeConstraint → Constraint
//-------------------------------------------------------------------------

/// Check a type constraint from syntax and record it
/// Per native_type_checker_design_principles: SRTP resolved DURING type checking
/// Returns the constraint to add to the type parameter, or None if handled inline
let rec checkSynConstraint (env: TypeEnv) (constraint_: SynTypeConstraint) : Constraint option =
    match constraint_ with
    // KEY FOR SRTP: (^a or ^b) : (static member op : signature)
    | SynTypeConstraint.WhereTyparSupportsMember(typars, memberSig, range) ->
        let typarType = checkSynType env typars
        let nativeRange = rangeToSourceRange range
        // Extract member name and signature from the member signature
        let memberName =
            match memberSig with
            | SynMemberSig.Member(SynValSig(ident = SynIdent(id, _)), _, _, _) -> id.idText
            | _ -> "unknown_member"
        let memberType =
            match memberSig with
            | SynMemberSig.Member(SynValSig(synType = synRetType), _, _, _) ->
                checkSynType env synRetType
            | _ -> freshTypeVar nativeRange
        Some (Constraint.HasMember(typarType, memberName, memberType, nativeRange))

    // Subtype/inheritance constraint: 'a :> ISomething
    | SynTypeConstraint.WhereTyparSubtypeOfType(synTypar, superType, range) ->
        let typar = checkSynTypar env synTypar
        let superTy = checkSynType env superType
        let nativeRange = rangeToSourceRange range
        Some (Constraint.Subtype(NativeType.TVar typar, superTy, nativeRange))

    // Struct constraint: 'a : struct
    | SynTypeConstraint.WhereTyparIsValueType(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // Record as layout constraint - type must be inline (stack-allocated)
        Some (Constraint.LayoutCompatible(NativeType.TVar typar, TypeLayout.Inline(-1, -1), nativeRange))

    // Reference type constraint: 'a : not struct
    | SynTypeConstraint.WhereTyparIsReferenceType(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // Record as layout constraint - type must be reference (arena-allocated)
        Some (Constraint.LayoutCompatible(NativeType.TVar typar, TypeLayout.Reference ArenaAffinity.CurrentActor, nativeRange))

    // Unmanaged constraint: 'a : unmanaged
    | SynTypeConstraint.WhereTyparIsUnmanaged(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // Unmanaged = no GC references, blittable - use inline layout
        Some (Constraint.LayoutCompatible(NativeType.TVar typar, TypeLayout.Inline(-1, -1), nativeRange))

    // NULL CONSTRAINT - REJECTED in fsnative
    // Per fsnative-spec types-and-type-constraints.md: null is not permitted
    | SynTypeConstraint.WhereTyparSupportsNull(_, range) ->
        addNativeError DiagnosticCodes.FS8710_NullConstraint range
            "The 'null' constraint is not permitted in F# Native. Use ValueOption for optional values."
            env
        None

    // Not null constraint: 'a : not null
    | SynTypeConstraint.WhereTyparNotSupportsNull(_, _, _) ->
        // All types in native are non-nullable by default - this is a no-op
        None

    // Comparison constraint: 'a : comparison
    | SynTypeConstraint.WhereTyparIsComparable(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // In Alloy, comparison is via SRTP - generate HasMember for comparison operations
        // Type must implement: compare : 'a -> 'a -> int
        let compareTy = NativeType.TFun(NativeType.TVar typar, NativeType.TFun(NativeType.TVar typar, Types.intType))
        Some (Constraint.HasMember(NativeType.TVar typar, "compare", compareTy, nativeRange))

    // Equality constraint: 'a : equality
    | SynTypeConstraint.WhereTyparIsEquatable(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // In Alloy, equality is via SRTP - generate HasMember for equality operations
        // Type must implement: op_Equality : 'a -> 'a -> bool
        let eqTy = NativeType.TFun(NativeType.TVar typar, NativeType.TFun(NativeType.TVar typar, Types.boolType))
        Some (Constraint.HasMember(NativeType.TVar typar, "op_Equality", eqTy, nativeRange))

    // Default type constraint: 'a : > Type (defaults to Type if unconstrained)
    | SynTypeConstraint.WhereTyparDefaultsToType(synTypar, defaultType, _range) ->
        // Record the default but don't emit as constraint - used during generalization
        let _typar = checkSynTypar env synTypar
        let _defaultTy = checkSynType env defaultType
        // TODO: Store default types for generalization
        None

    // Enum constraint: 'a : enum<int>
    | SynTypeConstraint.WhereTyparIsEnum(_, _, range) ->
        addNativeError DiagnosticCodes.FS8711_UnsupportedConstraint range
            "Enum constraints are not supported in F# Native. Use discriminated unions instead."
            env
        None

    // Delegate constraint: 'a : delegate<arg, ret>
    | SynTypeConstraint.WhereTyparIsDelegate(_, _, range) ->
        addNativeError DiagnosticCodes.FS8711_UnsupportedConstraint range
            "Delegate constraints are not supported in F# Native. Use function types instead."
            env
        None

    // Self constraint (used in recursive type definitions)
    | SynTypeConstraint.WhereSelfConstrained(selfType, range) ->
        let selfTy = checkSynType env selfType
        let nativeRange = rangeToSourceRange range
        // Self constraints typically appear in recursive type definitions
        // For now, treat as type equality with fresh variable
        let freshTy = freshTypeVar nativeRange
        Some (Constraint.Equals(selfTy, freshTy, nativeRange))

//-------------------------------------------------------------------------
// SynType → NativeType
//-------------------------------------------------------------------------

/// Check a SynType and convert to NativeType
and checkSynType (env: TypeEnv) (synType: SynType) : NativeType =
    match synType with
    | SynType.LongIdent(longIdent) ->
        let name = longIdent.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
        let range = longIdent.Range

        // FS8500: BCL type references are FORBIDDEN - check FIRST
        if isBclReference name then
            addBclError name range env
            NativeType.TError $"BCL type: {name}"
        // CRITICAL: Reject 'obj' - FS8011
        // The type 'obj' (System.Object) does not exist in F# Native.
        // The native type system is closed - no boxing, no runtime type inspection.
        elif name = "obj" || name = "System.Object" || name = "Object" then
            addObjError range env
            NativeType.TError "obj not supported"
        else
            match tryFindBuiltinTyCon name with
            | Some tyCon -> mkSimpleType tyCon
            | None ->
                // Try to find in type definitions
                match Map.tryFind name env.TypeDefs with
                | Some tyCon -> mkSimpleType tyCon
                | None ->
                    // Try to find in type abbreviations
                    match tryLookupTypeAbbrev name env with
                    | Some ty -> ty
                    | None -> NativeType.TError $"Unknown type: {name}"

    | SynType.App(typeName, _, typeArgs, _, _, _, _) ->
        let baseTy = checkSynType env typeName
        let argTys = typeArgs |> List.map (checkSynType env)
        match baseTy with
        | NativeType.TApp(tyCon, []) -> NativeType.TApp(tyCon, argTys)
        | _ -> baseTy  // Already an error or complex type

    | SynType.LongIdentApp(typeName, _longIdent, _, typeArgs, _, _, _) ->
        // Qualified generic type: Module.Type<arg1, arg2>
        let baseTy = checkSynType env typeName
        let argTys = typeArgs |> List.map (checkSynType env)
        match baseTy with
        | NativeType.TApp(tyCon, []) -> NativeType.TApp(tyCon, argTys)
        | _ -> baseTy

    | SynType.Tuple(isStruct, elementTypes, _) ->
        // SynTupleTypeSegment is a union: Type of SynType | Star of range | Slash of range
        // Filter for Type segments only
        let elemTys =
            elementTypes
            |> List.choose (function
                | SynTupleTypeSegment.Type ty -> Some (checkSynType env ty)
                | SynTupleTypeSegment.Star _ -> None
                | SynTupleTypeSegment.Slash _ -> None)
        NativeType.TTuple(elemTys, isStruct)

    | SynType.AnonRecd(isStruct, fields, _) ->
        // Anonymous record: {| field1: T1; field2: T2 |}
        let fieldTys = fields |> List.map (fun (id, ty) -> (id.idText, checkSynType env ty))
        NativeType.TAnon(fieldTys, isStruct)

    | SynType.Array(_rank, elementType, _) ->
        // Array types: int[], byte[], etc.
        let elemTy = checkSynType env elementType
        // Note: rank > 1 for multidimensional arrays - for now, treat all as 1D
        mkArrayType elemTy

    | SynType.Fun(argType, returnType, _, _) ->
        let argTy = checkSynType env argType
        let retTy = checkSynType env returnType
        NativeType.TFun(argTy, retTy)

    | SynType.Var(_typar, _) ->
        // Type variable - create a fresh type variable
        freshTypeVar dummyRange

    | SynType.Anon _ ->
        // Anonymous type: _
        freshTypeVar dummyRange

    | SynType.WithGlobalConstraints(typeName, constraints, _) ->
        // Type with constraints: 'a when 'a :> IComparable
        // Per native_type_checker_design_principles: SRTP resolved DURING type checking
        let innerTy = checkSynType env typeName

        // Process each constraint and record them
        let nativeConstraints =
            constraints
            |> List.choose (checkSynConstraint env)

        // Add constraints to type parameter if inner type is a TVar
        // This attaches constraints to the type parameter for later resolution
        match innerTy with
        | NativeType.TVar typar ->
            typar.Constraints <- nativeConstraints @ typar.Constraints
        | _ ->
            // For non-variable types, add constraints to the environment
            for constraint_ in nativeConstraints do
                addConstraint constraint_ env

        innerTy

    | SynType.HashConstraint(innerType, _) ->
        // Hash constraint: #IInterface (flexible type)
        checkSynType env innerType

    | SynType.MeasurePower(baseMeasure, exponent, _) ->
        // Measure type: int<m^2> - units of measure
        // Per fsnative-spec units-of-measure.md: measures support product, quotient, power
        // Convert the SynMeasure base and apply the exponent
        let measure =
            match baseMeasure with
            | SynType.Var(synTypar, _) ->
                // Type variable as measure: 'u^2
                let tp = checkSynTypar env synTypar
                let measureTp = { tp with Kind = TypeParamKind.Measure }
                MVar measureTp
            | SynType.LongIdent(longIdent) ->
                // Named measure: kg^2, m^-1
                let parts = longIdent.LongIdent |> List.map (fun id -> id.idText)
                let name = parts |> List.last
                let modulePath = parts |> List.rev |> List.tail |> List.rev
                MCon(name, modulePath)
            | _ ->
                // Complex measure expression - try to parse as measure
                MOne
        let exp = evalRationalConst exponent
        NativeType.TMeasure(expandMeasurePower measure exp)

    | SynType.StaticConstant(constant, _range) ->
        // Static type constant - used in type-level programming
        match constant with
        | SynConst.Int32 n -> NativeType.TError $"Static constant {n} not yet supported"
        | SynConst.String(s, _, _) -> NativeType.TError $"Static constant \"{s}\" not yet supported"
        | _ -> NativeType.TError "Static constant type not yet supported"

    | SynType.StaticConstantNull range ->
        // null type constant - REJECTED in native
        addNullError range env
        NativeType.TError "null not allowed in F# Native"

    | SynType.StaticConstantExpr(_expr, _) ->
        // Static type-level expression
        NativeType.TError "Static constant expressions not yet supported"

    | SynType.StaticConstantNamed(_ident, _value, _) ->
        // Named static constant
        NativeType.TError "Named static constants not yet supported"

    | SynType.WithNull(innerType, _ambivalent, range, _) ->
        // Nullable type annotation: string | null
        // Native types are null-free by design - emit warning and return inner type
        // The type system doesn't support null; use ValueOption instead
        addNullWarning range env
        checkSynType env innerType

    | SynType.Paren(innerType, _) ->
        checkSynType env innerType

    | SynType.SignatureParameter(_, _, _, usedType, _) ->
        // Parameter in a signature - check the actual type
        checkSynType env usedType

    | SynType.Or(lhsType, _rhsType, _, _) ->
        // Flexible type: (type | type) - use the left type for now
        // This is typically used for flexible generic constraints
        checkSynType env lhsType

    | SynType.FromParseError _ ->
        // Parse error recovery - return error type
        NativeType.TError "Parse error in type syntax"

    | SynType.Intersection(_typar, types, _, _) ->
        // Intersection type: for SRTP constraints like ^T & IComparable
        match types with
        | first :: _ -> checkSynType env first
        | [] -> NativeType.TError "Empty intersection type"

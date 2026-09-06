// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Type unification algorithm for the native type checker.
/// Uses Union-Find for efficient substitution with path compression.
module Clef.Compiler.NativeTypedTree.Unify

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind

//-------------------------------------------------------------------------
// Type Errors
//-------------------------------------------------------------------------

/// Errors that can occur during unification
type UnificationError =
    /// Two types could not be unified
    | TypeMismatch of expected: NativeType * actual: NativeType * range: SourceRange
    /// Occurs check failed (infinite type)
    | InfiniteType of typar: TypeParam * ty: NativeType * range: SourceRange
    /// Arity mismatch in type application
    | ArityMismatch of expected: int * actual: int * range: SourceRange
    /// Tuple length mismatch
    | TupleLengthMismatch of expected: int * actual: int * range: SourceRange
    /// Struct vs reference tuple mismatch
    | TupleKindMismatch of expected: bool * actual: bool * range: SourceRange
    /// Byref kind mismatch
    | ByrefKindMismatch of expected: ByrefKind * actual: ByrefKind * range: SourceRange

exception UnificationException of UnificationError

let private freshArgument (parameter: TypeParam) range =
    let fresh = freshTypeParamAuto parameter.Kind range
    match parameter.Kind with
    | TypeParamKind.Type -> NativeType.TVar fresh
    | TypeParamKind.Measure -> NativeType.TMeasure(MVar fresh)

/// Format source range for display
let formatRange (range: SourceRange) : string =
    $"{range.File}({range.Start.Line},{range.Start.Column})"

/// Format a unification error for display
let formatError (err: UnificationError) : string =
    match err with
    | TypeMismatch(expected, actual, range) ->
        $"Type mismatch at {formatRange range}: expected '{formatType expected}', got '{formatType actual}'"
    | InfiniteType(typar, ty, range) ->
        $"Infinite type at {formatRange range}: type parameter '{typar.Name}' would be equivalent to '{formatType ty}'"
    | ArityMismatch(expected, actual, range) ->
        $"Arity mismatch at {formatRange range}: expected {expected} type arguments, got {actual}"
    | TupleLengthMismatch(expected, actual, range) ->
        $"Tuple length mismatch at {formatRange range}: expected {expected} elements, got {actual}"
    | TupleKindMismatch(expected, actual, range) ->
        let expectedKind = if expected then "struct tuple" else "reference tuple"
        let actualKind = if actual then "struct tuple" else "reference tuple"
        $"Tuple kind mismatch at {formatRange range}: expected {expectedKind}, got {actualKind}"
    | ByrefKindMismatch(expected, actual, range) ->
        $"Byref kind mismatch at {formatRange range}: expected {expected}, got {actual}"

/// Keep eager and deferred constraint diagnostics consistent.
let diagnosticCode = function
    | TypeMismatch(NativeType.TMeasure _, NativeType.TMeasure _, _) -> "CCS8040"
    | TypeMismatch(left, right, _) when (tryNumericComponents left).IsSome && (tryNumericComponents right).IsSome -> "CCS8003"
    | _ -> "FS0001"

//-------------------------------------------------------------------------
// Unification Algorithm
//-------------------------------------------------------------------------

/// Unify two types, updating the Union-Find structure.
/// Raises UnificationException on failure.
let rec unify (t1: NativeType) (t2: NativeType) (range: SourceRange) : unit =
    // Apply current substitutions first
    let t1 = applySubst t1
    let t2 = applySubst t2
    
    match (t1, t2) with
    // Both are type variables
    | NativeType.TVar v1, NativeType.TVar v2 ->
        let (root1, _) = find v1
        let (root2, _) = find v2
        if root1.Id <> root2.Id then
            union v1 v2
    
    // One is a type variable, one is concrete
    | NativeType.TVar v, ty
    | ty, NativeType.TVar v ->
        let (root, bound) = find v
        match bound with
        | None ->
            // Occurs check
            if occursIn root ty then
                raise (UnificationException(InfiniteType(root, ty, range)))
            bind root ty
        | Some boundTy ->
            unify boundTy ty range
    
    // Numeric inference keeps kind and dimension independent. A kind variable
    // can only meet a numeric type here; it cannot be instantiated as string/bool.
    | NativeType.TApp(tc, _), _ when isNumericInferenceTyCon tc ->
        match tryNumericComponents t1, tryNumericComponents t2 with
        | Some(kind1, measure1), Some(kind2, measure2) ->
            unify kind1 kind2 range
            unifyMeasure measure1 measure2 range
        | _ -> raise (UnificationException(TypeMismatch(t1, t2, range)))
    | _, NativeType.TApp(tc, _) when isNumericInferenceTyCon tc -> unify t2 t1 range

    // Type applications
    // NOTE: TypeConRef.Qualifiers are NOT part of type identity.
    // Types with different placement qualifiers unify as the same type.
    | NativeType.TApp(tc1, args1), NativeType.TApp(tc2, args2) ->
        if tc1.Name <> tc2.Name || tc1.Module <> tc2.Module then
            raise (UnificationException(TypeMismatch(t1, t2, range)))
        // A bare numeric kind denotes the dimensionless measure, not a wildcard.
        let dimensions args =
            if List.isEmpty args && (tc1.Name = "int" || tc1.Name = "float") then
                [NativeType.TMeasure MOne]
            else args
        let args1, args2 = dimensions args1, dimensions args2
        if List.length args1 <> List.length args2 then
            raise (UnificationException(ArityMismatch(List.length args1, List.length args2, range)))
        List.iter2 (fun a1 a2 -> unify a1 a2 range) args1 args2
    
    // Function types
    | NativeType.TFun(d1, r1), NativeType.TFun(d2, r2) ->
        unify d1 d2 range
        unify r1 r2 range
    
    // Tuple types
    | NativeType.TTuple(elems1, isStruct1), NativeType.TTuple(elems2, isStruct2) ->
        if isStruct1 <> isStruct2 then
            raise (UnificationException(TupleKindMismatch(isStruct1, isStruct2, range)))
        if List.length elems1 <> List.length elems2 then
            raise (UnificationException(TupleLengthMismatch(List.length elems1, List.length elems2, range)))
        List.iter2 (fun e1 e2 -> unify e1 e2 range) elems1 elems2
    
    // Forall types (polymorphic)
    | NativeType.TForall(tps1, body1), NativeType.TForall(tps2, body2) ->
        if List.length tps1 <> List.length tps2 then
            raise (UnificationException(ArityMismatch(List.length tps1, List.length tps2, range)))
        if List.map (fun tp -> tp.Kind) tps1 <> List.map (fun tp -> tp.Kind) tps2 then
            raise (UnificationException(TypeMismatch(t1, t2, range)))
        // Never bind a declaration's quantified parameters during a use/probe.
        let body1 = instantiate tps1 (tps1 |> List.map (fun tp -> freshArgument tp range)) body1
        let body2 = instantiate tps2 (tps2 |> List.map (fun tp -> freshArgument tp range)) body2
        unify body1 body2 range
    
    // Byref types
    | NativeType.TByref(elem1, kind1), NativeType.TByref(elem2, kind2) ->
        if kind1 <> kind2 then
            raise (UnificationException(ByrefKindMismatch(kind1, kind2, range)))
        unify elem1 elem2 range
    
    // Native pointer types
    | NativeType.TNativePtr elem1, NativeType.TNativePtr elem2 ->
        unify elem1 elem2 range

    // Handle TNativePtr vs TApp(nativeptr, [elem]) - both represent the same concept
    | NativeType.TNativePtr elem1, NativeType.TApp(tc, [elem2]) when tc.Name = "nativeptr" ->
        unify elem1 elem2 range
    | NativeType.TApp(tc, [elem1]), NativeType.TNativePtr elem2 when tc.Name = "nativeptr" ->
        unify elem1 elem2 range

    // Lazy types (PRD-14)
    | NativeType.TLazy elem1, NativeType.TLazy elem2 ->
        unify elem1 elem2 range

    // Handle TLazy vs TApp(Lazy, [elem]) - both represent the same concept
    // TLazy is the canonical form (has proper struct layout), TApp comes from type syntax parsing
    | NativeType.TLazy elem1, NativeType.TApp(tc, [elem2]) when tc.Name = "Lazy" || tc.Name = "lazy" ->
        unify elem1 elem2 range
    | NativeType.TApp(tc, [elem1]), NativeType.TLazy elem2 when tc.Name = "Lazy" || tc.Name = "lazy" ->
        unify elem1 elem2 range

    // Seq types (PRD-15)
    | NativeType.TSeq elem1, NativeType.TSeq elem2 ->
        unify elem1 elem2 range

    // Handle TSeq vs TApp(seq, [elem]) - both represent the same concept
    // TSeq is the canonical form (has proper struct layout), TApp comes from type syntax parsing
    | NativeType.TSeq elem1, NativeType.TApp(tc, [elem2]) when tc.Name = "seq" ->
        unify elem1 elem2 range
    | NativeType.TApp(tc, [elem1]), NativeType.TSeq elem2 when tc.Name = "seq" ->
        unify elem1 elem2 range

    // SeqEnumerator types (PRD-15/16)
    | NativeType.TSeqEnumerator elem1, NativeType.TSeqEnumerator elem2 ->
        unify elem1 elem2 range

    // List types (PRD-13a)
    | NativeType.TList elem1, NativeType.TList elem2 ->
        unify elem1 elem2 range

    // Handle TList vs TApp(list/List, [elem]) - both represent the same concept
    // TList is the canonical form, TApp comes from type syntax parsing
    | NativeType.TList elem1, NativeType.TApp(tc, [elem2]) when tc.Name = "list" || tc.Name = "List" ->
        unify elem1 elem2 range
    | NativeType.TApp(tc, [elem1]), NativeType.TList elem2 when tc.Name = "list" || tc.Name = "List" ->
        unify elem1 elem2 range

    // Map types (PRD-13a)
    | NativeType.TMap(k1, v1), NativeType.TMap(k2, v2) ->
        unify k1 k2 range
        unify v1 v2 range

    // Handle TMap vs TApp(Map, [k; v]) - both represent the same concept
    // TMap is the canonical form, TApp comes from type syntax parsing
    | NativeType.TMap(k1, v1), NativeType.TApp(tc, [k2; v2]) when tc.Name = "Map" ->
        unify k1 k2 range
        unify v1 v2 range
    | NativeType.TApp(tc, [k1; v1]), NativeType.TMap(k2, v2) when tc.Name = "Map" ->
        unify k1 k2 range
        unify v1 v2 range

    // Set types (PRD-13a)
    | NativeType.TSet elem1, NativeType.TSet elem2 ->
        unify elem1 elem2 range

    // Handle TSet vs TApp(Set, [elem]) - both represent the same concept
    // TSet is the canonical form, TApp comes from type syntax parsing
    | NativeType.TSet elem1, NativeType.TApp(tc, [elem2]) when tc.Name = "Set" ->
        unify elem1 elem2 range
    | NativeType.TApp(tc, [elem1]), NativeType.TSet elem2 when tc.Name = "Set" ->
        unify elem1 elem2 range

    // Handle TByref vs TApp(byref/inref/outref, [elem]) - both represent the same concept
    // TApp(byref, ...) maps to TByref(..., InOut)
    | NativeType.TByref(elem1, ByrefKind.InOut), NativeType.TApp(tc, [elem2]) when tc.Name = "byref" ->
        unify elem1 elem2 range
    | NativeType.TApp(tc, [elem1]), NativeType.TByref(elem2, ByrefKind.InOut) when tc.Name = "byref" ->
        unify elem1 elem2 range
    // TApp(inref, ...) maps to TByref(..., In)
    | NativeType.TByref(elem1, ByrefKind.In), NativeType.TApp(tc, [elem2]) when tc.Name = "inref" ->
        unify elem1 elem2 range
    | NativeType.TApp(tc, [elem1]), NativeType.TByref(elem2, ByrefKind.In) when tc.Name = "inref" ->
        unify elem1 elem2 range
    // TApp(outref, ...) maps to TByref(..., Out)
    | NativeType.TByref(elem1, ByrefKind.Out), NativeType.TApp(tc, [elem2]) when tc.Name = "outref" ->
        unify elem1 elem2 range
    | NativeType.TApp(tc, [elem1]), NativeType.TByref(elem2, ByrefKind.Out) when tc.Name = "outref" ->
        unify elem1 elem2 range

    // Anonymous record types - must match on isStruct (struct vs reference)
    | NativeType.TAnon(fields1, isStruct1), NativeType.TAnon(fields2, isStruct2) ->
        if isStruct1 <> isStruct2 then
            raise (UnificationException(TypeMismatch(t1, t2, range)))
        if List.length fields1 <> List.length fields2 then
            raise (UnificationException(TypeMismatch(t1, t2, range)))
        let sorted1 = fields1 |> List.sortBy fst
        let sorted2 = fields2 |> List.sortBy fst
        List.iter2 (fun (n1, ty1) (n2, ty2) ->
            if n1 <> n2 then
                raise (UnificationException(TypeMismatch(t1, t2, range)))
            unify ty1 ty2 range
        ) sorted1 sorted2
    
    // Named records use TApp - unified above by TypeConRef identity

    // Union types
    | NativeType.TUnion(tc1, _), NativeType.TUnion(tc2, _) ->
        if tc1.Name <> tc2.Name || tc1.Module <> tc2.Module then
            raise (UnificationException(TypeMismatch(t1, t2, range)))
        // Cases are part of the type definition, not compared here
    
    // Measure types
    | NativeType.TMeasure m1, NativeType.TMeasure m2 ->
        unifyMeasure m1 m2 range
    
    // Error types unify with anything (for error recovery)
    | NativeType.TError _, _ -> ()
    | _, NativeType.TError _ -> ()

    // TForall vs non-TForall: instantiate the TForall first
    // This handles implicit polymorphic instantiation (e.g., `let f x = x` being used at a specific type)
    | NativeType.TForall(tps, body), other
    | other, NativeType.TForall(tps, body) ->
        // Instantiate with fresh type variables
        let freshVars = tps |> List.map (fun tp -> freshArgument tp range)
        let instantiatedBody = NativeTypes.instantiate tps freshVars body
        unify instantiatedBody other range

    // Anything else is a mismatch
    | _ ->
        raise (UnificationException(TypeMismatch(t1, t2, range)))

/// Unify two measures
and unifyMeasure (m1: Measure) (m2: Measure) (range: SourceRange) : unit =
    let difference = measureFactors (MProd(m1, MInv m2))
    if not difference.IsEmpty then
        // Isolate a variable when all remaining exponents are divisible by its
        // coefficient (including roots such as 'u^2 = m^2/s^2).
        let variable = difference |> Map.toList |> List.tryPick (fun (key, (atom, exponent)) ->
            match atom with
            | MVar tp when difference |> Map.forall (fun other (_, power) -> other = key || power % exponent = 0I) ->
                Some(key, tp, exponent)
            | _ -> None)
        match variable with
        | Some(key, tp, exponent) ->
            let solution = difference |> Map.remove key |> Map.map (fun _ (atom, power) -> atom, -power / exponent) |> measureFromFactors
            bind tp (NativeType.TMeasure solution)
        | None ->
            // Euclidean change of variables. Reduce another variable's coefficient
            // modulo the smallest one, preserving all integer solutions. Repeating
            // reaches the gcd; indivisible constant exponents then prove failure.
            let variables = difference |> Map.toList |> List.choose (fun (_, (atom, power)) ->
                match atom with MVar tp -> Some(tp, power) | _ -> None)
            match variables |> List.sortBy (snd >> abs) with
            | (pivot, power) :: rest ->
                match rest |> List.tryFind (fun (_, otherPower) -> otherPower % power <> 0I) with
                | Some(other, otherPower) ->
                    let fresh = freshMeasureVar range
                    bind pivot (NativeType.TMeasure(MProd(MVar fresh, measurePower (MVar other) -(otherPower / power))))
                    unifyMeasure m1 m2 range
                | None -> raise (UnificationException(TypeMismatch(NativeType.TMeasure m1, NativeType.TMeasure m2, range)))
            | [] -> raise (UnificationException(TypeMismatch(NativeType.TMeasure m1, NativeType.TMeasure m2, range)))

//-------------------------------------------------------------------------
// Try Unification (non-throwing)
//-------------------------------------------------------------------------

/// Try to unify two types, returning None on failure
let tryUnify (t1: NativeType) (t2: NativeType) (range: SourceRange) : Result<unit, UnificationError> =
    try
        unify t1 t2 range
        Ok ()
    with
    | UnificationException err -> Error err

/// Probe with fresh copies, preserving shared variables across both types.
/// This uses the same measure solver as checking without committing bindings.
let canUnify (t1: NativeType) (t2: NativeType) : bool =
    let pair = applySubst (NativeType.TTuple([t1; t2], false))
    let parameters = collectFreeTypeParams pair |> List.distinctBy (fun tp -> tp.Id)
    let arguments = parameters |> List.map (fun tp -> freshArgument tp tp.Range)
    match instantiate parameters arguments pair with
    | NativeType.TTuple([left; right], _) ->
        match tryUnify left right dummyRange with Ok () -> true | Error _ -> false
    | _ -> false

//-------------------------------------------------------------------------
// Subsumption (for contravariance/covariance)
//-------------------------------------------------------------------------

/// Check if t1 subsumes t2 (t1 is more general than t2)
/// For function types: (A -> B) subsumes (A' -> B') if A' subsumes A and B subsumes B'
let rec subsumes (t1: NativeType) (t2: NativeType) (range: SourceRange) : bool =
    let t1 = applySubst t1
    let t2 = applySubst t2
    
    match (t1, t2) with
    | NativeType.TVar _, _ -> true  // Type var subsumes anything
    | _, NativeType.TVar _ -> true  // Anything subsumes type var (when instantiated)
    
    | NativeType.TForall(tps1, body1), NativeType.TForall(tps2, body2) ->
        // t1 is more general if it has more or equal type parameters
        List.length tps1 >= List.length tps2 && subsumes body1 body2 range
    
    | NativeType.TForall(_, body1), t2 ->
        subsumes body1 t2 range
    
    | NativeType.TFun(d1, r1), NativeType.TFun(d2, r2) ->
        // Contravariant in domain, covariant in range
        subsumes d2 d1 range && subsumes r1 r2 range
    
    | _ -> canUnify t1 t2

//-------------------------------------------------------------------------
// Constraint Solving
//-------------------------------------------------------------------------

/// Result of constraint solving
type SolveResult =
    | Solved
    | Deferred of Constraint list
    | Failed of UnificationError list

/// Solve a single constraint
let solveConstraint (c: Constraint) : Result<unit, UnificationError> =
    match c with
    | Constraint.Equals(t1, t2, range) ->
        tryUnify t1 t2 range
    
    | Constraint.HasMember(ty, name, signature, range) ->
        // SRTP constraint - member lookup will be implemented in SRTPResolution module
        // For now, record this as a deferred constraint
        // The signature and range are kept for error reporting
        ignore (ty, name, signature, range)
        Ok ()

    | Constraint.HasMeasure(ty, measure, range) ->
        let ty = applySubst ty
        match tryNumericComponents ty with
        | Some(_, actual) -> tryUnify (NativeType.TMeasure actual) (NativeType.TMeasure measure) range
        | None ->
            match ty with
            | NativeType.TVar _ -> tryUnify ty (withMeasure (freshTypeVar range) measure) range
            | NativeType.TError _ -> Ok ()
            | _ -> Error(TypeMismatch(ty, NativeType.TMeasure measure, range))

    | Constraint.Subtype(sub, super, range) ->
        // Subtype constraint - for now, treat as equality
        tryUnify sub super range

    | Constraint.LayoutCompatible(ty, layout, range) ->
        // Layout constraint - verify ty has compatible layout
        let actualLayout = layoutOf ty
        match (actualLayout, layout) with
        | TypeLayout.Opaque, _ -> Ok ()  // Unknown layout, defer check
        | _, TypeLayout.Opaque -> Ok ()  // Any layout is compatible with opaque
        | TypeLayout.Inline(s1, a1), TypeLayout.Inline(s2, a2) when s1 = s2 && a1 = a2 -> Ok ()
        | TypeLayout.Reference _, TypeLayout.Reference _ -> Ok ()
        | TypeLayout.PlatformWord, TypeLayout.PlatformWord -> Ok ()  // Platform word matches platform word
        | TypeLayout.PlatformWord, _ -> Ok ()  // Platform word deferred to codegen
        | _, TypeLayout.PlatformWord -> Ok ()  // Platform word deferred to codegen
        | _ ->
            ignore range  // Would be used for error location
            Ok ()  // For now, accept - codegen will validate

    | Constraint.HasTypeArgs(forallTy, args, resultTy, range) ->
        // Type application constraint - forallTy should be generic and instantiate to resultTy
        match forallTy with
        | NativeType.TForall(typeParams, bodyType) ->
            if List.length typeParams = List.length args then
                // Instantiate body with args and unify with result
                let substituted = NativeTypes.instantiate typeParams args bodyType
                tryUnify substituted resultTy range
            else
                // Arity mismatch
                Error (UnificationError.ArityMismatch(List.length typeParams, List.length args, range))
        | NativeType.TVar _ ->
            // Type variable - cannot resolve yet, this is okay
            Ok ()
        | _ ->
            // Non-forall type - this constraint will fail unless resolved later
            // For now, accept it; later constraint solving may refine
            ignore (args, resultTy, range)
            Ok ()

/// Solve a list of constraints, returning any that couldn't be solved immediately
let solveConstraints (constraints: Constraint list) : SolveResult =
    let mutable errors = []
    let mutable deferred = []
    
    for c in constraints do
        match solveConstraint c with
        | Ok () -> ()
        | Error e -> 
            match c with
            | Constraint.HasMember _ -> 
                // SRTP constraints can be deferred
                deferred <- c :: deferred
            | _ ->
                errors <- e :: errors
    
    if not (List.isEmpty errors) then
        Failed (List.rev errors)
    elif not (List.isEmpty deferred) then
        Deferred (List.rev deferred)
    else
        Solved

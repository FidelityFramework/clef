// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Union-Find data structure for efficient type substitution.
/// Uses path compression for near-constant-time operations.
module Clef.Compiler.NativeTypedTree.UnionFind

open Clef.Compiler.NativeTypedTree.NativeTypes

//-------------------------------------------------------------------------
// Core Union-Find Operations
//-------------------------------------------------------------------------

/// Find the representative type parameter with path compression.
/// Returns the root type parameter and its bound type (if any).
let rec find (typar: TypeParam) : TypeParam * NativeType option =
    match typar.Parent with
    | TypeParamState.Unbound -> 
        (typar, None)
    
    | TypeParamState.Bound(NativeType.TVar other) ->
        // Path compression: find root and update parent
        let (root, ty) = find other
        if root.Id <> other.Id then
            typar.Parent <- TypeParamState.Bound(NativeType.TVar root)
        (root, ty)
    
    | TypeParamState.Bound ty ->
        (typar, Some ty)

/// Get the current binding of a type parameter (after following indirections)
let getBinding (typar: TypeParam) : NativeType option =
    let (_, binding) = find typar
    binding

/// Check if a type parameter is still unbound
let isUnbound (typar: TypeParam) : bool =
    match find typar with
    | (_, None) -> true
    | (_, Some _) -> false

/// Union two type parameters (make them equivalent)
let union (tp1: TypeParam) (tp2: TypeParam) : unit =
    let (root1, bound1) = find tp1
    let (root2, bound2) = find tp2
    
    if root1.Id = root2.Id then
        () // Already unified
    else
        match (bound1, bound2) with
        | (None, None) ->
            // Both unbound: point one to the other
            root1.Parent <- TypeParamState.Bound(NativeType.TVar root2)
        
        | (None, Some _) ->
            // root1 is unbound, root2 is bound: bind root1 via root2
            root1.Parent <- TypeParamState.Bound(NativeType.TVar root2)

        | (Some _, None) ->
            // root1 is bound, root2 is unbound: bind root2 via root1
            root2.Parent <- TypeParamState.Bound(NativeType.TVar root1)
        
        | (Some _, Some _) ->
            // Both bound: this is a unification constraint, not handled here
            failwith "union: both type parameters are already bound - use unify instead"

/// Bind a type parameter to a concrete type
let bind (typar: TypeParam) (ty: NativeType) : unit =
    let (root, existing) = find typar
    match existing with
    | None ->
        root.Parent <- TypeParamState.Bound ty
    | Some _ ->
        failwith $"bind: type parameter '{typar.Name}' is already bound"

//-------------------------------------------------------------------------
// Type Substitution
//-------------------------------------------------------------------------

/// Apply substitutions to a type, following Union-Find pointers
let rec applySubst (ty: NativeType) : NativeType =
    match ty with
    | NativeType.TVar typar ->
        match find typar with
        | (root, None) -> NativeType.TVar root
        | (_, Some boundTy) -> applySubst boundTy  // Follow binding
    
    | NativeType.TApp(tc, [kind; NativeType.TMeasure measure]) when isNumericInferenceTyCon tc ->
        withMeasure (applySubst kind) measure
    | NativeType.TApp(tc, args) ->
        NativeType.TApp(tc, List.map applySubst args)
    
    | NativeType.TFun(domain, range) ->
        NativeType.TFun(applySubst domain, applySubst range)
    
    | NativeType.TTuple(elems, isStruct) ->
        NativeType.TTuple(List.map applySubst elems, isStruct)
    
    | NativeType.TForall(typars, body) ->
        // Don't substitute bound variables inside forall
        NativeType.TForall(typars, applySubst body)
    
    | NativeType.TByref(elem, kind) ->
        NativeType.TByref(applySubst elem, kind)
    
    | NativeType.TNativePtr elem ->
        NativeType.TNativePtr(applySubst elem)
    
    | NativeType.TAnon(fields, isStruct) ->
        NativeType.TAnon(fields |> List.map (fun (n, t) -> (n, applySubst t)), isStruct)

    // Named records use TApp - handled above (empty args)

    | NativeType.TUnion(tc, cases) ->
        NativeType.TUnion(tc, cases |> List.map (fun c ->
            { c with Fields = c.Fields |> List.map (fun (n, t) -> (n, applySubst t)) }))

    | NativeType.TLazy elem ->
        NativeType.TLazy(applySubst elem)  // PRD-14

    | NativeType.TSeq elem ->
        NativeType.TSeq(applySubst elem)  // PRD-15

    | NativeType.TSeqEnumerator elem ->
        NativeType.TSeqEnumerator(applySubst elem)  // PRD-15/16

    // PRD-13a: Immutable collection types
    | NativeType.TList elem ->
        NativeType.TList(applySubst elem)

    | NativeType.TMap(keyTy, valueTy) ->
        NativeType.TMap(applySubst keyTy, applySubst valueTy)

    | NativeType.TSet elem ->
        NativeType.TSet(applySubst elem)

    // Note: option<'T> is handled via TUnion - it's a discriminated union

    | NativeType.TMeasure measure -> NativeType.TMeasure(normalizeMeasure measure)
    | NativeType.TError _ -> ty

//-------------------------------------------------------------------------
// Occurs Check
//-------------------------------------------------------------------------

/// Check if a type parameter occurs in a type (for occurs check in unification)
let rec occursIn (typar: TypeParam) (ty: NativeType) : bool =
    match ty with
    | NativeType.TVar other ->
        let (root1, _) = find typar
        let (root2, bound2) = find other
        if root1.Id = root2.Id then
            true
        else
            match bound2 with
            | Some boundTy -> occursIn typar boundTy
            | None -> false
    
    | NativeType.TApp(_, args) ->
        List.exists (occursIn typar) args
    
    | NativeType.TFun(domain, range) ->
        occursIn typar domain || occursIn typar range
    
    | NativeType.TTuple(elems, _) ->
        List.exists (occursIn typar) elems
    
    | NativeType.TForall(typars, body) ->
        // Don't check bound variables
        if List.exists (fun tp -> tp.Id = typar.Id) typars then
            false
        else
            occursIn typar body
    
    | NativeType.TByref(elem, _) ->
        occursIn typar elem
    
    | NativeType.TNativePtr elem ->
        occursIn typar elem
    
    | NativeType.TAnon(fields, _) ->
        fields |> List.exists (fun (_, t) -> occursIn typar t)

    // Named records use TApp - handled above (empty args)

    | NativeType.TUnion(_, cases) ->
        cases |> List.exists (fun c ->
            c.Fields |> List.exists (fun (_, t) -> occursIn typar t))

    | NativeType.TLazy elem ->
        occursIn typar elem  // PRD-14

    | NativeType.TSeq elem ->
        occursIn typar elem  // PRD-15

    | NativeType.TSeqEnumerator elem ->
        occursIn typar elem  // PRD-15/16

    // PRD-13a: Immutable collection types
    | NativeType.TList elem ->
        occursIn typar elem

    | NativeType.TMap(keyTy, valueTy) ->
        occursIn typar keyTy || occursIn typar valueTy

    | NativeType.TSet elem ->
        occursIn typar elem

    // Note: option<'T> is handled via TUnion - it's a discriminated union

    | NativeType.TMeasure m -> occursInMeasure typar m
    | NativeType.TError _ -> false

and occursInMeasure (typar: TypeParam) (m: Measure) : bool =
    let root, _ = find typar
    measureFactors m |> Map.containsKey (Choice2Of2 root.Id)

//-------------------------------------------------------------------------
// Free Type Variables
//-------------------------------------------------------------------------

/// Collect all free type variables in a type
let rec freeTypeVars (ty: NativeType) : Set<TypeParamId> =
    match ty with
    | NativeType.TVar typar ->
        match find typar with
        | (root, None) -> Set.singleton root.Id
        | (_, Some boundTy) -> freeTypeVars boundTy
    
    | NativeType.TApp(_, args) ->
        args |> List.map freeTypeVars |> Set.unionMany
    
    | NativeType.TFun(domain, range) ->
        Set.union (freeTypeVars domain) (freeTypeVars range)
    
    | NativeType.TTuple(elems, _) ->
        elems |> List.map freeTypeVars |> Set.unionMany
    
    | NativeType.TForall(typars, body) ->
        let bound = typars |> List.map (fun tp -> tp.Id) |> Set.ofList
        Set.difference (freeTypeVars body) bound
    
    | NativeType.TByref(elem, _) ->
        freeTypeVars elem
    
    | NativeType.TNativePtr elem ->
        freeTypeVars elem
    
    | NativeType.TAnon(fields, _) ->
        fields |> List.map (fun (_, t) -> freeTypeVars t) |> Set.unionMany

    // Named records use TApp - handled above (empty args)

    | NativeType.TUnion(_, cases) ->
        cases
        |> List.collect (fun c -> c.Fields |> List.map snd)
        |> List.map freeTypeVars
        |> Set.unionMany

    | NativeType.TLazy elem ->
        freeTypeVars elem  // PRD-14

    | NativeType.TSeq elem ->
        freeTypeVars elem  // PRD-15

    | NativeType.TSeqEnumerator elem ->
        freeTypeVars elem  // PRD-15/16

    // PRD-13a: Immutable collection types
    | NativeType.TList elem ->
        freeTypeVars elem

    | NativeType.TMap(keyTy, valueTy) ->
        Set.union (freeTypeVars keyTy) (freeTypeVars valueTy)

    | NativeType.TSet elem ->
        freeTypeVars elem

    // Note: option<'T> is handled via TUnion - it's a discriminated union

    | NativeType.TMeasure m -> freeTypeVarsInMeasure m
    | NativeType.TError _ -> Set.empty

and freeTypeVarsInMeasure (m: Measure) : Set<TypeParamId> =
    measureFactors m |> Map.toList |> List.choose (fun (key, _) ->
        match key with Choice2Of2 id -> Some id | _ -> None) |> Set.ofList

/// Check if a type contains any unbound type variables
let hasUnboundVars (ty: NativeType) : bool =
    not (Set.isEmpty (freeTypeVars ty))

/// Check if a type is fully resolved (no unbound type variables)
let isResolved (ty: NativeType) : bool =
    Set.isEmpty (freeTypeVars ty)

/// Collect all free (unbound) TypeParam objects in a type
/// Returns the actual TypeParam records, not just IDs, for use in TForall construction
let rec collectFreeTypeParams (ty: NativeType) : TypeParam list =
    match ty with
    | NativeType.TVar typar ->
        match find typar with
        | (root, None) -> [root]  // Unbound - collect it
        | (_, Some boundTy) -> collectFreeTypeParams boundTy

    | NativeType.TApp(_, args) ->
        args |> List.collect collectFreeTypeParams

    | NativeType.TFun(domain, range) ->
        collectFreeTypeParams domain @ collectFreeTypeParams range

    | NativeType.TTuple(elems, _) ->
        elems |> List.collect collectFreeTypeParams

    | NativeType.TForall(typars, body) ->
        // Exclude bound type parameters
        let boundIds = typars |> List.map (fun tp -> tp.Id) |> Set.ofList
        collectFreeTypeParams body |> List.filter (fun tp -> not (Set.contains tp.Id boundIds))

    | NativeType.TByref(elem, _) ->
        collectFreeTypeParams elem

    | NativeType.TNativePtr elem ->
        collectFreeTypeParams elem

    | NativeType.TAnon(fields, _) ->
        fields |> List.collect (fun (_, t) -> collectFreeTypeParams t)

    // Named records use TApp - handled above (empty args)

    | NativeType.TUnion(_, cases) ->
        cases
        |> List.collect (fun c -> c.Fields |> List.map snd)
        |> List.collect collectFreeTypeParams

    | NativeType.TLazy elem ->
        collectFreeTypeParams elem  // PRD-14

    | NativeType.TSeq elem ->
        collectFreeTypeParams elem  // PRD-15

    | NativeType.TSeqEnumerator elem ->
        collectFreeTypeParams elem  // PRD-15/16

    // PRD-13a: Immutable collection types
    | NativeType.TList elem ->
        collectFreeTypeParams elem

    | NativeType.TMap(keyTy, valueTy) ->
        collectFreeTypeParams keyTy @ collectFreeTypeParams valueTy

    | NativeType.TSet elem ->
        collectFreeTypeParams elem

    // Note: option<'T> is handled via TUnion - it's a discriminated union

    | NativeType.TMeasure measure ->
        measureFactors measure |> Map.toList |> List.choose (fun (_, (atom, _)) ->
            match atom with MVar tp -> Some tp | _ -> None)
    | NativeType.TError _ -> []

/// Generalize a type by wrapping free type variables in TForall
/// This is used for let-bound polymorphic functions
let generalizeType (ty: NativeType) : NativeType =
    let freeParams = collectFreeTypeParams ty |> List.distinctBy (fun tp -> tp.Id)
    if List.isEmpty freeParams then
        ty
    else
        NativeType.TForall(freeParams, ty)

//-------------------------------------------------------------------------
// Type Parameter Generation
//-------------------------------------------------------------------------

/// Mutable counter for generating fresh type parameter IDs
let mutable private nextTypeParamId = 0

/// Generate a fresh type parameter with a name and kind
let freshTypeParam (name: string) (kind: TypeParamKind) (range: SourceRange) : TypeParam =
    let id = nextTypeParamId
    nextTypeParamId <- nextTypeParamId + 1
    { Id = id
      Name = name
      Kind = kind
      Constraints = []
      Parent = TypeParamState.Unbound
      Range = range }

/// Generate a fresh type parameter with an auto-generated name
let freshTypeParamAuto (kind: TypeParamKind) (range: SourceRange) : TypeParam =
    let id = nextTypeParamId
    nextTypeParamId <- nextTypeParamId + 1
    let prefix = match kind with TypeParamKind.Type -> "'?" | TypeParamKind.Measure -> "'u?"
    { Id = id
      Name = $"{prefix}{id}"
      Kind = kind
      Constraints = []
      Parent = TypeParamState.Unbound
      Range = range }

/// Generate a fresh type variable (type parameter, not measure)
let freshTypeVar (range: SourceRange) : NativeType =
    NativeType.TVar(freshTypeParamAuto TypeParamKind.Type range)

/// Generate a fresh measure variable
let freshMeasureVar (range: SourceRange) : TypeParam =
    freshTypeParamAuto TypeParamKind.Measure range

/// Reset the type parameter counter (for testing)
let resetTypeParamCounter () =
    nextTypeParamId <- 0

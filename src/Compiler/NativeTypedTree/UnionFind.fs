// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Union-Find data structure for efficient type substitution.
/// Uses path compression for near-constant-time operations.
module Clef.Compiler.NativeTypedTree.UnionFind

open Clef.Compiler.NativeTypedTree.DimensionAlgebra
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
        | (_, None) -> ty  // Still unbound
        | (_, Some boundTy) -> applySubst boundTy  // Follow binding
    
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

    // A dimension holds measure variables, not type parameters; the measure store is read
    // through `Dimension.resolve` by its own readers, never through the type substitution.
    | NativeType.TNum _ | NativeType.TMeasure _ -> ty
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

    // A type parameter never occurs in a dimension: Dimension.Vars holds measure variables, and
    // measures need no occurs check of their own (design b.3).
    | NativeType.TNum _ | NativeType.TMeasure _ -> false
    | NativeType.TError _ -> false

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

    // Free measure variables are Dimension.Vars, collected by the generalisation of CS-6.
    | NativeType.TNum _ | NativeType.TMeasure _ -> Set.empty
    | NativeType.TError _ -> Set.empty

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

    | NativeType.TNum _ | NativeType.TMeasure _ -> []  // measure variables are not TypeParams (CS-6 collects them)
    | NativeType.TError _ -> []

/// Like applySubst, and additionally rewrite every still-unbound variable to its union-find
/// ROOT record. TypeParam has reference equality, so a type must mention each variable through
/// one canonical record for substitution tables (NativeTypes.instantiate) to find it.
let rec canonicalizeVars (ty: NativeType) : NativeType =
    match ty with
    | NativeType.TVar typar ->
        match find typar with
        | (root, None) -> NativeType.TVar root
        | (_, Some boundTy) -> canonicalizeVars boundTy
    | NativeType.TApp(tc, args) -> NativeType.TApp(tc, List.map canonicalizeVars args)
    | NativeType.TFun(domain, range) -> NativeType.TFun(canonicalizeVars domain, canonicalizeVars range)
    | NativeType.TTuple(elems, isStruct) -> NativeType.TTuple(List.map canonicalizeVars elems, isStruct)
    | NativeType.TForall(typars, body) -> NativeType.TForall(typars, canonicalizeVars body)
    | NativeType.TByref(elem, kind) -> NativeType.TByref(canonicalizeVars elem, kind)
    | NativeType.TNativePtr elem -> NativeType.TNativePtr(canonicalizeVars elem)
    | NativeType.TAnon(fields, isStruct) -> NativeType.TAnon(fields |> List.map (fun (n, t) -> (n, canonicalizeVars t)), isStruct)
    | NativeType.TUnion(tc, cases) ->
        NativeType.TUnion(tc, cases |> List.map (fun c -> { c with Fields = c.Fields |> List.map (fun (n, t) -> (n, canonicalizeVars t)) }))
    | NativeType.TLazy elem -> NativeType.TLazy(canonicalizeVars elem)
    | NativeType.TSeq elem -> NativeType.TSeq(canonicalizeVars elem)
    | NativeType.TSeqEnumerator elem -> NativeType.TSeqEnumerator(canonicalizeVars elem)
    | NativeType.TList elem -> NativeType.TList(canonicalizeVars elem)
    | NativeType.TMap(keyTy, valueTy) -> NativeType.TMap(canonicalizeVars keyTy, canonicalizeVars valueTy)
    | NativeType.TSet elem -> NativeType.TSet(canonicalizeVars elem)
    | NativeType.TNum _ | NativeType.TMeasure _ | NativeType.TError _ -> ty

/// Generalize a type by wrapping free type variables in TForall
/// This is used for let-bound polymorphic functions. The body is canonicalized first so the
/// scheme's parameters and the variables in its body are the same TypeParam records.
let generalizeType (ty: NativeType) : NativeType =
    let ty = canonicalizeVars ty
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

/// Mint a fresh measure variable (design a.1: `_` anonymous, `'u` named) from the same counter as
/// the type parameters, so a measure variable id and a type parameter id never coincide.
let freshMeasureVar (name: string option) : MeasureVar =
    let id = nextTypeParamId
    nextTypeParamId <- nextTypeParamId + 1
    { Id = id; Name = name }

/// A supply of fresh measure variables for a pure step (`dimensionOfSyntax`, `solveDim`), taken
/// at the counter; the step returns the advanced supply and `commitMeasureSupply` reserves the ids
/// it used. The invariant is that nothing mints on a path that commits: a translation that fails
/// (the one path on which the translator's type-name check may mint a parameter) is never
/// committed, and the solver mints nothing, so the ids stay distinct.
let freshMeasureSupply () : MeasureSupply = MeasureSupply.startingAt nextTypeParamId

/// Reserve the ids a pure step minted from a supply taken by `freshMeasureSupply`. On a path that
/// commits, nothing mints a type parameter between the two calls, so the counter cannot have moved;
/// the guard refuses the one state that would prove otherwise (a counter past the supply) rather
/// than silently rewinding it.
let commitMeasureSupply (supply: MeasureSupply) : unit =
    if supply.Next < nextTypeParamId then
        failwith "commitMeasureSupply: the counter has passed the supply; something minted a variable between taking and committing it"
    nextTypeParamId <- supply.Next

//-------------------------------------------------------------------------
// Measure cells: the bindings of measure variables, in the one store (plan D7, U-2)
//-------------------------------------------------------------------------

/// The cell of a measure variable in the union-find: a Measure-kinded type parameter whose
/// `Parent` holds `Bound (TMeasure d)` once the variable is bound. One cell per variable, made on
/// first touch (a variable nothing has touched is unbound by definition), indexed by the
/// variable's id, which the shared counter keeps distinct from every type parameter's.
let private measureCells = System.Collections.Generic.Dictionary<int, TypeParam>()

let private measureCell (v: MeasureVar) : TypeParam =
    match measureCells.TryGetValue v.Id with
    | true, cell -> cell
    | false, _ ->
        let cell =
            { Id = v.Id
              Name = Dimension.renderVar v
              Kind = TypeParamKind.Measure
              Constraints = []
              Parent = TypeParamState.Unbound
              Range = dummyRange }
        measureCells.[v.Id] <- cell
        cell

/// The binding of a measure variable, if any: the one read of a measure cell, kind-checked (a
/// measure cell holds a dimension and nothing else).
let lookupMeasure (v: MeasureVar) : Dimension option =
    match (measureCell v).Parent with
    | TypeParamState.Unbound -> None
    | TypeParamState.Bound(NativeType.TMeasure d) -> Some d
    | TypeParamState.Bound other ->
        failwith $"lookupMeasure: the cell of {Dimension.renderVar v} holds a type, '{formatType other}': kind violation"

/// A dimension with every bound variable replaced by its binding, to a fixpoint: `resolve` is the
/// only read of the measure store (design b.2, (h) 8).
let resolveDim (d: Dimension) : Dimension =
    Dimension.resolve lookupMeasure d

/// Apply the bindings `solveDim` returned: the only writer of measure cells. Each variable is
/// unbound in the store (the solver binds only unbound variables) and is never rebound (I2).
let bindMeasures (bindings: (MeasureVar * Dimension) list) : unit =
    bindings
    |> List.iter (fun (v, d) ->
        let cell = measureCell v
        match cell.Parent with
        | TypeParamState.Unbound -> cell.Parent <- TypeParamState.Bound(NativeType.TMeasure d)
        | TypeParamState.Bound _ ->
            failwith $"bindMeasures: {Dimension.renderVar v} is already bound; a measure variable is never rebound")

/// Reset the type parameter counter and the measure cells (for testing)
let resetTypeParamCounter () =
    nextTypeParamId <- 0
    measureCells.Clear()

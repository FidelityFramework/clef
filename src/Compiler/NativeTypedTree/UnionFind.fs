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
        // What is attached to a variable (an operand dispatch, design c.3) survives the union on
        // the root of the class.
        let carry (from: TypeParam) (into: TypeParam) =
            into.Constraints <- into.Constraints @ (from.Constraints |> List.filter (fun c -> not (List.contains c into.Constraints)))
        match (bound1, bound2) with
        | (None, None) ->
            // Both unbound: point one to the other
            carry root1 root2
            root1.Parent <- TypeParamState.Bound(NativeType.TVar root2)
        
        | (None, Some _) ->
            // root1 is unbound, root2 is bound: bind root1 via root2
            carry root1 root2
            root1.Parent <- TypeParamState.Bound(NativeType.TVar root2)

        | (Some _, None) ->
            // root1 is bound, root2 is unbound: bind root2 via root1
            carry root2 root1
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
// Measure cells: the bindings of measure variables, in the one store (plan D7, U-2)
//-------------------------------------------------------------------------

/// The cell of a measure variable in the union-find: a Measure-kinded type parameter whose
/// `Parent` holds `Bound (TMeasure d)` once the variable is bound. One cell per variable, made on
/// first touch (a variable nothing has touched is unbound by definition), indexed by the
/// variable's id, which the shared counter keeps distinct from every type parameter's. The
/// variable is kept beside its cell so that a scheme quantifying the cell (design b.4) can
/// instantiate the variable by identity and name.
let private measureCells = System.Collections.Generic.Dictionary<int, TypeParam * MeasureVar>()

let private measureCell (v: MeasureVar) : TypeParam =
    match measureCells.TryGetValue v.Id with
    | true, (cell, _) -> cell
    | false, _ ->
        let cell =
            { Id = v.Id
              Name = Dimension.renderVar v
              Kind = TypeParamKind.Measure
              Constraints = []
              Parent = TypeParamState.Unbound
              Range = dummyRange }
        measureCells.[v.Id] <- (cell, v)
        cell

/// The cell of a measure variable: the Measure-kinded type parameter a scheme quantifies for it.
let measureCellOf (v: MeasureVar) : TypeParam = measureCell v

/// The measure variable of a Measure-kinded scheme parameter (its cell), by identity.
let measureVarOf (tp: TypeParam) : MeasureVar =
    match measureCells.TryGetValue tp.Id with
    | true, (_, v) -> v
    | false, _ -> failwith $"measureVarOf: {tp.Name} is not the cell of a measure variable: kind violation"

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

/// Apply a list of measure bindings: the only writer of measure cells, called with `solveDim`'s
/// bindings by the unifier and with the change of basis of generalisation (design b.4 step 3,
/// `generalizeType`). Each variable is unbound in the store (both callers bind only unbound
/// variables) and is never rebound (I2).
let bindMeasures (bindings: (MeasureVar * Dimension) list) : unit =
    bindings
    |> List.iter (fun (v, d) ->
        let cell = measureCell v
        match cell.Parent with
        | TypeParamState.Unbound -> cell.Parent <- TypeParamState.Bound(NativeType.TMeasure d)
        | TypeParamState.Bound _ ->
            failwith $"bindMeasures: {Dimension.renderVar v} is already bound; a measure variable is never rebound")

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

    // The carrier position is read through the one carrier read (a bound carrier variable
    // becomes its constructor, an unbound one its root) and the dimension through the one
    // measure read: a type leaving the store mentions only unbound variables (design b.4 step 1).
    | NativeType.TNum(carrier, dim) -> NativeType.TNum(CarrierRef.resolve carrier, resolveDim dim)
    | NativeType.TMeasure dim -> NativeType.TMeasure(resolveDim dim)
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

    // An unbound carrier variable is free in the type (it is a type parameter of kind Carrier);
    // free measure variables are Dimension.Vars, collected by the generalisation of CS-6.
    | NativeType.TNum(carrier, _) ->
        match CarrierRef.resolve carrier with
        | CarrierRef.CVar root -> Set.singleton root.Id
        | CarrierRef.Carrier _ -> Set.empty
    | NativeType.TMeasure _ -> Set.empty
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

    // An unbound carrier variable is collected as its root record, like a type variable;
    // measure variables are not TypeParams (the generalisation of CS-6 collects them).
    | NativeType.TNum(carrier, _) ->
        match CarrierRef.resolve carrier with
        | CarrierRef.CVar root -> [root]
        | CarrierRef.Carrier _ -> []
    | NativeType.TMeasure _ -> []
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
    | NativeType.TNum(carrier, dim) -> NativeType.TNum(CarrierRef.resolve carrier, resolveDim dim)
    | NativeType.TMeasure dim -> NativeType.TMeasure(resolveDim dim)
    | NativeType.TError _ -> ty

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
    let prefix =
        match kind with
        | TypeParamKind.Type -> "'?"
        | TypeParamKind.Measure -> "'u?"
        | TypeParamKind.Carrier -> "'k?"
    { Id = id
      Name = $"{prefix}{id}"
      Kind = kind
      Constraints = []
      Parent = TypeParamState.Unbound
      Range = range }

/// Generate a fresh type variable (type parameter, not measure)
let freshTypeVar (range: SourceRange) : NativeType =
    NativeType.TVar(freshTypeParamAuto TypeParamKind.Type range)

/// The operator whose operand position a variable was minted for, if any (design c.1, c.3).
let operandOf (tp: TypeParam) : string option =
    tp.Constraints |> List.tryPick (function Constraint.OperandOf(op, _) -> Some op | _ -> None)

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
// Carrier cells: the bindings of carrier variables, in the one store (design a.2, plan D7)
//-------------------------------------------------------------------------

/// Bind an unbound carrier variable to a numeric constructor: the cell holds the constructor at
/// the measure 1, and `CarrierRef.resolve` is its only read. Kind-checked: only a
/// Carrier-kinded parameter may hold a carrier, and it is never rebound (I2).
let bindCarrier (tp: TypeParam) (tc: TypeConRef) : unit =
    if tp.Kind <> TypeParamKind.Carrier then
        failwith $"bindCarrier: {tp.Name} is not a carrier variable: kind violation"
    match CarrierRef.resolve (CarrierRef.CVar tp) with
    | CarrierRef.CVar root -> root.Parent <- TypeParamState.Bound(NativeType.TNum(CarrierRef.Carrier tc, Dimension.one))
    | CarrierRef.Carrier bound ->
        failwith $"bindCarrier: {tp.Name} is already bound to {bound.Name}; a carrier variable is never rebound"

/// Union two unbound carrier variables: the first's root links to the second's, so the second
/// becomes the root of the class (the caller chooses which survives).
let unionCarriers (tp1: TypeParam) (tp2: TypeParam) : unit =
    if tp1.Kind <> TypeParamKind.Carrier || tp2.Kind <> TypeParamKind.Carrier then
        failwith $"unionCarriers: {tp1.Name} and {tp2.Name} must both be carrier variables: kind violation"
    match CarrierRef.resolve (CarrierRef.CVar tp1), CarrierRef.resolve (CarrierRef.CVar tp2) with
    | CarrierRef.CVar root1, CarrierRef.CVar root2 ->
        if root1.Id <> root2.Id then
            root1.Parent <- TypeParamState.Bound(NativeType.TVar root2)
    | _ -> failwith $"unionCarriers: {tp1.Name} or {tp2.Name} is already bound; bind the other instead"

//-------------------------------------------------------------------------
// Generalisation over type, carrier and measure variables (design b.4)
//-------------------------------------------------------------------------

/// The distinct dimension occurrences of a type, resolved, in first-occurrence order: the
/// dimension of every numeric position. A measure-sorted position on a non-numeric constructor
/// (`Arena<'lifetime>`) is not a numeric occurrence and is not generalised here: region and
/// lifetime take their own kind at step 5, and quantifying them would change nothing a program
/// can observe. A nested scheme is opaque to this walk.
let dimensionOccurrences (ty: NativeType) : Dimension list =
    let rec go (acc: Dimension list) (ty: NativeType) : Dimension list =
        match ty with
        | NativeType.TNum(_, d) | NativeType.TMeasure d ->
            let d = resolveDim d
            if List.contains d acc then acc else acc @ [ d ]
        | NativeType.TVar tp ->
            match find tp with
            | (_, Some bound) -> go acc bound
            | (_, None) -> acc
        | NativeType.TApp(_, args) -> List.fold go acc args
        | NativeType.TTuple(elems, _) -> List.fold go acc elems
        | NativeType.TFun(d, r) -> go (go acc d) r
        | NativeType.TByref(e, _) | NativeType.TNativePtr e | NativeType.TLazy e | NativeType.TSeq e
        | NativeType.TSeqEnumerator e | NativeType.TList e | NativeType.TSet e -> go acc e
        | NativeType.TMap(k, v) -> go (go acc k) v
        | NativeType.TAnon(fields, _) -> fields |> List.fold (fun acc (_, t) -> go acc t) acc
        | NativeType.TUnion(_, cases) ->
            cases |> List.fold (fun acc c -> c.Fields |> List.fold (fun acc (_, t) -> go acc t) acc) acc
        | NativeType.TForall _ | NativeType.TError _ -> acc
    go [] ty

/// The free measure variables of a type's numeric positions, resolved, in first-occurrence
/// order (within one dimension, by variable identity, the order they were minted in).
let freeMeasureVars (ty: NativeType) : MeasureVar list =
    dimensionOccurrences ty
    |> List.collect (fun d -> d.Vars |> Map.toList |> List.map fst)
    |> List.distinct

/// Whether a type mentions a free measure variable (in a numeric position) or a free carrier variable.
let hasFreeMeasureOrCarrierVars (ty: NativeType) : bool =
    not (List.isEmpty (freeMeasureVars ty))
    || (collectFreeTypeParams ty |> List.exists (fun tp -> tp.Kind = TypeParamKind.Carrier))

/// A column of the working matrix of the Hermite step: its entries in `E` (one per dimension
/// occurrence) and in `Q` (one per candidate variable), carried together so that every column
/// operation applies to both.
type private HermiteColumn = { E: int list; Q: int list }

/// Column Hermite normal form (design b.4 step 3, DBC line 204 "fewest free variables"). `E` is
/// the integer matrix whose rows are the exponent vectors, over the candidate measure variables,
/// of the distinct dimension occurrences; unimodular column operations, applied alike to `Q`
/// (from the identity), bring `E Q` to column Hermite form: row by row, Euclid across the
/// columns not yet pivoted leaves at most one non-zero entry, at the pivot column, made positive,
/// and the entries of that row in the earlier pivot columns are reduced modulo the pivot to
/// `0 <= entry < pivot`; after every row the non-pivot columns are zero in every row. Returns the
/// pivot columns, in pivot order, and the zero columns. The columns of `Q` are the new variables
/// (`v = Q w`); the pivot count is the rank, the number of survivors.
let private columnHermite (columns: HermiteColumn list) (rows: int) : HermiteColumn list * HermiteColumn list =
    let combine (k: int) (src: HermiteColumn) (dst: HermiteColumn) : HermiteColumn =
        { E = List.map2 (fun d s -> d + k * s) dst.E src.E
          Q = List.map2 (fun d s -> d + k * s) dst.Q src.Q }
    let negate (c: HermiteColumn) : HermiteColumn = { E = List.map (~-) c.E; Q = List.map (~-) c.Q }
    let floorDiv (a: int) (b: int) : int =
        let q = a / b
        if a % b <> 0 && ((a < 0) <> (b < 0)) then q - 1 else q
    let rec reduceRow (r: int) (free: HermiteColumn list) : HermiteColumn option * HermiteColumn list =
        let entry (c: HermiteColumn) = List.item r c.E
        match free |> List.filter (fun c -> entry c <> 0) with
        | [] -> None, free
        | _ ->
            let pivotIndex = free |> List.findIndex (fun c -> entry c <> 0 && free |> List.forall (fun c' -> entry c' = 0 || abs (entry c') >= abs (entry c)))
            let pivot = List.item pivotIndex free
            let rest = free |> List.indexed |> List.filter (fun (i, _) -> i <> pivotIndex) |> List.map snd
            let reduced = rest |> List.map (fun c -> combine (-(entry c / entry pivot)) pivot c)
            if reduced |> List.forall (fun c -> entry c = 0) then
                Some (if entry pivot < 0 then negate pivot else pivot), reduced
            else
                reduceRow r (pivot :: reduced)
    let pivots, zeros =
        [ 0 .. rows - 1 ]
        |> List.fold
            (fun (pivots, free) r ->
                match reduceRow r free with
                | Some pivot, free' ->
                    // The earlier pivot columns are zero in every row before r, and so is this
                    // pivot column, so reducing their row-r entries modulo the pivot keeps the form.
                    let reducedPivots =
                        pivots |> List.map (fun c -> combine (-(floorDiv (List.item r c.E) (List.item r pivot.E))) pivot c)
                    reducedPivots @ [ pivot ], free'
                | None, free' -> pivots, free')
            ([], columns)
    pivots, zeros

/// The names anonymous survivors take, in order: `'u 'v 'w 'x 'y 'z 'u1 'v1 ...`, skipping names in use.
let private measureNamePool (taken: Set<string>) : string seq =
    Seq.initInfinite (fun i ->
        let letter = "uvwxyz".[i % 6]
        if i < 6 then string letter else string letter + string (i / 6))
    |> Seq.filter (fun name -> not (Set.contains name taken))

/// Simplify the measure part of a scheme (design b.4 steps 3 and 4). The candidates are the
/// measure variables to quantify; the occurrences are the type's distinct dimensions. The
/// exponent matrix is brought to column Hermite form; each pivot column is a survivor, a fresh
/// variable named in pivot (first-occurrence) order: a survivor that is one of the candidates
/// unchanged keeps that candidate's name, an anonymous one takes the next unused name; a zero
/// column is a fresh anonymous variable no occurrence mentions. Every candidate is then bound in
/// the store to its expression in the new variables (`v = Q w`), so the binding's body, which
/// still mentions the candidates, resolves to the survivors the scheme quantifies. Returns the
/// survivors, in order.
let private simplifyMeasures (candidates: MeasureVar list) (occurrences: Dimension list) (taken: Set<string>) : MeasureVar list =
    match candidates with
    | [] -> []
    | _ ->
        let m = List.length candidates
        let columns =
            candidates
            |> List.mapi (fun i v ->
                { E = occurrences |> List.map (fun d -> Map.tryFind v d.Vars |> Option.defaultValue 0)
                  Q = List.init m (fun j -> if i = j then 1 else 0) })
        let pivots, zeros = columnHermite columns (List.length occurrences)
        // Full rank: the candidates are already the survivors (design b.4 step 3 exists to reach
        // rank(E) many variables; step 4 renames in first-occurrence order and never changes the
        // basis of a scheme that has nothing to drop). Names are kept; an anonymous candidate takes
        // a pool name through a binding to a named survivor.
        if List.length pivots = m then
            candidates
            |> List.fold
                (fun (acc: MeasureVar list, taken: Set<string>) v ->
                    match v.Name with
                    | Some name when not (Set.contains name taken) -> acc @ [ v ], Set.add name taken
                    | _ ->
                        let name = measureNamePool taken |> Seq.head
                        let survivor = freshMeasureVar (Some name)
                        bindMeasures [ v, Dimension.ofVar survivor ]
                        acc @ [ survivor ], Set.add name taken)
                ([], taken)
            |> fst
        else
        // A pivot column that is a unit vector e_i whose candidate i appears in no other column
        // is that candidate itself; it keeps the candidate's name.
        let unchangedCandidate (col: HermiteColumn) : MeasureVar option =
            match col.Q |> List.indexed |> List.filter (fun (_, q) -> q <> 0) with
            | [ (i, 1) ] when pivots @ zeros |> List.forall (fun c -> obj.ReferenceEquals(c, col) || List.item i c.Q = 0) ->
                Some (List.item i candidates)
            | _ -> None
        let named =
            pivots
            |> List.fold
                (fun (acc: (HermiteColumn * MeasureVar) list, taken: Set<string>) col ->
                    let name =
                        match unchangedCandidate col |> Option.bind (fun v -> v.Name) with
                        | Some name when not (Set.contains name taken) -> name
                        | _ -> measureNamePool taken |> Seq.head
                    let survivor = freshMeasureVar (Some name)
                    acc @ [ col, survivor ], Set.add name taken)
                ([], taken)
            |> fst
        // A dropped (zero) column is a degree of freedom the type never constrains: it cancels
        // in every occurrence, so it is the measure 1 in every candidate's binding, never a
        // variable the scheme would have to quantify or a local binding could leave unresolved.
        let newVars = named
        let bindings =
            candidates
            |> List.mapi (fun i v ->
                let expression =
                    newVars
                    |> List.fold
                        (fun acc (col, w) ->
                            match List.item i col.Q with
                            | 0 -> acc
                            | e -> Dimension.mul acc (Dimension.pow e (Dimension.ofVar w)))
                        Dimension.one
                v, expression)
        bindMeasures bindings
        named |> List.map snd

/// Generalise a type (design b.4): resolve it through the stores; collect its free type
/// variables, free carrier variables and free measure variables; subtract the variables free in
/// the environment (`envFree`, by id, resolved by the caller through the same stores); simplify
/// the measure part by column Hermite form; rename the survivors in first-occurrence order and
/// quantify. A carrier survivor is a fresh variable named `'k`, `'k1`, ... that the old variable
/// is unioned into (so the body resolves to it); a measure survivor is quantified through its
/// cell. The body is canonicalised so the scheme's parameters and the variables in its body are
/// the same records. Type variables are also subtracted, so nested bindings cannot quantify a captured
/// value or mutable storage cell.
let generalizeType (envFree: Set<int>) (ty: NativeType) : NativeType =
    let ty = canonicalizeVars ty
    let freeParams = collectFreeTypeParams ty |> List.distinctBy (fun tp -> tp.Id)
    let typeParams = freeParams |> List.filter (fun tp -> tp.Kind = TypeParamKind.Type && not (Set.contains tp.Id envFree))
    let carrierParams = freeParams |> List.filter (fun tp -> tp.Kind = TypeParamKind.Carrier && not (Set.contains tp.Id envFree))
    let allMeasures = freeMeasureVars ty
    let measureCandidates = allMeasures |> List.filter (fun v -> not (Set.contains v.Id envFree))
    if List.isEmpty typeParams && List.isEmpty carrierParams && List.isEmpty measureCandidates then
        ty
    else
        let keptNames =
            allMeasures
            |> List.filter (fun v -> Set.contains v.Id envFree)
            |> List.choose (fun v -> v.Name)
            |> Set.ofList
        let measureSurvivors = simplifyMeasures measureCandidates (dimensionOccurrences ty) keptNames
        let carrierSurvivors =
            carrierParams
            |> List.mapi (fun i tp ->
                let fresh = freshTypeParam (if i = 0 then "'k" else $"'k{i}") TypeParamKind.Carrier tp.Range
                fresh.Constraints <- tp.Constraints
                unionCarriers tp fresh
                fresh)
        let body = canonicalizeVars ty
        NativeType.TForall(typeParams @ carrierSurvivors @ (measureSurvivors |> List.map measureCellOf), body)


/// A fresh variable of the same kind as a scheme parameter, in the form that parameter's
/// positions take: a type variable, a carrier variable at the measure 1 (its occurrences keep
/// their own dimensions), or a measure variable in a measure position (design b.4 step 4:
/// "instantiation mints fresh variables of the same kind"). What was attached to the parameter
/// (an operand dispatch) is attached to the fresh variable. This is the one minting place
/// for instantiation, so every instantiation site agrees on the form of each kind.
let freshInstanceOf (tp: TypeParam) (range: SourceRange) : NativeType =
    match tp.Kind with
    | TypeParamKind.Type ->
        let fresh = freshTypeParamAuto TypeParamKind.Type range
        fresh.Constraints <- tp.Constraints
        NativeType.TVar fresh
    | TypeParamKind.Carrier ->
        let fresh = freshTypeParamAuto TypeParamKind.Carrier range
        fresh.Constraints <- tp.Constraints
        NativeType.TNum(CarrierRef.CVar fresh, Dimension.one)
    | TypeParamKind.Measure ->
        NativeType.TMeasure(Dimension.ofVar (freshMeasureVar None))

/// Reset the type parameter counter and the measure cells (for testing)
let resetTypeParamCounter () =
    nextTypeParamId <- 0
    measureCells.Clear()

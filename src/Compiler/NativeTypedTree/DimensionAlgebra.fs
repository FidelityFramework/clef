/// The dimension algebra: the measure component of a numeric type and its unifier.
///
/// Design of record: docs/fidelity/phg/Dimensional_Step1_2_Design.md (a.1), (a.4) render rule,
/// (b.1), (b.2), (b.3); docs/fidelity/phg/Dimensional_Steps_1_2_Sequence.md CS-1; plan D7.
///
/// A dimension is a point of the free abelian group Z^B (+) Z^M, B the declared base measures and
/// M the measure inference variables, held in canonical form: no stored exponent is zero and both
/// maps empty is the measure 1. Because `Dimension.mk` is the only constructor, structural equality
/// on `Dimension` is dimensional equality (units-of-measure.md §Relations of Measures: normalise
/// by commutativity, associativity, identity, inverses, abbreviation; then compare).
///
/// This module depends on nothing in the type checker. It is placed before NativeTypes.fs and
/// knows no type DU; the measure environment (abbreviations, the syntax translator) and the
/// numeric type that carries a `Dimension` arrive in later changesets.
module Clef.Compiler.NativeTypedTree.DimensionAlgebra

//-------------------------------------------------------------------------
// Generators
//-------------------------------------------------------------------------

/// A declared base measure, `[<Measure>] type m`. Identity is the declaration, module-qualified.
/// `Module` is the declaring module's path (the same shape as NativeTypes.ModulePath, spelled out
/// here so that this file precedes NativeTypes.fs with no dependency on it).
type BaseMeasure = { Name: string; Module: string list }

/// A measure inference variable. `_` mints an anonymous one, `'u` a named one.
/// Its kind is Measure: it is a type parameter of the measure sort and never of the type sort.
/// Identity is the `Id` and nothing else: equality, hashing and ordering exclude the name, so the
/// map keys, the lookup partition in `resolve` and the removal in `solveDim` all see one variable
/// however it is presented (design (b.4) step 4 renames survivors without changing their identity).
[<CustomEquality; CustomComparison>]
type MeasureVar =
    { Id: int; Name: string option }

    override this.Equals(other: obj) =
        match other with
        | :? MeasureVar as v -> this.Id = v.Id
        | _ -> false

    override this.GetHashCode() = this.Id

    interface System.IComparable with
        member this.CompareTo(other: obj) =
            match other with
            | :? MeasureVar as v -> compare this.Id v.Id
            | _ -> invalidArg "other" "MeasureVar compared with a value of another type"

//-------------------------------------------------------------------------
// The canonical form
//-------------------------------------------------------------------------

/// A point of Z^B (+) Z^M in canonical form: no stored exponent is zero.
/// Both maps empty is the measure 1. Constructed only through `Dimension.mk`; no other code
/// builds this record, so structural equality is dimensional equality.
type Dimension = { Bases: Map<BaseMeasure, int>; Vars: Map<MeasureVar, int> }

module Dimension =

    /// The one constructor: drops every zero exponent so the representation is canonical.
    let mk (bases: Map<BaseMeasure, int>) (vars: Map<MeasureVar, int>) : Dimension =
        { Bases = Map.filter (fun _ e -> e <> 0) bases
          Vars = Map.filter (fun _ e -> e <> 0) vars }

    /// The measure 1.
    let one : Dimension = mk Map.empty Map.empty

    let ofBase (b: BaseMeasure) : Dimension = mk (Map.ofList [ b, 1 ]) Map.empty

    let ofVar (v: MeasureVar) : Dimension = mk Map.empty (Map.ofList [ v, 1 ])

    /// Exponent-wise sum of two maps over the same generator set; zeros are dropped by `mk`.
    let private addExponents (xs: Map<'g, int>) (ys: Map<'g, int>) : Map<'g, int> =
        Map.fold
            (fun acc g e ->
                match Map.tryFind g acc with
                | Some e0 -> Map.add g (e0 + e) acc
                | None -> Map.add g e acc)
            xs
            ys

    /// Multiplication adds exponent vectors.
    let mul (d1: Dimension) (d2: Dimension) : Dimension =
        mk (addExponents d1.Bases d2.Bases) (addExponents d1.Vars d2.Vars)

    /// Inversion negates every exponent.
    let inv (d: Dimension) : Dimension =
        mk (Map.map (fun _ e -> -e) d.Bases) (Map.map (fun _ e -> -e) d.Vars)

    /// Exponentiation scales every exponent; `pow 0 d = one`.
    let pow (n: int) (d: Dimension) : Dimension =
        mk (Map.map (fun _ e -> n * e) d.Bases) (Map.map (fun _ e -> n * e) d.Vars)

    /// A dimension with no measure variables.
    let isGround (d: Dimension) : bool = Map.isEmpty d.Vars

    /// Replace every bound variable by its binding, to a fixpoint. Idempotent: the result contains
    /// only variables the lookup leaves unbound. The lookup is the caller's store; this module owns
    /// none. Bindings are acyclic by construction (b.3: the eliminated variable is always replaced by
    /// a fresh one), so the fixpoint is reached.
    let rec resolve (lookup: MeasureVar -> Dimension option) (d: Dimension) : Dimension =
        let bound, free = d.Vars |> Map.partition (fun v _ -> (lookup v).IsSome)
        if Map.isEmpty bound then
            d
        else
            let substituted =
                Map.fold
                    (fun acc v e ->
                        match lookup v with
                        | Some target -> mul acc (pow e target)
                        | None -> acc)
                    (mk d.Bases free)
                    bound
            resolve lookup substituted

    /// The presentation label of a measure variable: `'u` for a named one, `'_n` for an anonymous one.
    let renderVar (v: MeasureVar) : string =
        match v.Name with
        | Some name -> "'" + name
        | None -> "'_" + string v.Id

    /// The spec's normalised presentation (units-of-measure.md §Relations of Measures):
    /// measure parameters first, alphabetical, then measure identifiers, alphabetical; positive
    /// powers, then `/` and the negative powers written as positive; a power greater than 1 is
    /// written with `^`; the empty dimension is `1`. "Alphabetical" is ordinal and case-sensitive,
    /// as F# itself orders measures, so `N` sorts before `m`. This is the one formatter: hover,
    /// diagnostics and the reified attribute read it.
    let render (d: Dimension) : string =
        let ordered =
            let vars =
                d.Vars
                |> Map.toList
                |> List.sortBy (fun (v, _) -> renderVar v, v.Id)
                |> List.map (fun (v, e) -> renderVar v, e)
            let bases =
                d.Bases
                |> Map.toList
                |> List.sortBy (fun (b, _) -> b.Name, b.Module)
                |> List.map (fun (b, e) -> b.Name, e)
            vars @ bases
        let atom (label: string, e: int) =
            if e = 1 then label else label + "^" + string e
        let positives = ordered |> List.filter (fun (_, e) -> e > 0) |> List.map atom
        let negatives = ordered |> List.filter (fun (_, e) -> e < 0) |> List.map (fun (l, e) -> atom (l, -e))
        let numerator =
            match positives with
            | [] -> "1"
            | _ -> String.concat " " positives
        match negatives with
        | [] -> numerator
        | _ -> numerator + " / " + String.concat " " negatives

//-------------------------------------------------------------------------
// Fresh variables
//-------------------------------------------------------------------------

/// The supply of fresh measure variables, a value threaded through the solver and returned with
/// its result. `Next` is the id the next fresh variable receives.
type MeasureSupply = { Next: int }

module MeasureSupply =

    /// A supply whose first fresh variable has id `first`.
    let startingAt (first: int) : MeasureSupply = { Next = first }

    /// Mint one variable, returning it with the advanced supply.
    let fresh (name: string option) (supply: MeasureSupply) : MeasureVar * MeasureSupply =
        { Id = supply.Next; Name = name }, { Next = supply.Next + 1 }

//-------------------------------------------------------------------------
// Unification
//-------------------------------------------------------------------------

/// Why a measure equation has no solution. Each carries the resolved operands or the offending
/// variable and the residual, the unsatisfiable core, for the diagnostic to print through
/// `Dimension.render` (design (b.5): CCS8040 for `Mismatch`, CCS8041 for `NoIntegerSolution`).
type DimFailure =
    /// No variable remains and the residual is not 1: `lhs` and `rhs`, resolved, differ by `residual`.
    | Mismatch of lhs: Dimension * rhs: Dimension * residual: Dimension
    /// One variable `var` with exponent `exponent` remains, and `exponent` does not divide every
    /// exponent of `residual`: no integer solution.
    | NoIntegerSolution of var: MeasureVar * exponent: int * residual: Dimension

/// Floor division (F#'s `/` truncates toward zero; the Euclid step needs the floor).
let private floorDiv (a: int) (b: int) : int =
    let q = a / b
    if a % b <> 0 && ((a < 0) <> (b < 0)) then q - 1 else q

/// Solve one measure equation `d1 = d2` as the residual `e = d1 * d2^-1 = 1` (design (b.2)).
///
/// Pure: the lookup is the caller's store, read only; the supply is threaded in and returned; the
/// result is the list of bindings `(v, d)` the caller makes, each `v` unbound in the lookup and
/// never rebound (I2). The bindings are returned in the order they were decided; the target of an
/// earlier binding may mention a fresh variable a later binding fixes, and `resolve` chases it.
///
/// Steps:
///   1. e <- resolve (mul d1 (inv d2)).
///   2. No variable in e: succeed iff no base in e, else Mismatch(resolve d1, resolve d2, e).
///   3. One variable v with exponent k, residual r = e without v: if k divides every exponent of r,
///      bind v := r^(-1/k); else NoIntegerSolution(v, k, r).
///   4. Several variables: choose v with the smallest |k|, mint a fresh w, bind
///      v := w * prod_{g <> v} g^(-floor(e_g / k)); the new residual has w at exponent k and every
///      other exponent reduced modulo k; recurse on it.
///
/// Termination (Euclid on exponent magnitudes). Let m be the smallest |k| over the variables of the
/// residual and n the number of variables. A step-4 round replaces v by w at the same exponent k and
/// reduces every other exponent g to e_g - k * floor(e_g / k), whose magnitude is strictly below |k|.
/// Either some other variable keeps a non-zero exponent, so the next round's m is strictly smaller
/// than this one's, or every other variable's exponent is now zero and the residual has the single
/// variable w, which step 3 decides. The pair (m, n) therefore decreases in lexicographic order on
/// every recursive call, and m is a positive integer, so the recursion ends. No occurs check is
/// needed (b.3): the eliminated variable v never appears in its own binding, because the residual
/// it came from is replaced by one in which v has been substituted by the fresh w.
let solveDim
    (lookup: MeasureVar -> Dimension option)
    (supply: MeasureSupply)
    (d1: Dimension)
    (d2: Dimension)
    : Result<(MeasureVar * Dimension) list * MeasureSupply, DimFailure> =

    let rec solveResidual
        (supply: MeasureSupply)
        (bindings: (MeasureVar * Dimension) list)
        (e: Dimension)
        : Result<(MeasureVar * Dimension) list * MeasureSupply, DimFailure> =
        match Map.toList e.Vars with
        | [] ->
            // Step 2: ground residual.
            if Map.isEmpty e.Bases then
                Ok(List.rev bindings, supply)
            else
                Error(Mismatch(Dimension.resolve lookup d1, Dimension.resolve lookup d2, e))
        | [ v, k ] ->
            // Step 3: one variable.
            let r = Dimension.mk e.Bases Map.empty
            let divides = r.Bases |> Map.forall (fun _ eg -> eg % k = 0)
            if divides then
                let target = Dimension.mk (Map.map (fun _ eg -> -(eg / k)) r.Bases) Map.empty
                Ok(List.rev ((v, target) :: bindings), supply)
            else
                Error(NoIntegerSolution(v, k, r))
        | vars ->
            // Step 4: several variables; Euclid on the one with the smallest |k|.
            let v, k = vars |> List.minBy (fun (_, k) -> abs k)
            let w, supply' = MeasureSupply.fresh None supply
            let others = Map.remove v e.Vars
            let quotient (eg: int) = -(floorDiv eg k)
            let target =
                Dimension.mk
                    (Map.map (fun _ eg -> quotient eg) e.Bases)
                    (Map.add w 1 (Map.map (fun _ eg -> quotient eg) others))
            // The residual with v replaced by its binding: w at exponent k, the rest reduced modulo k.
            let residual' =
                Dimension.mk
                    (Map.map (fun _ eg -> eg - k * floorDiv eg k) e.Bases)
                    (Map.add w k (Map.map (fun _ eg -> eg - k * floorDiv eg k) others))
            solveResidual supply' ((v, target) :: bindings) residual'

    // Step 1: the residual, resolved through the caller's store.
    let e = Dimension.resolve lookup (Dimension.mul d1 (Dimension.inv d2))
    solveResidual supply [] e

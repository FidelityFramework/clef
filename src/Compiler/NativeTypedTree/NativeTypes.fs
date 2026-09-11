// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Core type representation for the native type checker.
/// These types are used throughout the type checking process and in the output semantic graph.
module Clef.Compiler.NativeTypedTree.NativeTypes

open System.Collections.Generic
open Clef.Compiler.NativeTypedTree.DimensionAlgebra

/// Exact source-real value, independent of the hosted floating-point approximation.
/// Construct through ExactRational.create to reduce the fraction and keep its denominator positive.
type ExactRational = {
    Numerator: bigint
    Denominator: bigint
}

module ExactRational =
    let create (numerator: bigint) (denominator: bigint) : ExactRational =
        if denominator.IsZero then invalidArg "denominator" "A rational denominator cannot be zero."
        let sign = if denominator.Sign < 0 then -bigint.One else bigint.One
        let divisor = System.Numerics.BigInteger.GreatestCommonDivisor(numerator, denominator)
        { Numerator = sign * numerator / divisor
          Denominator = sign * denominator / divisor }

    /// Bounded exact parsing of the source spelling, including exponent and digit separators.
    /// The limit is an implementation limit, not a rounding rule or a source representation choice.
    let tryParseDecimal (source: string) : Result<ExactRational, string> =
        let limit = 4096
        let limitMessage = "This real literal exceeds the current exact-source limit of 4096 characters or decimal scale; shorten the literal or reduce its exponent."
        if source.Length = 0 then Error "A real literal requires a decimal value."
        elif source.Length > limit then Error limitMessage
        else
            let text = source.Replace("_", "")
            let matched = System.Text.RegularExpressions.Regex.Match(text, @"\A([+-]?)([0-9]+)(?:\.([0-9]*))?(?:[eE]([+-]?[0-9]+))?\z")
            if not matched.Success then Error "The source real literal is not a supported decimal value."
            else
                let exponentText = matched.Groups[4].Value
                let exponentOk, exponent =
                    if exponentText = "" then true, 0
                    else System.Int32.TryParse(exponentText, System.Globalization.NumberStyles.AllowLeadingSign, System.Globalization.CultureInfo.InvariantCulture)
                if not exponentOk || exponent < -limit || exponent > limit then Error limitMessage
                else
                    let fractional = matched.Groups[3].Value
                    let scale = fractional.Length - exponent
                    if scale < -limit || scale > limit then Error limitMessage
                    else
                        let coefficient = System.Numerics.BigInteger.Parse(matched.Groups[2].Value + fractional, System.Globalization.CultureInfo.InvariantCulture)
                        let coefficient = if matched.Groups[1].Value = "-" then -coefficient else coefficient
                        if scale >= 0 then Ok (create coefficient (System.Numerics.BigInteger.Pow(bigint 10, scale)))
                        else Ok (create (coefficient * System.Numerics.BigInteger.Pow(bigint 10, -scale)) bigint.One)

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
// Node Identity (PSG)
//-------------------------------------------------------------------------

/// Unique identifier for semantic nodes in the PSG.
/// Moved here from SemanticGraph.fs to break circular dependencies.
[<Struct>]
type NodeId = NodeId of int

module NodeId =
    let mutable private counter = 0

    let fresh () =
        let id = counter
        counter <- counter + 1
        NodeId id

    let reset () = counter <- 0

    let value (NodeId id) = id

//-------------------------------------------------------------------------
// Type Layout (Memory Representation)
//-------------------------------------------------------------------------


//-------------------------------------------------------------------------
// NTU (Native Type Universe) Kind System
// Following F* pattern: type identity is separate from type width.
// Width is a first-class dimension, not baked into discrete variants.
// Width is part of type identity and never erases: CCS resolves a Resolved width against the
// platform description at saturation (see PlatformContext.resolveWidth) and the resolved value
// rides on the PSG as an annotation that Alex reads. (Design: ntu-dimensional-architecture.md §0/§4.3.)
//-------------------------------------------------------------------------

/// Platform-resolved width dimensions — NTU-native vocabulary.
/// These are NOT named after C types. Farscape maps C types to these dimensions;
/// the NTU doesn't know or care about C.
///
/// A width dimension is a name the platform description declares
/// (ntu-dimensional-architecture.md §7.1); these two cases are the spellings the
/// language's own seals (`int`, `nativeint`) name, and `WidthDimension.name` is
/// the one place that spelling meets the declared name. `PlatformContext.Dimensions`
/// is keyed by the declared name, so a fabric binding may declare dimensions the
/// language has no spelling for.
[<RequireQualifiedAccess>]
type WidthDimension =
    /// Address width — the description's `Pointer` declaration
    | Pointer
    /// Machine register / natural computational word width — the description's `Register` declaration
    | Register

module WidthDimension =
    /// The name the platform description declares the dimension under.
    let name (dimension: WidthDimension) : string =
        match dimension with
        | WidthDimension.Pointer -> "Pointer"
        | WidthDimension.Register -> "Register"

/// The representation a numeric seal spelling names (plan D8): the language carries
/// only a name, the platform description declares what that name is on the target.
/// `nativeint` names no fixed representation: it is the signed integer of the Pointer
/// dimension's declared width, `int<bits>` once the dimension resolves.
[<RequireQualifiedAccess>]
type SealRepresentation =
    /// A representation named outright: `int32` -> "int32", `float` -> "float64".
    | Named of string
    /// A representation named through a declared width dimension: the offered
    /// representation of the family ("int" or "uint") at the dimension's declared
    /// width, found by family and bits, never by a synthesised name.
    | OfDimension of family: string * dimension: WidthDimension

/// How the width of a numeric type is determined.
[<RequireQualifiedAccess>]
type NTUWidth =
    /// Known at all times: 8, 16, 32, 64, 128 bits
    | Fixed of bits: int
    /// Platform-dependent, resolved by CCS at saturation via PlatformContext; Alex reads the result
    | Resolved of WidthDimension

/// The analysed range of an integer value (Dimensional_Range_Design.md §1; width-inference.md
/// §2, §3). The range is a coeffect beside the type (§0.1 item 7; Horizon_Requirements.md C3): the
/// width is derived from it on read and is never stored beside it. The forms:
///   `Bounded (lo, hi)`  a finite interval, the one form with a width;
///   `Above lo`, `Below hi`  a half-line: the working form the fixpoint's widening leaves when one
///                       endpoint keeps growing (§1.2), unobservable if it survives the narrowing;
///   `Unbounded`         no bound either way, unobservable (§1.3, CCS8011);
///   `Empty`             the join of no values at all, the least element: a record field no
///                       reachable expression constructs. Its width is the minimum, one bit.
/// The endpoints are exact integers (CS-11): arithmetic on analysed ranges never overflows (§0.1
/// item 6), so a product that leaves 64 bits is a bounded range the coverage check can name
/// (CCS8012, §4.2) rather than an unobservable one, and a declared representation's range (a
/// 64-bit unsigned unit's `[0, 2^64 - 1]`) is representable as declared. A half-line arises only
/// from the widening, never from arithmetic.
/// `Range`, `Width` and `Empty` are not spellings of the language (§0.1 items 1, 5): nothing in a
/// program names a width, and no value of this type is ever written by a program.
[<RequireQualifiedAccess>]
type ValueRange =
    | Empty
    | Bounded of lo: bigint * hi: bigint
    | Above of lo: bigint
    | Below of hi: bigint
    | Unbounded

/// Interval arithmetic and the lattice operations the range pass uses, and the §3 width formula.
/// Every arithmetic rule is over-approximating: the result contains every value the operation can
/// produce from values in the operands. The computation is exact; nothing wraps and nothing
/// saturates.
[<RequireQualifiedAccess>]
module ValueRange =

    /// An endpoint of the working interval: finite, or the infinity a widening leaves.
    /// Ordered NegInf < Finite < PosInf by the case order.
    [<RequireQualifiedAccess>]
    type Endpoint =
        | NegInf
        | Finite of bigint
        | PosInf

    let private zero = Endpoint.Finite bigint.Zero

    /// The endpoints of a non-empty range: `(lo, hi)` with lo in {NegInf, Finite}, hi in {Finite, PosInf}.
    let endpoints (r: ValueRange) : (Endpoint * Endpoint) option =
        match r with
        | ValueRange.Empty -> None
        | ValueRange.Bounded (lo, hi) -> Some (Endpoint.Finite lo, Endpoint.Finite hi)
        | ValueRange.Above lo -> Some (Endpoint.Finite lo, Endpoint.PosInf)
        | ValueRange.Below hi -> Some (Endpoint.NegInf, Endpoint.Finite hi)
        | ValueRange.Unbounded -> Some (Endpoint.NegInf, Endpoint.PosInf)

    /// The range with these endpoints; an inverted pair is the empty range.
    let ofEndpoints (lo: Endpoint) (hi: Endpoint) : ValueRange =
        match lo, hi with
        | Endpoint.Finite a, Endpoint.Finite b -> if a <= b then ValueRange.Bounded (a, b) else ValueRange.Empty
        | Endpoint.Finite a, Endpoint.PosInf -> ValueRange.Above a
        | Endpoint.NegInf, Endpoint.Finite b -> ValueRange.Below b
        | Endpoint.NegInf, Endpoint.PosInf -> ValueRange.Unbounded
        | Endpoint.PosInf, _ | _, Endpoint.NegInf -> ValueRange.Empty

    /// The point range of one value.
    let point (v: bigint) : ValueRange = ValueRange.Bounded (v, v)

    /// The bounded range `[lo, hi]` of two exact values (empty when inverted).
    let bounded (lo: bigint) (hi: bigint) : ValueRange = ofEndpoints (Endpoint.Finite lo) (Endpoint.Finite hi)

    /// The range of a boolean, `[0, 1]` (§1.1).
    let boolean : ValueRange = ValueRange.Bounded (bigint.Zero, bigint.One)

    /// The range of a `char`: a code point, `[0, 0x10FFFF]`.
    let codePoint : ValueRange = ValueRange.Bounded (bigint.Zero, bigint 0x10FFFF)

    /// The two's-complement range of `bits` bits: `[-2^(bits-1), 2^(bits-1) - 1]`.
    let twosComplement (bits: int) : ValueRange =
        let half = bigint.Pow (bigint 2, max 0 (bits - 1))
        ValueRange.Bounded (-half, half - bigint.One)

    /// The unsigned range of `bits` bits: `[0, 2^bits - 1]`.
    let unsignedOf (bits: int) : ValueRange =
        ValueRange.Bounded (bigint.Zero, bigint.Pow (bigint 2, max 0 bits) - bigint.One)

    /// The least upper bound: the smallest interval containing both.
    let join (a: ValueRange) (b: ValueRange) : ValueRange =
        match endpoints a, endpoints b with
        | None, _ -> b
        | _, None -> a
        | Some (alo, ahi), Some (blo, bhi) -> ofEndpoints (min alo blo) (max ahi bhi)

    /// The greatest lower bound: the intersection.
    let meet (a: ValueRange) (b: ValueRange) : ValueRange =
        match endpoints a, endpoints b with
        | None, _ | _, None -> ValueRange.Empty
        | Some (alo, ahi), Some (blo, bhi) -> ofEndpoints (max alo blo) (min ahi bhi)

    /// Whether `inner` is contained in `outer` (containment is the check of every range claim, C5).
    let contains (outer: ValueRange) (inner: ValueRange) : bool =
        match endpoints inner, endpoints outer with
        | None, _ -> true
        | Some _, None -> false
        | Some (ilo, ihi), Some (olo, ohi) -> olo <= ilo && ihi <= ohi

    /// Whether every value of the range is non-negative: the range spends no sign bit (§3).
    /// Vacuously true of the empty range.
    let isNonNegative (r: ValueRange) : bool =
        match r with
        | ValueRange.Empty -> true
        | ValueRange.Bounded (lo, _) | ValueRange.Above lo -> lo.Sign >= 0
        | ValueRange.Below _ | ValueRange.Unbounded -> false

    /// Whether the range has a width: finite at both ends, or empty.
    let isObservable (r: ValueRange) : bool =
        match r with
        | ValueRange.Empty | ValueRange.Bounded _ -> true
        | ValueRange.Above _ | ValueRange.Below _ | ValueRange.Unbounded -> false

    /// ceil(log2 m) for m >= 1: the number of bits of m - 1.
    let private ceilLog2 (m: bigint) : int =
        let rec bits (v: bigint) (n: int) = if v.IsZero then n else bits (v >>> 1) (n + 1)
        if m <= bigint.One then 0 else bits (m - bigint.One) 0

    /// The width of a range, width-inference.md §3:
    ///   a >= 0:  ceil(log2(b + 1))                      (unsigned: no sign bit)
    ///   a <  0:  1 + ceil(log2(max(|a|, b + 1)))        (two's complement)
    /// with a minimum of one bit (a wire exists), which is also the width of the empty range.
    /// A half-line and the unbounded range have no width.
    let width (r: ValueRange) : int option =
        match r with
        | ValueRange.Empty -> Some 1
        | ValueRange.Bounded (lo, hi) when lo.Sign >= 0 ->
            Some (max 1 (ceilLog2 (hi + bigint.One)))
        | ValueRange.Bounded (lo, hi) ->
            let magnitude = max (bigint.Abs lo) (hi + bigint.One)
            Some (max 1 (1 + ceilLog2 magnitude))
        | ValueRange.Above _ | ValueRange.Below _ | ValueRange.Unbounded -> None

    /// The range as text: `[lo, hi]`, `[lo, +inf)`, `(-inf, hi]`, `(-inf, +inf)`, `[]`.
    let render (r: ValueRange) : string =
        match r with
        | ValueRange.Empty -> "[]"
        | ValueRange.Bounded (lo, hi) -> sprintf "[%s, %s]" (lo.ToString()) (hi.ToString())
        | ValueRange.Above lo -> sprintf "[%s, +inf)" (lo.ToString())
        | ValueRange.Below hi -> sprintf "(-inf, %s]" (hi.ToString())
        | ValueRange.Unbounded -> "(-inf, +inf)"

    //---------------------------------------------------------------------
    // Interval arithmetic
    //---------------------------------------------------------------------

    /// Endpoint sum: an infinity absorbs; a finite sum is exact.
    let private addE (a: Endpoint) (b: Endpoint) : Endpoint =
        match a, b with
        | Endpoint.Finite x, Endpoint.Finite y -> Endpoint.Finite (x + y)
        | Endpoint.NegInf, _ | _, Endpoint.NegInf -> Endpoint.NegInf
        | Endpoint.PosInf, _ | _, Endpoint.PosInf -> Endpoint.PosInf

    let private negE (a: Endpoint) : Endpoint =
        match a with
        | Endpoint.Finite x -> Endpoint.Finite (-x)
        | Endpoint.NegInf -> Endpoint.PosInf
        | Endpoint.PosInf -> Endpoint.NegInf

    let private signE (a: Endpoint) : int =
        match a with
        | Endpoint.Finite x -> x.Sign
        | Endpoint.NegInf -> -1
        | Endpoint.PosInf -> 1

    /// Endpoint product with the interval-arithmetic reading of 0 * infinity = 0.
    let private mulE (a: Endpoint) (b: Endpoint) : Endpoint =
        match a, b with
        | Endpoint.Finite x, Endpoint.Finite y -> Endpoint.Finite (x * y)
        | _ ->
            match signE a * signE b with
            | 0 -> zero
            | s when s > 0 -> Endpoint.PosInf
            | _ -> Endpoint.NegInf

    /// Truncating endpoint quotient (F# `/`): a finite over an infinity tends to zero, an infinity
    /// over a finite keeps its sign; two infinities have no quotient (None).
    let private divE (a: Endpoint) (b: Endpoint) : Endpoint option =
        match a, b with
        | Endpoint.Finite x, Endpoint.Finite y -> Some (Endpoint.Finite (bigint.Divide (x, y)))   // y <> 0 by the caller
        | Endpoint.Finite _, _ -> Some zero
        | _, Endpoint.Finite _ -> Some (if signE a * signE b > 0 then Endpoint.PosInf else Endpoint.NegInf)
        | _ -> None

    /// Apply a binary rule to two ranges: an empty operand gives the empty result.
    let private lift2 (f: Endpoint * Endpoint -> Endpoint * Endpoint -> ValueRange) (a: ValueRange) (b: ValueRange) : ValueRange =
        match endpoints a, endpoints b with
        | Some ea, Some eb -> f ea eb
        | _ -> ValueRange.Empty

    /// `[alo + blo, ahi + bhi]`.
    let add : ValueRange -> ValueRange -> ValueRange =
        lift2 (fun (alo, ahi) (blo, bhi) -> ofEndpoints (addE alo blo) (addE ahi bhi))

    /// `[alo - bhi, ahi - blo]`.
    let sub : ValueRange -> ValueRange -> ValueRange =
        lift2 (fun (alo, ahi) (blo, bhi) -> ofEndpoints (addE alo (negE bhi)) (addE ahi (negE blo)))

    /// `[-hi, -lo]`.
    let neg (a: ValueRange) : ValueRange =
        match endpoints a with
        | Some (lo, hi) -> ofEndpoints (negE hi) (negE lo)
        | None -> ValueRange.Empty

    /// The four corner products.
    let mul : ValueRange -> ValueRange -> ValueRange =
        lift2 (fun (alo, ahi) (blo, bhi) ->
            let corners = [ mulE alo blo; mulE alo bhi; mulE ahi blo; mulE ahi bhi ]
            ofEndpoints (List.min corners) (List.max corners))

    /// Truncating division. A divisor whose range contains zero has no image (Unbounded); otherwise
    /// the four corner quotients.
    let div : ValueRange -> ValueRange -> ValueRange =
        lift2 (fun (alo, ahi) (blo, bhi) ->
            let containsZero = blo <= zero && zero <= bhi
            if containsZero then ValueRange.Unbounded
            else
                let corners = [ divE alo blo; divE alo bhi; divE ahi blo; divE ahi bhi ]
                if corners |> List.forall Option.isSome then
                    let cs = corners |> List.choose id
                    ofEndpoints (List.min cs) (List.max cs)
                else ValueRange.Unbounded)

    /// `x % k`, the sign following the dividend (F# semantics): with `|k|` in `[1, m]`, a non-negative
    /// `x` gives `[0, min(x.hi, m - 1)]` and any other `x` gives `[-(m - 1), m - 1]` clipped to `|x|`;
    /// a divisor whose range contains zero has no image.
    let rem : ValueRange -> ValueRange -> ValueRange =
        lift2 (fun (xlo, xhi) (klo, khi) ->
            let containsZero = klo <= zero && zero <= khi
            if containsZero then ValueRange.Unbounded
            else
                // the largest |k| less one: the bound on |x % k|
                let magnitude = max (negE klo) khi   // |k| <= max(-klo, khi); one of them is the magnitude
                let bound = addE magnitude (Endpoint.Finite bigint.MinusOne)
                let clip (e: Endpoint) = min bound e
                if xlo >= zero then ofEndpoints zero (clip xhi)
                elif xhi <= zero then ofEndpoints (negE (clip (negE xlo))) zero
                else ofEndpoints (negE (clip (negE xlo))) (clip xhi))

    /// The largest shift amount the arithmetic follows exactly. A shift past it is a value no
    /// declared representation holds and no program means (a `<<< 5000`), read as the half-line
    /// by the sign of the operand rather than computed.
    let private shiftLimit = bigint 4096

    /// `x <<< n` as `x * 2^n` for a non-negative bounded amount; any other amount has no image.
    let shl (x: ValueRange) (n: ValueRange) : ValueRange =
        match n with
        | ValueRange.Bounded (nlo, nhi) when nlo.Sign >= 0 && nhi <= shiftLimit ->
            let pow2 (k: bigint) = Endpoint.Finite (bigint.Pow (bigint 2, int k))
            mul x (ofEndpoints (pow2 nlo) (pow2 nhi))
        | ValueRange.Bounded (nlo, _) when nlo.Sign >= 0 ->
            // Past the limit: the half-line by the sign of x, never an empty range (an empty
            // range is observable and one bit wide, which would be a silent wrong width).
            if x = ValueRange.Empty then ValueRange.Empty
            elif isNonNegative x then ValueRange.Above bigint.Zero
            else ValueRange.Unbounded
        | ValueRange.Empty -> ValueRange.Empty
        | _ -> if x = ValueRange.Empty then ValueRange.Empty else ValueRange.Unbounded

    /// `x >>> n` (arithmetic on a signed value) for a non-negative bounded amount: the extreme
    /// shifts of each endpoint; an infinite endpoint stays infinite.
    let shr (x: ValueRange) (n: ValueRange) : ValueRange =
        let shiftE (e: Endpoint) (k: bigint) : Endpoint =
            match e with
            | Endpoint.Finite v -> Endpoint.Finite (v >>> int (min k shiftLimit))
            | _ -> e
        match endpoints x, n with
        | None, _ -> ValueRange.Empty
        | Some (lo, hi), ValueRange.Bounded (nlo, nhi) when nlo.Sign >= 0 ->
            ofEndpoints (min (shiftE lo nlo) (shiftE lo nhi)) (max (shiftE hi nlo) (shiftE hi nhi))
        | Some _, ValueRange.Empty -> ValueRange.Empty
        | Some _, _ -> ValueRange.Unbounded

    /// The smallest 2^k - 1 at or above every value of a non-negative range: the bound of `|||` and `^^^`.
    let private maskAbove (hi: Endpoint) : Endpoint =
        match hi with
        | Endpoint.Finite v -> Endpoint.Finite (bigint.Pow (bigint 2, ceilLog2 (v + bigint.One)) - bigint.One)
        | _ -> Endpoint.PosInf

    /// `x &&& m`: with a non-negative mask the result is `[0, m.hi]` for any `x` (the mask clears
    /// the sign), and no larger than a non-negative `x`; a mask that may be negative has no image.
    let band (x: ValueRange) (m: ValueRange) : ValueRange =
        match endpoints x, endpoints m with
        | None, _ | _, None -> ValueRange.Empty
        | Some (xlo, xhi), Some (mlo, mhi) when mlo >= zero ->
            let hi = if xlo >= zero then min xhi mhi else mhi
            ofEndpoints zero hi
        | Some (xlo, xhi), Some _ when xlo >= zero ->
            // a non-negative x masked by anything is in [0, x]
            ofEndpoints zero xhi
        | _ -> ValueRange.Unbounded

    /// `x ||| y` and `x ^^^ y`: for two non-negative ranges, `[0, 2^k - 1]` where `2^k` is the
    /// first power of two above both; otherwise no image.
    let bor (x: ValueRange) (y: ValueRange) : ValueRange =
        match endpoints x, endpoints y with
        | None, _ | _, None -> ValueRange.Empty
        | Some (xlo, xhi), Some (ylo, yhi) when xlo >= zero && ylo >= zero ->
            ofEndpoints zero (maskAbove (max xhi yhi))
        | _ -> ValueRange.Unbounded

    /// `~~~x` is `-x - 1`.
    let bnot (x: ValueRange) : ValueRange = sub (neg x) (point bigint.One)

    /// The non-negative image of a range: `|x|` (§1.1: `abs x` is non-negative).
    let abs (x: ValueRange) : ValueRange =
        match endpoints x with
        | None -> ValueRange.Empty
        | Some (lo, hi) ->
            if lo >= zero then x
            elif hi <= zero then neg x
            else ofEndpoints zero (max (negE lo) hi)

    /// `min x y`: `[min lo, min hi]`.
    let minOf : ValueRange -> ValueRange -> ValueRange =
        lift2 (fun (xlo, xhi) (ylo, yhi) -> ofEndpoints (min xlo ylo) (min xhi yhi))

    /// `max x y`: `[max lo, max hi]`.
    let maxOf : ValueRange -> ValueRange -> ValueRange =
        lift2 (fun (xlo, xhi) (ylo, yhi) -> ofEndpoints (max xlo ylo) (max xhi yhi))

    //---------------------------------------------------------------------
    // Widening (§1.2; numeric-selection.md §9.1: the thresholds are the declared representations'
    // boundaries; on a substrate that declares none, the endpoint goes to its infinity)
    //---------------------------------------------------------------------

    /// One declared integer representation's range, a widening threshold.
    type Threshold = { Family: string; Lo: bigint; Hi: bigint }

    /// `old` widened by `grown`: an endpoint that moved goes to the nearest threshold beyond it,
    /// and past the last threshold to its infinity; an endpoint that did not move is kept. The
    /// thresholds are the boundaries of the declared representations of the family the range's
    /// sign selects (`uint` for a non-negative range when the platform declares one, else `int`)
    /// and, for either family, the program's settled constants: `c - 1` and `c` above, `c` and
    /// `c + 1` below, for every constant `c` the analysis has found so far. The constants are what
    /// let a free-running counter stop at its modulus (`x % k` is `[0, k - 1]`, width-inference.md
    /// §2: "a free-running counter mod N has range [0, N-1]") when nothing but the modulus bounds
    /// it, since a cycle that carries its own value forward (`if hold then x else (x + 1) % k`)
    /// keeps whatever the widening overshoots to. Per endpoint, so a counter whose ceiling is a
    /// comparison keeps its floor, and the narrowing recovers the ceiling from the comparison.
    let widen (thresholds: Threshold list) (constants: bigint list) (old: ValueRange) (grown: ValueRange) : ValueRange =
        match endpoints old, endpoints grown with
        | _, None -> old
        | None, _ -> grown
        | Some (olo, ohi), Some (glo, ghi) ->
            let family =
                if glo >= zero && thresholds |> List.exists (fun t -> t.Family = "uint") then "uint" else "int"
            let declared = thresholds |> List.filter (fun t -> t.Family = family)
            let hi =
                if ghi <= ohi then ohi
                else
                    match ghi with
                    | Endpoint.Finite g ->
                        let above =
                            (declared |> List.map (fun t -> t.Hi))
                            @ (constants |> List.collect (fun c -> [ c - bigint.One; c ]))
                            |> List.filter (fun v -> v >= g)
                        if List.isEmpty above then Endpoint.PosInf else Endpoint.Finite (List.min above)
                    | _ -> Endpoint.PosInf
            let lo =
                if glo >= olo then olo
                else
                    match glo with
                    | Endpoint.Finite g ->
                        let below =
                            (declared |> List.map (fun t -> t.Lo))
                            @ (constants |> List.collect (fun c -> [ c; c + bigint.One ]))
                            |> List.filter (fun v -> v <= g)
                        if List.isEmpty below then Endpoint.NegInf else Endpoint.Finite (List.max below)
                    | _ -> Endpoint.NegInf
            ofEndpoints lo hi

/// NTU (Native Type Universe) type kinds.
/// Numeric types are parameterized by width — 3 kinds replace 16 discrete variants.
/// Type identity: NTUint(Fixed 32) ≠ NTUint(Resolved Register) even if same width on LP64.
[<RequireQualifiedAccess>]
type NTUKind =
    //-----------------------------------------------------------------------
    // Parameterized numeric types (width as dimension)
    //-----------------------------------------------------------------------

    /// Signed integer of any width
    /// Fixed 8/16/32/64 or Resolved Register/Pointer
    | NTUint of NTUWidth

    /// Unsigned integer of any width
    /// Fixed 8/16/32/64 or Resolved Register/Pointer
    | NTUuint of NTUWidth

    /// IEEE floating point of any width
    /// Fixed 32 or Fixed 64 (extensible to Fixed 128 for long double)
    | NTUfloat of NTUWidth

    //-----------------------------------------------------------------------
    // Pointer types (width = Pointer, implicit)
    //-----------------------------------------------------------------------

    /// Native pointer type (pointer-sized)
    | NTUptr

    /// Function pointer type (pointer-sized)
    /// Used for callbacks to top-level functions (no closures)
    | NTUfnptr

    /// Size type (unsigned, pointer-width) — array lengths, memory sizes
    | NTUsize

    /// Pointer difference type (signed, pointer-width)
    | NTUdiff

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

    /// Sequence/generator (resumable computation producing values on demand)
    /// PRD-15: Simple Sequence Expressions
    | NTUseq

    //-----------------------------------------------------------------------
    // Collection types (PRD-13a: Core Collections)
    //-----------------------------------------------------------------------

    /// Mutable contiguous array (fat pointer: ptr + length)
    /// C-04: Type constructor arity = 1
    | NTUarray

    /// Bounded foreign storage, valid only during its declared mapping scope.
    /// The nominal schema selects its physical elements; it is not an array.
    | NTUborrowedview

    /// Immutable singly-linked list
    /// PRD-13a: Core Collections
    | NTUlist

    /// Immutable key-value map (balanced BST)
    /// PRD-13a: Core Collections
    | NTUmap

    /// Immutable set (balanced BST)
    /// PRD-13a: Core Collections
    | NTUset

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

    //-----------------------------------------------------------------------
    // Posit numeric types (Gustafson Type III Unum)
    //-----------------------------------------------------------------------

    /// Posit number: tapered-precision floating point.
    /// Width determines storage size (8/16/32/64 bits).
    /// es = exponent field size (0-3), determines dynamic range vs precision tradeoff.
    /// Type identity: NTUposit(Fixed 32, 2) ≠ NTUfloat(Fixed 32) — different numeric semantics.
    /// CPU: software decode/encode or AVX-512 vectorized.
    /// FPGA: dedicated hardware pipeline via CIRCT (PACoGen-style).
    | NTUposit of NTUWidth * es: int

//-------------------------------------------------------------------------
// NTU Dimensional Qualifiers (Multi-Substrate Compilation)
//-------------------------------------------------------------------------

/// Memory space qualifier for substrate-aware type placement.
/// These do NOT affect type identity — `int @Global` and `int @Shared`
/// are the same NTU type with different placement. Qualifiers inform
/// code generation and BAREWire inter-substrate transfer strategy.
[<RequireQualifiedAccess>]
type NTUMemorySpace =
    /// Substrate chooses (escape analysis on CPU, compiler on GPU)
    | Default
    /// Function-local (universal concept across substrates)
    | Stack
    /// Main memory / VRAM / HBM
    | Global
    /// Explicitly managed cache (GPU shared mem, NPU tile mem)
    | Shared
    /// Per-thread/per-PE (GPU registers, NPU private mem)
    | Private
    /// HSA unified (CPU↔GPU↔NPU on Strix Halo — zero-copy)
    | Coherent
    /// Cross-device (FPGA BRAM from CPU perspective)
    | External
    /// MMIO (volatile access from BAREWire patterns)
    | Peripheral

/// Access pattern qualifier for cache-aware compilation.
/// Informs cache bypass strategy on CPU, coalescing on GPU,
/// and AXI stream vs memory-mapped on FPGA.
[<RequireQualifiedAccess>]
type NTUAccessPattern =
    /// Regular read/write
    | Normal
    /// Sequential, don't cache (non-temporal on CPU, coalesced on GPU)
    | Streaming
    /// MMIO / peripheral
    | Volatile
    /// Immutable view (enables sharing without coherency cost)
    | ReadOnly
    /// Producer-only (enables GPU write-combine)
    | WriteOnly

/// Bundle of placement qualifiers for substrate-aware compilation.
/// Attached to TypeLayout, not type identity.
type NTUQualifiers = {
    MemorySpace: NTUMemorySpace option
    AccessPattern: NTUAccessPattern option
}

/// NTUQualifiers helpers
module NTUQualifiers =
    /// Empty qualifiers (no explicit placement)
    let empty = { MemorySpace = None; AccessPattern = None }

    /// Create qualifiers with only a memory space
    let withMemorySpace space = { MemorySpace = Some space; AccessPattern = None }

    /// Create qualifiers with only an access pattern
    let withAccessPattern pattern = { MemorySpace = None; AccessPattern = Some pattern }

/// Legacy capability identifiers. The context map currently has no general
/// resolver/consumer. ClefPredicate device-access conditions use the separate
/// Predicates/DeviceAccess path and retain their evidence in graph codata.
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

//-------------------------------------------------------------------------
// Freestanding Startup Data (Platform Entry Point)
//-------------------------------------------------------------------------

/// Freestanding startup configuration for platforms without libc.
/// This is DATA only - contains offsets, syscall numbers, register names.
/// Baker provides the BEHAVIOR through ingredients and recipes.
///
/// Platform bindings flow: Fidelity.Platform → PlatformContext → RecipeContext → Baker
[<NoComparison; NoEquality>]
type FreestandingStartup = {
    /// Entry point symbol name (typically "_start" for freestanding)
    EntrySymbol: string

    /// Main function name (what _start calls)
    MainFunction: string

    /// Offset from stack pointer to argc on entry (bytes)
    /// Linux x86_64: argc is at [rsp]
    ArgcOffset: int

    /// Offset from stack pointer to argv pointer array (bytes)
    /// Linux x86_64: argv is at [rsp + 8]
    ArgvOffset: int

    /// Exit syscall number
    /// Linux x86_64: 60 (sys_exit)
    ExitSyscall: int

    /// Register for syscall number
    /// Linux x86_64: "rax"
    SyscallRegister: string

    /// Register for first syscall argument (exit code)
    /// Linux x86_64: "rdi"
    Arg0Register: string
}

module FreestandingStartup =
    /// Default freestanding startup for Linux x86_64
    let defaultLinux_x86_64 = {
        EntrySymbol = "_start"
        MainFunction = "main"
        ArgcOffset = 0      // argc at [rsp]
        ArgvOffset = 8      // argv at [rsp + 8]
        ExitSyscall = 60    // sys_exit
        SyscallRegister = "rax"
        Arg0Register = "rdi"
    }

    /// Look up freestanding startup config for a platform
    let forPlatform (platformId: string) : FreestandingStartup option =
        match platformId with
        | "Linux_x86_64" -> Some defaultLinux_x86_64
        | "Linux_aarch64" ->
            Some {
                EntrySymbol = "_start"
                MainFunction = "main"
                ArgcOffset = 0
                ArgvOffset = 8
                ExitSyscall = 93    // sys_exit on aarch64
                SyscallRegister = "x8"
                Arg0Register = "x0"
            }
        | _ -> None

//-------------------------------------------------------------------------
// Substrate and Platform Context (NTU Resolution)
//-------------------------------------------------------------------------

/// One numeric representation the platform description declares (plan D8; the
/// `Representation` record of BAREWire's `Platform/Description.fs` and of the
/// Contracts twin, read structurally at saturation). Every tag is the declared
/// string; the range bounds are exact decimal text.
type NumericRepresentation = {
    Name: string
    /// "native" | "emulated" | "unavailable"
    Capability: string
    /// "int" | "uint" | "ieee" | "posit" | "fixed"
    Family: string
    Bits: int
    MinMagnitude: string
    MaxMagnitude: string
    /// "wrap" | "saturate" | "exact"
    Boundary: string
}

/// The closed vocabularies a declared representation may use, and what "offered"
/// means: the three sets BAREWire's `Platform/Tags.fs` and the Contracts twin fix.
/// A tag outside its set is a defect of the declaration (CCS8207), never an
/// offered representation.
module NumericRepresentation =
    let capabilities = [ "native"; "emulated"; "unavailable" ]
    let families = [ "int"; "uint"; "ieee"; "posit"; "fixed" ]
    let boundaries = [ "wrap"; "saturate"; "exact" ]

    /// A representation the platform offers: native or emulated. `unavailable` is
    /// declared so that the name is known and refused, not silently absent.
    let isOffered (r: NumericRepresentation) : bool =
        r.Capability = "native" || r.Capability = "emulated"

    /// Every way the declaration is outside its vocabulary; empty when it is sound.
    let problems (r: NumericRepresentation) : string list =
        [ if not (List.contains r.Capability capabilities) then
              yield sprintf "capability '%s' is not one of native, emulated, unavailable" r.Capability
          if not (List.contains r.Family families) then
              yield sprintf "family '%s' is not one of int, uint, ieee, posit, fixed" r.Family
          if not (List.contains r.Boundary boundaries) then
              yield sprintf "boundary '%s' is not one of wrap, saturate, exact" r.Boundary
          if r.Bits <= 0 then
              yield sprintf "declares %d bits; a representation has a positive number of bits" r.Bits
          if r.MinMagnitude = "" || r.MaxMagnitude = "" then
              yield "declares no dynamic range; MinMagnitude and MaxMagnitude are exact decimal text" ]

/// Runtime model — what execution environment services are available.
/// This is a capability coeffect: what the computation requires from
/// its environment. Comes from the platform binding's [platform] section.
/// See DTS+DMM paper Section 3.1.
[<RequireQualifiedAccess>]
type RuntimeModel =
    /// C library available (CPU console apps)
    | Libc
    /// Direct syscalls only, no libc (CPU standalone)
    | Freestanding
    /// No OS, hardware target (FPGA, MCU)
    | Bare
    /// AMD GPU runtime
    | ROCm
    /// AMD NPU runtime
    | XDNA

/// Compute substrate kind for multi-substrate compilation.
/// Each fidproj targets a single substrate; the fidsln orchestrates across them.
[<RequireQualifiedAccess>]
type SubstrateKind =
    /// CPU target (Zen 5, ARM, RISC-V) → MLIR → LLVM → native
    | CPU
    /// GPU target (RDNA 3.5, etc.) → MLIR → GPU/AMDGPU → ROCm
    | GPU
    /// NPU target (XDNA 2, etc.) → MLIR → MLIR-AIE → AI Engine runtime
    | NPU
    /// FPGA target (Xilinx, etc.) → MLIR → CIRCT → handshake → hw/comb/seq → SV
    | FPGA

/// The declared return bound of a platform endpoint (Dimensional_Range_Design.md,
/// ruling 2 of CS-12; BAREWire docs/11): the least value the return takes (`Floor`,
/// the errno floor on Linux) and the name of the parameter the return is at most
/// (`AtMost`, `"count"` for read and write). Read from the description's Contract
/// (`Floor`, `AtMost`) by PlatformResolution; the compiler holds no such number.
type ReturnBound = {
    Floor: bigint
    AtMost: string
}

/// Platform context for NTU type resolution.
/// Carries quotation-resolved platform information used to
/// resolve platform-dependent types (NTUint, NTUptr, etc.) to concrete widths.
/// Extended with substrate-awareness for multi-target compilation.
[<NoComparison; NoEquality>]
type PlatformContext = {
    /// Platform identifier (e.g., "Linux_x86_64", "Windows_ARM64")
    PlatformId: string

    /// The width dimensions the platform description declares, by declared name
    /// (ntu-dimensional-architecture.md §7.1): `Pointer` -> 64, `Register` -> 64 on
    /// x86_64. Filled once, at the saturation entry, from the description compiled
    /// into the graph (PlatformDeclaration.fill); empty until then and empty when
    /// the description declares no core. A dimension absent here is CCS8203 at the
    /// site that needs it, never a default.
    Dimensions: Map<string, int>

    /// The numeric representations the platform description offers, by name
    /// (plan D8). Filled with `Dimensions`. A sealed value whose representation is
    /// absent here, or declared unavailable, is CCS8204 at its site.
    Representations: Map<string, NumericRepresentation>

    /// The return bounds the platform description's endpoint contracts declare,
    /// by endpoint name (`read`, `write`). Filled with `Dimensions`. An endpoint
    /// absent here has an unobservable result (CCS8011), never a number.
    EndpointReturns: Map<string, ReturnBound>

    /// Path to the Fidelity.Platform library
    PlatformLibraryPath: string option

    /// Explicit description export from the selected platform manifest. When
    /// absent, legacy platform selection uses the binding directory.
    PlatformDescription: string option

    /// Normalized source identities in the selected platform's dependency
    /// closure. An application's other declarations cannot supply its exports.
    PlatformSourcePaths: Set<string>

    /// Selected manifest claims, checked against an explicit description's core.
    PlatformArchitecture: string option
    PlatformOS: string option

    /// Legacy capability map, currently initialized empty. This is not the
    /// evidence carrier for ClefPredicate or MMIO access settlement.
    Predicates: Map<PlatformPredicate, bool>

    /// Freestanding startup configuration (populated for freestanding builds)
    FreestandingStartup: FreestandingStartup option

    /// Substrate kind (None = CPU for backward compat with single-substrate builds)
    SubstrateKind: SubstrateKind option

    /// Runtime model from platform binding — capability coeffect.
    /// What execution environment services are available.
    RuntimeModel: RuntimeModel option

    /// Memory spaces available on this substrate.
    /// Empty = all spaces available (for backward compat).
    AvailableMemorySpaces: NTUMemorySpace list

    /// Default memory space for allocation on this substrate.
    /// None = substrate default (Stack/heap via escape analysis on CPU, Global on GPU, etc.)
    DefaultMemorySpace: NTUMemorySpace option

    /// Clock frequency in MHz from platform binding (FPGA/MCU).
    /// Used to compute combinational depth threshold.
    ClockFrequencyMhz: int option

    /// Fabric-specific ns per weighted depth unit (from binding, calibrated against Vivado).
    /// threshold = floor(clock_period_ns / ns_per_weight_unit)
    NsPerWeightUnit: float option
}

/// SubstrateContext is PlatformContext with substrate-aware fields populated.
/// Type alias for documentation and gradual migration — not a separate type.
type SubstrateContext = PlatformContext

/// Why a seal has no representation on this platform: the two messages the site
/// reports, CCS8203's or CCS8204's.
[<RequireQualifiedAccess>]
type SealFailure =
    /// The dimension the seal names is not declared; carries CCS8203's text.
    | UndeclaredWidth of message: string
    /// The representation is not offered; carries CCS8204's text.
    | NotOffered of message: string

/// Platform context operations for NTU type resolution. Every width read goes
/// through `tryWidth`: the declaration is the one source, and the `Error` case
/// carries the text of CCS8203 for the site that needed the width to report
/// (plan L-13, D8). There is no default context and no platform-word fallback.
module PlatformContext =
    /// The message of CCS8203: the description declares no such dimension.
    let undeclaredWidthMessage (ctx: PlatformContext) (name: string) : string =
        sprintf "The platform description of '%s' declares no width dimension '%s'" ctx.PlatformId name

    /// The message of CCS8204: the description does not offer the representation.
    let unofferedRepresentationMessage (ctx: PlatformContext) (name: string) : string =
        sprintf "The platform description of '%s' does not offer the representation '%s'" ctx.PlatformId name

    /// The declared width of the named dimension, in bits; `Error` is CCS8203's text.
    let tryWidth (ctx: PlatformContext) (name: string) : Result<int, string> =
        match Map.tryFind name ctx.Dimensions with
        | Some bits -> Ok bits
        | None -> Error (undeclaredWidthMessage ctx name)

    /// Resolve an NTUWidth to bits: a fixed width is its own, a resolved one is read
    /// from the declaration under the dimension's declared name.
    let resolveWidth (ctx: PlatformContext) (width: NTUWidth) : Result<int, string> =
        match width with
        | NTUWidth.Fixed bits -> Ok bits
        | NTUWidth.Resolved dim -> tryWidth ctx (WidthDimension.name dim)

    /// The representation the description offers under this name: declared, and
    /// native or emulated. `Error` is CCS8204's text.
    let tryRepresentation (ctx: PlatformContext) (name: string) : Result<NumericRepresentation, string> =
        match Map.tryFind name ctx.Representations with
        | Some r when NumericRepresentation.isOffered r -> Ok r
        | _ -> Error (unofferedRepresentationMessage ctx name)

    /// The representation a seal resolves to on this platform. A named seal is
    /// looked up by its name. One named through a dimension (`int`, `nativeint`) is
    /// the offered representation of that family at the dimension's declared width,
    /// whatever the description calls it: no name is synthesised, so a description
    /// is free in how it names its representations.
    let tryRepresentationOfSeal (ctx: PlatformContext) (seal: SealRepresentation) : Result<NumericRepresentation, SealFailure> =
        match seal with
        | SealRepresentation.Named name ->
            tryRepresentation ctx name |> Result.mapError SealFailure.NotOffered
        | SealRepresentation.OfDimension (family, dim) ->
            match tryWidth ctx (WidthDimension.name dim) with
            | Error message -> Error (SealFailure.UndeclaredWidth message)
            | Ok bits ->
                let offered =
                    ctx.Representations
                    |> Map.toList
                    |> List.tryPick (fun (_, r) ->
                        if r.Family = family && r.Bits = bits && NumericRepresentation.isOffered r then Some r else None)
                match offered with
                | Some r -> Ok r
                | None ->
                    let wanted = sprintf "%s at the declared %s width of %d bits" family (WidthDimension.name dim) bits
                    Error (SealFailure.NotOffered (unofferedRepresentationMessage ctx wanted))

    /// Pointer size in bytes, from the declared Pointer width.
    let pointerSize (ctx: PlatformContext) : Result<int, string> =
        tryWidth ctx (WidthDimension.name WidthDimension.Pointer) |> Result.map (fun bits -> bits / 8)

    /// Word size in bits, from the declared Register width.
    let wordSize (ctx: PlatformContext) : Result<int, string> =
        tryWidth ctx (WidthDimension.name WidthDimension.Register)

    /// Resolve the byte size for an NTU kind on this platform
    let resolveSize (ctx: PlatformContext) (kind: NTUKind) : Result<int, string> =
        match kind with
        // Parameterized numeric types — resolve width dimension
        | NTUKind.NTUint w | NTUKind.NTUuint w | NTUKind.NTUfloat w
        | NTUKind.NTUposit (w, _) ->
            resolveWidth ctx w |> Result.map (fun bits -> bits / 8)
        // Pointer types — pointer-sized
        | NTUKind.NTUptr | NTUKind.NTUfnptr | NTUKind.NTUsize | NTUKind.NTUdiff ->
            pointerSize ctx
        // Special types
        | NTUKind.NTUstring -> Ok 16  // Fat pointer: ptr + length
        | NTUKind.NTUbool -> Ok 1
        | NTUKind.NTUchar -> Ok 4  // UTF-32
        | NTUKind.NTUunit -> Ok 0
        | NTUKind.NTUdecimal -> Ok 16
        // Temporal and identity types
        | NTUKind.NTUuuid -> Ok 16  // 128-bit UUID
        | NTUKind.NTUdatetime -> Ok 8  // 64-bit ticks
        | NTUKind.NTUtimespan -> Ok 8  // 64-bit duration
        | NTUKind.NTUlazy -> Ok -1  // Size depends on element type (PRD-14)
        | NTUKind.NTUseq -> Ok -1  // Size depends on element type (PRD-15)
        | NTUKind.NTUarray -> Ok 16  // Fat pointer: ptr + length (C-04)
        | NTUKind.NTUborrowedview -> pointerSize ctx |> Result.map (fun bytes -> 5 * bytes)
        | NTUKind.NTUlist -> pointerSize ctx  // Pointer to cons cell (PRD-13a)
        | NTUKind.NTUmap -> pointerSize ctx  // Pointer to tree root (PRD-13a)
        | NTUKind.NTUset -> pointerSize ctx  // Pointer to tree root (PRD-13a)

    /// Resolve the alignment for an NTU kind on this platform: a pointer aligns to
    /// the declared Pointer width, a numeric to its own.
    let resolveAlign (ctx: PlatformContext) (kind: NTUKind) : Result<int, string> =
        match kind with
        // Parameterized numeric types — align to width
        | NTUKind.NTUint w | NTUKind.NTUuint w | NTUKind.NTUfloat w
        | NTUKind.NTUposit (w, _) ->
            resolveWidth ctx w |> Result.map (fun bits -> bits / 8)
        // Pointer types — pointer alignment
        | NTUKind.NTUptr | NTUKind.NTUfnptr | NTUKind.NTUsize | NTUKind.NTUdiff ->
            pointerSize ctx
        // Special types
        | NTUKind.NTUstring -> Ok 8  // Pointer alignment for fat pointer
        | NTUKind.NTUbool -> Ok 1
        | NTUKind.NTUchar -> Ok 4
        | NTUKind.NTUunit -> Ok 1
        | NTUKind.NTUdecimal -> Ok 8
        // Temporal and identity types
        | NTUKind.NTUuuid -> Ok 8  // 64-bit aligned (two i64s)
        | NTUKind.NTUdatetime -> Ok 8  // 64-bit aligned
        | NTUKind.NTUtimespan -> Ok 8  // 64-bit aligned
        | NTUKind.NTUlazy -> Ok 8  // Pointer-aligned (PRD-14)
        | NTUKind.NTUseq -> Ok 8  // Pointer-aligned (PRD-15)
        | NTUKind.NTUarray -> Ok 8  // Pointer-aligned (C-04)
        | NTUKind.NTUborrowedview -> pointerSize ctx
        | NTUKind.NTUlist -> pointerSize ctx  // Pointer-aligned (PRD-13a)
        | NTUKind.NTUmap -> pointerSize ctx  // Pointer-aligned (PRD-13a)
        | NTUKind.NTUset -> pointerSize ctx  // Pointer-aligned (PRD-13a)

    /// Get the substrate kind (defaults to CPU for backward compatibility)
    let substrateKind (ctx: PlatformContext) : SubstrateKind =
        ctx.SubstrateKind |> Option.defaultValue SubstrateKind.CPU

    /// Check if a memory space is available on this substrate
    let isMemorySpaceAvailable (ctx: PlatformContext) (space: NTUMemorySpace) : bool =
        match ctx.AvailableMemorySpaces with
        | [] -> true  // Empty = all available (backward compat)
        | spaces -> List.contains space spaces

    /// Get the default memory space for this substrate
    let defaultMemorySpace (ctx: PlatformContext) : NTUMemorySpace =
        ctx.DefaultMemorySpace |> Option.defaultValue NTUMemorySpace.Default

/// Helpers for NTUKind
module NTUKind =
    /// Check if an NTUKind is platform-dependent (requires quotation resolution)
    let isPlatformDependent = function
        | NTUKind.NTUint (NTUWidth.Resolved _)
        | NTUKind.NTUuint (NTUWidth.Resolved _)
        | NTUKind.NTUfloat (NTUWidth.Resolved _)
        | NTUKind.NTUposit (NTUWidth.Resolved _, _) -> true
        | NTUKind.NTUptr | NTUKind.NTUfnptr | NTUKind.NTUsize | NTUKind.NTUdiff -> true
        | _ -> false

    /// Check if an NTUKind is a fixed-width integer
    let isFixedWidthInteger = function
        | NTUKind.NTUint (NTUWidth.Fixed _) -> true
        | NTUKind.NTUuint (NTUWidth.Fixed _) -> true
        | _ -> false

    /// Check if an NTUKind is any integer type (signed or unsigned, any width)
    let isInteger = function
        | NTUKind.NTUint _ | NTUKind.NTUuint _ -> true
        | NTUKind.NTUsize | NTUKind.NTUdiff -> true
        | _ -> false

    /// Check if an NTUKind is a signed integer
    let isSigned = function
        | NTUKind.NTUint _ -> true
        | NTUKind.NTUdiff -> true
        | _ -> false

    /// Check if an NTUKind is floating point
    let isFloatingPoint = function
        | NTUKind.NTUfloat _ -> true
        | _ -> false

    /// Check if an NTUKind is a posit (Gustafson Type III Unum)
    let isPosit = function
        | NTUKind.NTUposit _ -> true
        | _ -> false

    /// Check if an NTUKind is numeric (integer, floating point, or posit)
    let isNumeric kind = isInteger kind || isFloatingPoint kind || isPosit kind

    /// Get the human-readable name for an NTUKind
    let name = function
        | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register) -> "int"
        | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register) -> "uint"
        | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer) -> "nativeint"
        | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer) -> "unativeint"
        | NTUKind.NTUint (NTUWidth.Fixed 8) -> "int8"
        | NTUKind.NTUint (NTUWidth.Fixed 16) -> "int16"
        | NTUKind.NTUint (NTUWidth.Fixed 32) -> "int32"
        | NTUKind.NTUint (NTUWidth.Fixed 64) -> "int64"
        | NTUKind.NTUuint (NTUWidth.Fixed 8) -> "uint8"
        | NTUKind.NTUuint (NTUWidth.Fixed 16) -> "uint16"
        | NTUKind.NTUuint (NTUWidth.Fixed 32) -> "uint32"
        | NTUKind.NTUuint (NTUWidth.Fixed 64) -> "uint64"
        | NTUKind.NTUfloat (NTUWidth.Fixed 32) -> "float32"
        | NTUKind.NTUfloat (NTUWidth.Fixed 64) -> "float"
        | NTUKind.NTUint w -> $"int({w})"
        | NTUKind.NTUuint w -> $"uint({w})"
        | NTUKind.NTUfloat w -> $"float({w})"
        | NTUKind.NTUposit (NTUWidth.Fixed 8, _) -> "posit8"
        | NTUKind.NTUposit (NTUWidth.Fixed 16, _) -> "posit16"
        | NTUKind.NTUposit (NTUWidth.Fixed 32, _) -> "posit32"
        | NTUKind.NTUposit (NTUWidth.Fixed 64, _) -> "posit64"
        | NTUKind.NTUposit (w, es) -> $"posit({w},es={es})"
        | NTUKind.NTUptr -> "nativeptr"
        | NTUKind.NTUfnptr -> "fnptr"
        | NTUKind.NTUsize -> "size"
        | NTUKind.NTUdiff -> "diff"
        | NTUKind.NTUstring -> "string"
        | NTUKind.NTUbool -> "bool"
        | NTUKind.NTUchar -> "char"
        | NTUKind.NTUunit -> "unit"
        | NTUKind.NTUdecimal -> "decimal"
        | NTUKind.NTUlazy -> "Lazy"
        | NTUKind.NTUseq -> "Seq"
        | NTUKind.NTUarray -> "array"
        | NTUKind.NTUborrowedview -> "BorrowedView"
        | NTUKind.NTUlist -> "List"
        | NTUKind.NTUmap -> "Map"
        | NTUKind.NTUset -> "Set"
        | NTUKind.NTUuuid -> "Uuid"
        | NTUKind.NTUdatetime -> "DateTime"
        | NTUKind.NTUtimespan -> "TimeSpan"

/// Type layout determines memory representation
[<RequireQualifiedAccess>]
type TypeLayout =
    /// Stack-allocated, known size and alignment
    | Inline of size: int * align: int
    /// Arena-allocated (heap-like but deterministic)
    | Reference of arena: ArenaAffinity
    /// Platform-specific, size determined at codegen
    | Opaque
    /// Platform word size - size/alignment depend on target architecture.
    /// CCS preserves type identity at type checking and resolves the size at saturation, where
    /// the platform is (Placement reads the declared Pointer width into `SemanticGraph.Layouts`);
    /// Alex reads the settled layout and resolves nothing (Layout_As_Joint_Constraint.md §3).
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
    /// Substrate-qualified layout: same type, different placement.
    /// Qualifiers do NOT affect type identity — only inform codegen
    /// and BAREWire inter-substrate transfer strategy.
    | Qualified of inner: TypeLayout * qualifiers: NTUQualifiers
    /// A record: the identity of a type laid out field by field in declaration order. Its byte
    /// layout is settled at saturation from its fields' selected representations and the declared
    /// Pointer width (Placement, `SemanticGraph.Layouts`; Dimensional_Range_Design.md ruling 2),
    /// never computed here against a word of eight.
    | Record
    /// A union: the identity of a type laid out as a tag and the payload slot of its widest case,
    /// settled at saturation likewise.
    | Union

/// Arena affinity for memory management
and [<RequireQualifiedAccess>] ArenaAffinity =
    /// Default: current actor's arena
    | CurrentActor
    /// Named arena (explicit allocation context)
    | Explicit of name: string
    /// Stack allocation (no arena, scope-bound)
    | Stack

/// TypeLayout helpers
module TypeLayout =
    /// Strip qualifiers to get the underlying layout (for size/align calculations).
    /// Most code should use this when computing layout properties.
    let rec baseLayout = function
        | TypeLayout.Qualified (inner, _) -> baseLayout inner
        | layout -> layout

    /// Get qualifiers from a layout, if present
    let qualifiers = function
        | TypeLayout.Qualified (_, q) -> Some q
        | _ -> None

//-------------------------------------------------------------------------
// Type Parameter Kind
//-------------------------------------------------------------------------

/// Distinguishes type parameters from measure parameters and carrier parameters.
/// In Clef, measures work on ANY type (not just numerics like in .NET F#).
[<RequireQualifiedAccess>]
type TypeParamKind =
    /// Regular type parameter: 'T
    | Type
    /// Measure parameter: [<Measure>] 'u
    /// Measures on non-numeric types enable memory region tracking, access control, etc.
    | Measure
    /// Carrier parameter (design a.2): the numeric kind an operator scheme quantifies over,
    /// `κ` in `κ<'u> -> κ<'u> -> κ<'u>`. The carrier variable is the numeric constraint (c.1):
    /// it binds only to a numeric carrier, so a non-numeric operand fails to unify with it.
    | Carrier

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
    /// Parameter kinds - which positions are type-sorted and which measure-sorted
    /// e.g., Arena<[<Measure>] 'lifetime> = [Measure]
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
    /// Number of union cases (if this is a DU type).
    /// 0 for non-DU types. >0 for discriminated unions.
    /// Platform elision decides concrete tag representation from case count.
    CaseCount: int
    /// Placement qualifiers for substrate-aware compilation.
    /// None = no explicit placement (substrate default).
    /// These do NOT affect type identity — types with different
    /// qualifiers unify as the same type.
    Qualifiers: NTUQualifiers option
    /// Pin attributes on record fields: Map<fieldName, pinLogicalNames>
    /// Populated from [<Pin("name")>] and [<Pins("a","b","c")>] attributes on SynField.
    /// Empty for non-record types and records without pin attributes.
    FieldPinAttributes: Map<string, string list>
}

/// Total arity (type + measure parameters)
let arity (tc: TypeConRef) = List.length tc.ParamKinds

/// Create a simple type constructor with only type parameters (non-NTU kind)
let mkTypeConRef name typeArity layout =
    { Name = name; Module = []; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = None; FieldCount = 0; CaseCount = 0; Qualifiers = None; FieldPinAttributes = Map.empty }


/// Create a type constructor with an NTU kind (for native primitives)
let mkNTUTypeConRef name ntuKind layout =
    { Name = name; Module = []; ParamKinds = []; Layout = layout; NTUKind = Some ntuKind; FieldCount = 0; CaseCount = 0; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a parameterized type constructor with an NTU kind
let mkNTUTypeConRefWithArity name ntuKind typeArity layout =
    { Name = name; Module = []; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = Some ntuKind; FieldCount = 0; CaseCount = 0; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a type constructor for a record type
/// Field info is accessed via SemanticGraph.Types lookup (not embedded in TypeConRef)
let mkRecordTypeConRef name modulePath typeArity layout fieldCount =
    { Name = name; Module = modulePath; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = None; FieldCount = fieldCount; CaseCount = 0; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a type constructor for a record type with pin attributes
let mkRecordTypeConRefWithPins name modulePath typeArity layout fieldCount (pinAttrs: Map<string, string list>) =
    { Name = name; Module = modulePath; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = None; FieldCount = fieldCount; CaseCount = 0; Qualifiers = None; FieldPinAttributes = pinAttrs }

/// Create a type constructor for a discriminated union type
let mkUnionTypeConRef name typeArity layout caseCount =
    { Name = name; Module = []; ParamKinds = List.replicate typeArity TypeParamKind.Type; Layout = layout; NTUKind = None; FieldCount = 0; CaseCount = caseCount; Qualifiers = None; FieldPinAttributes = Map.empty }

/// Create a qualified type constructor (same type, different placement)
let withQualifiers (qualifiers: NTUQualifiers) (tycon: TypeConRef) : TypeConRef =
    { tycon with Qualifiers = Some qualifiers }

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
    /// Subtype relationship (minimal, for inheritance)
    | Subtype of sub: NativeType * super: NativeType * SourceRange
    /// Type must have compatible memory layout
    | LayoutCompatible of NativeType * TypeLayout * SourceRange
    /// Type application: forall type must instantiate with given args to yield result
    | HasTypeArgs of forallTy: NativeType * args: NativeType list * resultTy: NativeType * SourceRange
    /// Attached to a variable minted for an operand position of operator `op` (design c.1, c.3):
    /// on a carrier variable it is the provenance CCS8000 names; on the type variable of `+` it
    /// is the kind dispatch of D5, which fires when the variable binds (numeric or string, else
    /// CCS8000) and travels with the variable through union, generalisation and instantiation.
    | OperandOf of op: string * SourceRange

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
    
    /// A numeric type (design a.2, plan D4): the carrier position and the dimension. The
    /// carrier position holds the numeric type constructor (which still carries the NTUKind with
    /// its interim width and is still compared by name until step 7, plan D7) or a carrier
    /// variable of kind `TypeParamKind.Carrier`; the dimension is the measure component.
    /// `float` is `TNum(Carrier floatTyCon, Dimension.one)` (`float = float<1>`),
    /// `float<kg m / s^2>` the same carrier at that dimension, `κ<'u>` a carrier variable at a
    /// measure variable. Identity is carrier plus `Dimension` (D2).
    | TNum of carrier: CarrierRef * dim: Dimension

    /// A measure-sorted positional argument on a non-numeric constructor,
    /// `Arena<[<Measure>] 'lifetime>`: a dimension in type-argument position (design a.2).
    | TMeasure of dim: Dimension
    
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
    
    /// Sequence type: Seq<T>
    /// PRD-15: Resumable computation producing values on demand
    | TSeq of element: NativeType

    /// Sequence enumerator type: SeqEnumerator<T>
    /// PRD-15/16: State machine for iterating over a seq
    /// This is the mutable iteration state returned by Seq.getEnumerator
    | TSeqEnumerator of element: NativeType

    /// List type: List<T>
    /// PRD-13a: Immutable singly-linked list
    | TList of element: NativeType

    /// Map type: Map<K, V>
    /// PRD-13a: Immutable key-value map (balanced BST)
    | TMap of keyType: NativeType * valueType: NativeType

    /// Set type: Set<T>
    /// PRD-13a: Immutable set (balanced BST)
    | TSet of element: NativeType

    /// Error type (used during recovery from type errors)
    | TError of message: string

//-------------------------------------------------------------------------
// Supporting Types
//-------------------------------------------------------------------------

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

/// A carrier position (design a.2): a numeric type constructor, or a carrier variable. A carrier
/// variable is a type parameter of kind `Carrier` whose cell in the one union-find store binds,
/// kind-checked, to a constructor (`Bound (TNum (Carrier tc, one))`) or links to another
/// carrier variable (`Bound (TVar other)`); `CarrierRef.resolve` is the only read of that cell.
/// Interim (plan D7): the constructor is one of the per-width numeric constructors; at step 7
/// it collapses to `Int | Real` beside a seal.
and [<RequireQualifiedAccess; NoComparison>] CarrierRef =
    | Carrier of tycon: TypeConRef
    | CVar of var: TypeParam

//-------------------------------------------------------------------------
// Carrier positions: the one read of a carrier variable
//-------------------------------------------------------------------------

module CarrierRef =

    /// Follow a carrier variable to what it stands for: the constructor it is bound to, or the
    /// root variable of its class when it is still unbound. This is the only read of a carrier
    /// cell; every reader of a `TNum` carrier goes through it (or `tryConstructor` below), so no
    /// site outside this module inspects a carrier variable's binding. The cell's binding is
    /// kind-checked: a carrier cell holds a constructor at the measure 1 or a link to another
    /// carrier variable, and anything else is a kind violation, not a value.
    let rec resolve (c: CarrierRef) : CarrierRef =
        match c with
        | CarrierRef.Carrier _ -> c
        | CarrierRef.CVar tp ->
            match tp.Parent with
            | TypeParamState.Unbound -> c
            | TypeParamState.Bound(NativeType.TVar other) -> resolve (CarrierRef.CVar other)
            | TypeParamState.Bound(NativeType.TNum(carrier, dim)) when Map.isEmpty dim.Bases && Map.isEmpty dim.Vars ->
                resolve carrier
            | TypeParamState.Bound other ->
                failwith $"CarrierRef.resolve: the cell of carrier variable {tp.Name} holds '%A{other}': kind violation"

    /// The constructor a carrier position stands for, if it is resolved; `None` is the failure
    /// value for a carrier variable that is still unbound, and a reader that needs a constructor
    /// reports it (CCS8001 at a non-generalisable binding, design c.1), never defaults it.
    let tryConstructor (c: CarrierRef) : TypeConRef option =
        match resolve c with
        | CarrierRef.Carrier tc -> Some tc
        | CarrierRef.CVar _ -> None

//-------------------------------------------------------------------------
// Literal Values (NTU-typed)
//-------------------------------------------------------------------------

/// Literal value representation, typed by NTU.
/// Consolidates literal representation with the Native Type Universe.
/// The NTUKind specifies which numeric type (int8, int32, float64, etc.).
[<RequireQualifiedAccess>]
type NativeLiteral =
    /// Integer literal with NTU kind specifying width/signedness
    /// Covers: int8, uint8, int16, uint16, int32, uint32, int64, uint64, nativeint, unativeint
    | Int of value: int64 * kind: NTUKind
    /// Unsigned integer literal (for values > int64.MaxValue)
    | UInt of value: uint64 * kind: NTUKind
    /// Floating point literal with NTU kind (float32 or float64)
    | Float of value: float * kind: NTUKind
    /// String literal (UTF-8)
    | String of string
    /// Boolean literal
    | Bool of bool
    /// Character literal (UTF-32 code point)
    | Char of char
    /// Unit literal
    | Unit
    /// Decimal literal (128-bit)
    | Decimal of decimal
    /// Embedded byte array
    | ByteArray of byte[]
    /// Embedded uint16 array (for some string encodings)
    | UInt16Array of uint16[]

module NativeLiteral =
    /// Get the NTUKind for a literal.
    /// Returns None for compound literals (ByteArray, UInt16Array)
    /// that decompose to NTUarray or user-defined composite types.
    let tryKind = function
        | NativeLiteral.Int (_, k) -> Some k
        | NativeLiteral.UInt (_, k) -> Some k
        | NativeLiteral.Float (_, k) -> Some k
        | NativeLiteral.String _ -> Some NTUKind.NTUstring
        | NativeLiteral.Bool _ -> Some NTUKind.NTUbool
        | NativeLiteral.Char _ -> Some NTUKind.NTUchar
        | NativeLiteral.Unit -> Some NTUKind.NTUunit
        | NativeLiteral.Decimal _ -> Some NTUKind.NTUdecimal
        | NativeLiteral.ByteArray _ -> Some NTUKind.NTUarray   // array<uint8>
        | NativeLiteral.UInt16Array _ -> Some NTUKind.NTUarray  // array<uint16>

    /// Get the NTUKind for a literal (backward-compat; use tryKind for new code)
    let kind lit =
        match tryKind lit with
        | Some k -> k
        | None -> failwith "NativeLiteral.kind: no NTUKind for this literal"

//-------------------------------------------------------------------------
// Closure Capture Information
//-------------------------------------------------------------------------

/// Information about a variable captured by a lambda (closure).
/// Capture analysis is performed during CCS type checking as part of scope resolution.
/// MLKit-style flat closures: immutable bindings captured by value, mutable by reference.
type CaptureInfo = {
    /// Name of the captured variable
    Name: string
    /// Type of the captured variable
    Type: NativeType
    /// Whether the captured variable is mutable (determines ByRef vs ByValue capture)
    IsMutable: bool
    /// NodeId of the binding that defines this variable (for SSA lookup in Alex)
    SourceNodeId: NodeId option
}

//-------------------------------------------------------------------------
// Record Type Infrastructure (for Field Label Resolution)
// Per clef-lang-spec inference-procedures.md: "Field order determines memory layout"
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
    /// Declared parameters used to instantiate each field at a use site.
    TypeParameters: TypeParam list
    /// Mutable fields forbid generalizing shared record storage.
    MutableFields: Set<string>
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
    // A type constructor's layout is the identity it declares: a record or union's family, a
    // primitive's fixed extent, a platform word, a view. An option or a Result is a union whose
    // size is settled with its argument at saturation (Placement), not computed here.
    | NativeType.TApp(tycon, _) -> tycon.Layout
    // The carrier's layout; the dimension has no extent. An unresolved carrier variable has no
    // layout yet, the same failure value a type variable has.
    | NativeType.TNum(carrier, _) ->
        match CarrierRef.tryConstructor carrier with
        | Some tc -> tc.Layout
        | None -> TypeLayout.Opaque
    | NativeType.TTuple(_, isStruct) when isStruct -> TypeLayout.Record  // laid out by position, settled at saturation
    | NativeType.TTuple(_, _) -> TypeLayout.Reference ArenaAffinity.CurrentActor
    | NativeType.TFun _ -> TypeLayout.NTUCompound 2  // a function value: the closure pair, two platform words
    | NativeType.TVar _ -> TypeLayout.Opaque  // Not yet known
    | NativeType.TNativePtr _ -> TypeLayout.PlatformWord  // Pointer size is platform-dependent
    | NativeType.TByref _ -> TypeLayout.PlatformWord  // Byref size is platform-dependent
    | NativeType.TForall(_, body) -> layoutOf body
    | NativeType.TMeasure _ -> TypeLayout.Inline(0, 1)  // Phantom type
    | NativeType.TAnon(_, isStruct) when isStruct -> TypeLayout.Record
    | NativeType.TAnon(_, _) -> TypeLayout.Reference ArenaAffinity.CurrentActor
    | NativeType.TUnion(tycon, _) -> tycon.Layout
    | NativeType.TLazy _ -> TypeLayout.Inline(-1, -1)  // Size depends on element type (PRD-14)
    | NativeType.TSeq _ -> TypeLayout.Inline(-1, -1)  // Size depends on element type (PRD-15)
    | NativeType.TSeqEnumerator _ -> TypeLayout.Inline(-1, -1)  // Size depends on seq state machine (PRD-15/16)
    | NativeType.TList _ -> TypeLayout.PlatformWord  // Pointer to cons cell (PRD-13a)
    | NativeType.TMap _ -> TypeLayout.PlatformWord  // Pointer to tree root (PRD-13a)
    | NativeType.TSet _ -> TypeLayout.PlatformWord  // Pointer to tree root (PRD-13a)
    | NativeType.TError _ -> TypeLayout.Opaque

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


/// Construct array<'T> type
/// Substitute type arguments into a forall type
let instantiate (typars: TypeParam list) (args: NativeType list) (body: NativeType) : NativeType =
    if List.length typars <> List.length args then
        failwith $"instantiate: arity mismatch - expected {List.length typars} args, got {List.length args}"
    
    let subst = List.zip typars args |> dict

    // A measure parameter (the cell of a measure variable, quantified by design b.4) is
    // substituted by identity in every dimension the body mentions; its argument is a dimension
    // in a measure position (`TMeasure`, as the instantiation mints it). Anything else for a
    // measure parameter is a kind violation, not a value.
    let measureSubst : Map<int, Dimension> =
        List.zip typars args
        |> List.choose (fun (tp, arg) ->
            match tp.Kind, arg with
            | TypeParamKind.Measure, NativeType.TMeasure d -> Some (tp.Id, d)
            | TypeParamKind.Measure, other ->
                failwith $"instantiate: measure parameter {tp.Name} instantiated at a non-measure argument '%A{other}': kind violation"
            | _ -> None)
        |> Map.ofList
    let substDim (d: Dimension) : Dimension =
        if Map.isEmpty measureSubst then d
        else
            d.Vars
            |> Map.fold
                (fun acc v e ->
                    match Map.tryFind v.Id measureSubst with
                    | Some target -> Dimension.mul acc (Dimension.pow e target)
                    | None -> Dimension.mul acc (Dimension.pow e (Dimension.ofVar v)))
                (Dimension.mk d.Bases Map.empty)
    
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
        | NativeType.TSeq elem -> NativeType.TSeq(go elem)  // PRD-15
        | NativeType.TSeqEnumerator elem -> NativeType.TSeqEnumerator(go elem)  // PRD-15/16
        | NativeType.TList elem -> NativeType.TList(go elem)  // PRD-13a
        | NativeType.TMap(k, v) -> NativeType.TMap(go k, go v)  // PRD-13a
        | NativeType.TSet elem -> NativeType.TSet(go elem)  // PRD-13a
        // A carrier parameter is substituted by the carrier of its argument, which is a numeric
        // type at the measure 1 (the instantiation mints it so); the dimension is kept. A
        // non-numeric argument for a carrier parameter is a kind violation, not a value.
        | NativeType.TNum(CarrierRef.CVar tp, dim) when subst.ContainsKey tp ->
            match subst.[tp] with
            | NativeType.TNum(carrier, _) -> NativeType.TNum(carrier, substDim dim)
            | other -> failwith $"instantiate: carrier parameter {tp.Name} instantiated at a non-numeric type '%A{other}': kind violation"
        | NativeType.TNum(carrier, dim) -> NativeType.TNum(carrier, substDim dim)
        | NativeType.TMeasure dim -> NativeType.TMeasure(substDim dim)
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
    // The one renderer for a dimension is Dimension.render (design a.4): a TNum at `one` renders
    // as its bare carrier, otherwise as the carrier applied to the normalised presentation.
    // A carrier variable renders as its name.
    | NativeType.TNum(carrier, dim) ->
        let name =
            match CarrierRef.resolve carrier with
            | CarrierRef.Carrier tc -> tc.Name
            | CarrierRef.CVar tp -> tp.Name
        if dim = Dimension.one then name else $"{name}<{Dimension.render dim}>"
    | NativeType.TMeasure dim -> Dimension.render dim
    | NativeType.TAnon(fields, isStruct) ->
        let fieldsStr = fields |> List.map (fun (n, t) -> $"{n}: {formatType t}") |> String.concat "; "
        if isStruct then $"struct {{| {fieldsStr} |}}" else $"{{| {fieldsStr} |}}"
    // Named records use TApp - formatted above (just shows type name)
    | NativeType.TUnion(tc, _) -> tc.Name
    | NativeType.TLazy elem -> $"Lazy<{formatType elem}>"  // PRD-14
    | NativeType.TSeq elem -> $"seq<{formatType elem}>"  // PRD-15
    | NativeType.TSeqEnumerator elem -> $"SeqEnumerator<{formatType elem}>"  // PRD-15/16
    | NativeType.TList elem -> $"List<{formatType elem}>"  // PRD-13a
    | NativeType.TMap(k, v) -> $"Map<{formatType k}, {formatType v}>"  // PRD-13a
    | NativeType.TSet elem -> $"Set<{formatType elem}>"  // PRD-13a
    | NativeType.TError msg -> $"<error: {msg}>"

//-------------------------------------------------------------------------
// Standard Types Module (NTU-based type definitions)
//-------------------------------------------------------------------------

/// Standard type definitions for native compilation.
/// These are the canonical type values used throughout the compiler.
module Types =
    // Type constructors for primitive types (NTU kinds)
    // Platform-dependent types use PlatformWord layout (size resolved by CCS at saturation from PlatformContext)
    let intTyCon = mkNTUTypeConRef "int" (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)) TypeLayout.PlatformWord
    // Fixed-width types use Inline layout with known sizes
    let int8TyCon = mkNTUTypeConRef "int8" (NTUKind.NTUint (NTUWidth.Fixed 8)) (TypeLayout.Inline(1, 1))
    let int16TyCon = mkNTUTypeConRef "int16" (NTUKind.NTUint (NTUWidth.Fixed 16)) (TypeLayout.Inline(2, 2))
    let int32TyCon = mkNTUTypeConRef "int32" (NTUKind.NTUint (NTUWidth.Fixed 32)) (TypeLayout.Inline(4, 4))
    let int64TyCon = mkNTUTypeConRef "int64" (NTUKind.NTUint (NTUWidth.Fixed 64)) (TypeLayout.Inline(8, 8))
    // Platform-dependent unsigned
    let uintTyCon = mkNTUTypeConRef "uint" (NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register)) TypeLayout.PlatformWord
    // Fixed-width unsigned
    let uint8TyCon = mkNTUTypeConRef "uint8" (NTUKind.NTUuint (NTUWidth.Fixed 8)) (TypeLayout.Inline(1, 1))
    let uint16TyCon = mkNTUTypeConRef "uint16" (NTUKind.NTUuint (NTUWidth.Fixed 16)) (TypeLayout.Inline(2, 2))
    let uint32TyCon = mkNTUTypeConRef "uint32" (NTUKind.NTUuint (NTUWidth.Fixed 32)) (TypeLayout.Inline(4, 4))
    let uint64TyCon = mkNTUTypeConRef "uint64" (NTUKind.NTUuint (NTUWidth.Fixed 64)) (TypeLayout.Inline(8, 8))
    // Native pointer-sized integers (always platform-dependent)
    let nintTyCon = mkNTUTypeConRef "nativeint" (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer)) TypeLayout.PlatformWord
    let unintTyCon = mkNTUTypeConRef "unativeint" (NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer)) TypeLayout.PlatformWord
    let float32TyCon = mkNTUTypeConRef "float32" (NTUKind.NTUfloat (NTUWidth.Fixed 32)) (TypeLayout.Inline(4, 4))
    let floatTyCon = mkNTUTypeConRef "float" (NTUKind.NTUfloat (NTUWidth.Fixed 64)) (TypeLayout.Inline(8, 8))

    // Posit numeric types (Gustafson Type III Unum)
    // es = exponent field size: determines dynamic range vs precision tradeoff
    let posit8TyCon = mkNTUTypeConRef "posit8" (NTUKind.NTUposit (NTUWidth.Fixed 8, 0)) (TypeLayout.Inline(1, 1))
    let posit16TyCon = mkNTUTypeConRef "posit16" (NTUKind.NTUposit (NTUWidth.Fixed 16, 1)) (TypeLayout.Inline(2, 2))
    let posit32TyCon = mkNTUTypeConRef "posit32" (NTUKind.NTUposit (NTUWidth.Fixed 32, 2)) (TypeLayout.Inline(4, 4))
    let posit64TyCon = mkNTUTypeConRef "posit64" (NTUKind.NTUposit (NTUWidth.Fixed 64, 3)) (TypeLayout.Inline(8, 8))

    let boolTyCon = mkNTUTypeConRef "bool" NTUKind.NTUbool (TypeLayout.Inline(1, 1))
    let charTyCon = mkNTUTypeConRef "char" NTUKind.NTUchar (TypeLayout.Inline(4, 4))
    let unitTyCon = mkNTUTypeConRef "unit" NTUKind.NTUunit (TypeLayout.Inline(0, 1))
    let stringTyCon = mkNTUTypeConRef "string" NTUKind.NTUstring TypeLayout.Opaque
    let decimalTyCon = mkNTUTypeConRef "decimal" NTUKind.NTUdecimal (TypeLayout.Inline(16, 8))
    
    // Array type constructor (arity 1, fat pointer layout)
    // C-04: No helper function - use TApp(arrayTyCon, [elemType]) directly
    let arrayTyCon = mkNTUTypeConRefWithArity "array" NTUKind.NTUarray 1 TypeLayout.FatPointer

    // Option type constructor (arity 1) - no specialized DU case, uses TApp
    // Usage: NativeType.TApp(Types.optionTyCon, [elemType])
    let optionTyCon = mkTypeConRef "option" 1 (TypeLayout.Inline(-1, -1))

    /// The numeric carriers, in one place. The kind <-> carrier fact is stated by these
    /// definitions alone; `tryNumericTyConOfKind` reads it back (a literal's type is its
    /// carrier at `one`), so no second table maps an NTUKind to a type.
    let numericTyCons : TypeConRef list =
        [ intTyCon; int8TyCon; int16TyCon; int32TyCon; int64TyCon
          uintTyCon; uint8TyCon; uint16TyCon; uint32TyCon; uint64TyCon
          nintTyCon; unintTyCon; float32TyCon; floatTyCon
          posit8TyCon; posit16TyCon; posit32TyCon; posit64TyCon ]

    /// The numeric carrier whose NTUKind is `kind`, if any.
    let tryNumericTyConOfKind (kind: NTUKind) : TypeConRef option =
        numericTyCons |> List.tryFind (fun tc -> tc.NTUKind = Some kind)

    /// A numeric type value at the dimensionless measure: `float = float<1>` (plan D4).
    let numericType (carrier: TypeConRef) : NativeType = NativeType.TNum(CarrierRef.Carrier carrier, Dimension.one)
    let private numType = numericType

    /// The seal spellings (design e.1), read in one place (e.2, sequence CS-5): every name a
    /// source may write for a numeric carrier, with the carrier it names, the conversion
    /// operation the intrinsic of that name performs, and the representation the spelling
    /// seals (plan D8, CS-7b): the name the platform description must declare, or the width
    /// dimension through which that name is found (`int` and `nativeint` are the signed
    /// integer of the Register and Pointer widths). Aliases (`sbyte`, `byte`, `double`,
    /// `float64`, `single`) share their carrier's row. The type-position resolver, the conversion
    /// intrinsics, the SRTP conversion set, the parse/format dispatch and the saturation
    /// representation check all read this list; no second name-to-carrier table exists. The
    /// posit seals take their spelling with the seal form of step 7 (`Posit32`,
    /// numeric-selection.md §5) and are not written here.
    ///
    /// Interim shape (plan D7): the carrier column points at a per-width constructor because width
    /// still lives in the type until step 7. In the design's end state there is one integer carrier
    /// and one real carrier; every spelling here except `int` and `float` is a seal, so at step 7
    /// this column becomes `Int | Real` beside a seal column (`FixedInt(8, signed)`, `Ieee 64`,
    /// `Posit(32, 2)`; design note e.1) and the per-width constructors are deleted. `float64` is
    /// the explicit IEEE-64 seal (numeric-selection.md readouts); today it aliases `float`.
    let numericSpellings : (string * TypeConRef * string * SealRepresentation) list =
        [ "int", intTyCon, "toInt", SealRepresentation.OfDimension ("int", WidthDimension.Register)
          "int8", int8TyCon, "toSByte", SealRepresentation.Named "int8"
          "sbyte", int8TyCon, "toSByte", SealRepresentation.Named "int8"
          "int16", int16TyCon, "toInt16", SealRepresentation.Named "int16"
          "int32", int32TyCon, "toInt32", SealRepresentation.Named "int32"
          "int64", int64TyCon, "toInt64", SealRepresentation.Named "int64"
          "nativeint", nintTyCon, "toNativeInt", SealRepresentation.OfDimension ("int", WidthDimension.Pointer)
          "uint", uintTyCon, "toUInt", SealRepresentation.OfDimension ("uint", WidthDimension.Register)
          "uint8", uint8TyCon, "toByte", SealRepresentation.Named "uint8"
          "byte", uint8TyCon, "toByte", SealRepresentation.Named "uint8"
          "uint16", uint16TyCon, "toUInt16", SealRepresentation.Named "uint16"
          "uint32", uint32TyCon, "toUInt32", SealRepresentation.Named "uint32"
          "uint64", uint64TyCon, "toUInt64", SealRepresentation.Named "uint64"
          "unativeint", unintTyCon, "toUNativeInt", SealRepresentation.OfDimension ("uint", WidthDimension.Pointer)
          "float", floatTyCon, "toFloat", SealRepresentation.Named "float64"
          "double", floatTyCon, "toFloat", SealRepresentation.Named "float64"
          "float64", floatTyCon, "toFloat", SealRepresentation.Named "float64"
          "float32", float32TyCon, "toFloat32", SealRepresentation.Named "float32"
          "single", float32TyCon, "toFloat32", SealRepresentation.Named "float32" ]

    /// The numeric carrier a spelling names, if any.
    let tryNumericTyConOfName (name: string) : TypeConRef option =
        numericSpellings |> List.tryPick (fun (spelling, tc, _, _) -> if spelling = name then Some tc else None)

    /// The conversion operation and target carrier the conversion intrinsic of a spelling performs.
    let tryConversionOfName (name: string) : (string * TypeConRef) option =
        numericSpellings |> List.tryPick (fun (spelling, tc, op, _) -> if spelling = name then Some (op, tc) else None)

    /// The representation a numeric carrier seals: its spelling row's, or, for a carrier the
    /// table does not spell (a posit carrier before step 7's seal form), the carrier's own
    /// name, so the description is asked for it by that name rather than passed over.
    let representationOfCarrier (carrier: TypeConRef) : SealRepresentation =
        numericSpellings
        |> List.tryPick (fun (_, tc, _, representation) -> if tc.Name = carrier.Name then Some representation else None)
        |> Option.defaultValue (SealRepresentation.Named carrier.Name)

    /// The one identity of numeric carriers (Dimensional_Range_Design.md §0, §2; CS-12 step 5a,
    /// the alias, ruling 5): every integer kind is the one integer kind `int` and every real kind
    /// the one real kind `float`, whatever width its spelling names; two carriers agree when they
    /// are the same kind. The width a spelling names is not a type identity: it is the interim
    /// declared boundary of the annotated node (`RangeSources.declarationOfKind`), read by
    /// RangeAnalysis exactly as a descriptor's declaration. A non-numeric constructor agrees by
    /// name and module as before. `Unify` is the reader.
    let sameCarrierIdentity (tc1: TypeConRef) (tc2: TypeConRef) : bool =
        let real k = NTUKind.isFloatingPoint k || NTUKind.isPosit k
        match tc1.NTUKind, tc2.NTUKind with
        | Some k1, Some k2 when NTUKind.isInteger k1 && NTUKind.isInteger k2 -> true
        | Some k1, Some k2 when real k1 && real k2 -> true
        | _ -> tc1.Name = tc2.Name && tc1.Module = tc2.Module

    /// The width-named spellings the alias period keeps compiling (CS-12 ruling 5), CCS8019 at
    /// every site that writes one: every spelling of the table but the bare kinds `int`, `uint`
    /// and `float`, and `double`, which names no width.
    let isWidthSpelling (name: string) : bool =
        name <> "int" && name <> "uint" && name <> "float" && name <> "double"
        && numericSpellings |> List.exists (fun (spelling, _, _, _) -> spelling = name)

    // Standard type values
    let intType = numType intTyCon
    let int8Type = numType int8TyCon
    let int16Type = numType int16TyCon
    let int32Type = numType int32TyCon
    let int64Type = numType int64TyCon
    let uintType = numType uintTyCon
    let uint8Type = numType uint8TyCon
    let uint16Type = numType uint16TyCon
    let uint32Type = numType uint32TyCon
    let uint64Type = numType uint64TyCon
    let nintType = numType nintTyCon
    let unintType = numType unintTyCon
    let float32Type = numType float32TyCon
    let floatType = numType floatTyCon
    let posit8Type = numType posit8TyCon
    let posit16Type = numType posit16TyCon
    let posit32Type = numType posit32TyCon
    let posit64Type = numType posit64TyCon
    let boolType = mkSimpleType boolTyCon
    let charType = mkSimpleType charTyCon
    let unitType = mkSimpleType unitTyCon
    let stringType = mkSimpleType stringTyCon
    let decimalType = mkSimpleType decimalTyCon

    // ValueOption type constructor (arity 1)
    // Usage: NativeType.TApp(Types.voptionTyCon, [elemType])
    let voptionTyCon = mkTypeConRef "ValueOption" 1 (TypeLayout.Inline(-1, -1))

    // FnPtr type constructor (arity 1)
    // Usage: NativeType.TApp(Types.fnPtrTyCon, [funcType])
    let fnPtrTyCon = mkNTUTypeConRefWithArity "FnPtr" NTUKind.NTUfnptr 1 (TypeLayout.Inline(8, 8))

    // Opaque foreign handle. NTUptr supplies its target-dependent representation;
    // it does not introduce pointer arithmetic, dereference or integer conversions.
    let cHandleTyCon = mkNTUTypeConRefWithArity "CHandle" NTUKind.NTUptr 1 TypeLayout.PlatformWord

    // Distinct nominal types, represented by the platform's pointer word.
    let mmio8TyCon = mkNTUTypeConRefWithArity "Mmio8" NTUKind.NTUptr 0 TypeLayout.PlatformWord
    let mmio16TyCon = mkNTUTypeConRefWithArity "Mmio16" NTUKind.NTUptr 0 TypeLayout.PlatformWord
    let mmio32TyCon = mkNTUTypeConRefWithArity "Mmio32" NTUKind.NTUptr 0 TypeLayout.PlatformWord

    /// The schema is a nominal source type named by ViewLayoutDescriptor.
    let borrowedViewTyCon = mkNTUTypeConRefWithArity "BorrowedView" NTUKind.NTUborrowedview 1 TypeLayout.FatPointer

    // Arena type constructor (arity 1 - lifetime measure parameter, design a.2:
    // `Arena<[<Measure>] 'lifetime>`; the position is measure-sorted and holds a TMeasure)
    // Usage: NativeType.TApp(Types.arenaTyCon, [lifetimeMeasure])
    // Layout: fat pointer (ptr to memory region + remaining size)
    let arenaTyCon = { mkTypeConRef "Arena" 1 TypeLayout.FatPointer with ParamKinds = [ TypeParamKind.Measure ] }

    // Expr type constructor (arity 1 - for quoted expressions)
    // Usage: NativeType.TApp(Types.exprTyCon, [innerType])
    let exprTyCon = mkTypeConRef "Expr" 1 (TypeLayout.Inline(-1, -1))

    /// Construct array<'T> type
    let mkArrayType elemType =
        NativeType.TApp(arrayTyCon, [elemType])

    /// Construct Lazy<'T> type
    let mkLazyType elemType =
        NativeType.TLazy elemType

    /// Construct seq<'T> type
    let mkSeqType elemType =
        NativeType.TSeq elemType

    /// Construct Expr<'T> type (quotation)
    let mkExprType exprType =
        NativeType.TApp(exprTyCon, [exprType])

    /// Try to extract NTUKind from a NativeType (for use with NTUKind predicates).
    /// A numeric type's kind is its carrier's (plan D7: the width still rides there).
    let tryGetNTUKind (ty: NativeType) : NTUKind option =
        match ty with
        | NativeType.TNum(carrier, _) -> CarrierRef.tryConstructor carrier |> Option.bind (fun tc -> tc.NTUKind)
        | NativeType.TApp(tycon, _) -> tycon.NTUKind
        | _ -> None

    /// A numeric type is a TNum; nothing else carries a dimension (design a.2).
    let isNumericType (ty: NativeType) : bool =
        match ty with
        | NativeType.TNum _ -> true
        | _ -> false

    /// Check if a type is an integer (signed or unsigned): a TNum whose carrier is an integer kind
    let isIntegerType (ty: NativeType) : bool =
        match ty with
        | NativeType.TNum(carrier, _) ->
            CarrierRef.tryConstructor carrier |> Option.bind (fun tc -> tc.NTUKind) |> Option.exists NTUKind.isInteger
        | _ -> false

    /// Check if a type is a floating point type: a TNum whose carrier is a floating-point kind
    let isFloatType (ty: NativeType) : bool =
        match ty with
        | NativeType.TNum(carrier, _) ->
            CarrierRef.tryConstructor carrier |> Option.bind (fun tc -> tc.NTUKind) |> Option.exists NTUKind.isFloatingPoint
        | _ -> false

    /// Check if a type is the string type
    let isStringType (ty: NativeType) : bool =
        match tryGetNTUKind ty with
        | Some NTUKind.NTUstring -> true
        | _ -> false

// SPDX-License-Identifier: MIT

/// Obligation Discharge -- the design-time dispatch.
///
/// A pure projection of F: every obligation node, in NodeId order, rendered as
/// the ledger (06a_obligations.json) and the solver-ready SMT-LIB artifact
/// (06b_obligations.smt2) that cvc5 discharges. Refutation style throughout:
/// each obligation is a named Boolean anchor; its definition and its negation
/// are asserted. Conditional foreign claims also require the dispatcher's
/// separate premise-satisfiability check; a rendered query is no discharge.
///
/// The anchor name is the identity that travels: the build-time dispatch
/// (Composer's SMTTransfer, over the witnessed MLIR) reads the same records
/// from the same graph and declares the same names, so the two can be paired
/// one for one (C-01 14.5; HelloProof proof-trace 03).
///
/// Every constant here was fixed at saturation. This module transcribes.
module Clef.Compiler.Nanopass.ObligationDischarge

open System.IO
open Fidelity.Data.JSON
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.NativeTypedTree.Infrastructure.PhaseConfig
module Published = Clef.Compiler.Baker.Ingredients.PublishedFactRows

//=============================================================================
// SMT-LIB RENDERING
//=============================================================================

// Transcribe native data only. The public owner supplies the conditional law.
let private foreignProjection (model: ForeignResultCoverageModel) =
    let bound = function
        | ForeignResultBound.Constant value -> Fidelity.PSG.ForeignResultBound.Constant value
        | ForeignResultBound.Argument index -> Fidelity.PSG.ForeignResultBound.Argument index
    let range = function
        | ValueRange.Empty -> Fidelity.PSG.ValueRange.Empty
        | ValueRange.Bounded(lower, upper) -> Fidelity.PSG.ValueRange.Bounded(lower, upper)
        | ValueRange.Above lower -> Fidelity.PSG.ValueRange.Above lower
        | ValueRange.Below upper -> Fidelity.PSG.ValueRange.Below upper
        | ValueRange.Unbounded -> Fidelity.PSG.ValueRange.Unbounded
    match model.Application.Hypothesis with
    | None -> Error "Foreign result behavior contract is missing"
    | Some _ when model.Abi.IsNone ->
        Error "Foreign result coverage has no actual ABI premise"
    | Some hypothesis ->
        Fidelity.PSG.ForeignResultCoverage.project
            (bound hypothesis.Lower) (bound hypothesis.Upper)
            (model.Application.Arguments |> List.map (fun actual -> actual.Index, range actual.Enclosure))
            (range model.ResultRange) (range model.Destination) (range model.AbiRange)

/// One obligation's scope: the anchor's definition, then its negation.
let private bodyToSmtLib (id: string) (body: ObligationBody) : string list =
    let integer (value: bigint) =
        if value.Sign < 0 then sprintf "(- %s)" (string (-value)) else string value
    let real (value: Clef.Compiler.NativeTypedTree.NativeTypes.ExactRational) =
        if value.Denominator <= 0I then invalidArg "body" "A real obligation requires positive rational denominators."
        let numerator = value.Numerator
        let magnitude = sprintf "%s.0" (abs numerator |> string)
        let signed = if numerator.Sign < 0 then sprintf "(- %s)" magnitude else magnitude
        if value.Denominator = 1I then signed else sprintf "(/ %s %s.0)" signed (string value.Denominator)
    match body with
    | ObligationBody.Pending reasons ->
        invalidArg "body" ("A pending obligation has no solver term: " + String.concat "; " reasons)
    | ObligationBody.OptionalEntryArgumentConversion model ->
        match Published.mapOptionalEntryArgumentConversionModel model |> Fidelity.PSG.OptionalEntryArgumentProof.project with
        | Ok projection -> Fidelity.PSG.ResourceProof.refutation id projection
        | Error reason -> invalidArg "body" reason
    | ObligationBody.ResourceConversion model ->
        match Published.mapResourceConversionModel model |> Fidelity.PSG.ResourceProof.ofConversion with
        | Ok projection -> Fidelity.PSG.ResourceProof.refutation id projection
        | Error reason -> invalidArg "body" reason
    | ObligationBody.ResourceCleanup model ->
        match Published.mapResourceCleanupModel model |> Fidelity.PSG.ResourceProof.ofCleanup with
        | Ok projection -> Fidelity.PSG.ResourceProof.refutation id projection
        | Error reason -> invalidArg "body" reason
    | ObligationBody.SnapshotBorrowBound(_,_,_,_,minimum,maximum) ->
        match Fidelity.PSG.SnapshotBorrowProof.ofBounds minimum maximum with
        | Ok projection -> Fidelity.PSG.ResourceProof.refutation id projection
        | Error reason -> invalidArg "body" reason
    | ObligationBody.ForeignResultCoverage model ->
        match foreignProjection model with
        | Error reason -> invalidArg "body" reason
        | Ok projection ->
            Fidelity.PSG.ForeignResultCoverage.declarations projection
            @ [ sprintf "(assert (= %s %s))" id (Fidelity.PSG.ForeignResultCoverage.smtLib projection.Conclusion)
                sprintf "(assert (not %s))" id ]
    | ObligationBody.ProgramInitializationOrder(initializerOrdinal, initializerCount, useOrdinals) ->
        let ordinal, count = integer (bigint initializerOrdinal), integer (bigint initializerCount)
        let clauses =
            [ sprintf "(<= 0 %s)" ordinal; sprintf "(< %s %s)" ordinal count ]
            @ (useOrdinals |> List.collect (fun useOrdinal ->
                let usePhase = integer (bigint useOrdinal)
                [ sprintf "(< %s %s)" ordinal usePhase; sprintf "(<= %s %s)" usePhase count ]))
        [ sprintf "(assert (= %s (and %s)))" id (String.concat " " clauses)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.FiniteLoopTrip model ->
        let start, limit, step, count = integer model.InitialLower, integer model.LimitUpper, integer model.MinimumStep, integer model.MaximumIterations
        let beyond = if model.Inclusive then ">" else ">="
        [ sprintf "(assert (= %s (and (> %s 0) (>= %s 0) (%s (+ %s (* %s %s)) %s))))" id step count beyond start count step limit
          sprintf "(assert (not %s))" id ]
    | ObligationBody.FiniteSequencePull model ->
        let steps = model.Steps |> List.map (fun step -> step.Label, step) |> Map.ofList
        let wellShaped =
            not model.Steps.IsEmpty && steps.Count = model.Steps.Length &&
            steps.ContainsKey model.Entry &&
            (model.Steps |> List.forall (fun step -> step.Successors |> List.forall steps.ContainsKey))
        let conclusion =
            if not wellShaped then "false"
            else
                let clauses =
                    [ yield sprintf "(>= %s 0)" (integer model.MaximumPulls)
                      yield sprintf "(<= %s %s)" (integer steps[model.Entry].Remaining) (integer model.MaximumPulls)
                      for step in model.Steps do
                          let remaining = integer step.Remaining
                          let weight = if step.Suspend then "1" else "0"
                          yield sprintf "(>= %s 0)" remaining
                          match step.Successors with
                          | [] -> yield sprintf "(>= %s %s)" remaining weight
                          | successors ->
                              for successor in successors do
                                  yield sprintf "(>= %s (+ %s %s))" remaining weight (integer steps[successor].Remaining) ]
                sprintf "(and %s)" (String.concat " " clauses)
        [ sprintf "(assert (= %s %s))" id conclusion
          sprintf "(assert (not %s))" id ]
    | ObligationBody.AdditiveLoopInvariant model ->
        let lo, hi = integer model.InitialLower, integer model.InitialUpper
        let dlo, dhi = integer model.DeltaLower, integer model.DeltaUpper
        let lower, upper, count = integer model.Lower, integer model.Upper, integer model.MaximumIterations
        let down, up = integer (min 0I model.DeltaLower), integer (max 0I model.DeltaUpper)
        [ "(declare-const recurrence_k Int)"
          "(declare-const recurrence_value Int)"
          "(declare-const recurrence_delta Int)"
          sprintf "(define-fun recurrence_lo ((k Int)) Int (+ %s (* k %s)))" lo down
          sprintf "(define-fun recurrence_hi ((k Int)) Int (+ %s (* k %s)))" hi up
          // Premises are local implications. Inconsistent numeric models must
          // refute the conclusion, rather than make global assumptions empty.
          sprintf "(assert (= %s (and (>= %s 0) (<= %s %s) (<= %s %s) (<= %s %s) (<= %s %s) (<= %s %s)" id count lo hi dlo dhi lower upper lower lo hi upper
          sprintf "  (=> (and (<= 0 recurrence_k) (<= recurrence_k %s)) (and (<= %s (recurrence_lo recurrence_k)) (<= (recurrence_hi recurrence_k) %s)))" count lower upper
          sprintf "  (=> (and (<= 0 recurrence_k) (< recurrence_k %s) (<= (recurrence_lo recurrence_k) recurrence_value) (<= recurrence_value (recurrence_hi recurrence_k)) (<= %s recurrence_delta) (<= recurrence_delta %s)) (and (<= (recurrence_lo (+ recurrence_k 1)) (+ recurrence_value recurrence_delta)) (<= (+ recurrence_value recurrence_delta) (recurrence_hi (+ recurrence_k 1))))))))" count dlo dhi
          sprintf "(assert (not %s))" id ]
    | ObligationBody.FiniteAdditiveEffects(initial, contributions, lower, upper) ->
        let terms = contributions |> List.mapi (fun index (count, delta) ->
            sprintf "effect_count_%d" index, count, delta)
        let domain = terms |> List.collect (fun (name, count, _) -> [sprintf "(<= 0 %s)" name; sprintf "(<= %s %s)" name (integer count)])
        let increments = terms |> List.map (fun (name, _, delta) -> sprintf "(* %s %s)" name (integer delta))
        let total = sprintf "(+ %s %s)" (integer initial) (if increments.IsEmpty then "0" else String.concat " " increments)
        let counts = terms |> List.map (fun (_, count, _) -> sprintf "(>= %s 0)" (integer count))
        let premise = if domain.IsEmpty then "true" else sprintf "(and %s)" (String.concat " " domain)
        (terms |> List.map (fun (name, _, _) -> sprintf "(declare-const %s Int)" name)) @
        [ sprintf "(assert (= %s (and %s (=> %s (and (<= %s %s) (<= %s %s))))))"
              id (String.concat " " counts) premise (integer lower) total total (integer upper)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.FiniteLinearRecurrence model ->
        let dimension = model.InitialLower.Length
        let vectorShape values = List.length values = dimension
        let matrixShape rows = List.length rows = dimension && List.forall vectorShape rows
        let wellShaped =
            (dimension = 1 || dimension = 2) && vectorShape model.InitialUpper &&
            vectorShape model.Lower && vectorShape model.Upper &&
            matrixShape model.CoefficientLower && matrixShape model.CoefficientUpper &&
            (model.Powers |> List.forall (fun step -> matrixShape step.Matrix))
        if not wellShaped then
            [ sprintf "(assert (= %s false))" id; sprintf "(assert (not %s))" id ]
        else
            let vector values = values |> List.map integer |> List.toArray
            let matrix rows = rows |> List.map vector |> List.toArray
            let dot (left: string array) (right: string array) =
                match Array.map2 (fun a b -> sprintf "(* %s %s)" a b) left right with
                | [| product |] -> product
                | products -> products |> String.concat " " |> sprintf "(+ %s)"
            let multiply (left: string array array) (right: string array array) =
                Array.init dimension (fun row ->
                    Array.init dimension (fun column ->
                        dot left.[row] (Array.init dimension (fun k -> right.[k].[column]))))
            let initialLo, initialHi = vector model.InitialLower, vector model.InitialUpper
            let coefficientLo, coefficientHi = matrix model.CoefficientLower, matrix model.CoefficientUpper
            let lower, upper = vector model.Lower, vector model.Upper
            let clauses = ResizeArray<string>()
            clauses.Add(sprintf "(>= %s 0)" (integer model.MaximumIterations))
            for row in 0 .. dimension - 1 do
                clauses.Add(sprintf "(<= 0 %s)" initialLo.[row])
                clauses.Add(sprintf "(<= %s %s)" initialLo.[row] initialHi.[row])
                clauses.Add(sprintf "(<= %s 0)" lower.[row])
                // A nonnegative matrix preserves this initial upper-vector order,
                // so the checked final power encloses every earlier prefix too.
                clauses.Add(sprintf "(<= %s %s)" initialHi.[row] (dot coefficientHi.[row] initialHi))
                for column in 0 .. dimension - 1 do
                    clauses.Add(sprintf "(<= 0 %s)" coefficientLo.[row].[column])
                    clauses.Add(sprintf "(<= %s %s)" coefficientLo.[row].[column] coefficientHi.[row].[column])
            let mutable previousExponent = "0"
            let mutable previousMatrix =
                Array.init dimension (fun row -> Array.init dimension (fun column -> if row = column then "1" else "0"))
            for step in model.Powers do
                let squared = multiply previousMatrix previousMatrix
                let expected = if step.Odd then multiply squared coefficientHi else squared
                let supplied = matrix step.Matrix
                clauses.Add(sprintf "(= %s (+ (* 2 %s) %d))" (integer step.Exponent) previousExponent (if step.Odd then 1 else 0))
                for row in 0 .. dimension - 1 do
                    for column in 0 .. dimension - 1 do
                        clauses.Add(sprintf "(= %s %s)" supplied.[row].[column] expected.[row].[column])
                previousExponent <- integer step.Exponent
                previousMatrix <- supplied
            clauses.Add(sprintf "(= %s %s)" previousExponent (integer model.MaximumIterations))
            for row in 0 .. dimension - 1 do
                clauses.Add(sprintf "(<= %s %s)" (dot previousMatrix.[row] initialHi) upper.[row])
            // These are conclusion clauses, never contradictory global premises.
            // Transcribe the supplied certificate; do not repair a bad power.
            [ sprintf "(assert (= %s (and %s)))" id (String.concat " " clauses)
              sprintf "(assert (not %s))" id ]
    | ObligationBody.MappedElementSpan model ->
        [ "(declare-const mapped_base Int)"
          "(declare-const mapped_bytes Int)"
          "(declare-const mapped_index Int)"
          "(assert (> mapped_base 0))"
          "(assert (> mapped_bytes 0))"
          sprintf "(assert (<= mapped_bytes %s))" (integer model.MaximumExtent)
          sprintf "(assert (<= mapped_base (- %s mapped_bytes)))" (integer model.MaximumExtent)
          sprintf "(assert (= (mod mapped_bytes %d) 0))" model.ElementBytes
          sprintf "(assert (= (mod mapped_base %d) 0))" model.BaseAlignment
          "(assert (<= 0 mapped_index))"
          sprintf "(assert (< mapped_index (div mapped_bytes %d)))" model.ElementBytes
          sprintf "(define-fun element_start () Int (+ mapped_base (* mapped_index %d)))" model.ElementBytes
          sprintf "(define-fun element_end () Int (+ element_start %d))" model.ElementBytes
          sprintf "(assert (= %s (and (<= mapped_base element_start) (<= element_end (+ mapped_base mapped_bytes)) (<= element_end %s) (= (mod element_start %d) 0))))" id (integer model.MaximumExtent) model.ElementAlignment
          sprintf "(assert (not %s))" id ]
    | ObligationBody.IntegerLiteralRange (value, lower, upper) ->
        [ sprintf "(assert (= %s (and (<= %s %s) (<= %s %s))))" id (integer lower) (integer value) (integer value) (integer upper)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.IntegerRepresentationCoverage (lower, upper, minimum, maximum) ->
        [ sprintf "(assert (= %s (and (<= %s %s) (<= %s %s) (<= %s %s))))" id (integer minimum) (integer lower) (integer lower) (integer upper) (integer upper) (integer maximum)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.IntegerDivisorNonzero (lower, upper) ->
        [ sprintf "(assert (= %s (and (<= %s %s) (or (< %s 0) (> %s 0)))))" id (integer lower) (integer upper) (integer upper) (integer lower)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.IntegerShiftCount (lower, upper, bits) ->
        [ sprintf "(assert (= %s (and (> %s 0) (<= 0 %s) (<= %s %s) (< %s %s))))" id (integer (bigint bits)) (integer lower) (integer lower) (integer upper) (integer upper) (integer (bigint bits))
          sprintf "(assert (not %s))" id ]
    | ObligationBody.SpatialKernelPartition(elements, grain, columns, slices, depth, iterations) ->
        let clauses =
            [ yield sprintf "(> %s 0)" (integer elements)
              yield sprintf "(> %s 0)" (integer grain)
              yield sprintf "(> %s 0)" (integer(bigint columns))
              yield sprintf "(> %s 0)" (integer(bigint depth))
              yield sprintf "(> %s 0)" (integer iterations)
              yield sprintf "(> %d 0)" slices.Length
              yield sprintf "(= %s (* %d %s))" (integer elements) slices.Length (integer grain)
              for ordinal, (column, offset, count) in List.indexed slices do
                  yield sprintf "(and (<= 0 %s) (< %s %s) (<= 0 %s) (= %s %s))" (integer(bigint column)) (integer(bigint column)) (integer(bigint columns)) (integer offset) (integer count) (integer grain)
                  let previous =
                      if ordinal = 0 then "0" else
                      let _, previousOffset, previousCount = slices[ordinal - 1]
                      sprintf "(+ %s %s)" (integer previousOffset) (integer previousCount)
                  yield sprintf "(= %s %s)" (integer offset) previous
                  yield sprintf "(<= (+ %s %s) %s)" (integer offset) (integer count) (integer elements)
                  for other, _, _ in slices |> List.take ordinal do
                      yield sprintf "(not (= %s %s))" (integer(bigint column)) (integer(bigint other))
              match List.tryLast slices with
              | Some(_, offset, count) -> yield sprintf "(= (+ %s %s) %s)" (integer offset) (integer count) (integer elements)
              | None -> yield "false" ]
        [ sprintf "(assert (= %s (and %s)))" id (String.concat " " clauses)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.ApplicationDimensions comparisons ->
        let integer value = if value < 0 then sprintf "(- %d)" (-(int64 value)) else string value
        let equality left right =
            let coordinates project =
                let l, r = project left, project right
                Set.union (l |> Map.keys |> Set.ofSeq) (r |> Map.keys |> Set.ofSeq)
                |> Set.toList |> List.map (fun axis ->
                    sprintf "(= %s %s)" (Map.tryFind axis l |> Option.defaultValue 0 |> integer) (Map.tryFind axis r |> Option.defaultValue 0 |> integer))
            coordinates (fun d -> d.Bases) @ coordinates (fun d -> d.Vars)
        let clauses = comparisons |> List.collect (fun (_, expected, actual) ->
            match expected, actual with Some left, Some right -> equality left right | _ -> ["false"])
        let proposition =
            match comparisons, clauses with
            | [], _ -> "false"
            | _, [] -> "true"
            | _, [clause] -> clause
            | _, clauses -> sprintf "(and %s)" (String.concat " " clauses)
        [ sprintf "(assert (= %s %s))" id proposition
          sprintf "(assert (not %s))" id ]
    | ObligationBody.RealLiteralRange (value, lower, upper) ->
        [ "(declare-const value Real)"
          sprintf "(assert (= value %s))" (real value)
          sprintf "(assert (= %s (and (<= %s value) (<= value %s))))" id (real lower) (real upper)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.RealRepresentationCoverage (lower, upper, minimum, maximum) ->
        [ sprintf "(assert (= %s (and (<= %s %s) (<= %s %s) (<= %s %s))))"
              id (real minimum) (real lower) (real lower) (real upper) (real upper) (real maximum)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.DimensionalRelation (rule, left, right, result) ->
        // Compare all declared-base and formal-variable coefficients. Formal
        // generators remain distinct, so a successful check holds under every
        // substitution of dimensions for those variables.
        let dimensions = left :: right :: Option.toList result
        let axes project = dimensions |> List.collect (project >> Map.toList >> List.map fst) |> Set.ofList |> Set.toList
        let integer (value: int) =
            if value < 0 then sprintf "(- %d)" (-int64 value) else string value
        let clauses project axis =
            let exponent dim = project dim |> Map.tryFind axis |> Option.defaultValue 0 |> integer
            let l, r = exponent left, exponent right
            match rule, result with
            | DimensionalRule.Product, Some output -> [ sprintf "(= %s (+ %s %s))" (exponent output) l r ]
            | DimensionalRule.Quotient, Some output -> [ sprintf "(= %s (- %s %s))" (exponent output) l r ]
            | DimensionalRule.SameDimension, Some output -> [ sprintf "(= %s %s)" l r; sprintf "(= %s %s)" (exponent output) l ]
            | DimensionalRule.Comparison, None -> [ sprintf "(= %s %s)" l r ]
            | _ -> [ "false" ]
        let baseClauses = axes (fun d -> d.Bases) |> List.collect (clauses (fun d -> d.Bases))
        let variableClauses = axes (fun d -> d.Vars) |> List.collect (clauses (fun d -> d.Vars))
        let wellFormed = (rule = DimensionalRule.Comparison) = Option.isNone result
        let proposition =
            match baseClauses @ variableClauses with
            | _ when not wellFormed -> "false"
            | [] -> "true"
            | [ clause ] -> clause
            | all -> sprintf "(and %s)" (String.concat " " all)
        [ sprintf "(assert (= %s %s))" id proposition
          sprintf "(assert (not %s))" id ]
    | ObligationBody.StorageReservation (len, storage) ->
        [ sprintf "(assert (= %s (= %d (+ %d 1))))" id storage len
          sprintf "(assert (not %s))" id ]
    | ObligationBody.ViewContainment (view, len, storage) ->
        [ sprintf "(assert (= %s (and (= %d %d) (< %d %d))))" id view len view storage
          sprintf "(assert (not %s))" id ]
    | ObligationBody.NulSentinel lastByte ->
        [ sprintf "(assert (= %s (= #x%02x #x00)))" id lastByte
          sprintf "(assert (not %s))" id ]
    | ObligationBody.StaticStorageLayout (slots, used, allocated, alignment, capacity, spaceAlignment, granularity) ->
        let number (value: int) = integer (bigint value)
        let endpoint (offset: int, length: int, _) = bigint offset + bigint length
        let divides value divisor =
            if divisor <= 0 then "false"
            else sprintf "(= (mod %s %s) 0)" (number value) (number divisor)
        let maximum = slots |> List.map endpoint |> List.fold max 0I
        let clauses =
            [ sprintf "(>= %s 0)" (number used)
              sprintf "(<= %s %s)" (number used) (number allocated)
              sprintf "(<= %s %s)" (number allocated) (integer (bigint capacity))
              sprintf "(= %s %s)" (number used) (integer maximum)
              sprintf "(> %s 0)" (number alignment)
              sprintf "(>= %s %s)" (number alignment) (number spaceAlignment)
              divides alignment spaceAlignment
              divides allocated granularity ]
            @ (slots |> List.collect (fun (offset, length, required) ->
                [ sprintf "(>= %s 0)" (number offset)
                  sprintf "(> %s 0)" (number length)
                  divides offset required
                  divides alignment required
                  sprintf "(<= %s %s)" (integer (endpoint (offset, length, required))) (number allocated) ]))
            @ [ for i in 0 .. slots.Length - 1 do
                    for j in i + 1 .. slots.Length - 1 do
                        let left, right = slots[i], slots[j]
                        let lo, _, _ = left
                        let ro, _, _ = right
                        yield sprintf "(or (<= %s %s) (<= %s %s))" (integer (endpoint left)) (number ro) (integer (endpoint right)) (number lo) ]
        [ sprintf "(assert (= %s (and %s)))" id (String.concat " " clauses)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.ContinuationLayout (slots, extent, alignment) ->
        let number (value: int) = integer (bigint value)
        let powerOfTwo value =
            [0 .. 30] |> List.map (fun exponent -> sprintf "(= %s %s)" (number value) (integer (1I <<< exponent)))
            |> String.concat " " |> sprintf "(or %s)"
        let aligned endpoint required =
            // Invalid alignment still fails its power-of-two conjunct; keep
            // the division defined so malformed facts cannot create vacuity.
            let divisor = integer (bigint (max 1 required))
            sprintf "(* (div (+ %s (- %s 1)) %s) %s)" endpoint divisor divisor divisor
        let endpoint (offset, length, _) = sprintf "(+ %s %s)" (number offset) (number length)
        let previous = "0" :: (slots |> List.map endpoint)
        let clauses =
            [ sprintf "(>= %s 0)" (number extent)
              powerOfTwo alignment
              sprintf "(>= %s 1)" (number alignment)
              // Together with >= every field alignment this is exactly max.
              ("(= " + number alignment + " 1)") :: (slots |> List.map (fun (_, _, required) -> sprintf "(= %s %s)" (number alignment) (number required)))
              |> String.concat " " |> sprintf "(or %s)"
              sprintf "(= %s %s)" (number extent) (aligned (List.last previous) alignment) ]
            @ (slots |> List.mapi (fun index (offset, length, required) ->
                [ sprintf "(>= %s 0)" (number offset)
                  sprintf "(> %s 0)" (number length)
                  powerOfTwo required
                  sprintf "(>= %s %s)" (number alignment) (number required)
                  sprintf "(= (mod %s %s) 0)" (number offset) (number (max 1 required))
                  sprintf "(= (mod %s %s) 0)" (number alignment) (number (max 1 required))
                  sprintf "(= %s %s)" (number offset) (aligned previous[index] required)
                  sprintf "(<= %s %s)" (endpoint (offset, length, required)) (number extent) ]) |> List.concat)
            @ [ for index, left in List.indexed slots do
                    for right in List.skip (index + 1) slots do
                        let leftOffset, _, _ = left
                        let rightOffset, _, _ = right
                        yield sprintf "(or (<= %s %s) (<= %s %s))" (endpoint left) (number rightOffset) (endpoint right) (number leftOffset) ]
        [ sprintf "(assert (= %s (and %s)))" id (String.concat " " clauses)
          sprintf "(assert (not %s))" id ]
    | ObligationBody.EnvironmentStorageReservation (extent, alignment, capacity, spaceAlignment, granularity) ->
        let proposition =
            match extent, alignment, capacity, spaceAlignment, granularity with
            | Some extent, Some alignment, Some capacity, Some spaceAlignment, Some granularity ->
                let number (value: int) = integer (bigint value)
                let powerOfTwo value =
                    [0 .. 30] |> List.map (fun exponent -> sprintf "(= %s %s)" (number value) (integer (1I <<< exponent)))
                    |> String.concat " " |> sprintf "(or %s)"
                // Keep division defined even for invalid source declarations.
                // Their own conjunct still fails; no zero divisor creates vacuity.
                let divisor = number (max 1 granularity)
                let rounded = sprintf "(* (div (+ %s (- %s 1)) %s) %s)" (number extent) divisor divisor divisor
                [ sprintf "(> %s 0)" (number extent)
                  powerOfTwo alignment; powerOfTwo spaceAlignment; powerOfTwo granularity
                  sprintf "(= (mod %s %s) 0)" (number spaceAlignment) (number (max 1 alignment))
                  sprintf "(<= %s %s)" rounded (integer (bigint capacity)) ]
                |> String.concat " " |> sprintf "(and %s)"
            | _ -> "false"
        [ sprintf "(assert (= %s %s))" id proposition; sprintf "(assert (not %s))" id ]
    | ObligationBody.ConsecutiveLayout (storages, span, capacity) ->
        let n = List.length storages
        let bases = [ for i in 0 .. n - 1 -> sprintf "b%d" i ]
        let sizes = List.toArray storages
        let decls = [ for b in bases -> sprintf "(declare-const %s Int)" b ]
        let adjacency =
            [ for i in 1 .. n - 1 -> sprintf "(assert (= %s (+ %s %d)))" bases[i] bases[i-1] sizes[i-1] ]
        let disjoint =
            [ for i in 0 .. n - 1 do
                for j in i + 1 .. n - 1 ->
                    sprintf "(or (<= (+ %s %d) %s) (<= (+ %s %d) %s))" bases[i] sizes[i] bases[j] bases[j] sizes[j] bases[i] ]
        let spanClause = sprintf "(= (+ %s %d) (+ %s %d))" bases[n-1] sizes[n-1] bases[0] span
        // Where a declared space bounds the layout, the span is within its capacity.
        let fits = capacity |> Option.map (fun c -> sprintf " (<= %d %d)" span c) |> Option.defaultValue ""
        decls
        @ [ sprintf "(assert (>= %s 0))" bases[0] ]
        @ adjacency
        @ [ sprintf "(assert (= %s (and %s %s%s)))" id (String.concat " " disjoint) spanClause fits
            sprintf "(assert (not %s))" id ]
    | ObligationBody.ConcatCopyBound (leftLen, rightLen) ->
        let pin name = function
            | Some v -> [ sprintf "(assert (= %s %d))" name v ]
            | None -> []
        [ "(declare-const len_l Int)"
          "(declare-const len_r Int)"
          "(declare-const alloc Int)"
          "(assert (>= len_l 0))"
          "(assert (>= len_r 0))" ]
        @ pin "len_l" leftLen
        @ pin "len_r" rightLen
        @ [ "(assert (= alloc (+ len_l len_r)))"
            sprintf "(assert (= %s (and (<= len_l alloc) (<= (+ len_l len_r) alloc))))" id
            sprintf "(assert (not %s))" id ]
    | ObligationBody.CapacityPositive cap ->
        [ sprintf "(assert (= %s (> %d 0)))" id cap
          sprintf "(assert (not %s))" id ]
    | ObligationBody.CapacityFits (cap, spaceCap) ->
        [ sprintf "(assert (= %s (<= %d %d)))" id cap spaceCap
          sprintf "(assert (not %s))" id ]
    | ObligationBody.InputBufferBound (count, allocation) ->
        [ sprintf "(assert (= %s (<= %d %d)))" id count allocation
          sprintf "(assert (not %s))" id ]
    | ObligationBody.StringBorrowBound origins ->
        let conditions = origins |> List.map (fun (count, extent, storage) ->
            sprintf "(and (<= 0 %s) (= %s %s) (< %s %s))" (integer count) (integer count) (integer extent) (integer extent) (integer storage))
        [ sprintf "(assert (= %s %s))" id (if conditions.IsEmpty then "false" else "(and " + String.concat " " conditions + ")")
          sprintf "(assert (not %s))" id ]
    | ObligationBody.InputCopyBound (cap, bound) ->
        [ "(declare-const r Int)"
          "(assert (>= r 1))"
          sprintf "(assert (<= r %d))" cap
          sprintf "(assert (= %s (<= (- r 1) %d)))" id bound
          sprintf "(assert (not %s))" id ]

/// The solver-ready artifact: one scope per obligation; `unsat` on every
/// (check-sat) supplies the refutation result. Conditional premises must also
/// pass their separate satisfiability check before discharge is accepted.
let private readySmtLib (obligations: ObligationInfo list) : string =
    obligations
    |> List.map (fun ob ->
        String.concat "\n"
            ([ sprintf "; %s: %s" ob.Id ob.Statement
               sprintf "; origin: %s" ob.Source
               sprintf "(set-logic %s)" ob.Logic
               sprintf "(declare-const %s Bool)" ob.Id ]
             @ bodyToSmtLib ob.Id ob.Body
             @ [ "(check-sat)"; "(reset)" ]))
    |> String.concat "\n\n"

/// Missing premises are evidence of unavailability, never Boolean conclusions.
type UnavailableObligation = {
    Anchor: string
    Source: string
    MissingPremises: string list
}

let unavailable (obligations: ObligationInfo list) : UnavailableObligation list =
    obligations |> List.choose (fun obligation ->
        match obligation.Body with
        | ObligationBody.Pending reasons ->
            Some { Anchor = obligation.Id; Source = obligation.Source; MissingPremises = reasons }
        | ObligationBody.ForeignResultCoverage model ->
            match foreignProjection model with
            | Ok _ -> None
            | Error reason ->
                Some { Anchor = obligation.Id; Source = obligation.Source; MissingPremises = [reason] }
        | ObligationBody.ResourceConversion model ->
            match Published.mapResourceConversionModel model |> Fidelity.PSG.ResourceProof.ofConversion with
            | Ok _ -> None
            | Error reason -> Some {Anchor=obligation.Id;Source=obligation.Source;MissingPremises=[reason]}
        | ObligationBody.OptionalEntryArgumentConversion model ->
            match Published.mapOptionalEntryArgumentConversionModel model |> Fidelity.PSG.OptionalEntryArgumentProof.project with
            | Ok _ -> None
            | Error reason -> Some {Anchor=obligation.Id;Source=obligation.Source;MissingPremises=[reason]}
        | ObligationBody.ResourceCleanup model ->
            match Published.mapResourceCleanupModel model |> Fidelity.PSG.ResourceProof.ofCleanup with
            | Ok _ -> None
            | Error reason -> Some {Anchor=obligation.Id;Source=obligation.Source;MissingPremises=[reason]}
        | ObligationBody.SnapshotBorrowBound(_,_,_,_,minimum,maximum) ->
            match Fidelity.PSG.SnapshotBorrowProof.ofBounds minimum maximum with
            | Ok _ -> None
            | Error reason -> Some {Anchor=obligation.Id;Source=obligation.Source;MissingPremises=[reason]}
        | _ -> None)

let trySmtLib (obligations: ObligationInfo list) : Result<string, UnavailableObligation list> =
    match unavailable obligations with
    | [] -> Ok (readySmtLib obligations)
    | pending -> Error pending

/// Existing ready callers retain their exact text. A caller requiring a query
/// cannot accidentally submit an incomplete inventory or a surrogate predicate.
let smtLib (obligations: ObligationInfo list) : string =
    match trySmtLib obligations with
    | Ok query -> query
    | Error pending ->
        pending
        |> List.map (fun item -> sprintf "'%s' (%s): %s" item.Anchor item.Source (String.concat "; " item.MissingPremises))
        |> String.concat "; "
        |> sprintf "Required obligations have unavailable premises: %s"
        |> invalidOp

//=============================================================================
// LEDGER RENDERING
//=============================================================================

/// The ledger: id, kind, logic, statement, source, refs -- the demo and audit
/// surface, and the anchor list the build-time dispatch is paired against.
let private stringArray values = values |> List.map JsonValue.String |> JsonValue.Array

/// Transcribe stated foreign premises separately from graph-derived enclosures.
/// These rows describe the trusted base; projection readiness is no discharge.
let private foreignLedgerFields (model: ForeignResultCoverageModel) =
    let node id =
        JsonValue.String(string (NodeId.value id))

    let bound =
        function
        | ForeignResultBound.Constant value -> string value
        | ForeignResultBound.Argument index -> sprintf "argument[%d]" index

    let hypothesis =
        model.Application.Hypothesis
        |> Option.map (fun hypothesis ->
            JsonValue.Object
                [
                    "kind", JsonValue.String "external-execution-hypothesis"
                    "identity", JsonValue.String hypothesis.Identity
                    "version", JsonValue.String hypothesis.Version
                    "source", JsonValue.String hypothesis.Source
                    "quote", node hypothesis.Quote
                    "declaration", node hypothesis.Declaration
                    "lower", JsonValue.String(bound hypothesis.Lower)
                    "upper", JsonValue.String(bound hypothesis.Upper)
                ])
        |> Option.toList

    let abi =
        model.Abi
        |> Option.map (fun premise ->
            JsonValue.Object
                [
                    "kind", JsonValue.String "stated-target-abi"
                    "node", node premise
                    "identity",
                    model.AbiIdentity
                    |> Option.map JsonValue.String
                    |> Option.defaultValue JsonValue.Null
                    "range", JsonValue.String(ValueRange.render model.AbiRange)
                ])
        |> Option.toList

    [
        "role",
        JsonValue.String(
            match model.Role with
            | ForeignResultProofRole.LogicalCoverage -> "logical-coverage"
            | ForeignResultProofRole.AbiNarrowing -> "abi-narrowing"
        )
        "trustedBase", JsonValue.Array(hypothesis @ abi)
    ]

let ledgerJson (obligations: ObligationInfo list) : string =
    let hasPending = unavailable obligations |> List.isEmpty |> not

    let hasConditional =
        obligations
        |> List.exists (fun obligation ->
            match obligation.Body with
            | ObligationBody.ForeignResultCoverage _ | ObligationBody.ResourceConversion _ | ObligationBody.ResourceCleanup _
            | ObligationBody.SnapshotBorrowBound _ | ObligationBody.OptionalEntryArgumentConversion _ -> true
            | _ -> false)

    let rows =
        obligations
        |> List.map (fun ob ->
            let fields =
                [
                    "id", JsonValue.String ob.Id
                    "kind", JsonValue.String ob.Kind
                    "logic", JsonValue.String ob.Logic
                    "statement", JsonValue.String ob.Statement
                    "source", JsonValue.String ob.Source
                    "refs", stringArray ob.Refs
                ]

            let foreign =
                match ob.Body with
                | ObligationBody.ForeignResultCoverage model -> foreignLedgerFields model
                | _ -> []

            let readiness =
                if not hasPending && not hasConditional then
                    []
                else
                    let state, reasons =
                        match ob.Body with
                        | ObligationBody.Pending reasons -> "pending", reasons
                        | ObligationBody.OptionalEntryArgumentConversion _ -> "target-pending", ["The finite source plan requires its exact per-call target artifact observation."]
                        | ObligationBody.ForeignResultCoverage model ->
                            match foreignProjection model with
                            | Ok _ -> "ready", []
                            | Error reason -> "pending", [ reason ]
                        | ObligationBody.ResourceConversion model ->
                            match Published.mapResourceConversionModel model |> Fidelity.PSG.ResourceProof.ofConversion with
                            | Ok _ -> "ready", []
                            | Error reason -> "pending",[reason]
                        | ObligationBody.ResourceCleanup model ->
                            match Published.mapResourceCleanupModel model |> Fidelity.PSG.ResourceProof.ofCleanup with
                            | Ok _ -> "ready", []
                            | Error reason -> "pending",[reason]
                        | ObligationBody.SnapshotBorrowBound(_,_,_,_,minimum,maximum) ->
                            match Fidelity.PSG.SnapshotBorrowProof.ofBounds minimum maximum with
                            | Ok _ -> "ready",[]
                            | Error reason -> "pending",[reason]
                        | _ -> "ready", []

                    [ "state", JsonValue.String state; "missingPremises", stringArray reasons ]

            JsonValue.Object(fields @ foreign @ readiness))

    JsonValue.Object
        [
            "version",
            JsonValue.String(
                if hasConditional then "1.2"
                elif hasPending then "1.1"
                else "1.0"
            )
            "description", JsonValue.String "Proof obligations: born in the PSG as graph citizens, design-time form"
            "obligations", JsonValue.Array rows
        ]
    |> Json.serializePretty

let private unavailableJson (pending: UnavailableObligation list) =
    pending
    |> List.map (fun obligation -> JsonValue.Object [
        "Anchor", JsonValue.String obligation.Anchor
        "Source", JsonValue.String obligation.Source
        "MissingPremises", stringArray obligation.MissingPremises ])
    |> JsonValue.Array
    |> Json.serializePretty

//=============================================================================
// PROJECTION AND EMISSION
//=============================================================================

/// The obligations of a graph, in NodeId order: the design-time dispatch's
/// input and the build-time dispatch's, the same list.
let ofGraph (graph: SemanticGraph) : ObligationInfo list =
    SemanticGraph.obligations graph |> List.map snd

/// Write an explicitly validated source inventory beside the intermediates.
/// The source caller owns completeness; this early artifact owner consumes its
/// result without invoking later recipes or reading an unvalidated graph.
let emit (inventory: Result<ObligationInfo list, string list>) : unit =
    if shouldEmit () then
        let dir = getOutputDir ()
        let ledgerPath = Path.Combine(dir, "06a_obligations.json")
        let queryPath = Path.Combine(dir, "06b_obligations.smt2")
        let unavailablePath = Path.Combine(dir, "06b_obligations.unavailable.json")
        let clear () =
            if Directory.Exists dir then
                for path in [ledgerPath; queryPath; unavailablePath] do File.Delete path
        // The source owner reports census diagnostics. This artifact owner must
        // still withdraw earlier output; neither silence nor a partial ledger
        // represents an incomplete current inventory.
        match inventory with
        | Error _ | Ok [] -> clear ()
        | Ok obs ->
            Directory.CreateDirectory dir |> ignore
            File.WriteAllText(ledgerPath, ledgerJson obs)
            match trySmtLib obs with
            | Ok query ->
                File.Delete unavailablePath
                File.WriteAllText(queryPath, query + "\n")
                if isVerbose () then printfn "[CCS] Wrote obligations: 06a_obligations.json, 06b_obligations.smt2 (%d obligations)" obs.Length
            | Error pending ->
                File.Delete queryPath
                File.WriteAllText(unavailablePath, unavailableJson pending)
                if isVerbose () then printfn "[CCS] Wrote obligation ledger; query unavailable for %d pending obligations" pending.Length

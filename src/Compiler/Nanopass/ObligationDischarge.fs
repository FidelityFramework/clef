// SPDX-License-Identifier: MIT

/// Obligation Discharge -- the design-time dispatch.
///
/// A pure projection of F: every obligation node, in NodeId order, rendered as
/// the ledger (06a_obligations.json) and the solver-ready SMT-LIB artifact
/// (06b_obligations.smt2) that cvc5 discharges. Refutation style throughout:
/// each obligation is a named Boolean anchor; its definition and its negation
/// are asserted; `unsat` means it holds.
///
/// The anchor name is the identity that travels: the build-time dispatch
/// (Composer's SMTTransfer, over the witnessed MLIR) reads the same records
/// from the same graph and declares the same names, so the two can be paired
/// one for one (C-01 14.5; HelloProof proof-trace 03).
///
/// Every constant here was fixed at saturation. This module transcribes.
module Clef.Compiler.Nanopass.ObligationDischarge

open System.IO
open System.Text.Json
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.NativeTypedTree.Infrastructure.PhaseConfig

//=============================================================================
// SMT-LIB RENDERING
//=============================================================================

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
    | ObligationBody.InputCopyBound (cap, bound) ->
        [ "(declare-const r Int)"
          "(assert (>= r 1))"
          sprintf "(assert (<= r %d))" cap
          sprintf "(assert (= %s (<= (- r 1) %d)))" id bound
          sprintf "(assert (not %s))" id ]

/// The solver-ready artifact: one scope per obligation; `unsat` on every
/// (check-sat) means every obligation holds.
let smtLib (obligations: ObligationInfo list) : string =
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

//=============================================================================
// LEDGER RENDERING
//=============================================================================

/// The ledger: id, kind, logic, statement, source, refs -- the demo and audit
/// surface, and the anchor list the build-time dispatch is paired against.
let ledgerJson (obligations: ObligationInfo list) : string =
    let ledger =
        {| version = "1.0"
           description = "Proof obligations: born in the PSG as graph citizens, design-time form"
           obligations =
             [ for ob in obligations ->
                 {| id = ob.Id; kind = ob.Kind; logic = ob.Logic
                    statement = ob.Statement; source = ob.Source
                    refs = ob.Refs |} ] |}
    JsonSerializer.Serialize(ledger, JsonSerializerOptions(WriteIndented = true))

//=============================================================================
// PROJECTION AND EMISSION
//=============================================================================

/// The obligations of a graph, in NodeId order: the design-time dispatch's
/// input and the build-time dispatch's, the same list.
let ofGraph (graph: SemanticGraph) : ObligationInfo list =
    SemanticGraph.obligations graph |> List.map snd

/// Write 06a and 06b beside the other intermediates when emission is enabled.
let emit (graph: SemanticGraph) : unit =
    if shouldEmit () then
        match ofGraph graph with
        | [] -> ()
        | obs ->
            let dir = getOutputDir ()
            Directory.CreateDirectory dir |> ignore
            File.WriteAllText(Path.Combine(dir, "06a_obligations.json"), ledgerJson obs)
            File.WriteAllText(Path.Combine(dir, "06b_obligations.smt2"), smtLib obs + "\n")
            if isVerbose () then printfn "[CCS] Wrote obligations: 06a_obligations.json, 06b_obligations.smt2 (%d obligations)" obs.Length

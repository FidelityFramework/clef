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
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.NativeTypedTree.Infrastructure.PhaseConfig

//=============================================================================
// SMT-LIB RENDERING
//=============================================================================

/// One obligation's scope: the anchor's definition, then its negation.
let private bodyToSmtLib (id: string) (body: ObligationBody) : string list =
    match body with
    | ObligationBody.StorageReservation (len, storage) ->
        [ sprintf "(assert (= %s (= %d (+ %d 1))))" id storage len
          sprintf "(assert (not %s))" id ]
    | ObligationBody.ViewContainment (view, len, storage) ->
        [ sprintf "(assert (= %s (and (= %d %d) (< %d %d))))" id view len view storage
          sprintf "(assert (not %s))" id ]
    | ObligationBody.NulSentinel lastByte ->
        [ sprintf "(assert (= %s (= #x%02x #x00)))" id lastByte
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

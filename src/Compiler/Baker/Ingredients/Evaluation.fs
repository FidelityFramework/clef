// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Atomic local evaluation relations. No target representation or state
/// numbering is chosen here; every dependency is resident in the source set.
module Clef.Compiler.Baker.Ingredients.Evaluation

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let private edge owner participants target role ordinal : Hyperedge =
    { Sources = owner :: participants; Target = target
      Class = EdgeClass.Evaluation; Role = role; Ordinal = ordinal }

let operand owner target slot access value =
    edge owner [value] target (EdgeRole.EvaluationOperand access) slot

let capture owner target slot declaration =
    edge owner [declaration] target EdgeRole.EvaluationCapture slot

let root owner generator body =
    edge owner [generator] body EdgeRole.EvaluationRoot 0

let pending owner target reason related =
    edge owner related target (EdgeRole.EvaluationPending reason) 0

/// Only operand ports carry operand identities. Entry/Ready/Exit are local
/// phase boundaries on the target; they cannot conceal a global successor.
let flow owner target (operands: (int * NodeId) list) fromPort toPort transfer =
    let at = function
        | EvaluationPort.OperandEntry slot | EvaluationPort.OperandExit slot ->
            operands |> List.find (fst >> (=) slot) |> snd |> List.singleton
        | _ -> []
    edge owner (at fromPort @ at toPort |> List.distinct) target
        (EdgeRole.EvaluationFlow (fromPort, toPort, transfer)) 0

/// Ordered eager value demands followed by the container's own operation.
/// A shared operand identity remains shared; later composition must establish
/// availability/dominance instead of treating this as an execution walk.
let ordered owner target operands exitTransfer =
    let link = flow owner target operands
    let rec demands previous = function
        | [] -> [link previous EvaluationPort.Ready EvaluationTransfer.Continue]
        | (slot, _) :: rest ->
            link previous (EvaluationPort.OperandEntry slot) EvaluationTransfer.Continue
            :: demands (EvaluationPort.OperandExit slot) rest
    demands EvaluationPort.Entry operands
    @ [link EvaluationPort.Ready EvaluationPort.Exit exitTransfer]

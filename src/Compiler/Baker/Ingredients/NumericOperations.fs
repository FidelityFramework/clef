// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Ingredients.NumericOperations

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.NativeTypedTree.NativeTypes

let classify = function
    | "op_Addition" -> Some NumericOperationKind.Add
    | "op_Subtraction" -> Some NumericOperationKind.Subtract
    | "op_Multiply" -> Some NumericOperationKind.Multiply
    | "op_Division" -> Some NumericOperationKind.Divide
    | "op_Modulus" -> Some NumericOperationKind.Remainder
    | "op_BitwiseAnd" -> Some NumericOperationKind.BitAnd
    | "op_BitwiseOr" -> Some NumericOperationKind.BitOr
    | "op_ExclusiveOr" -> Some NumericOperationKind.BitXor
    | "op_LeftShift" -> Some NumericOperationKind.ShiftLeft
    | "op_RightShift" -> Some NumericOperationKind.ShiftRight
    | "op_Equality" -> Some NumericOperationKind.Equal
    | "op_Inequality" -> Some NumericOperationKind.NotEqual
    | "op_LessThan" -> Some NumericOperationKind.Less
    | "op_LessThanOrEqual" -> Some NumericOperationKind.LessOrEqual
    | "op_GreaterThan" -> Some NumericOperationKind.Greater
    | "op_GreaterThanOrEqual" -> Some NumericOperationKind.GreaterOrEqual
    | "op_UnaryNegation" -> Some NumericOperationKind.Negate
    | "op_LogicalNot" -> Some NumericOperationKind.Complement
    | "op_UnaryPlus" -> Some NumericOperationKind.Identity
    | "not" -> Some NumericOperationKind.LogicalNot
    | _ -> None

let comparison = function
    | NumericOperationKind.Equal | NumericOperationKind.NotEqual | NumericOperationKind.Less
    | NumericOperationKind.LessOrEqual | NumericOperationKind.Greater | NumericOperationKind.GreaterOrEqual -> true
    | _ -> false

let arity = function
    | NumericOperationKind.Negate | NumericOperationKind.Complement | NumericOperationKind.Identity | NumericOperationKind.LogicalNot -> 1
    | _ -> 2

/// Identity-preserving wrappers participate in the one source operation row.
/// The complete source snapshot retains membership and absence dependencies.
let operation (graph: SemanticGraph) (node: SemanticNode) =
    let rec resolve seen id arguments =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Application(callee, actuals) } -> resolve seen callee (actuals @ arguments)
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
        | Some { Kind = SemanticKind.VarRef(_, Some inner) } -> resolve seen inner arguments
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [inner] } -> resolve seen inner arguments
        | Some { Kind = SemanticKind.Intrinsic info } when info.Module = IntrinsicModule.Operators ->
            classify info.Operation |> Option.map (fun kind -> id, kind, arguments, seen)
        | _ -> None
    match node.Kind with
    | SemanticKind.Application(callee, _) -> resolve Set.empty node.Id [] |> Option.map (fun (_, kind, actuals, identities) -> callee, kind, actuals, identities)
    | _ -> None

let proofOutcome = function
    | ObligationBody.IntegerDivisorNonzero(lo, hi) -> lo <= hi && (hi < 0I || lo > 0I)
    | ObligationBody.IntegerShiftCount(lo, hi, bits) -> bits > 0 && 0I <= lo && lo <= hi && hi < bigint bits
    | body -> StringBytes.proofOutcome body = BoundaryProofOutcome.Proven

let operationRow (operation: NumericOperationWitness) =
    NumericValues.row (EdgeRole.NumericOperation operation)
        (operation.Callee :: (operation.Operands |> List.map _.Actual) @ Set.toList operation.Participants) operation.Site
let proofRows (proof: NumericOperationProof) =
    let sources = proof.Site :: Set.toList proof.Participants
    [ NumericValues.row (EdgeRole.NumericOperationProof proof) sources proof.Obligation
      { Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = 0; Sources = sources; Target = proof.Obligation }
      { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = sources; Target = proof.Obligation } ]

let meets (operation: NumericOperationWitness) =
    (operation.Operands |> List.choose _.Adaptation) @ Option.toList operation.ResultAdaptation |> List.distinct

/// Bind proof propositions to the published operation's exact scalar facts.
/// This performs no representation selection and never recovers source types.
let requiredBodies (operation: NumericOperationWitness) =
    let bounded = function ValueRange.Bounded(lo, hi) when lo <= hi -> Some(lo, hi) | _ -> None
    let bits = function SettledSlot.Integer(bits, _) -> Some bits | SettledSlot.Bool -> Some 1 | SettledSlot.Char -> Some 32 | _ -> None
    match operation.Form with
    | NumericOperationForm.Unit | NumericOperationForm.OpaqueReference -> Some []
    | NumericOperationForm.Real -> None
    | NumericOperationForm.Integer _ | NumericOperationForm.Boolean ->
        match operation.Range |> Option.bind bounded, operation.OperationCarrier |> Option.bind bits with
        | Some(lo, hi), Some width when width > 0 ->
            let capacity =
                match operation.Representation with
                | Some representation -> Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange representation
                | None -> Some(if lo >= 0I then ValueRange.unsignedOf width else ValueRange.twosComplement width)
            let precondition =
                match operation.Kind with
                | NumericOperationKind.Divide | NumericOperationKind.Remainder | NumericOperationKind.ShiftLeft | NumericOperationKind.ShiftRight ->
                    operation.Operands |> List.tryItem 1 |> Option.bind _.Carrier |> Option.bind (fun carrier -> bounded carrier.Range)
                    |> Option.map (fun (lower, upper) ->
                        if operation.Kind = NumericOperationKind.Divide || operation.Kind = NumericOperationKind.Remainder then
                            [ObligationBody.IntegerDivisorNonzero(lower, upper)]
                        else [ObligationBody.IntegerShiftCount(lower, upper, width)])
                | _ -> Some []
            match capacity |> Option.bind bounded, precondition with
            | Some(minimum, maximum), Some precondition -> Some(ObligationBody.IntegerRepresentationCoverage(lo, hi, minimum, maximum) :: precondition)
            | _ -> None
        | _ -> None

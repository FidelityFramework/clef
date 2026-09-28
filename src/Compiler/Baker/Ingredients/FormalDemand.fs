// SPDX-License-Identifier: MIT
/// The calls that reach a closed formal, apart by role. A demanded input is a
/// call that is entered and supplies its actual to the formal. An omission is a
/// resident `OrdinaryUnusedActual` relation whose actual contains a call that
/// reaches the formal; such a call is never entered and supplies no value. The
/// origin enumeration of a string borrow and the array extent reader read this
/// one decision; neither decides the exclusion itself.
module Clef.Compiler.Baker.Ingredients.FormalDemand

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module CallableOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module CallableIngress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress
module OrdinaryDemand = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand

/// A call that reaches a formal: the call, the formal's ordinal at it, and its actual.
type Input = { Call: NodeId; Ordinal: int; Actual: NodeId }

/// Each list is ordered by the identity of the call and then by ordinal.
type Inputs = {
    /// The calls that are entered.
    Demanded: Input list
    /// The omission relations (call, ordinal, omitted actual) under which the
    /// remaining calls are never entered.
    Omissions: OrdinaryOmission list
    /// The calls inside an actual of `Omissions`. Each remains a participant of
    /// a relation over the calls reaching the formal and contributes no value.
    Omitted: Input list
    /// The complete ingress of the formal (`CallableIngress.closedFormalInputs`).
    Participants: Set<NodeId>
}

/// The inputs of each closed formal. A call of the formal is a call of the
/// ingress evidence whose parameters include it; its ordinal is the formal's
/// position there and its actual the argument at that position. Such a call
/// has one argument per parameter: `CallableOrigins.resolve` makes a target
/// only for an exact invocation, with the parameters that remain after an
/// earlier partial application (CallableOrigins.fs lines 265 to 267). The one
/// target with unequal lengths, a lambda without parameters applied to one
/// argument, has no parameter and is not a call of any formal.
let reader (graph: SemanticGraph) (flow: CallableOrigins.Resolution) =
    let formalInputs = CallableIngress.closedFormalInputs graph flow (CallableIngress.analyzeWith graph flow)
    let deferrals = OrdinaryDemand.deferrals graph
    fun formal ->
        formalInputs formal |> Option.map (fun ingress ->
            let inputs =
                ingress.Closure.Calls |> List.collect (fun call ->
                    call.Parameters |> List.indexed |> List.choose (fun (ordinal, parameter) ->
                        if parameter = formal then Some { Call = call.Site; Ordinal = ordinal; Actual = call.Arguments[ordinal] } else None))
                |> Set.ofList
            let omitted, demanded = inputs |> Set.partition (fun input -> deferrals.ContainsKey input.Call)
            { Demanded = Set.toList demanded
              Omissions = omitted |> Seq.collect (fun input -> deferrals[input.Call]) |> Set.ofSeq |> Set.toList
              Omitted = Set.toList omitted
              Participants = ingress.Participants })

/// The nodes of the omission relations (call and omitted actual of each),
/// which a relation over the calls reaching the formal takes as participants.
let premises (inputs: Inputs) =
    inputs.Omissions |> List.collect (fun omission -> [omission.Site; omission.Actual]) |> Set.ofList

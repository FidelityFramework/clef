// SPDX-License-Identifier: MIT
/// The occurrences of a relation over nodes, each with its role, its ordinal and its
/// group (`Participant`). The string borrow rows state their participants in this form.
module Clef.Compiler.Baker.Ingredients.Participants

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module CallableOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins

let occurrence node role ordinal group : Participant = { Node = node; Role = role; Ordinal = ordinal; Group = group }

/// The groups that a formal's inputs state: each demanded input's call and actual, and
/// each omitted input's call and actual with the site and actual of every omission that
/// contains the call, each in the group of its call and at its ordinal. An omission that
/// contains two omitted calls occurs in the group of each. When the formal has an input,
/// the formal's ingress follows in the group of the formal.
let ofInputs (formal: NodeId) (inputs: FormalDemand.Inputs) : Participant list =
    let demanded =
        inputs.Demanded |> List.collect (fun input ->
            [ occurrence input.Call ParticipantRole.ReachingCall input.Ordinal input.Call
              occurrence input.Actual ParticipantRole.ReachingActual input.Ordinal input.Call ])
    let omitted =
        inputs.Omitted |> List.collect (fun omitted ->
            let call = omitted.Input.Call
            [ occurrence call ParticipantRole.OmittedCall omitted.Input.Ordinal call
              occurrence omitted.Input.Actual ParticipantRole.OmittedCallActual omitted.Input.Ordinal call ]
            @ (omitted.Omissions |> List.collect (fun omission ->
                [ occurrence omission.Site ParticipantRole.OmissionSite omission.Ordinal call
                  occurrence omission.Actual ParticipantRole.OmittedActual omission.Ordinal call ])))
    let ingress =
        match demanded @ omitted with
        | [] -> []
        | _ -> inputs.Participants |> Set.toList |> List.map (fun node -> occurrence node ParticipantRole.Ingress 0 formal)
    demanded @ omitted @ ingress

/// The lambdas a call resolves to, each with its body, its arguments and its parameters,
/// in the group of the call; an argument or a parameter at its position.
let ofTargets (call: NodeId) (targets: CallableOrigins.CallTarget list) : Participant list =
    targets |> List.collect (fun target ->
        [ occurrence target.Lambda ParticipantRole.Callee 0 call
          occurrence target.Body ParticipantRole.CalleeBody 0 call ]
        @ (target.Arguments |> List.mapi (fun ordinal argument -> occurrence argument ParticipantRole.CalleeArgument ordinal call))
        @ (target.Parameters |> List.mapi (fun ordinal (_, _, parameter) -> occurrence parameter ParticipantRole.CalleeParameter ordinal call)))

/// The occurrences in their order: the row's own occurrences (the group of `site`) first,
/// then the other groups by node, each with its roles in case order, then by ordinal and
/// node. An occurrence derived twice, with equal node, role, ordinal and group, is one.
let ordered (site: NodeId) (occurrences: Participant list) : Participant list =
    occurrences
    |> List.distinct
    |> List.sortBy (fun occurrence -> occurrence.Group <> site, occurrence.Group, occurrence.Role, occurrence.Ordinal, occurrence.Node)

/// The nodes of the occurrences, in their order.
let nodes (participants: Participant list) : NodeId list =
    participants |> List.map _.Node

/// The participants of an established relation. A pending relation states none.
let established (evidence: ParticipantEvidence) : Result<Participant list, string> =
    match evidence with
    | ParticipantEvidence.Established participants -> Ok participants
    | ParticipantEvidence.Pending _ -> Error "The string borrow participants are pending."

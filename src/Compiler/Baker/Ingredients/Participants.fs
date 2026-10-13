// SPDX-License-Identifier: MIT
/// The occurrences of a relation over nodes, each with its role, its ordinal and its
/// group (`Participant`). The string borrow rows state their participants in this form.
module Clef.Compiler.Baker.Ingredients.Participants

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module CallableOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins

let occurrence node role ordinal group : Participant = { Node = node; Role = role; Ordinal = ordinal; Group = group }

/// The groups that a formal's inputs state: each demanded input's call and actual, and
/// each omitted input's call and actual with the site of every omission that contains the
/// call, each in the group of its call and at its ordinal. The omitted actual of an
/// omission is in the group of the omission's site, at the omission's ordinal, so the
/// site and ordinal name the omission and its actual. An omission that contains two
/// omitted calls names its site in the group of each and its actual once. When the
/// formal has an input, the formal's ingress follows in the group of the formal.
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
                match omission.Origin with
                | OrdinaryOmissionOrigin.CallArgument ordinal ->
                    [ occurrence omission.Site ParticipantRole.OmissionSite ordinal call
                      occurrence omission.Actual ParticipantRole.OmittedActual ordinal omission.Site ]
                | OrdinaryOmissionOrigin.BindingInitializer ->
                    [ occurrence omission.Site ParticipantRole.OmissionBinding 0 call
                      occurrence omission.Actual ParticipantRole.OmittedInitializer 0 omission.Site ])))
    let ingress =
        match demanded @ omitted with
        | [] -> []
        | _ -> inputs.Participants |> Set.toList |> List.map (fun node -> occurrence node ParticipantRole.Ingress 0 formal)
    // Origin enumeration consumed these memoization protocols to close its
    // callers, even when the actual string itself is a plain literal. This
    // marker activates the exact whole-graph relation/root snapshot; the
    // navigation participants above are not a selective proof/cache key.
    let lazyIngress = inputs.UsedLazyForces |> Set.toList |> List.map (fun site ->
        occurrence site ParticipantRole.LazyStringOrigin 0 formal)
    demanded @ omitted @ ingress @ lazyIngress

/// A call whose targets the participant form cannot state (`ofTargets`).
[<RequireQualifiedAccess>]
type TargetFailure =
    /// A target of the call with a number of arguments other than its number of remaining parameters.
    | UnequalCounts of call: NodeId * target: NodeId * arguments: int * parameters: int
    /// Targets of the call whose argument or parameter lists differ.
    | DifferentLists of call: NodeId

/// The lambdas a call resolves to, each in the group of the call, and each lambda's body in
/// the group of that lambda. The call's arguments and the parameters that remain for the
/// call (CallableOrigins.fs lines 263 to 267) are in the group of the call, each at its
/// position. The group of a call states one argument list and one parameter list: a call
/// whose targets do not have the same argument nodes and the same parameter nodes in the
/// same order cannot be stated, and the result is `DifferentLists`. Two different lambdas
/// have different parameters, so a call that resolves to two of them is such a case; the
/// source call `(pick true) "hello"` of a `pick` that returns one of two functions of one
/// string is one. The resolver makes a target for an exact invocation only, with as many
/// remaining parameters as the call has arguments; a target with other counts, a lambda
/// without parameters applied to one argument, is `UnequalCounts`.
let ofTargets (call: NodeId) (targets: CallableOrigins.CallTarget list) : Result<Participant list, TargetFailure> =
    let positions (target: CallableOrigins.CallTarget) = target.Arguments, target.Parameters |> List.map (fun (_, _, parameter) -> parameter)
    match targets |> List.filter (fun target -> target.Arguments.Length <> target.Parameters.Length), targets |> List.map positions |> List.distinct with
    | target :: _, _ ->
        Error (TargetFailure.UnequalCounts(call, target.Lambda, target.Arguments.Length, target.Parameters.Length))
    | [], _ :: _ :: _ -> Error (TargetFailure.DifferentLists call)
    | [], lists ->
        Ok ((lists |> List.collect (fun (arguments, parameters) ->
                (arguments |> List.mapi (fun ordinal argument -> occurrence argument ParticipantRole.CalleeArgument ordinal call))
                @ (parameters |> List.mapi (fun ordinal parameter -> occurrence parameter ParticipantRole.CalleeParameter ordinal call))))
            @ (targets |> List.collect (fun target ->
                [ occurrence target.Lambda ParticipantRole.Callee 0 call
                  occurrence target.Body ParticipantRole.CalleeBody 0 target.Lambda ])))

/// The nodes a failure names: the call, and the target whose counts differ.
let failureNodes (failure: TargetFailure) : NodeId list =
    match failure with
    | TargetFailure.UnequalCounts(call, target, _, _) -> [ call; target ]
    | TargetFailure.DifferentLists call -> [ call ]

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

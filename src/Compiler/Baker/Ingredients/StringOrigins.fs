// SPDX-License-Identifier: MIT
/// Conservative source observations for validated lazy and captured string origins.
/// This records facts; it grants no protocol, residence or borrow proof.
module Clef.Compiler.Baker.Ingredients.StringOrigins

open Microsoft.FSharp.Reflection
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let sourceNode (node: SemanticNode) = not (node.Metadata.ContainsKey "Baker.BoundaryOwned")

let used participants =
    let occurrences =
        match participants with
        | ParticipantEvidence.Established values -> values
        | ParticipantEvidence.Pending early -> early.Derived
    occurrences |> List.exists (fun participant ->
        participant.Role = ParticipantRole.LazyStringOrigin || participant.Role = ParticipantRole.CapturedStringOrigin)

/// The complete recorded incidence census, including duplicates and extra
/// consumers, plus every provenance/demand relation read by the origin readers.
/// Payload-bearing roles are explicitly typed; an unexpected incidence payload
/// cannot be reduced to its name. Only explicitly marked derivations invoke it.
let relations (graph: SemanticGraph) : Result<StringOriginRelation list, string> =
    let selected = function
        | EdgeRole.LazyInstance | EdgeRole.LazyMemoization | EdgeRole.LazyResultDestination
        | EdgeRole.CaptureReferenceOrigin | EdgeRole.EnvironmentFormal | EdgeRole.CaptureOrigin
        | EdgeRole.EnvironmentResultDestination | EdgeRole.CallableReferenceOrigin
        | EdgeRole.SequenceCaptureFormation
        | EdgeRole.ContinuationSlotAccess | EdgeRole.ContinuationValue | EdgeRole.SuspensionLiveAcross
        | EdgeRole.OrdinaryUnusedFormal | EdgeRole.OrdinaryUnusedActual | EdgeRole.EnrichedWith
        | EdgeRole.ProgramInitialization | EdgeRole.ProgramEntryCall | EdgeRole.ProgramInitializer
        | EdgeRole.ProgramValue | EdgeRole.ProgramValueIntent -> true
        | _ -> false
    let observed =
        (graph.Edges |> List.map (fun edge -> true, edge)) @
        (graph.Nodes.Values |> Seq.filter sourceNode |> Seq.collect Closures.structuralIncidence
         |> Seq.map (fun edge -> false, edge) |> Seq.toList)
    observed |> List.fold (fun state (recorded, edge) ->
        let owned = graph.Nodes.TryFind edge.Target |> Option.exists (sourceNode >> not)
        let incidence = edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference
        let flavor =
            if owned then Ok None else
            match edge.Role with
            | EdgeRole.LazyCapture value -> Ok (Some(StringOriginRelationKind.LazyCapture value))
            | EdgeRole.EnvironmentCapture value -> Ok (Some(StringOriginRelationKind.EnvironmentCapture value))
            | EdgeRole.SequenceCaptureInitializer value -> Ok (Some(StringOriginRelationKind.SequenceCaptureInitializer value))
            | EdgeRole.EagerDemand value -> Ok (Some(StringOriginRelationKind.EagerDemand value))
            | EdgeRole.BoundaryDeclaration value -> Ok (Some(StringOriginRelationKind.BoundaryImplementation value.Implementation))
            | EdgeRole.ContinuationCase value when incidence -> Ok (Some(StringOriginRelationKind.ContinuationCase value))
            | role when not recorded || incidence || selected role ->
                let case, fields = FSharpValue.GetUnionFields(role, typeof<EdgeRole>)
                if fields.Length = 0 then Ok (Some(StringOriginRelationKind.Named case.Name))
                else Error ("A string origin has an unsupported recorded incidence payload: " + case.Name + ".")
            | _ -> Ok None
        match state, flavor with
        | Error reason, _ | _, Error reason -> Error reason
        | Ok rows, Ok None -> Ok rows
        | Ok rows, Ok (Some flavor) ->
            Ok ({ Recorded = recorded; Class = edge.Class; Flavor = flavor; Ordinal = edge.Ordinal
                  Sources = edge.Sources; Target = edge.Target } :: rows)) (Ok [])
    |> Result.map List.rev

// The complete source-node census is BoundaryDomain.Premises. These ordered
// relations and DeclarationRoots supplement that joint premise, including its
// negative dependencies. A view retains its actual derivation occurrences and
// explicit origin marker; repeating the global census in early participants
// would accidentally depend on later numeric/memory proof-node allocation.

// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Local source-demand relations. Each relation is conditional on activation of
/// its own target; no recursive search enters arguments, branches or deferred
/// bodies looking for work to execute. Value dependencies remain graph citizens.
module Clef.Compiler.Baker.Recipes.EagerDemandRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Explicit = Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module Carriers = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers

type Inputs = {
    Boundaries: Lazy<Map<NodeId, Origins.FirstBoundary>>
    Environments: Lazy<Map<NodeId, int * NodeId>>
    Known: Lazy<NodeId -> KnownCallable option>
    Environmental: Lazy<Set<NodeId>>
    Destinations: Lazy<Map<NodeId, Set<NodeId>>>
}

let inputs (graph: SemanticGraph) =
    { Boundaries = lazy ((Origins.resolve graph).FirstBoundaries)
      Environments = lazy (Environments.callEnvironments graph)
      Known = lazy (Environments.tryKnown graph)
      Environmental = lazy (
          let owners = graph.Nodes.Values |> Seq.choose (fun node ->
              match node.Kind with SemanticKind.ClosureValue(code, _) when node.IsReachable -> Some code | _ -> None)
          let rows = graph.Edges |> Seq.choose (fun edge ->
              if edge.Role = EdgeRole.EnvironmentFormal then List.tryLast edge.Sources else None)
          Seq.append owners rows |> Set.ofSeq)
      Destinations = lazy (
          graph.Nodes.Values |> Seq.choose (fun node ->
              match node.Kind with
              | SemanticKind.Lambda(_, body, _, _, _) -> Some(node.Id, Carriers.resultDestinations graph node.Id body)
              | _ -> None) |> Map.ofSeq) }

let private edge owner role ordinal sources : Hyperedge =
    { Sources = sources; Target = owner; Class = EdgeClass.Demand
      Role = role; Ordinal = ordinal }

let forNode (graph: SemanticGraph) (inputs: Inputs) (node: SemanticNode) : Enrichment =
    let resident id = graph.Nodes.TryFind id |> Option.exists _.IsReachable
    let pending ordinal participants =
        edge node.Id EdgeRole.EagerDemandPending ordinal
            (participants |> List.filter graph.Nodes.ContainsKey |> List.distinct)
    let frontiers frontier authority values =
        values |> List.mapi (fun ordinal value ->
            match Explicit.direct graph value with
            | Ok (Some marker) ->
                let sourceOrdinal, admitted, extra = authority ordinal
                let participants = [marker.Marker; marker.Operand] @ marker.Wrappers @ extra
                if admitted && (extra |> List.forall resident) then
                    [edge node.Id (EdgeRole.EagerDemand frontier) sourceOrdinal participants]
                else [pending sourceOrdinal participants]
            | Ok None -> []
            | Error participants ->
                let sourceOrdinal, _, extra = authority ordinal
                [pending sourceOrdinal (participants @ extra)])
        |> List.concat
    let direct frontier = frontiers frontier (fun ordinal -> ordinal, true, [])
    let actuals callee values =
        // Code identity is only one component of an elaborated captured call.
        // The actual callable formation must precede its explicit eager actuals;
        // demanding a generated code reference alone does not establish that.
        let sourceSignaturesAgree (hidden: Set<int>) =
            match inputs.Boundaries.Value.TryFind node.Id with
            | Some boundary -> boundary.Targets |> List.forall (fun target ->
                match graph.Nodes.TryFind target.Lambda with
                | Some { Kind = SemanticKind.Lambda(_, body, _, _, _); Metadata = metadata } ->
                    match metadata.TryFind ClosureMetadata.SourceSignature, graph.Nodes.TryFind body with
                    | Some(MetadataValue.Type declared), Some result ->
                        let destinations = inputs.Destinations.Value.TryFind target.Lambda |> Option.defaultValue Set.empty
                        let visible = target.Parameters |> List.indexed |> List.choose (fun (index, parameter) ->
                            let _, _, formal = parameter
                            if destinations.Contains formal || hidden.Contains(index - target.Offset) then None else Some parameter)
                        let logical = List.foldBack (fun (_, ty, _) result -> NativeType.TFun(ty, result)) visible result.Type
                        applySubst logical = applySubst declared
                    | None, _ -> true
                    | _ -> false
                | _ -> false)
            | _ -> false
        let callContext = lazy (
            match inputs.Boundaries.Value.TryFind node.Id with
            | Some boundary when boundary.Callee = callee ->
                let resultPositions = boundary.Targets |> List.map (fun target ->
                    let hidden = inputs.Destinations.Value.TryFind target.Lambda |> Option.defaultValue Set.empty
                    target.Parameters |> List.indexed |> List.choose (fun (index, (_, _, formal)) ->
                        if index >= target.Offset && hidden.Contains formal then Some(index - target.Offset) else None)
                    |> Set.ofList)
                let commonResults =
                    match List.distinct resultPositions with [] -> Some Set.empty | [positions] -> Some positions | _ -> None
                let needsEnvironment =
                    (boundary.Targets |> List.exists (fun target -> inputs.Environmental.Value.Contains target.Lambda)) ||
                    (values |> List.exists (fun value ->
                        match graph.Nodes.TryFind value with Some { Kind = SemanticKind.EnvironmentReference _ } -> true | _ -> false))
                match commonResults, needsEnvironment, inputs.Environments.Value.TryFind node.Id with
                | Some hidden, false, None -> sourceSignaturesAgree hidden, hidden, [callee]
                | Some hidden, true, Some(ordinal, environment) ->
                    match graph.Nodes.TryFind environment with
                    | Some { Kind = SemanticKind.EnvironmentReference logical; Children = [actual]; Type = ty }
                        when actual = logical && applySubst ty = Environments.environmentType ->
                        match inputs.Known.Value logical with
                        | Some known when not boundary.Targets.IsEmpty && boundary.UnknownOrigins.IsEmpty &&
                                          boundary.Targets |> List.forall (fun target -> target.Lambda = known.Implementation && target.Offset = 0) ->
                            let rows = graph.Edges |> List.filter (fun edge ->
                                edge.Role = EdgeRole.EnvironmentFormal && edge.Sources = [known.EnvironmentOwner; known.Implementation])
                            match rows with
                            | [{ Class = EdgeClass.Provenance; Target = formal }] ->
                                let hidden = Set.add ordinal hidden
                                sourceSignaturesAgree hidden, hidden, [known.EnvironmentOwner; formal; callee; environment; logical]
                            | _ -> false, hidden, [callee; environment; logical]
                        | _ -> false, hidden, [callee; environment; logical]
                    | _ -> false, hidden, [callee; environment]
                | _ -> false, defaultArg commonResults Set.empty, callee :: values
            | _ -> false, Set.empty, [callee])
        let authority ordinal =
            match graph.Nodes.TryFind callee, inputs.Boundaries.Value.TryFind node.Id with
            | Some calleeNode, Some boundary when boundary.Callee = callee && calleeNode.IsReachable ->
                let participants =
                    (boundary.Targets |> List.collect (fun target ->
                        let body =
                            match graph.Nodes.TryFind target.Lambda with
                            | Some { Kind = SemanticKind.Lambda(_, body, _, _, _); Metadata = metadata }
                                when metadata.ContainsKey ClosureMetadata.SourceSignature -> [body]
                            | _ -> []
                        target.Lambda :: ((target.Parameters |> List.map (fun (_, _, id) -> id)) @ body)))
                    @ Set.toList boundary.UnknownOrigins |> List.distinct
                let counts = boundary.Targets |> List.map _.Remaining
                // The outer callable type admits one logical actual even when
                // its implementation is opaque. It does not reveal later
                // declared boundaries by counting function arrows.
                let counts =
                    if boundary.UnknownOrigins.IsEmpty then counts else
                    match applySubst calleeNode.Type with
                    | NativeType.TFun _ -> 1 :: counts
                    | _ -> 0 :: counts
                let formation, hidden, formationParticipants = callContext.Value
                let sourceOrdinal = ordinal - (hidden |> Set.filter (fun index -> index < ordinal) |> Set.count)
                let admitted = formation && not (hidden.Contains ordinal) && not counts.IsEmpty && ordinal < List.min counts
                sourceOrdinal, admitted, (participants |> List.filter (fun id -> not (List.contains id formationParticipants))) @ formationParticipants
            | _ -> ordinal, false, [callee]
        frontiers EagerFrontier.Actual authority values
    let edges =
        match node.Kind with
        | SemanticKind.EagerExpr _ -> direct EagerFrontier.Expression [node.Id]
        | SemanticKind.Binding _ ->
            match List.tryLast node.Children with
            | Some value -> direct EagerFrontier.Binding [value]
            | None -> []
        | SemanticKind.Application(callee, arguments) -> actuals callee arguments
        | SemanticKind.TupleExpr components | SemanticKind.ArrayExpr components
        | SemanticKind.ListExpr components -> direct EagerFrontier.Component components
        | SemanticKind.RecordExpr(fields, _) -> direct EagerFrontier.Component (List.map snd fields)
        | SemanticKind.UnionCase(_, _, payload) | SemanticKind.DUConstruct(_, _, payload, _) ->
            direct EagerFrontier.Component (Option.toList payload)
        | _ -> []
    { Enrichment.empty with NewEdges = edges }

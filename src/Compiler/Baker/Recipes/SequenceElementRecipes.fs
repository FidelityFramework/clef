// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Joint element incidence for admitted current reads. The range solver reads
/// these source identities in its own fixed point; this recipe assigns no range.
module Clef.Compiler.Baker.Recipes.SequenceElementRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins

let elaborate (graph: SemanticGraph) : Hyperedge list =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let _, origins = Origins.settle graph graph.Codata.Value.Curry
    let edge role sources target =
        { Class = EdgeClass.Suspension; Role = role; Sources = sources; Target = target; Ordinal = 0 }
    let rec intrinsic seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Intrinsic info } -> Some info
        | Some { Kind = SemanticKind.VarRef (_, Some source) }
        | Some { Kind = SemanticKind.TypeAnnotation (source, _) } -> intrinsic seen source
        | Some { Kind = SemanticKind.Binding (_, false, _, _); Children = [source] } -> intrinsic seen source
        | _ -> None
    let payloads owner =
        match nodes.TryFind owner with
        | Some { Kind = SemanticKind.SeqExpr (generator, _) } ->
            match nodes.TryFind generator with
            | Some { Kind = SemanticKind.Lambda (_, _, _, _, LambdaContext.SeqGenerator) } ->
                let sites = graph.Edges |> List.filter (fun item ->
                    item.Class = EdgeClass.Suspension && item.Role = EdgeRole.Delimiter
                    && item.Sources = [owner; generator])
                let values = sites |> List.choose (fun item ->
                    match nodes.TryFind item.Target with
                    | Some { Kind = SemanticKind.Yield payload } when nodes.ContainsKey payload -> Some payload
                    | _ -> None)
                if values.Length = sites.Length then Some (List.distinct values) else None
            | _ -> None
        | _ -> None
    graph.Edges |> List.collect (fun certificate ->
        match certificate.Class, certificate.Role, certificate.Sources, nodes.TryFind certificate.Target with
        | EdgeClass.Suspension, EdgeRole.IteratorCurrentAdmitted, [enumerator; guard; loop],
          Some { Kind = SemanticKind.Application (callee, [iterator]) }
            when [enumerator; guard; loop] |> List.forall nodes.ContainsKey ->
            match intrinsic Set.empty callee, nodes.TryFind iterator with
            | Some { Module = IntrinsicModule.SeqEnumerator; Operation = "current" },
              Some { Kind = SemanticKind.VarRef (_, Some actual) } when actual = enumerator ->
                let target = certificate.Target
                let unknown site = edge EdgeRole.SequenceElementUnknown [iterator; site] target
                let facts =
                    match origins.TryFind iterator with
                    | Some facts when not facts.IsEmpty ->
                        facts |> Set.toList |> List.collect (function
                            | Origins.Origin.Unknown site -> [unknown site]
                            | Origins.Origin.Known owner ->
                                let known = edge EdgeRole.SequenceElementOwner [iterator; owner] target
                                match payloads owner with
                                | Some values -> known :: (values |> List.map (fun payload ->
                                    edge EdgeRole.SequenceElementPayload [owner; payload] target))
                                | None -> [known; unknown owner])
                    | _ -> [unknown iterator]
                edge EdgeRole.SequenceElementAdmission certificate.Sources target :: facts
            | _ -> []
        | _ -> [])

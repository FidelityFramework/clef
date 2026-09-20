// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Iterator source effects depend on complete finite origin incidence. Pulls
/// invoke their possible generator bodies; fresh acquisition does not. Operand
/// evaluation remains ordinary structural evaluation in the caller.
module Clef.Compiler.Baker.Recipes.SequenceEffectRecipes

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
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> intrinsic seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [source] } -> intrinsic seen source
        | _ -> None
    nodes.Values |> Seq.collect (fun node ->
        match node.Kind with
        | SemanticKind.Application(callee, [operand]) ->
            match intrinsic Set.empty callee with
            | Some ({ Module = IntrinsicModule.Seq; Operation = "getEnumerator" } as info)
            | Some ({ Module = IntrinsicModule.SeqEnumerator; Operation = "moveNext" } as info) ->
                let pulling = info.Module = IntrinsicModule.SeqEnumerator
                let unknown site = edge EdgeRole.SequenceEffectUnknown [operand; site] node.Id
                match origins.TryFind operand with
                | Some alternatives when not alternatives.IsEmpty ->
                    alternatives |> Set.toList |> List.collect (function
                        | Origins.Origin.Unknown site -> [unknown site]
                        | Origins.Origin.Known owner ->
                            match nodes.TryFind owner with
                            | Some { Kind = SemanticKind.SeqExpr(generator, _) } ->
                                match nodes.TryFind generator with
                                | Some { Kind = SemanticKind.Lambda(_, body, _, _, LambdaContext.SeqGenerator) } when nodes.ContainsKey body ->
                                    if pulling then [edge EdgeRole.SequencePullBody [operand; owner; generator; body] node.Id]
                                    else [edge EdgeRole.SequenceInitialize [operand; owner; generator] node.Id]
                                | _ -> [unknown owner]
                            | _ -> [unknown owner])
                | _ -> [unknown operand]
            | _ -> []
        | _ -> []) |> Seq.toList

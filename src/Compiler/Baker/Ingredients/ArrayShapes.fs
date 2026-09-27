// SPDX-License-Identifier: MIT
/// Exact array extent dependencies. Counts remain source operands; ranges only
/// enclose their values and never replace a descriptor's runtime extent.
module Clef.Compiler.Baker.Ingredients.ArrayShapes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module Ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress
module Boundaries = Clef.Compiler.Baker.Recipes.BoundaryDeclarations

[<RequireQualifiedAccess>]
type Length = Constant of bigint | Count of NodeId
type Extent = { Sources:Length list; StringSources:Set<NodeId>; Participants:Set<NodeId> }

let intrinsicApplication (graph:SemanticGraph) start =
    let rec follow seen id arguments =
        if Set.contains id seen then None else
        let seen=Set.add id seen
        match graph.Nodes.TryFind id with
        | Some {Kind=SemanticKind.Application(callee,actuals)} -> follow seen callee (actuals@arguments)
        | _ ->
            match Boundaries.target graph id with
            | Some({Kind=SemanticKind.Intrinsic info},path) -> Some(info,arguments,Set.union seen path)
            | _ -> None
    follow Set.empty start []

let reader (graph:SemanticGraph) =
    let flow=Origins.resolve graph
    let ingress=Ingress.analyzeWith graph flow
    let formalInputs=Ingress.closedFormalInputs graph flow ingress
    let combine values =
        if List.isEmpty values || values |> List.exists Option.isNone then None else
        let values=List.choose id values
        Some { Sources=values |> List.collect _.Sources; StringSources=values |> List.map _.StringSources |> Set.unionMany
               Participants=values |> List.map _.Participants |> Set.unionMany }
    let rec follow seen id =
        if Set.contains id seen then None else
        let seen=Set.add id seen
        let add (value:Extent option)=value |> Option.map(fun value -> {value with Participants=Set.add id value.Participants})
        let constant value=Some {Sources=[Length.Constant value];StringSources=Set.empty;Participants=Set.singleton id}
        let count value=Some {Sources=[Length.Count value];StringSources=Set.empty;Participants=Set.ofList[id;value]}
        match graph.Nodes.TryFind id with
        | Some {Kind=SemanticKind.Literal(NativeLiteral.String text)} ->
            constant(bigint(System.Text.Encoding.UTF8.GetByteCount text)) |> Option.map(fun extent -> {extent with StringSources=Set.singleton id})
        | Some {Kind=SemanticKind.ArrayExpr values} -> constant(bigint values.Length)
        | Some {Kind=SemanticKind.ArrayAllocate value} -> count value
        | Some {Kind=SemanticKind.VarRef(_,Some value) | SemanticKind.TypeAnnotation(value,_) | SemanticKind.EagerExpr value} -> follow seen value |> add
        | Some {Kind=SemanticKind.Binding(_,false,_,_);Children=[value]} -> follow seen value |> add
        | Some {Kind=SemanticKind.Sequential values} -> List.tryLast values |> Option.bind(follow seen) |> add
        | Some {Kind=SemanticKind.IfThenElse(_,yes,Some no)} -> combine[follow seen yes;follow seen no] |> add
        | Some {Kind=SemanticKind.PatternBinding _} ->
            match formalInputs id with
            | Some ingress ->
                ingress.Inputs |> List.map(fun (site,value) -> follow seen value |> Option.map(fun extent ->
                    {extent with Participants=Set.union ingress.Participants (extent.Participants.Add site)})) |> combine |> add
            | _ -> None
        | Some {Kind=SemanticKind.Application _} ->
            match intrinsicApplication graph id with
            | Some({Module=IntrinsicModule.Array;Operation=("zeroCreate"|"create"|"init")},value::_,_) -> count value
            | Some({Module=IntrinsicModule.Array;Operation="sub"},[_;_;value],_) -> count value
            | Some({Module=IntrinsicModule.String;Operation="toBytes"},[source],_) ->
                follow seen source |> add
            | Some({Module=IntrinsicModule.String;Operation="fromBytes"},[snapshot],_) ->
                let rows=graph.Edges |> List.filter(fun edge ->
                    edge.Role=EdgeRole.StringByteSnapshot &&
                    (match edge.Sources with [_;copy] -> copy=snapshot | _ -> false))
                match rows with
                | [row] -> follow seen snapshot |> Option.map(fun extent ->
                    {extent with StringSources=Set.singleton id; Participants=Set.union extent.Participants (Set.ofList(id::row.Target::row.Sources))})
                | _ -> None
            | _ ->
                match flow.Calls.TryFind id with
                | Some {Complete=true;Unknown=false;Targets=targets} when not targets.IsEmpty ->
                    targets |> List.map(fun target -> follow seen target.Body |> Option.map(fun extent ->
                        {extent with Participants=Set.union extent.Participants (Set.ofList(target.Lambda::target.Body::target.Arguments))})) |> combine |> add
                | _ -> None
        | Some {Kind=SemanticKind.StringByteBorrow source} ->
            follow seen source |> add
        | _ -> None
    follow Set.empty

let observations (graph:SemanticGraph) =
    let read=reader graph
    graph.Nodes |> Map.fold(fun values id node ->
        let source=
            match node.Kind with
            | SemanticKind.FieldGet(buffer,"Length") -> Some buffer
            | SemanticKind.Application _ ->
                match intrinsicApplication graph id with
                | Some({Module=IntrinsicModule.Array | IntrinsicModule.String;Operation="length"},[buffer],_) -> Some buffer
                | _ -> None
            | _ -> None
        source |> Option.bind read |> Option.map(fun extent -> Map.add id extent values) |> Option.defaultValue values) Map.empty

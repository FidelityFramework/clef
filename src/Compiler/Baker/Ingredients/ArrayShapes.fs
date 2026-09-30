// SPDX-License-Identifier: MIT
/// Exact array extent dependencies. Counts remain source operands; ranges only
/// enclose their values and never replace a descriptor's runtime extent.
module Clef.Compiler.Baker.Ingredients.ArrayShapes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
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

/// Source-only logical extent, not byte storage, immutable residency or a borrow.
/// A private inline constant array has no intervening writes. Its whole UTF-8
/// payload must be valid; the descriptor length counts bytes, not characters.
/// The consumer/absence census is reread from the current graph. Participants
/// are direct support, not a sufficient key for selective proof reuse.
let private inlineStringExtent (graph:SemanticGraph) site input =
    let arrayType = NativeType.TApp(Types.arrayTyCon, [Types.intType])
    let live id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
    let sourceEdge (edge:Hyperedge) = edge.Class=EdgeClass.Structural || edge.Class=EdgeClass.Reference
    let key (edge:Hyperedge) = edge.Class,edge.Role,edge.Ordinal,edge.Target,edge.Sources
    let intact (node:SemanticNode) =
        let actual = graph.Edges |> List.filter (fun edge -> edge.Target=node.Id && sourceEdge edge) |> List.map key |> List.sort
        let expected = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node |> List.filter sourceEdge |> List.map key |> List.sort
        // Native F stores explicit enrichments. Kind/Children provide current
        // syntax incidence; optional recorded copies must be unique and agree.
        actual.Length=(List.distinct actual).Length && List.forall (fun row -> List.contains row expected) actual
    let onlyArgument (edge:Hyperedge) =
        edge.Class=EdgeClass.Structural && edge.Role=EdgeRole.Argument &&
        edge.Ordinal=0 && edge.Target=site && edge.Sources=[input]
    let privateInput () =
        let capturesInput (capture:CaptureInfo) =
            match capture.SourceNodeId with
            | Some source -> source=input
            | None -> applySubst capture.Type=arrayType
        let active = graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.toList
        let uncaptured =
            active |> List.forall (fun node ->
                let captures =
                    match node.Kind with
                    | SemanticKind.Lambda(_,_,captures,_,_)
                    | SemanticKind.LazyExpr(_,captures) | SemanticKind.SeqExpr(_,captures) -> captures
                    | _ -> []
                not (List.exists capturesInput captures))
        let implied =
            active |> List.collect Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence
            |> List.filter (fun edge -> List.contains input edge.Sources)
        let recorded =
            graph.Edges |> List.filter (fun edge ->
                (edge.Class=EdgeClass.Structural || edge.Class=EdgeClass.Reference) &&
                List.contains input edge.Sources && (live edge.Target |> Option.isSome))
        uncaptured && implied.Length=1 && List.forall onlyArgument implied &&
        recorded.Length<=1 && List.forall onlyArgument recorded
    match graph.Platform, live site, live input with
    | None, Some call, Some array when applySubst call.Type=Types.stringType && applySubst array.Type=arrayType ->
        match call.Kind, array.Kind with
        | SemanticKind.Application(callee,[argument]), SemanticKind.ArrayExpr values
            when argument=input && call.Children=[callee;input] && array.Children=values && array.Parent=Some site &&
                 intact call && intact array ->
            match live callee with
            | Some ({Kind=SemanticKind.Intrinsic {Module=IntrinsicModule.String;Operation="fromBytes"};Children=[];Type=ty} as target)
                when applySubst ty=NativeType.TFun(arrayType,Types.stringType) && intact target && privateInput () ->
                let bytes = values |> List.map (fun value ->
                    match live value with
                    | Some ({Kind=SemanticKind.Literal(NativeLiteral.Int(number,kind));Children=[];Parent=Some parent;Type=ty} as literal)
                        when parent=input && applySubst ty=Types.intType &&
                             Some kind=Types.tryGetNTUKind Types.intType && 0L<=number && number<=255L && intact literal -> Some(byte number)
                    | _ -> None)
                if List.exists Option.isNone bytes then None else
                try
                    System.Text.UTF8Encoding(false,true).GetCharCount(bytes |> List.choose id |> List.toArray) |> ignore
                    Some {Sources=[Length.Constant(bigint values.Length)]; StringSources=Set.singleton site
                          Participants=Set.ofList(site::callee::input::values)}
                with :? System.Text.DecoderFallbackException -> None
            | _ -> None
        | _ -> None
    | _ -> None

let reader (graph:SemanticGraph) =
    let flow=Origins.resolve graph
    let inputs=FormalDemand.reader graph flow
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
            match inputs id with
            | Some formal ->
                // A call in an omitted actual supplies no extent; the omission relations that contain it are premises.
                let omitted (input: FormalDemand.OmittedInput) =
                    Some {Sources=[];StringSources=Set.empty;Participants=input.Omissions |> List.collect (fun omission -> [omission.Site;omission.Actual]) |> Set.ofList}
                (formal.Demanded |> List.map(fun input -> input.Call,follow seen input.Actual))
                @ (formal.Omitted |> List.map(fun input -> input.Input.Call,omitted input))
                |> List.map(fun (call,supplied) -> supplied |> Option.map(fun extent ->
                    {extent with Participants=Set.union formal.Participants (extent.Participants.Add call)})) |> combine |> add
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
                | [] -> inlineStringExtent graph id snapshot
                | _ -> None
            | _ ->
                match flow.Calls.TryFind id with
                | Some {Complete=true;Unknown=false;Targets=targets} when not targets.IsEmpty ->
                    targets |> List.map(fun target -> follow seen target.Body |> Option.map(fun extent ->
                        {extent with Participants=Set.union extent.Participants (Set.ofList(target.Lambda::target.Body::target.Arguments))})) |> combine |> add
                | _ -> None
        | Some ({Kind=SemanticKind.StringByteBorrow source} as borrow) ->
            if graph.Platform.IsSome then follow seen source |> add else
            let sourceEdge (edge:Hyperedge) = edge.Class=EdgeClass.Structural || edge.Class=EdgeClass.Reference
            let key (edge:Hyperedge) = edge.Class,edge.Role,edge.Ordinal,edge.Target,edge.Sources
            let actual = graph.Edges |> List.filter (fun edge -> edge.Target=id && sourceEdge edge) |> List.map key |> List.sort
            let expected = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence borrow |> List.filter sourceEdge |> List.map key |> List.sort
            let agrees = actual.Length=(List.distinct actual).Length && List.forall (fun row -> List.contains row expected) actual
            match graph.Nodes.TryFind source with
            | Some value when borrow.IsReachable && value.IsReachable && borrow.Children=[source] && agrees &&
                              borrow.Type=Types.mkArrayType Types.intType && Types.isStringType value.Type ->
                // Reuse the owning source origin contract, including its lazy
                // protocol and complete formal-input validation. No new cache
                // semantics or physical byte-view authority is supplied here.
                match Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigin graph flow id source with
                | Ok(Some(identity,origins,participants)) when not origins.IsEmpty ->
                    Some {Sources=origins.Values |> Seq.map Length.Constant |> Seq.toList
                          StringSources=origins.Keys |> Set.ofSeq
                          Participants=Set.ofList(id::source::identity::(participants |> List.collect (fun p -> [p.Node;p.Group])))}
                | Ok None -> follow seen source |> add
                // An origin error cannot fall back to weaker descriptor flow.
                // StringBorrowRecipes reports that exact error at its own site.
                | Error _ | Ok(Some _) -> None
            | _ -> None
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

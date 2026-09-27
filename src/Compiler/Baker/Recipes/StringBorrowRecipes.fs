// SPDX-License-Identifier: MIT
/// Early source-owned read-only byte views and intrinsic ABI constraints.
module Clef.Compiler.Baker.Recipes.StringBorrowRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph
open Clef.Compiler.Baker.Ingredients.Obligations
module Bytes = Clef.Compiler.Baker.Ingredients.StringBytes

let private stringOrigin = StringComparisonRecipes.stringOrigin

let private scopeOf (graph: SemanticGraph) source =
    let rec follow seen id =
        if Set.contains id seen then None else
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.ModuleDef _ } -> Some id
        | Some { Parent = Some parent } -> follow (Set.add id seen) parent
        | _ -> None
    follow Set.empty source

let private plan enrichId (graph: SemanticGraph) =
    let flow = CallableOrigins.resolve graph
    let representation = Bytes.byteRepresentation graph
    let localOrigin view = StringComparisonRecipes.localView graph view |> Option.map (fun (source,_,participants) ->
        match stringOrigin graph flow source with
        | Some(_,origins,originPremises) -> source,origins,Set.union participants originPremises
        | None -> source,Map.empty,participants)
    let localExtent site =
        StringComparisonRecipes.constructions graph |> List.tryPick (fun construction ->
            let view = if construction.LeftLength=site then Some construction.LeftView elif construction.RightLength=site then Some construction.RightView else None
            view |> Option.bind localOrigin)
        |> Option.orElseWith (fun () ->
            StringComparisonRecipes.lengthConstructions graph |> List.tryPick (fun construction ->
                let source = if construction.LeftLength=site then Some construction.LeftSource elif construction.RightLength=site then Some construction.RightSource else None
                source |> Option.map (fun source ->
                    let origins,originPremises = stringOrigin graph flow source |> Option.map (fun (_,origins,participants) -> origins,participants) |> Option.defaultValue (Map.empty,Set.empty)
                    let participants = Set.union originPremises (Set.ofList(construction.Site::construction.Left::construction.Right::construction.Evidence))
                    source,origins,participants)))
    let extent site source path =
        let identity,origins,participants =
            localExtent site
            |> Option.orElseWith (fun () -> stringOrigin graph flow source)
            |> Option.defaultValue (source,Map.empty,Set.singleton source)
        { Site=site; Source=source; ExtentSource=identity; StaticOrigins=origins
          Participants=Set.unionMany [participants;path;Set.ofList [site;source]] }
    let views = graph.Nodes |> Map.fold (fun enrichment _ node ->
        if not node.IsReachable then enrichment else
        match node.Kind with
        | SemanticKind.FieldGet(source, "Bytes")
        | SemanticKind.StringByteBorrow source when graph.Nodes.TryFind source |> Option.exists (fun source -> Types.isStringType source.Type) ->
            let updated = { node with Kind = SemanticKind.StringByteBorrow source; Children = [source] } |> Elaboration.markBaker "StringByteBorrow" enrichId
            let rows =
                match (localOrigin node.Id |> Option.orElseWith (fun () -> stringOrigin graph flow source)), representation with
                | Some(identity, origins, participants), Some(rep, declaration) ->
                    let view = { Site = node.Id; Source = source; ExtentSource = identity; StaticOrigins = origins
                                 Representation = rep; RepresentationDeclaration = declaration
                                 Participants = Set.union participants (Set.ofList [node.Id; source; declaration]) }
                    [Bytes.viewRow view; Bytes.storageRow view]
                | _ -> []
            let rewrite = { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = [source]; Target = node.Id }
            { enrichment with Annotated = updated :: enrichment.Annotated
                              NewEdges = rows @ [rewrite] @ enrichment.NewEdges }
        | SemanticKind.FieldGet(source, "Length") when graph.Nodes.TryFind source |> Option.exists (fun source -> Types.isStringType source.Type) ->
            { enrichment with NewEdges=Bytes.extentRow (extent node.Id source Set.empty)::enrichment.NewEdges }
        | SemanticKind.Application(callee,[source]) when graph.Nodes.TryFind source |> Option.exists (fun source -> Types.isStringType source.Type) ->
            match BoundaryDeclarations.target graph callee with
            | Some({ Kind=SemanticKind.Intrinsic { Module=IntrinsicModule.String; Operation="length" } },path) ->
                { enrichment with NewEdges=Bytes.extentRow (extent node.Id source path)::enrichment.NewEdges }
            | _ -> enrichment
        | _ -> enrichment) Enrichment.empty
    let declaration =
        let reading = PlatformResolution.read graph
        match reading.Findings, reading.Platform, representation with
        | [], Some platform, Some(rep, representationNode) ->
            match platform.Core, PlatformResolution.syscall graph platform "write", platform.Returns |> List.filter (fun value -> value.Endpoint = "write" && value.AtMost = "count") with
            | Some core, Some endpoint, [result] ->
                match core.Widths |> List.filter (fun width -> width.Name = "Register") with
                | [width] when width.Bits > 0 ->
                    Some(core, endpoint, result, width, rep, Set.ofList [platform.Node; core.Node; endpoint.Node; endpoint.Surface; result.Node; width.Node; representationNode])
                | _ -> None
            | _ -> None
        | _ -> None
    let candidates = graph.Nodes |> Map.toList |> List.choose (fun (_, node) ->
        if not node.IsReachable then None else
        match node.Kind with
        | SemanticKind.Application(callee, [_; _; _]) ->
            match BoundaryDeclarations.target graph callee, scopeOf graph node.Id with
            | Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Sys; Operation = "write" }; Id = identity }, path), Some scope -> Some(node.Id, identity, scope, path)
            | _ -> None
        | _ -> None)
    let imports = candidates |> List.groupBy (fun (_, _, scope, _) -> scope) |> List.map (fun (scope, uses) ->
        scope, uses |> List.map (fun (_, identity, _, _) -> identity) |> List.min) |> Map.ofList
    let paths = candidates |> List.groupBy (fun (_, _, scope, _) -> scope) |> List.map (fun (scope, uses) ->
        scope, uses |> List.map (fun (_, _, _, path) -> path) |> Set.unionMany) |> Map.ofList
    let rows = candidates |> List.choose (fun (site, _, scope, _) ->
        declaration |> Option.map (fun (core, endpoint, result, width, rep, participants) ->
            let identity = imports[scope]
            let import = { Identity = identity; Scope = scope; Symbol = $"__clef_sys_write_{NodeId.value identity}"
                           Fd = BoundaryScalar.Integer(width.Bits, true); Count = BoundaryScalar.Integer(width.Bits, false); Result = BoundaryScalar.Integer(width.Bits, true)
                           ByteRepresentation = rep; Core = core.Node; ReturnContract = result.Node; Endpoint = endpoint.Node; Surface = endpoint.Surface; SyscallNumber = endpoint.Number
                           Participants = Set.unionMany [participants; paths[scope]; Set.ofList [identity; scope]] }
            Bytes.abiRow site import))
    { views with NewEdges = rows @ views.NewEdges }

let elaborate graph = plan (Elaboration.freshId ()) graph

/// The late owner rechecks the same complete source recipe premises after
/// rewriting/placement. Publication never invokes this source reader.
let evidence graph =
    (plan 0 graph).NewEdges |> List.filter (fun edge ->
        match edge.Role with
        | EdgeRole.StringByteView _ | EdgeRole.StringExtent _ | EdgeRole.IntrinsicWriteAbi _ | EdgeRole.StringByteStorage _ -> true
        | _ -> false)

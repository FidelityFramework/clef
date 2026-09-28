// SPDX-License-Identifier: MIT
/// Early source-owned read-only byte views and intrinsic ABI constraints.
module Clef.Compiler.Baker.Recipes.StringBorrowRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph
open Clef.Compiler.Baker.Ingredients.Obligations
module Bytes = Clef.Compiler.Baker.Ingredients.StringBytes
module Participants = Clef.Compiler.Baker.Ingredients.Participants

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
    // Occurrences at ordinal 0 in the group of the row's site: the row's own fields, a
    // callee path and the nodes of a local construction.
    let own site occurrences = occurrences |> List.map (fun (node, role) -> Participants.occurrence node role 0 site)
    let constructed site nodes = own site (nodes |> Set.toList |> List.map (fun node -> node, ParticipantRole.Construction))
    let localOrigin site view = StringComparisonRecipes.localView graph view |> Option.map (fun (source,_,participants) ->
        stringOrigin graph flow site source |> Result.map (function
            | Some(_,origins,originPremises) -> source,origins,constructed site participants @ originPremises
            | None -> source,Map.empty,constructed site participants))
    let localExtent site =
        StringComparisonRecipes.constructions graph |> List.tryPick (fun construction ->
            let view = if construction.LeftLength=site then Some construction.LeftView elif construction.RightLength=site then Some construction.RightView else None
            view |> Option.bind (localOrigin site))
        |> Option.orElseWith (fun () ->
            StringComparisonRecipes.lengthConstructions graph |> List.tryPick (fun construction ->
                let source = if construction.LeftLength=site then Some construction.LeftSource elif construction.RightLength=site then Some construction.RightSource else None
                source |> Option.map (fun source ->
                    stringOrigin graph flow site source |> Result.map (fun derived ->
                        let origins,originPremises = derived |> Option.map (fun (_,origins,participants) -> origins,participants) |> Option.defaultValue (Map.empty,[])
                        let participants = originPremises @ constructed site (Set.ofList(construction.Site::construction.Left::construction.Right::construction.Evidence))
                        source,origins,participants))))
    let extent site source path =
        localExtent site
        |> Option.defaultWith (fun () -> stringOrigin graph flow site source |> Result.map (Option.defaultValue (source,Map.empty,[])))
        |> Result.map (fun (identity,origins,participants) ->
            let occurrences =
                own site ([site, ParticipantRole.Site; source, ParticipantRole.Source; identity, ParticipantRole.ExtentSource]
                          @ (path |> Set.toList |> List.map (fun node -> node, ParticipantRole.Path)))
            { Site=site; Source=source; ExtentSource=identity; StaticOrigins=origins
              Participants=ParticipantEvidence.Established (Participants.ordered site (occurrences @ participants)) })
    // The extent row of a site, or the site's failure.
    let extentRows (enrichment: Enrichment, failures) site source path =
        match extent site source path with
        | Ok row -> { enrichment with NewEdges=Bytes.extentRow row::enrichment.NewEdges }, failures
        | Error failure -> enrichment, (site, failure) :: failures
    // A site whose origins fail has no row; the failure is returned with its site.
    let views, failures = graph.Nodes |> Map.fold (fun (enrichment: Enrichment, failures) _ node ->
        if not node.IsReachable then enrichment, failures else
        match node.Kind with
        | SemanticKind.FieldGet(source, "Bytes")
        | SemanticKind.StringByteBorrow source when graph.Nodes.TryFind source |> Option.exists (fun source -> Types.isStringType source.Type) ->
            let updated = { node with Kind = SemanticKind.StringByteBorrow source; Children = [source] } |> Elaboration.markBaker "StringByteBorrow" enrichId
            let derived = localOrigin node.Id node.Id |> Option.map (Result.map Some) |> Option.defaultWith (fun () -> stringOrigin graph flow node.Id source)
            let rows, failures =
                match derived, representation with
                | Error failure, _ -> [], (node.Id, failure) :: failures
                | Ok (Some(identity, origins, participants)), Some(rep, declaration) ->
                    let occurrences =
                        own node.Id [node.Id, ParticipantRole.Site; source, ParticipantRole.Source; identity, ParticipantRole.ExtentSource
                                     declaration, ParticipantRole.RepresentationDeclaration]
                    let view = { Site = node.Id; Source = source; ExtentSource = identity; StaticOrigins = origins
                                 Representation = rep; RepresentationDeclaration = declaration
                                 Participants = ParticipantEvidence.Established (Participants.ordered node.Id (occurrences @ participants)) }
                    [Bytes.viewRow view; Bytes.storageRow view], failures
                | Ok _, _ -> [], failures
            let rewrite = { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = [source]; Target = node.Id }
            { enrichment with Annotated = updated :: enrichment.Annotated
                              NewEdges = rows @ [rewrite] @ enrichment.NewEdges }, failures
        | SemanticKind.FieldGet(source, "Length") when graph.Nodes.TryFind source |> Option.exists (fun source -> Types.isStringType source.Type) ->
            extentRows (enrichment, failures) node.Id source Set.empty
        | SemanticKind.Application(callee,[source]) when graph.Nodes.TryFind source |> Option.exists (fun source -> Types.isStringType source.Type) ->
            match BoundaryDeclarations.target graph callee with
            | Some({ Kind=SemanticKind.Intrinsic { Module=IntrinsicModule.String; Operation="length" } },path) ->
                extentRows (enrichment, failures) node.Id source path
            | _ -> enrichment, failures
        | _ -> enrichment, failures) (Enrichment.empty, [])
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
    { views with NewEdges = rows @ views.NewEdges }, List.rev failures

/// The rows of the borrows whose origins are derived. A site whose origins fail has
/// no row here; the borrow owner derives the failure again from the graph it
/// settles and reports it at the site (`evidence`, BoundaryRecipes.intrinsicWrites).
let elaborate graph = fst (plan (Elaboration.freshId ()) graph)

/// The late owner rechecks the same complete source recipe premises after
/// rewriting/placement, with each site whose origins fail and its failure.
/// Publication never invokes this source reader.
let evidence graph =
    let enrichment, failures = plan 0 graph
    enrichment.NewEdges |> List.filter (fun edge ->
        match edge.Role with
        | EdgeRole.StringByteView _ | EdgeRole.StringExtent _ | EdgeRole.IntrinsicWriteAbi _ | EdgeRole.StringByteStorage _ -> true
        | _ -> false), failures

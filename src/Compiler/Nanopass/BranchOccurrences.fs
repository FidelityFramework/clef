// SPDX-License-Identifier: MIT
/// Distinct execution occurrences for elaborated branch bodies. Sharing a
/// source expression is not an SSA definition spanning mutually exclusive
/// regions. Preserve source/proof incidence while separating those occurrences
/// before range, control and representation saturation.
module Clef.Compiler.Nanopass.BranchOccurrences

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe

let private isBranch edge =
    edge.Class = EdgeClass.Structural &&
    match edge.Role with
    | EdgeRole.CaseBody | EdgeRole.ThenBranch | EdgeRole.ElseBranch -> true
    | _ -> false

let private incidence (graph: SemanticGraph) =
    graph.Nodes.Values |> Seq.collect (fun node ->
        let edges = kindEdges node.Id node.Kind |> List.filter Hyperedge.isStructural
        let represented = edges |> List.collect _.Sources |> Set.ofList
        edges @ (node.Children |> List.mapi (fun ordinal source -> ordinal, source)
                 |> List.choose (fun (ordinal, source) ->
                     if represented.Contains source then None
                     else Some(Hyperedge.edge1 EdgeClass.Structural EdgeRole.Attached ordinal source node.Id))))
    |> Seq.toList

/// Every enclosing execution path must establish the separation. Two unrelated
/// conditionals do not become mutually exclusive merely by sharing a body ID.
let private exclusive activations parents left right =
    let rec paths seen node =
        if Set.contains node activations then [Map.empty]
        elif Set.contains node seen then [] else
        let seen = Set.add node seen
        match Map.tryFind node parents with
        | None | Some [] -> [Map.empty]
        | Some edges ->
            edges |> List.collect (fun edge ->
                paths seen edge.Target |> List.map (fun path ->
                    if isBranch edge then Map.add edge.Target (edge.Role, edge.Ordinal) path else path))
    let through edge =
        paths Set.empty edge.Target
        |> List.map (Map.add edge.Target (edge.Role, edge.Ordinal))
    let leftPaths, rightPaths = through left, through right
    not leftPaths.IsEmpty && not rightPaths.IsEmpty &&
    (leftPaths |> List.forall (fun a -> rightPaths |> List.forall (fun b ->
        a |> Map.exists (fun decision arm -> b.TryFind decision |> Option.exists ((<>) arm)))))

let private replaceArm (edge: Hyperedge) body (parent: SemanticNode) =
    let kind =
        match parent.Kind, edge.Role with
        | SemanticKind.CaseElimination(input, arms), EdgeRole.CaseBody ->
            SemanticKind.CaseElimination(input, arms |> List.mapi (fun ordinal arm ->
                if ordinal = edge.Ordinal then { arm with Body = body } else arm))
        | SemanticKind.IfThenElse(guard, _, no), EdgeRole.ThenBranch -> SemanticKind.IfThenElse(guard, body, no)
        | SemanticKind.IfThenElse(guard, yes, _), EdgeRole.ElseBranch -> SemanticKind.IfThenElse(guard, yes, Some body)
        | _ -> invalidOp "Branch occurrence must name an explicit conditional body incidence."
    let children = kindEdges parent.Id kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
    { parent with Kind = kind; Children = children }

let rec normalize (graph: SemanticGraph) =
    let activations = graph.Nodes |> Map.toSeq |> Seq.choose (fun (id, node) ->
        match node.Kind with SemanticKind.Lambda _ -> Some id | _ -> None) |> Set.ofSeq
    let structural = incidence graph
    let parents = structural |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
                  |> List.groupBy fst |> Map.ofList |> Map.map (fun _ pairs -> pairs |> List.map snd)
    let next = parents |> Map.toSeq |> Seq.tryPick (fun (body, uses) ->
        match uses with
        | first :: rest when not rest.IsEmpty && List.forall isBranch uses ->
            rest |> List.tryFind (fun other -> exclusive activations parents first other)
            |> Option.map (fun edge -> body, edge)
        | _ -> None)
    match next with
    | None -> graph
    | Some(body, edge) ->
        let root, nodes, origins = Monomorphization.cloneSubtreeWithOrigins graph.Nodes body id (Some edge.Target)
        let remap id = origins.TryFind id |> Option.defaultValue id
        let inherited = graph.Edges |> List.filter (fun relation -> origins.ContainsKey relation.Target)
                        |> List.map (fun relation -> { relation with Sources = List.map remap relation.Sources; Target = remap relation.Target })
        let provenance = origins |> Map.toList |> List.map (fun (source, occurrence) ->
            { Class = EdgeClass.Provenance; Role = EdgeRole.BranchOccurrence
              Sources = List.distinct [source; body]; Target = occurrence; Ordinal = 0 })
        let recipe = {
            OriginalNodeId = edge.Target; ReplacementRootId = edge.Target
            NewNodes = replaceArm edge root graph.Nodes[edge.Target] :: nodes
            NewEdges = inherited @ provenance
            ElaborationKind = "Baker"; ElaborationSource = "Branch.occurrence"
        }
        FoldIn.foldIn (RecipeSet.fromList "Branch.occurrence" [recipe]) graph |> normalize

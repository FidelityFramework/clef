// SPDX-License-Identifier: MIT
/// Baker constructs the release of a scoped memory region on every exit path
/// of its owning lexical scope when the source writes no release (A-04,
/// clef#11). Construction precedes closure, range, numeric and memory
/// settlement, so every constructed operation carries ordinary source facts.
///
/// A unit-valued exit releases after the exit computation; any other exit
/// releases before its value is computed, which is admitted only when that
/// value reads no storage of the region. An exit that would read released
/// storage receives no construction; AsyncAndRegionSettlement refuses it.
module Clef.Compiler.Nanopass.RegionReleaseConstruction

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Nanopass.Recipe

/// Metadata on a constructed release: the region creation it releases.
[<Literal>]
let ScopeExitReleaseOf = "Region.ScopeExitReleaseOf"

/// Metadata on a constructed release: the exit path it is constructed on.
[<Literal>]
let ScopeExitPath = "Region.ScopeExitPath"

let rec private sourceIntrinsic (graph: SemanticGraph) (id: NodeId) (arguments: NodeId list) =
    match graph.Nodes.TryFind id with
    | Some ({ Kind = SemanticKind.Intrinsic info } as node) -> Some(node, info, arguments)
    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> sourceIntrinsic graph inner arguments
    | Some { Kind = SemanticKind.Application(callee, actuals) } -> sourceIntrinsic graph callee (actuals @ arguments)
    | _ -> None

let rec private bindingOf (graph: SemanticGraph) (seen: Set<NodeId>) (id: NodeId) : NodeId option =
    if Set.contains id seen then None else
    let seen = Set.add id seen
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.VarRef(_, Some definition) } -> bindingOf graph seen definition
    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> bindingOf graph seen inner
    | Some { Kind = SemanticKind.Binding(_, false, _, _) } -> Some id
    | _ -> None

let private subtree (graph: SemanticGraph) (root: NodeId) =
    let rec walk pending seen =
        match pending with
        | [] -> seen
        | head :: rest when Set.contains head seen -> walk rest seen
        | head :: rest ->
            match graph.Nodes.TryFind head with
            | Some node -> walk (node.Children @ rest) (Set.add head seen)
            | None -> walk rest (Set.add head seen)
    walk [root] Set.empty

/// The nearest enclosing lambda body: the owning lexical activation scope.
let rec private owningScope (graph: SemanticGraph) (seen: Set<NodeId>) (id: NodeId) : NodeId option =
    if Set.contains id seen then None else
    let seen = Set.add id seen
    match graph.Nodes.TryFind id |> Option.bind _.Parent |> Option.bind graph.Nodes.TryFind with
    | Some { Kind = SemanticKind.Lambda(_, body, _, _, _) } -> Some body
    | Some parent -> owningScope graph seen parent.Id
    | None -> None

/// Every exit path of a scope: the tail computations through sequencing and
/// both arms of every branch.
let rec exitTails (graph: SemanticGraph) (id: NodeId) : NodeId list =
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.Sequential items } when not items.IsEmpty -> exitTails graph (List.last items)
    | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } -> exitTails graph yes @ exitTails graph no
    | Some { Kind = SemanticKind.Match(_, cases) } when not cases.IsEmpty -> cases |> List.collect (fun case -> exitTails graph case.Body)
    | Some { Kind = SemanticKind.CaseElimination(_, arms) } when not arms.IsEmpty -> arms |> List.collect (fun arm -> exitTails graph arm.Body)
    | Some _ -> [ id ]
    | None -> []

/// A region creation with its binding, the binding's owning scope, and the
/// creation intrinsic (whose module and category the release reuses).
type RegionScope = {
    Creation: NodeId
    Binding: NodeId
    Scope: NodeId
    Intrinsic: IntrinsicInfo
}

let regionScopes (graph: SemanticGraph) : RegionScope list =
    graph.Nodes.Values
    |> Seq.filter _.IsReachable
    |> Seq.choose (fun node ->
        match node.Kind, node.Children with
        | SemanticKind.Binding(_, false, _, _), [value] ->
            match graph.Nodes.TryFind value with
            | Some { Kind = SemanticKind.Application _ } ->
                match sourceIntrinsic graph value [] with
                | Some(_, info, [_]) when info.FullName = "Region.create" ->
                    owningScope graph Set.empty node.Id
                    |> Option.map (fun scope -> { Creation = value; Binding = node.Id; Scope = scope; Intrinsic = info })
                | _ -> None
            | _ -> None
        | _ -> None)
    |> Seq.sortBy (fun row -> NodeId.value row.Creation)
    |> Seq.toList

/// Reachable source releases of a region binding.
let releasesOf (graph: SemanticGraph) (binding: NodeId) : SemanticNode list =
    graph.Nodes.Values
    |> Seq.filter (fun node -> node.IsReachable)
    |> Seq.choose (fun node ->
        match node.Kind with
        | SemanticKind.Application _ ->
            match sourceIntrinsic graph node.Id [] with
            | Some(_, info, [argument]) when info.FullName = "Region.release" && bindingOf graph Set.empty argument = Some binding -> Some node
            | _ -> None
        | _ -> None)
    |> Seq.sortBy (fun node -> NodeId.value node.Id)
    |> Seq.toList

/// Bindings whose value is storage of the region: its allocations and the
/// destinations it receives through Region.copyTo.
let storageBindings (graph: SemanticGraph) (binding: NodeId) : Set<NodeId> =
    graph.Nodes.Values
    |> Seq.choose (fun node ->
        match node.Kind, node.Children with
        | SemanticKind.Binding(_, false, _, _), [value] ->
            match sourceIntrinsic graph value [] with
            | Some(_, info, [region; _]) when info.FullName = "Region.alloc" && bindingOf graph Set.empty region = Some binding -> Some node.Id
            | Some(_, info, [_; region; _]) when info.FullName = "Region.copyTo" && bindingOf graph Set.empty region = Some binding -> Some node.Id
            | _ -> None
        | _ -> None)
    |> Set.ofSeq

/// Whether evaluating this computation reads the region or its storage.
let readsRegion (graph: SemanticGraph) (binding: NodeId) (storage: Set<NodeId>) (root: NodeId) =
    subtree graph root
    |> Set.exists (fun id ->
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some definition) } -> definition = binding || storage.Contains definition
        | _ -> false)

let private isUnit (ty: NativeType) =
    match applySubst ty with
    | NativeType.TApp({ NTUKind = Some NTUKind.NTUunit }, []) -> true
    | _ -> false

/// The exits of one region that receive a constructed release.
let private constructible (graph: SemanticGraph) (region: RegionScope) =
    let storage = storageBindings graph region.Binding
    exitTails graph region.Scope
    |> List.filter (fun tail ->
        match graph.Nodes.TryFind tail with
        | Some node -> isUnit node.Type || not (readsRegion graph region.Binding storage tail)
        | None -> false)

let private construct (graph: SemanticGraph) (region: RegionScope) (tail: SemanticNode) =
    let binding = graph.Nodes[region.Binding]
    let name = match binding.Kind with SemanticKind.Binding(name, _, _, _) -> name | _ -> "region"
    let regionType = binding.Type
    let releaseInfo = { region.Intrinsic with Operation = "release"; FullName = "Region.release" }
    let state = SaturationState.create tail.Range "Region.release" (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()) tail.Id graph.Platform
    let recipe =
        saturation {
            let! releaseFunction = createWithChildren (SemanticKind.Intrinsic releaseInfo) (NativeType.TFun(regionType, Types.unitType)) []
            let! regionReference = varRef name (Some region.Binding) regionType
            let! current = getUserState
            let release =
                { mkNode current (SemanticKind.Application(releaseFunction, [regionReference])) Types.unitType [releaseFunction; regionReference] with
                    Metadata =
                        Map.empty
                            .Add(ScopeExitReleaseOf, MetadataValue.NodeId region.Creation)
                            .Add(ScopeExitPath, MetadataValue.NodeId tail.Id) }
            do! emit release
            let! current = getUserState
            // The relocated exit value keeps its kind and operands; its source
            // obligation identity stays with the original exit occurrence.
            let exitMetadata = tail.Metadata.Remove("Source.ObligationSite").Remove("Source.DeclarationIncarnation")
            let exitValue = { mkNode current tail.Kind tail.Type tail.Children with Metadata = exitMetadata; Parent = Some tail.Id }
            do! emit exitValue
            let ordered = if isUnit tail.Type then [ exitValue.Id; release.Id ] else [ release.Id; exitValue.Id ]
            do! enrich tail (SemanticKind.Sequential ordered) tail.Type ordered tail.EmissionStrategy false
            return tail.Id
        }
    match run state recipe with
    | Matched root, nodes -> Some(root, nodes)
    | NoMatch _, _ -> None

let rec private elaborate (graph: SemanticGraph) =
    let pending =
        regionScopes graph
        |> List.tryPick (fun region ->
            if not (releasesOf graph region.Binding).IsEmpty then None
            else
                match constructible graph region with
                | [] -> None
                | tails -> Some(region, tails))
    match pending with
    | None -> graph
    | Some(region, tails) ->
        let expansions =
            tails |> List.choose (fun tail -> graph.Nodes.TryFind tail |> Option.bind (construct graph region))
        if expansions.Length <> tails.Length then graph
        else
            let byTail = expansions |> List.map (fun (root, nodes) -> root, nodes) |> Map.ofList
            let create (node: SemanticNode) _ =
                RecipeCreated { OriginalNodeId = node.Id; NewNodes = byTail[node.Id]
                                ReplacementRootId = node.Id; ElaborationKind = "Baker"; NewEdges = []
                                ElaborationSource = "Region.release" }
            let folded = FoldIn.foldIn (FanOut.fanOut "Region.release" (fun node -> byTail.ContainsKey node.Id) create graph) graph
            let reparentedNodes =
                expansions
                |> List.fold (fun (acc: Map<NodeId, SemanticNode>) (tailId, nodes) ->
                    let origChildren = graph.Nodes[tailId].Children
                    match nodes |> List.tryFind (fun n -> n.Id <> tailId && n.Parent = Some tailId && n.Children = origChildren && not origChildren.IsEmpty) with
                    | Some exitValueNode ->
                        origChildren
                        |> List.fold (fun m childId ->
                            match m.TryFind childId with
                            | Some childNode when childNode.Parent = Some tailId ->
                                m.Add(childId, { childNode with Parent = Some exitValueNode.Id })
                            | _ -> m) acc
                    | None -> acc) folded.Nodes
            let key (edge: Hyperedge) = edge.Target, edge.Class, edge.Role, edge.Ordinal, edge.Sources
            let replaced =
                tails |> List.collect (fun tail -> structuralIncidence graph.Nodes[tail]) |> List.map key |> Set.ofList
            let added = expansions |> List.collect (fun (_, nodes) -> nodes |> List.collect structuralIncidence)
            elaborate { folded with Nodes = reparentedNodes; Edges = (graph.Edges |> List.filter (fun edge -> not (replaced.Contains(key edge)))) @ added }

let private normalizeCore graph =
    let result = elaborate graph
    if Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.sameNodesAndEdges graph result || result.DeclarationRoots.IsEmpty then result
    else Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable result

let normalize graph =
    Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> normalizeCore graph)

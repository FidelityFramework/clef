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
    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
    | Some { Kind = SemanticKind.EagerExpr inner } -> exitTails graph inner
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

/// Independent copies live in the receiving activation. Construct their exact
/// cleanup after the scalar exit computation, before the caller returns.
let private retireReturnedCopies (graph: SemanticGraph) =
    let rec origin seen id =
        if Set.contains id seen then id else
        let seen=Set.add id seen
        match graph.Nodes.TryFind id with
        | Some {Kind=SemanticKind.VarRef(_,Some next)}
        | Some {Kind=SemanticKind.TypeAnnotation(next,_)} -> origin seen next
        | Some {Kind=SemanticKind.Binding(_,false,_,_);Children=[next]} -> origin seen next
        | Some {Kind=SemanticKind.Sequential items} when not items.IsEmpty -> origin seen (List.last items)
        | _ -> id
    let rec helper id =
        match graph.Nodes.TryFind id |> Option.bind _.Parent |> Option.bind graph.Nodes.TryFind with
        | Some {Kind=SemanticKind.Lambda _;Id=id} -> Some id
        | Some parent -> helper parent.Id
        | None -> None
    let rec straight id owner =
        if id=owner then (match graph.Nodes.TryFind owner with Some {Kind=SemanticKind.Sequential _} -> true | _ -> false) else
        match graph.Nodes.TryFind id with
        | Some ({Kind=SemanticKind.Application _} as node)
        | Some ({Kind=SemanticKind.Binding(_,false,_,_)} as node)
        | Some ({Kind=SemanticKind.TypeAnnotation _} as node)
        | Some ({Kind=SemanticKind.Sequential _} as node) -> node.Parent |> Option.exists(fun parent -> straight parent owner)
        | _ -> false
    let aliases initial =
        let rec grow family =
            let next=graph.Nodes.Values |> Seq.fold(fun family node ->
                let input=match node.Kind,node.Children with
                          | SemanticKind.VarRef(_,Some value),_ | SemanticKind.TypeAnnotation(value,_),_ -> Some value
                          | SemanticKind.Binding(_,false,_,_),[value] -> Some value
                          | _ -> None
                if input |> Option.exists(fun id -> Set.contains id family) then Set.add node.Id family else family) family
            if next=family then family else grow next
        grow (Set.singleton initial)
    let selected =
        match graph.Platform |> Option.bind _.ProjectMemoryPolicy,
              Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.resolve graph with
        | Some(_,_,_,true),Some platform ->
            platform.Spaces |> List.filter(fun space -> space.Kind="heap" && space.Access.Contains("w"))
            |> List.tryExactlyOne
        | _ -> None
    match selected with
    | None -> graph
    | Some heap ->
        let resolution=Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        let copies=graph.Nodes.Values |> Seq.choose(fun node ->
            match node.Kind,sourceIntrinsic graph node.Id [] with
            | SemanticKind.Application _,Some(_,info,[_;_]) when node.IsReachable && info.FullName="Region.copyOut"
                && not(node.Metadata.ContainsKey "Region.CopyLifetime") -> Some node
            | _ -> None) |> Seq.toList
        copies |> List.fold(fun graph copy ->
            let candidate =
                helper copy.Id |> Option.bind(fun implementation ->
                    match graph.Nodes[implementation].Kind with
                    | SemanticKind.Lambda(_,body,[],_,_) when exitTails graph body |> List.forall(fun tail -> origin Set.empty tail=copy.Id) ->
                        resolution.Calls |> Map.toList |> List.filter(fun (_,call) -> call.Targets |> List.exists(fun target -> target.Lambda=implementation))
                        |> List.tryExactlyOne |> Option.bind(fun (application,call) ->
                            if not call.Complete || call.Unknown || call.Targets.Length<>1 then None else
                            match owningScope graph Set.empty application,graph.Nodes[application].Parent |> Option.bind graph.Nodes.TryFind with
                            | Some caller,Some {Id=binding;Kind=SemanticKind.Binding(_,false,_,_);Children=[value]} when value=application && straight application caller ->
                                let family=aliases application
                                let allowed = family |> Set.forall(fun id ->
                                    owningScope graph Set.empty id=Some caller &&
                                    (id=application || graph.Nodes[id].Parent |> Option.bind graph.Nodes.TryFind |> Option.exists(fun parent ->
                                        if family.Contains parent.Id then true else
                                        match parent.Kind with
                                        | SemanticKind.Sequential _ -> graph.Nodes[id].Kind |> function SemanticKind.Binding _ -> true | _ -> false
                                        | SemanticKind.IndexGet(buffer,_) | SemanticKind.IndexSet(buffer,_,_) -> buffer=id
                                        | SemanticKind.Application _ ->
                                            match sourceIntrinsic graph parent.Id [] with
                                            | Some(_,info,[value]) when info.FullName="Array.length" && value=id -> true
                                            | _ -> false
                                        | _ -> false)))
                                if allowed then Some(implementation,application,caller,binding,family) else None
                            | _ -> None)
                    | _ -> None)
            match candidate with
            | None -> graph
            | Some(implementation,application,caller,binding,family) ->
                // Save the complete final scalar expression, including its
                // branches, before one retirement in the receiving activation.
                let rec finalExpression id =
                    match graph.Nodes[id].Kind with
                    | SemanticKind.Sequential items when not items.IsEmpty -> finalExpression (List.last items)
                    | _ -> id
                let tails=[finalExpression caller]
                let expansions=tails |> List.choose(fun tailId ->
                    let tail=graph.Nodes[tailId]
                    let state=SaturationState.create tail.Range "Region.retireCopy" (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId()) tail.Id graph.Platform
                    let recipe=saturation {
                        let! scalar=createWithChildren tail.Kind tail.Type tail.Children
                        let! saved=letBind "__region_copy_result" scalar tail.Type
                        let! value=varRef "__region_copy" (Some binding) copy.Type
                        let info={Module=IntrinsicModule.Arena;Operation="retireCopy";FullName="Region.retireCopy";Category=IntrinsicCategory.Memory}
                        let! fn=createAndEmit (SemanticKind.Intrinsic info) (NativeType.TFun(copy.Type,Types.unitType))
                        let! current=getUserState
                        let retirement={mkNode current (SemanticKind.Application(fn,[value])) Types.unitType [fn;value] with
                                          Metadata=Map.empty.Add("Region.CopyOwner",MetadataValue.NodeId copy.Id).Add(ScopeExitPath,MetadataValue.NodeId tail.Id)}
                        do! emit retirement
                        let! result=varRef "__region_copy_result" (Some saved) tail.Type
                        let items=[saved;retirement.Id;result]
                        do! enrich tail (SemanticKind.Sequential items) tail.Type items tail.EmissionStrategy false
                        return tail.Id,scalar }
                    match run state recipe with
                    | Matched(root,scalar),nodes -> Some(root,scalar,nodes)
                    | _ -> None)
                if expansions.Length<>tails.Length then graph else
                let byTail=expansions |> List.map(fun (root,_,nodes) -> root,nodes) |> Map.ofList
                let create (node:SemanticNode) _ =
                    RecipeCreated {OriginalNodeId=node.Id;NewNodes=byTail[node.Id];ReplacementRootId=node.Id
                                   ElaborationKind="Baker";NewEdges=[];ElaborationSource="Region.retireCopy"}
                let folded=FoldIn.foldIn (FanOut.fanOut "Region.retireCopy" (fun node -> byTail.ContainsKey node.Id) create graph) graph
                let nodes=expansions |> List.fold(fun (nodes:Map<NodeId,SemanticNode>) (tail,scalar,_) ->
                    graph.Nodes[tail].Children |> List.fold(fun nodes child ->
                        match Map.tryFind child nodes with
                        | Some node when node.Parent=Some tail -> Map.add child {node with Parent=Some scalar} nodes
                        | _ -> nodes) nodes) folded.Nodes
                let metadata =
                    copy.Metadata
                        .Add("Region.CopyLifetime",MetadataValue.NodeIdList[application;implementation;caller;binding;heap.Node])
                        .Add("Region.CopyUses",MetadataValue.NodeIdList(Set.toList family))
                let copy={nodes[copy.Id] with Metadata=metadata}
                let nodes=nodes.Add(copy.Id,copy)
                let key (edge:Hyperedge)=edge.Target,edge.Class,edge.Role,edge.Ordinal,edge.Sources
                let replaced=tails |> List.collect(fun id -> structuralIncidence graph.Nodes[id]) |> List.map key |> Set.ofList
                let added=expansions |> List.collect(fun (_,_,nodes) -> nodes |> List.collect structuralIncidence)
                {folded with Nodes=nodes;Edges=(graph.Edges |> List.filter(fun edge -> not(replaced.Contains(key edge))))@added}) graph

let private normalizeCore graph =
    let result = elaborate graph |> retireReturnedCopies
    if Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.sameNodesAndEdges graph result || result.DeclarationRoots.IsEmpty then result
    else Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable result

let normalize graph =
    Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> normalizeCore graph)

// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Reachability analysis for the semantic graph.
/// Implements soft-delete (mark unreachable) and hard prune for dead code elimination.
module Clef.Compiler.PSGSaturation.SemanticGraph.Reachability

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

//-------------------------------------------------------------------------
// Reachability Analysis
//-------------------------------------------------------------------------

/// Derive implementation function name from intrinsic info.
/// Convention: Module.operation → __module_operation (lowercase)
/// E.g., FnPtr.fromSymbol → __fnptr_fromSymbol
let intrinsicImplementationName (info: IntrinsicInfo) : string =
    let moduleName =
        match info.Module with
        | IntrinsicModule.FnPtr -> "fnptr"
        | _ -> info.Module.ToString().ToLowerInvariant()
    $"__{moduleName}_{info.Operation}"

/// Determine if an intrinsic is compiler-provided (Alex handles directly).
///
/// ARCHITECTURAL PRINCIPLE: Core native operations are part of the Native Type Universe
/// and are realized directly by Alex. All current intrinsics are compiler-provided.
let isCompilerProvidedIntrinsic (_info: IntrinsicInfo) : bool =
    // All intrinsic modules are compiler-provided (Alex handles directly)
    true

/// Every node the reachability walk must follow from this one: the structural
/// AND reference projection of the single edge table (Types.kindEdges).
///
/// This is the same table Builder.extractImpliedChildren projects; the only
/// difference is that this projection also admits `EdgeClass.Reference` edges
/// -- a resolved VarRef reaches its binding, which is a relation rather than
/// containment. Kinds whose children are attached by the builder rather than
/// carried in the kind payload (Binding's value, Intrinsic's arguments)
/// contribute node.Children directly.
let getSemanticReferences (node: SemanticNode) : NodeId list =
    let fromKind =
        kindEdges node.Id node.Kind
        |> List.filter (fun e -> Hyperedge.isStructural e || Hyperedge.isReference e)
        |> List.map Hyperedge.soleSource
    match node.Kind with
    | SemanticKind.Binding _ | SemanticKind.Intrinsic _ -> fromKind @ node.Children
    | _ -> fromKind

/// Extract type names from a NativeType (for reachability of TypeDef nodes)
/// Only extracts user-defined type names (records, unions) that need TypeDef lookup
let rec getTypeIdentities (ty: NativeType) : NominalTypeIdentity list =
    match ty with
    | NativeType.TApp(tycon, args) ->
        // TApp with FieldCount > 0 indicates a record type needing TypeDef
        let tyconNames = if tycon.FieldCount > 0 || tycon.CaseCount > 0 then [NominalTypeIdentity.ofConstructor tycon] else []
        tyconNames @ (args |> List.collect getTypeIdentities)
    | NativeType.TFun(domain, range) ->
        getTypeIdentities domain @ getTypeIdentities range
    | NativeType.TTuple(elements, _) ->
        elements |> List.collect getTypeIdentities
    // Named records use TApp - handled above via tycon.FieldCount > 0 check
    | NativeType.TUnion(tycon, cases) ->
        NominalTypeIdentity.ofConstructor tycon :: (cases |> List.collect (fun c -> c.Fields |> List.collect (fun (_, t) -> getTypeIdentities t)))
    | NativeType.TNativePtr(inner) ->
        getTypeIdentities inner
    | NativeType.TByref(inner, _) ->
        getTypeIdentities inner
    | NativeType.TAnon(fields, _) ->
        fields |> List.collect (fun (_, t) -> getTypeIdentities t)
    | NativeType.TForall(_, body) ->
        getTypeIdentities body
    | NativeType.TVar(tv) ->
        match tv.Parent with
        | TypeParamState.Bound t -> getTypeIdentities t
        | _ -> []
    | _ -> []

/// Get TypeDef NodeIds for types referenced by a node
let getTypeDefRefs (node: SemanticNode) (graph: SemanticGraph) : NodeId list =
    let typeNames = getTypeIdentities node.Type
    typeNames
    |> List.choose (fun identity -> RecordInstances.tryDefinition identity graph |> Option.map _.Id)

/// Find a binding node by name in the graph
let findBindingByName (name: string) (graph: SemanticGraph) : NodeId option =
    graph.Nodes
    |> Map.tryPick (fun id node ->
        match node.Kind with
        | SemanticKind.Binding (bindingName, _, _, _) when bindingName = name ->
            Some id
        | _ -> None)

/// Build an index of qualified binding names → NodeIds.
/// Qualified name = ModuleDef.name + "." + Binding.name.
/// Used by reachability analysis to resolve string literals that name
/// compiled functions (e.g., dlsym(RTLD_DEFAULT, "Module.function")).
let buildQualifiedBindingIndex (graph: SemanticGraph) : Map<string, NodeId> =
    graph.Nodes
    |> Map.fold (fun acc id node ->
        match node.Kind with
        | SemanticKind.Binding (bindingName, _, _, _) ->
            match node.Parent with
            | Some parentId ->
                match SemanticGraph.tryGetNode parentId graph with
                | Some parentNode ->
                    match parentNode.Kind with
                    | SemanticKind.ModuleDef (moduleName, _) ->
                        Map.add (moduleName + "." + bindingName) id acc
                    | _ -> acc
                | None -> acc
            | None -> acc
        | _ -> acc) Map.empty

/// Resolve a string literal to a binding NodeId if it names a compiled function.
/// This is the reachability edge for dlsym(RTLD_DEFAULT, "symbol_name") patterns:
/// a string literal naming a function in the compilation unit makes that function reachable.
let getStringLiteralBindingRef (node: SemanticNode) (qualifiedIndex: Map<string, NodeId>) : NodeId option =
    match node.Kind with
    | SemanticKind.Literal (NativeLiteral.String name) ->
        Map.tryFind name qualifiedIndex
    | _ -> None

/// Get implementation function references for intrinsic nodes
/// Returns the NodeId of the implementation function if found
let getIntrinsicImplementationRef (node: SemanticNode) (graph: SemanticGraph) : NodeId option =
    match node.Kind with
    | SemanticKind.Intrinsic info ->
        let implName = intrinsicImplementationName info
        findBindingByName implName graph
    | _ -> None

/// Compute the set of reachable nodes from given entry points
/// Follows structural children, semantic references, type references,
/// intrinsic implementation functions, AND string-literal symbol references.
/// A binding whose value, through an annotation, is a quotation.
let private isQuotationBinding (graph: SemanticGraph) (id: NodeId) : bool =
    let rec holdsQuotation (id: NodeId) =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.Quote _ } -> true
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> holdsQuotation inner
        | _ -> false
    match SemanticGraph.tryGetNode id graph with
    | Some { Kind = SemanticKind.Binding _; Children = [ valueId ] } -> holdsQuotation valueId
    | _ -> false

/// A hardware Design is a declaration boundary, matching Composer's hardware
/// witness: InitialState supplies register reset values and Step supplies
/// executable logic. Clock supplies pin/timing metadata, retained in the graph
/// for those readers rather than initialized as a runtime record. A separate
/// ordinary reference to clock data still follows the normal reachability walk.
let private hardwareDesignReferences (graph: SemanticGraph) (node: SemanticNode) =
    let rec record id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> record inner
        | Some ({ Kind = SemanticKind.RecordExpr(fields, _) } as value) when PlatformResolution.typeName value = Some "Design" ->
            let field name = fields |> List.tryFind (fst >> (=) name) |> Option.map snd
            match field "InitialState", field "Step", field "Clock" with
            | Some initial, Some step, Some _ -> Some [initial; step]
            | _ -> None
        | _ -> None
    match node.Kind, node.Children with
    | SemanticKind.Binding(_, _, _, Some DeclRoot.HardwareModule), [value] -> record value
    | _ -> None

let private computeContributions (graph: SemanticGraph) (entries: (NodeId * 'Root) list) : Map<NodeId, Set<'Root>> =
    // Build qualified binding index once for string-literal → binding resolution.
    // This enables reachability through dlsym(RTLD_DEFAULT, "Module.function"):
    // if a string literal naming a compiled function is itself reachable,
    // the function it names is reachable.
    let qualifiedIndex = buildQualifiedBindingIndex graph
    let mappedReferences =
        (MappedBindings.read graph).Mappings
        |> List.map (fun mapping -> mapping.Binding, [mapping.AcquireBinding; mapping.ReleaseBinding])
        |> Map.ofList
    // An issued native declaration retains its source path and formals. Its
    // placeholder is not an executable result; actual calls own result demand.
    // Missing or malformed incidence grants no exemption from the usual walk.
    let foreignBodies =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role with
            | EdgeClass.Boundary, EdgeRole.BoundaryDeclaration declaration
                when edge.Target = declaration.Binding &&
                     edge.Sources = declaration.Path @ declaration.Formals @ [declaration.Body] &&
                     List.tryLast declaration.Path = Some declaration.Implementation ->
                match graph.Nodes.TryFind declaration.Binding, graph.Nodes.TryFind declaration.Implementation with
                | Some binding, Some { Kind = SemanticKind.Lambda(formals, body, captures, _, _) }
                    when (binding.Metadata.ContainsKey "FidelityExtern.Library" || binding.Metadata.ContainsKey "FidelityExtern.Symbol") &&
                         captures.IsEmpty && body = declaration.Body &&
                         (formals |> List.map (fun (_, _, formal) -> formal)) = declaration.Formals ->
                    Some(declaration.Implementation, body)
                | _ -> None
            | _ -> None)
        |> List.groupBy fst
        |> List.choose (fun (implementation, rows) ->
            match rows with [(_, body)] -> Some(implementation, body) | _ -> None)
        |> Map.ofList
    // Lazy cache/guard declarations have no value initializer. Retain the
    // exact declarations named by their source formation, without making
    // either a computation or a cache value into a structural child. This
    // liveness projection grants no memoization, layout or storage authority;
    // the owning readers still validate the complete joint relation.
    let lazyDeclarations =
        graph.Edges
        |> List.filter (fun edge -> edge.Role = EdgeRole.LazyInstance)
        |> List.groupBy _.Target
        |> List.choose (fun (owner, rows) ->
            match graph.Nodes.TryFind owner, rows with
            | Some { Kind = SemanticKind.LazyValue(thunk, environment) },
              [{ Class = EdgeClass.Provenance; Ordinal = 0
                 Sources = [actualThunk; _; actualEnvironment; _; computed; cached; _] }]
                when thunk = actualThunk && environment = actualEnvironment && computed <> cached ->
                let declaration id =
                    match graph.Nodes.TryFind id with
                    | Some { Kind = SemanticKind.PatternBinding _; Children = [] } -> true
                    | _ -> false
                if declaration computed && declaration cached then Some(owner, [computed; cached]) else None
            | _ -> None)
        |> Map.ofList

    let bindingByName =
        graph.Nodes
        |> Map.fold (fun acc id node ->
            match node.Kind with
            | SemanticKind.Binding (bindingName, _, _, _) when not (Map.containsKey bindingName acc) ->
                Map.add bindingName id acc
            | _ -> acc) Map.empty
    let refsCache = System.Collections.Generic.Dictionary<NodeId, NodeId list>()
    let getAllRefs (node: SemanticNode) =
        match refsCache.TryGetValue node.Id with
        | true, cached -> cached
        | false, _ ->
                // Follow structural children and semantic references
                let refs =
                    match Map.tryFind node.Id mappedReferences with
                    | Some nativeBindings -> nativeBindings
                    | None -> getSemanticReferences node
                // Also follow type references to ensure TypeDefs are reachable
                let typeRefs = getTypeDefRefs node graph
                // Follow intrinsic implementation function references
                let intrinsicRef =
                    match node.Kind with
                    | SemanticKind.Intrinsic info -> Map.tryFind (intrinsicImplementationName info) bindingByName |> Option.toList
                    | _ -> []
                // Follow string-literal symbol references (dlsym reachability)
                let symbolRef = getStringLiteralBindingRef node qualifiedIndex |> Option.toList
                // A module's quotation bindings are declarations the compiler reads, not values the
                // module initialises (D9): the walk does not enter them from the module. A reference
                // from executed code still reaches one, and is CCS8066 there.
                let allRefs =
                    // A mapped wrapper is a compiler-owned scoped declaration.
                    // Its placeholder body is not executable Clef; the actual
                    // acquisition/release bindings above remain dependencies.
                    ((if Map.containsKey node.Id mappedReferences then [] else node.Children)
                     @ refs @ typeRefs @ intrinsicRef @ symbolRef
                     @ (lazyDeclarations.TryFind node.Id |> Option.defaultValue []))
                    |> List.distinct
                    |> List.filter (fun r ->
                        match node.Kind with
                        | SemanticKind.ModuleDef _ -> not (isQuotationBinding graph r)
                        | _ -> true)
                // Binding names select compile-time declarations. They are
                // retained in the graph for CCS, but do not occupy image bytes.
                let allRefs =
                    match Mmio.operation graph node.Id, node.Kind with
                    | Some(op, _), SemanticKind.Application(fn, _) when op.StartsWith("bind") -> [fn]
                    | _ -> allRefs
                let allRefs =
                    match hardwareDesignReferences graph node with
                    | Some executable -> executable @ typeRefs
                    | None -> allRefs
                let allRefs =
                    match foreignBodies.TryFind node.Id with
                    | Some placeholder -> allRefs |> List.filter ((<>) placeholder)
                    | None -> allRefs
                refsCache[node.Id] <- allRefs
                allRefs

    let visited = System.Collections.Generic.Dictionary<NodeId, System.Collections.Generic.HashSet<'Root>>()
    let rec walk (root: 'Root) (nodeId: NodeId) =
        match SemanticGraph.tryGetNode nodeId graph with
        | None -> ()
        | Some node ->
            let held =
                match visited.TryGetValue nodeId with
                | true, h -> h
                | false, _ ->
                    let h = System.Collections.Generic.HashSet<'Root>()
                    visited[nodeId] <- h
                    h
            if held.Add root then
                for r in getAllRefs node do
                    walk root r

    for (nodeId, root) in entries do
        if not (isQuotationBinding graph nodeId) then
            walk root nodeId

    visited |> Seq.map (fun kv -> kv.Key, Set.ofSeq kv.Value) |> Map.ofSeq

let private declarationPurposesCache =
    System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, Map<NodeId, Set<NodeId * DeclRoot>>>()

/// The same dependency walk carries each declaration's purpose. A binding can
/// contribute both library retention and concrete commitment; neither row may
/// erase the other. Read this from the current graph after allocating rewrites.
let declarationPurposes (graph: SemanticGraph) : Map<NodeId, Set<NodeId * DeclRoot>> =
    declarationPurposesCache.GetValue(
        graph,
        System.Runtime.CompilerServices.ConditionalWeakTable<_, _>.CreateValueCallback(fun g ->
            g.DeclarationRoots
            |> List.map (fun ((id, _) as root) -> id, root)
            |> computeContributions g))

/// Only an accounted, exclusively retained node avoids concrete representation
/// commitment. Missing purpose evidence grants no exemption.
let requiresRepresentation (purposes: Map<NodeId, Set<NodeId * DeclRoot>>) nodeId =
    match purposes.TryFind nodeId with
    | Some roots when not roots.IsEmpty ->
        roots |> Set.exists (fun (_, root) -> root <> DeclRoot.LibraryExport)
    | _ -> true

let computeReachable (graph: SemanticGraph) (entries: NodeId list) : Set<NodeId> =
    entries
    |> List.map (fun id -> id, ())
    |> computeContributions graph
    |> Map.keys
    |> Set.ofSeq

/// Check for missing intrinsic implementation functions.
/// Only checks LIBRARY-BACKED intrinsics (Signal, Effect, Memo, Batch).
/// COMPILER-PROVIDED intrinsics (Sys, Console, Array, etc.) are handled
/// directly by Alex and don't need F# implementation functions.
/// Returns list of (intrinsicName, implName, range) for missing functions.
let findMissingIntrinsicImplementations (graph: SemanticGraph) : (string * string * SourceRange) list =
    graph.Nodes.Values
    |> Seq.choose (fun node ->
        match node.Kind with
        | SemanticKind.Intrinsic info ->
            // Skip compiler-provided intrinsics - Alex handles them directly
            if isCompilerProvidedIntrinsic info then
                None
            else
                // Library-backed intrinsic - check for implementation function
                let implName = intrinsicImplementationName info
                match findBindingByName implName graph with
                | Some _ -> None
                | None -> Some (info.FullName, implName, node.Range)
        | _ -> None)
    |> Seq.toList

/// Soft-delete: mark unreachable nodes but preserve structure.
/// FAILS if any intrinsic is missing its implementation function - this is a fatal error.
let markUnreachable (graph: SemanticGraph) : SemanticGraph =
    // Check for missing implementation functions - this is a HARD ERROR
    let missingImplementations = findMissingIntrinsicImplementations graph
    if not (List.isEmpty missingImplementations) then
        printfn ""
        printfn "[REACHABILITY] FATAL: Missing intrinsic implementation functions!"
        printfn "  The following intrinsics are used but their implementation functions are not found:"
        for (intrinsicName, implName, range) in missingImplementations do
            printfn ""
            printfn "  Intrinsic: %s" intrinsicName
            printfn "  Requires:  %s" implName
            printfn "  Used at:   %s:%d:%d" range.File range.Start.Line range.Start.Column
        printfn ""
        printfn "  To fix: Ensure the library containing '%s' is included in your project dependencies."
            (missingImplementations |> List.head |> fun (_, impl, _) -> impl)
        failwithf "Missing %d intrinsic implementation function(s). Cannot continue compilation." missingImplementations.Length

    let reachable = computeReachable graph (graph.DeclarationRoots |> List.map fst)
    if graph.Nodes |> Map.forall (fun id node -> node.IsReachable = Set.contains id reachable) then
        graph
    else
        let updatedNodes =
            graph.Nodes
            |> Map.map (fun id node ->
                { node with IsReachable = Set.contains id reachable })

        { graph with Nodes = updatedNodes }

/// A conservative, read-only description of the part of a reachable graph
/// connected to a change. It does not authorize reuse of analysis results.
type ReachableDeltaCone = {
    SeedRoots: Set<NodeId>
    NewlyLitNodes: Set<NodeId>
    ExtinguishedNodes: Set<NodeId>
    AffectedCone: Set<NodeId>
    RetainedReachable: Set<NodeId>
}

/// Compare two already-marked graphs. Within a declaration, parent/child
/// structure is bidirectional; across declarations and hyperedges, invalidation
/// propagates forward along directed causal dependencies (from definitions and
/// hyperedge source premises to their target sites and consumers). Lexical
/// ModuleDef containers propagate parent-to-child containment without lifting
/// child edits back into sibling declarations.
let computeShadowCone (baseline: SemanticGraph) (current: SemanticGraph) : ReachableDeltaCone =
    let isModuleDef (node: SemanticNode) =
        match node.Kind with
        | SemanticKind.ModuleDef _ -> true
        | _ -> false

    let moduleMemberPairs (graph: SemanticGraph) =
        graph.Nodes
        |> Map.fold (fun acc id node ->
            match node.Kind with
            | SemanticKind.ModuleDef(_, members) ->
                (node.Children @ members)
                |> List.fold (fun a childId -> if childId <> id then Set.add (id, childId) a else a) acc
            | _ ->
                match node.Parent with
                | Some parentId when parentId <> id ->
                    match graph.Nodes.TryFind parentId with
                    | Some parentNode when isModuleDef parentNode -> Set.add (parentId, id) acc
                    | _ -> acc
                | _ -> acc) Set.empty

    let allModuleMemberPairs =
        Set.union (moduleMemberPairs baseline) (moduleMemberPairs current)

    let sameNode (a: SemanticNode) (b: SemanticNode) =
        match a.Kind, b.Kind with
        | SemanticKind.ModuleDef(nameA, _), SemanticKind.ModuleDef(nameB, _) ->
            a.Id = b.Id && nameA = nameB && a.Parent = b.Parent && a.Type = b.Type &&
            a.SRTPResolution = b.SRTPResolution && a.ArenaAffinity = b.ArenaAffinity &&
            a.LayoutHint = b.LayoutHint && a.Metadata = b.Metadata &&
            a.EmissionStrategy = b.EmissionStrategy && a.ValueRange = b.ValueRange
        | _ ->
            a.Id = b.Id && a.Kind = b.Kind && a.Range = b.Range && a.Type = b.Type &&
            a.SRTPResolution = b.SRTPResolution && a.ArenaAffinity = b.ArenaAffinity &&
            a.LayoutHint = b.LayoutHint && a.Children = b.Children && a.Parent = b.Parent &&
            a.Metadata = b.Metadata && a.EmissionStrategy = b.EmissionStrategy &&
            a.ValueRange = b.ValueRange

    let edgeKey (edge: Hyperedge) =
        edge.Class, edge.Role, edge.Ordinal, edge.Target, edge.Sources

    let sameEdgeMultiset xs ys =
        let rec loop remaining = function
            | [] -> List.isEmpty remaining
            | h :: t ->
                let rec removeFirst acc = function
                    | [] -> None
                    | x :: rest when x = h -> Some(List.rev acc @ rest)
                    | x :: rest -> removeFirst (x :: acc) rest
                match removeFirst [] remaining with
                | Some remaining' -> loop remaining' t
                | None -> false
        List.length xs = List.length ys && loop ys xs

    let incidentEdges (graph: SemanticGraph) =
        graph.Edges
        |> List.fold (fun index edge ->
            let key = edgeKey edge
            let previous = Map.tryFind edge.Target index |> Option.defaultValue []
            Map.add edge.Target (key :: previous) index) Map.empty

    let oldIncident = incidentEdges baseline
    let newIncident = incidentEdges current

    let baselineReachable =
        baseline.Nodes
        |> Map.fold (fun ids id node ->
            if node.IsReachable then Set.add id ids else ids) Set.empty

    let reachable =
        current.Nodes
        |> Map.fold (fun ids id node ->
            if node.IsReachable then Set.add id ids else ids) Set.empty

    let newlyLit = Set.difference reachable baselineReachable
    let extinguished = Set.difference baselineReachable reachable

    let changedNodes =
        current.Nodes
        |> Map.fold (fun changed id node ->
            match baseline.Nodes.TryFind id with
            | Some old when sameNode old node -> changed
            | _ -> Set.add id changed) Set.empty

    let incidenceChanged =
        Set.union (oldIncident |> Map.keys |> Set.ofSeq) (newIncident |> Map.keys |> Set.ofSeq)
        |> Set.filter (fun id ->
            Set.contains id reachable &&
            let oldEdges = Map.tryFind id oldIncident |> Option.defaultValue []
            let newEdges = Map.tryFind id newIncident |> Option.defaultValue []
            not (sameEdgeMultiset oldEdges newEdges))

    let changedRoots =
        let oldRoots = Set.ofList baseline.DeclarationRoots
        let newRoots = Set.ofList current.DeclarationRoots
        Set.union (Set.difference oldRoots newRoots) (Set.difference newRoots oldRoots)
        |> Set.map fst
        |> Set.filter current.Nodes.ContainsKey

    let localLinksFor (graph: SemanticGraph) =
        let qualifiedIndex = buildQualifiedBindingIndex graph
        let bindingByName =
            graph.Nodes |> Map.fold (fun index id node ->
                match node.Kind with
                | SemanticKind.Binding(name, _, _, _) when not (Map.containsKey name index) -> Map.add name id index
                | _ -> index) Map.empty
        graph.Nodes
        |> Map.fold (fun index id node ->
            let intrinsic =
                match node.Kind with
                | SemanticKind.Intrinsic info -> Map.tryFind (intrinsicImplementationName info) bindingByName |> Option.toList
                | _ -> []
            let parentLink = node.Parent |> Option.toList
            let ownLinks =
                match node.Kind with
                | SemanticKind.ModuleDef _ ->
                    (parentLink @ getTypeDefRefs node graph)
                    |> List.filter graph.Nodes.ContainsKey
                    |> Set.ofList
                | _ ->
                    (parentLink @ node.Children @ getSemanticReferences node @ getTypeDefRefs node graph
                     @ intrinsic @ (getStringLiteralBindingRef node qualifiedIndex |> Option.toList))
                    |> List.filter graph.Nodes.ContainsKey
                    |> Set.ofList
            Map.add id ownLinks index) Map.empty

    let oldLinks = localLinksFor baseline
    let newLinks = localLinksFor current
    let linksChanged =
        Set.union (oldLinks |> Map.keys |> Set.ofSeq) (newLinks |> Map.keys |> Set.ofSeq)
        |> Set.filter (fun id ->
            Set.contains id reachable &&
            Map.tryFind id oldLinks <> Map.tryFind id newLinks)

    let causalSuccessors (graph: SemanticGraph) =
        let addDirected fromId toId index =
            if not (graph.Nodes.ContainsKey fromId) || not (graph.Nodes.ContainsKey toId) || fromId = toId then
                index
            else
                let held = Map.tryFind fromId index |> Option.defaultValue Set.empty
                Map.add fromId (Set.add toId held) index
        let addStructuralContainment parentId childId index =
            let index = addDirected parentId childId index
            if Set.contains (parentId, childId) allModuleMemberPairs then
                index
            else
                addDirected childId parentId index
        let qualifiedIndex = buildQualifiedBindingIndex graph
        let bindingByName =
            graph.Nodes |> Map.fold (fun index id node ->
                match node.Kind with
                | SemanticKind.Binding(name, _, _, _) when not (Map.containsKey name index) -> Map.add name id index
                | _ -> index) Map.empty
        graph.Nodes
        |> Map.fold (fun index id node ->
            let structuralChildren =
                node.Children @
                (kindEdges id node.Kind
                 |> List.filter Hyperedge.isStructural
                 |> List.map Hyperedge.soleSource)
            let index =
                structuralChildren
                |> List.fold (fun acc childId -> addStructuralContainment id childId acc) index
            let index =
                match node.Parent with
                | Some parentId -> addStructuralContainment parentId id index
                | None -> index
            let intrinsic =
                match node.Kind with
                | SemanticKind.Intrinsic info -> Map.tryFind (intrinsicImplementationName info) bindingByName |> Option.toList
                | _ -> []
            let referencedDefs =
                (kindEdges id node.Kind
                 |> List.filter Hyperedge.isReference
                 |> List.map Hyperedge.soleSource)
                @ getTypeDefRefs node graph
                @ intrinsic
                @ (getStringLiteralBindingRef node qualifiedIndex |> Option.toList)
            referencedDefs
            |> List.fold (fun acc defId -> addDirected defId id acc) index) Map.empty
        |> fun index ->
            graph.Edges
            |> List.fold (fun index edge ->
                edge.Sources
                |> List.fold (fun acc sourceId -> addDirected sourceId edge.Target acc) index) index

    let seeds = Set.unionMany [changedNodes; newlyLit; extinguished; incidenceChanged; changedRoots; linksChanged]
    let successors = causalSuccessors current

    let rec visit pending seen =
        match pending with
        | [] -> seen
        | id :: rest when Set.contains id seen -> visit rest seen
        | id :: rest when not (Set.contains id reachable) && not (Set.contains id seeds) -> visit rest seen
        | id :: rest ->
            let next = Map.tryFind id successors |> Option.defaultValue Set.empty
            visit (Set.toList next @ rest) (Set.add id seen)

    let visited = visit (Set.toList seeds) Set.empty
    let affected = Set.intersect visited reachable
    { SeedRoots = seeds
      NewlyLitNodes = newlyLit
      ExtinguishedNodes = extinguished
      AffectedCone = affected
      RetainedReachable = Set.difference reachable affected }

/// Get counts of reachable and unreachable nodes
let getReachabilityStats (graph: SemanticGraph) : int * int =
    let reachableCount =
        graph.Nodes
        |> Map.filter (fun _ n -> n.IsReachable)
        |> Map.count
    let unreachableCount =
        graph.Nodes
        |> Map.filter (fun _ n -> not n.IsReachable)
        |> Map.count
    (reachableCount, unreachableCount)

/// Physical deletion is unavailable once resident proof incidence or a target
/// declaration phase needs the graph's non-executable participants. Preserve
/// that structure with the same reachability marks as ordinary soft deletion;
/// this does not turn declaration membership into an execution root.
let pruneUnreachable (graph: SemanticGraph) : SemanticGraph =
    if not graph.Edges.IsEmpty || graph.Platform.IsSome then markUnreachable graph
    else
        let reachable = computeReachable graph (graph.DeclarationRoots |> List.map fst)
        { graph with
            Nodes = graph.Nodes |> Map.filter (fun id _ -> Set.contains id reachable) }

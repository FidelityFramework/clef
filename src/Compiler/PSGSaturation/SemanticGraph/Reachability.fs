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
let rec getTypeNames (ty: NativeType) : string list =
    match ty with
    | NativeType.TApp(tycon, args) ->
        // TApp with FieldCount > 0 indicates a record type needing TypeDef
        let tyconNames = if tycon.FieldCount > 0 then [tycon.Name] else []
        tyconNames @ (args |> List.collect getTypeNames)
    | NativeType.TFun(domain, range) ->
        getTypeNames domain @ getTypeNames range
    | NativeType.TTuple(elements, _) ->
        elements |> List.collect getTypeNames
    // Named records use TApp - handled above via tycon.FieldCount > 0 check
    | NativeType.TUnion(tycon, cases) ->
        tycon.Name :: (cases |> List.collect (fun c -> c.Fields |> List.collect (fun (_, t) -> getTypeNames t)))
    | NativeType.TNativePtr(inner) ->
        getTypeNames inner
    | NativeType.TByref(inner, _) ->
        getTypeNames inner
    | NativeType.TAnon(fields, _) ->
        fields |> List.collect (fun (_, t) -> getTypeNames t)
    | NativeType.TForall(_, body) ->
        getTypeNames body
    | NativeType.TVar(tv) ->
        match tv.Parent with
        | TypeParamState.Bound t -> getTypeNames t
        | _ -> []
    | _ -> []

/// Get TypeDef NodeIds for types referenced by a node
let getTypeDefRefs (node: SemanticNode) (graph: SemanticGraph) : NodeId list =
    let typeNames = getTypeNames node.Type
    typeNames
    |> List.choose (fun name -> SemanticGraph.recallType name graph)

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

let computeReachable (graph: SemanticGraph) (entries: NodeId list) : Set<NodeId> =
    // Build qualified binding index once for string-literal → binding resolution.
    // This enables reachability through dlsym(RTLD_DEFAULT, "Module.function"):
    // if a string literal naming a compiled function is itself reachable,
    // the function it names is reachable.
    let qualifiedIndex = buildQualifiedBindingIndex graph
    let mappedReferences =
        (MappedBindings.read graph).Mappings
        |> List.map (fun mapping -> mapping.Binding, [mapping.AcquireBinding; mapping.ReleaseBinding])
        |> Map.ofList

    let rec walk (visited: Set<NodeId>) (nodeId: NodeId) =
        if Set.contains nodeId visited then
            visited
        else
            match SemanticGraph.tryGetNode nodeId graph with
            | None -> visited
            | Some node ->
                let visited = Set.add nodeId visited
                // Follow structural children and semantic references
                let refs =
                    match Map.tryFind node.Id mappedReferences with
                    | Some nativeBindings -> nativeBindings
                    | None -> getSemanticReferences node
                // Also follow type references to ensure TypeDefs are reachable
                let typeRefs = getTypeDefRefs node graph
                // Follow intrinsic implementation function references
                let intrinsicRef = getIntrinsicImplementationRef node graph |> Option.toList
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
                     @ refs @ typeRefs @ intrinsicRef @ symbolRef)
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
                allRefs |> List.fold walk visited

    entries |> List.fold walk Set.empty

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
    let updatedNodes =
        graph.Nodes
        |> Map.map (fun id node ->
            { node with IsReachable = Set.contains id reachable })

    { graph with Nodes = updatedNodes }

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

/// Hard prune unreachable nodes (not soft-delete!)
/// Use for production - removes unreachable nodes entirely
let pruneUnreachable (graph: SemanticGraph) : SemanticGraph =
    let reachable = computeReachable graph (graph.DeclarationRoots |> List.map fst)
    { graph with
        Nodes = graph.Nodes |> Map.filter (fun id _ -> Set.contains id reachable) }

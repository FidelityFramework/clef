// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Reachability analysis for the semantic graph.
/// Implements soft-delete (mark unreachable) and hard prune for dead code elimination.
module FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Reachability

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Core

//-------------------------------------------------------------------------
// Reachability Analysis
//-------------------------------------------------------------------------

/// Derive implementation function name from intrinsic info.
/// Convention: Module.operation → __module_operation (lowercase)
/// E.g., Signal.create → __signal_create
let intrinsicImplementationName (info: IntrinsicInfo) : string =
    let moduleName =
        match info.Module with
        | IntrinsicModule.Signal -> "signal"
        | IntrinsicModule.Effect -> "effect"
        | IntrinsicModule.Memo -> "memo"
        | IntrinsicModule.Batch -> "batch"
        | IntrinsicModule.FnPtr -> "fnptr"
        | _ -> info.Module.ToString().ToLowerInvariant()
    $"__{moduleName}_{info.Operation}"

/// Determine if an intrinsic is compiler-provided (Alex handles directly)
/// vs library-backed (needs F# implementation function in dependency graph).
///
/// ARCHITECTURAL PRINCIPLE: Core native operations are part of the Native Type Universe
/// and are realized directly by Alex. Library-backed intrinsics (reactive signals)
/// require F# implementation functions from libraries like Fidelity.Signal.
let isCompilerProvidedIntrinsic (info: IntrinsicInfo) : bool =
    match info.Module with
    // Library-backed: require F# implementation functions
    | IntrinsicModule.Signal
    | IntrinsicModule.Effect
    | IntrinsicModule.Memo
    | IntrinsicModule.Batch -> false
    // Compiler-provided: Alex handles directly, no F# implementation needed
    | IntrinsicModule.Sys
    | IntrinsicModule.NativePtr
    | IntrinsicModule.NativeStr
    | IntrinsicModule.NativeDefault
    | IntrinsicModule.String
    | IntrinsicModule.Array
    | IntrinsicModule.Math
    | IntrinsicModule.Unchecked
    | IntrinsicModule.Operators
    | IntrinsicModule.Parse
    | IntrinsicModule.Format
    | IntrinsicModule.Convert
    | IntrinsicModule.Crypto
    | IntrinsicModule.Bits
    | IntrinsicModule.FnPtr
    | IntrinsicModule.Arena
    | IntrinsicModule.DateTime
    | IntrinsicModule.TimeSpan
    | IntrinsicModule.Lazy  // Lazy operations handled by Alex (PRD-14)
    | IntrinsicModule.Seq  // Seq operations handled by Alex (PRD-15)
    | IntrinsicModule.SeqEnumerator  // SeqEnumerator operations handled by Alex (PRD-15/16)
    // PRD-13a: Collection operations handled by Alex
    | IntrinsicModule.Map
    | IntrinsicModule.Set
    | IntrinsicModule.List
    | IntrinsicModule.Option
    | IntrinsicModule.Result
    | IntrinsicModule.Platform -> true  // Platform introspection (sizeof, wordSize)

/// Extract semantic references from a node's Kind (call targets, definition refs, etc.)
/// Used by traversal to ensure all semantic children are visited.
/// IMPORTANT: ALL SemanticKind cases MUST be handled explicitly - no wildcards!
let getSemanticReferences (node: SemanticNode) : NodeId list =
    match node.Kind with
    // Application: follow function and arguments
    | SemanticKind.Application (funcId, argIds) ->
        funcId :: argIds
    // VarRef with definition: follow to definition
    | SemanticKind.VarRef (_, Some defId) ->
        [defId]
    | SemanticKind.VarRef (_, None) ->
        []  // Unresolved reference - no semantic edges
    // Match: follow scrutinee and case bodies
    | SemanticKind.Match (scrutinee, cases) ->
        // Include PatternBindings so they're in traversal path for SSA assignment
        scrutinee :: (cases |> List.collect (fun c ->
            let guardAndBody = match c.Guard with Some g -> [g; c.Body] | None -> [c.Body]
            c.PatternBindings @ guardAndBody))
    // Sequential: follow all nodes
    | SemanticKind.Sequential nodes ->
        nodes
    // Binding: follow value node (first child usually)
    | SemanticKind.Binding _ ->
        node.Children
    // Lambda: follow body
    | SemanticKind.Lambda (_, bodyId, _, _, _) ->
        [bodyId]
    // Control flow: follow branches
    | SemanticKind.IfThenElse (guard, thenB, elseB) ->
        guard :: thenB :: (Option.toList elseB)
    | SemanticKind.WhileLoop (guard, body) ->
        [guard; body]
    | SemanticKind.ForLoop (_, start, finish, _, body) ->
        [start; finish; body]
    | SemanticKind.ForEach (_, collection, body) ->
        [collection; body]
    | SemanticKind.TryWith (body, handler) ->
        [body; handler]
    | SemanticKind.TryFinally (body, cleanup) ->
        [body; cleanup]
    // Expressions with sub-expressions
    | SemanticKind.TupleExpr elements ->
        elements
    | SemanticKind.TupleGet(tupleId, _) ->
        [tupleId]
    | SemanticKind.ArrayExpr elements ->
        elements
    | SemanticKind.ListExpr elements ->
        elements
    | SemanticKind.RecordExpr (fields, copyFrom) ->
        (fields |> List.map snd) @ (Option.toList copyFrom)
    | SemanticKind.UnionCase (_, _, payload) ->
        Option.toList payload
    // DU Operations (January 2026)
    | SemanticKind.DUGetTag (duValue, _) ->
        [duValue]
    | SemanticKind.DUEliminate (duValue, _, _, _) ->
        [duValue]
    | SemanticKind.DUConstruct (_, _, payload, arenaHint) ->
        (Option.toList payload) @ (Option.toList arenaHint)
    | SemanticKind.FieldGet (expr, _) ->
        [expr]
    | SemanticKind.FieldSet (expr, _, value) ->
        [expr; value]
    | SemanticKind.IndexGet (expr, index) ->
        [expr; index]
    | SemanticKind.IndexSet (expr, index, value) ->
        [expr; index; value]
    | SemanticKind.NamedIndexedPropertySet (expr, _, index, value) ->
        [expr; index; value]
    | SemanticKind.TypeAnnotation (expr, _) ->
        [expr]
    | SemanticKind.Upcast (expr, _) ->
        [expr]
    | SemanticKind.Downcast (expr, _) ->
        [expr]
    | SemanticKind.TypeTest (expr, _) ->
        [expr]
    | SemanticKind.Set (target, value) ->
        [target; value]
    | SemanticKind.AddressOf (expr, _) ->
        [expr]
    | SemanticKind.Deref expr ->
        [expr]
    // ModuleDef: follow member bindings
    | SemanticKind.ModuleDef (_, memberIds) ->
        memberIds
    // TypeDef: follow member definitions
    | SemanticKind.TypeDef (_, _, memberIds) ->
        memberIds
    // MemberDef: follow body if present
    | SemanticKind.MemberDef (_, _, bodyOpt) ->
        Option.toList bodyOpt
    // ObjectExpr: follow member implementations
    | SemanticKind.ObjectExpr (_, memberIds) ->
        memberIds
    // InterpolatedString: follow expression parts
    | SemanticKind.InterpolatedString parts ->
        parts |> List.choose (function
            | InterpolatedPart.ExprPart id -> Some id
            | InterpolatedPart.StringPart _ -> None)
    // TraitCall: follow the argument
    | SemanticKind.TraitCall (_, _, argId) ->
        [argId]
    // Quote: follow quoted expression
    | SemanticKind.Quote (exprId, _) ->
        [exprId]
    // Intrinsic: implementation function reference is resolved during reachability walk
    // The actual connection to implementation functions happens in computeReachable
    | SemanticKind.Intrinsic _ ->
        node.Children  // Follow any children (arguments)
    // Lazy (PRD-14): deferred computation
    | SemanticKind.LazyExpr (bodyId, _captures) ->
        [bodyId]  // Follow the deferred computation body
    | SemanticKind.LazyForce lazyValueId ->
        [lazyValueId]  // Follow the lazy value to force
    // Seq (PRD-15): sequence expressions
    | SemanticKind.SeqExpr (bodyId, _captures) ->
        [bodyId]  // Follow the sequence body (MoveNext thunk)
    | SemanticKind.Yield valueId ->
        [valueId]  // Follow the yielded value
    | SemanticKind.YieldBang seqId ->
        [seqId]  // Follow the nested sequence
    // Leaf nodes with no semantic references
    | SemanticKind.Literal _ ->
        []
    | SemanticKind.PlatformBinding _ ->
        []
    | SemanticKind.PatternBinding _ ->
        []
    | SemanticKind.Error _ ->
        []

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

/// Get implementation function references for intrinsic nodes
/// Returns the NodeId of the implementation function if found
let getIntrinsicImplementationRef (node: SemanticNode) (graph: SemanticGraph) : NodeId option =
    match node.Kind with
    | SemanticKind.Intrinsic info ->
        let implName = intrinsicImplementationName info
        findBindingByName implName graph
    | _ -> None

/// Compute the set of reachable nodes from given entry points
/// Follows structural children, semantic references, type references, AND intrinsic implementation functions
let computeReachable (graph: SemanticGraph) (entries: NodeId list) : Set<NodeId> =
    let rec walk (visited: Set<NodeId>) (nodeId: NodeId) =
        if Set.contains nodeId visited then
            visited
        else
            match SemanticGraph.tryGetNode nodeId graph with
            | None -> visited
            | Some node ->
                let visited = Set.add nodeId visited
                // Follow structural children and semantic references
                let refs = getSemanticReferences node
                // Also follow type references to ensure TypeDefs are reachable
                let typeRefs = getTypeDefRefs node graph
                // Follow intrinsic implementation function references
                let intrinsicRef = getIntrinsicImplementationRef node graph |> Option.toList
                let allRefs = (node.Children @ refs @ typeRefs @ intrinsicRef) |> List.distinct
                allRefs |> List.fold walk visited

    entries |> List.fold walk Set.empty

/// Check for missing intrinsic implementation functions.
/// Only checks LIBRARY-BACKED intrinsics (Signal, Effect, Memo, Batch).
/// COMPILER-PROVIDED intrinsics (Sys, Console, NativePtr, etc.) are handled
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

    let reachable = computeReachable graph graph.EntryPoints
    let updatedNodes =
        graph.Nodes
        |> Map.map (fun id node ->
            { node with IsReachable = Set.contains id reachable })

    // Print reachability stats
    let reachableCount = updatedNodes |> Map.filter (fun _ n -> n.IsReachable) |> Map.count
    let unreachableCount = updatedNodes |> Map.filter (fun _ n -> not n.IsReachable) |> Map.count
    printfn "[REACHABILITY] Stats: %d reachable, %d unreachable (total: %d nodes)"
        reachableCount unreachableCount (reachableCount + unreachableCount)

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
    let reachable = computeReachable graph graph.EntryPoints
    { graph with
        Nodes = graph.Nodes |> Map.filter (fun id _ -> Set.contains id reachable) }

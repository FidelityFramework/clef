// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Core operations on SemanticGraph - creation, querying and type projection.
/// This module computes lazy type indexes and module classifications.
module Clef.Compiler.PSGSaturation.SemanticGraph.Core

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

//-------------------------------------------------------------------------
// SemanticGraph Module - Core Operations
//-------------------------------------------------------------------------

module SemanticGraph =
    /// Map every type carried by a node, including metadata consumed by lowering.
    /// Updating only node.Type leaves closures, patterns and witnesses unresolved.
    let mapNodeTypes (transform: NativeType -> NativeType) (node: SemanticNode) =
        let rec pattern = function
            | Pattern.Var(name, ty) -> Pattern.Var(name, transform ty)
            | Pattern.Tuple elements -> Pattern.Tuple(List.map pattern elements)
            | Pattern.Union(name, tag, payload, ty) -> Pattern.Union(name, tag, Option.map pattern payload, transform ty)
            | Pattern.Record(fields, ty) -> Pattern.Record(fields |> List.map (fun (name, p) -> name, pattern p), transform ty)
            | Pattern.Array elements -> Pattern.Array(List.map pattern elements)
            | Pattern.Or(left, right) -> Pattern.Or(pattern left, pattern right)
            | Pattern.And(left, right) -> Pattern.And(pattern left, pattern right)
            | Pattern.As(inner, name) -> Pattern.As(pattern inner, name)
            | Pattern.IsType ty -> Pattern.IsType(transform ty)
            | Pattern.Exception(ty, name) -> Pattern.Exception(transform ty, name)
            | (Pattern.Const _ | Pattern.Wildcard | Pattern.Null) as p -> p
        let captures items = items |> List.map (fun (capture: CaptureInfo) -> { capture with Type = transform capture.Type })
        let definition = function
            | RecordDef fields -> RecordDef(fields |> List.map (fun (name, ty) -> name, transform ty))
            | UnionDef cases -> UnionDef(cases |> List.map (fun (name, fields) -> name, fields |> List.map (fun (name, ty) -> name, transform ty)))
            | AbbreviationDef ty -> AbbreviationDef(transform ty)
            | (ClassDef | InterfaceDef | StructDef | EnumDef _) as kind -> kind
        let kind =
            match node.Kind with
            | SemanticKind.Lambda(parameters, body, captured, enclosing, context) ->
                SemanticKind.Lambda(parameters |> List.map (fun (name, ty, id) -> name, transform ty, id), body, captures captured, enclosing, context)
            | SemanticKind.Match(scrutinee, cases) ->
                SemanticKind.Match(scrutinee, cases |> List.map (fun case -> { case with Pattern = pattern case.Pattern }))
            | SemanticKind.CaseElimination(scrutinee, arms) ->
                SemanticKind.CaseElimination(scrutinee, arms |> List.map (fun arm -> { arm with Pattern = pattern arm.Pattern }))
            | SemanticKind.DUGetTag(value, ty) -> SemanticKind.DUGetTag(value, transform ty)
            | SemanticKind.DUEliminate(value, index, name, ty) -> SemanticKind.DUEliminate(value, index, name, transform ty)
            | SemanticKind.TypeAnnotation(value, ty) -> SemanticKind.TypeAnnotation(value, transform ty)
            | SemanticKind.Upcast(value, ty) -> SemanticKind.Upcast(value, transform ty)
            | SemanticKind.Downcast(value, ty) -> SemanticKind.Downcast(value, transform ty)
            | SemanticKind.TypeTest(value, ty) -> SemanticKind.TypeTest(value, transform ty)
            | SemanticKind.TraitCall(name, types, arg) -> SemanticKind.TraitCall(name, List.map transform types, arg)
            | SemanticKind.ObjectExpr(ty, members) -> SemanticKind.ObjectExpr(transform ty, members)
            | SemanticKind.TypeDef(name, kind, members) -> SemanticKind.TypeDef(name, definition kind, members)
            | SemanticKind.LazyExpr(body, captured) -> SemanticKind.LazyExpr(body, captures captured)
            | SemanticKind.SeqExpr(body, captured) -> SemanticKind.SeqExpr(body, captures captured)
            | kind -> kind
        { node with
            Type = transform node.Type
            Kind = kind
            SRTPResolution = node.SRTPResolution |> Option.map (fun witness -> { witness with ArgType = transform witness.ArgType })
            Metadata = node.Metadata |> Map.map (fun _ value ->
                match value with MetadataValue.Type ty -> MetadataValue.Type(transform ty) | value -> value) }

    /// Extract types index from witnessed TypeDef nodes (lazy computation)
    let private extractTypesIndex (nodes: Map<NodeId, SemanticNode>) : Map<string, NodeId> =
        nodes
        |> Map.values
        |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.TypeDef(name, _, _) -> Some (name, node.Id)
            | _ -> None)
        |> Map.ofSeq

    /// Create a lazy types index from nodes
    let mkTypesIndex (nodes: Map<NodeId, SemanticNode>) : Lazy<Map<string, NodeId>> =
        lazy (extractTypesIndex nodes)

    /// Extract module classifications from nodes (lazy computation)
    let private extractModuleClassifications (nodes: Map<NodeId, SemanticNode>) : Map<NodeId, ModuleClassification> =
        nodes
        |> Map.values
        |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.ModuleDef(name, memberIds) ->
                let mutable moduleInit = []
                let mutable definitions = []
                let mutable declRoot = None
                // A binding whose value is a quotation is a declaration the compiler reads (D9): it
                // is neither initialised by the module nor a definition to emit, and is in no list.
                let rec holdsQuotation (id: NodeId) =
                    match Map.tryFind id nodes with
                    | Some { Kind = SemanticKind.Quote _ } -> true
                    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> holdsQuotation inner
                    | _ -> false
                let isDeclaration (memberNode: SemanticNode) =
                    match memberNode.Kind, memberNode.Children with
                    | SemanticKind.Binding _, [ valueId ] -> holdsQuotation valueId
                    | _ -> false
                for memberId in memberIds do
                    match Map.tryFind memberId nodes with
                    | Some memberNode when isDeclaration memberNode -> ()
                    | Some memberNode ->
                        match memberNode.Kind with
                        | SemanticKind.Binding(_, _, _, dr) ->
                            if dr.IsSome then
                                declRoot <- Some (memberId, dr.Value)
                                definitions <- memberId :: definitions
                            elif memberNode.EmissionStrategy = EmissionStrategy.MainPrologue then
                                moduleInit <- memberId :: moduleInit
                            else
                                definitions <- memberId :: definitions
                        | _ -> definitions <- memberId :: definitions
                    | None -> ()
                Some (node.Id, {
                    Name = name
                    ModuleInit = List.rev moduleInit
                    Definitions = List.rev definitions
                    DeclarationRoot = declRoot
                })
            | _ -> None)
        |> Map.ofSeq

    /// Create lazy module classifications from nodes
    let mkModuleClassifications (nodes: Map<NodeId, SemanticNode>) : Lazy<Map<NodeId, ModuleClassification>> =
        lazy (extractModuleClassifications nodes)

    /// Recall a type definition by name (codata observation)
    let recallType (name: string) (graph: SemanticGraph) : NodeId option =
        graph.Types.Value |> Map.tryFind name

    /// Create an empty semantic graph
    let empty : SemanticGraph = {
        Nodes = Map.empty
        DeclarationRoots = []
        Modules = Map.empty
        Types = lazy Map.empty
        Platform = None
        ModuleClassifications = lazy Map.empty
        FieldRanges = lazy Map.empty
        ElementRanges = lazy Map.empty
        Layouts = lazy Map.empty
        StaticStringPool = None
        Escaping = lazy Map.empty
        Codata = lazy Codata.empty
        Edges = []
    }

    /// Create an empty semantic graph with platform context
    let emptyWithPlatform (platform: PlatformContext) : SemanticGraph = {
        Nodes = Map.empty
        DeclarationRoots = []
        Modules = Map.empty
        Types = lazy Map.empty
        Platform = Some platform
        ModuleClassifications = lazy Map.empty
        FieldRanges = lazy Map.empty
        ElementRanges = lazy Map.empty
        Layouts = lazy Map.empty
        StaticStringPool = None
        Escaping = lazy Map.empty
        Codata = lazy Codata.empty
        Edges = []
    }

    /// Set the platform context on a graph
    let withPlatform (platform: PlatformContext) (graph: SemanticGraph) : SemanticGraph =
        { graph with Platform = Some platform }

    /// Add a node to the graph
    let addNode (node: SemanticNode) (graph: SemanticGraph) : SemanticGraph =
        { graph with Nodes = Map.add node.Id node graph.Nodes }

    /// Get a node by ID
    let tryGetNode (id: NodeId) (graph: SemanticGraph) : SemanticNode option =
        Map.tryFind id graph.Nodes

    /// Get record field definitions by type name (FCS TyconRef.Deref pattern)
    /// Returns None if type is not found or is not a record type
    let tryGetRecordFields (typeName: string) (graph: SemanticGraph) : (string * NativeType) list option =
        match recallType typeName graph with
        | Some nodeId ->
            match tryGetNode nodeId graph with
            | Some node ->
                match node.Kind with
                | SemanticKind.TypeDef(_, TypeDefKind.RecordDef fields, _) -> Some fields
                | _ -> None  // Not a record type
            | None -> None  // Node not found (shouldn't happen)
        | None -> None  // Type not in index

    /// Get a node by ID (throws if not found)
    let getNode (id: NodeId) (graph: SemanticGraph) : SemanticNode =
        match Map.tryFind id graph.Nodes with
        | Some node -> node
        | None -> failwith $"Node not found: {NodeId.value id}"

    /// Add a declaration root
    let addDeclarationRoot (id: NodeId) (root: DeclRoot) (graph: SemanticGraph) : SemanticGraph =
        { graph with DeclarationRoots = (id, root) :: graph.DeclarationRoots }

    /// Get all nodes of a given kind
    let nodesOfKind (predicate: SemanticKind -> bool) (graph: SemanticGraph) : SemanticNode list =
        graph.Nodes
        |> Map.values
        |> Seq.filter (fun n -> predicate n.Kind)
        |> List.ofSeq

    /// Get all bindings in the graph
    let bindings (graph: SemanticGraph) : SemanticNode list =
        nodesOfKind (function SemanticKind.Binding _ -> true | _ -> false) graph

    //---------------------------------------------------------------------
    // F: the hyperedge set. Queries are pure projections; additions return
    // a new graph. The emission traversal never calls these (PHG paper 2.4).
    //---------------------------------------------------------------------

    /// Add nodes to V.
    let addNodes (nodes: SemanticNode list) (graph: SemanticGraph) : SemanticGraph =
        { graph with Nodes = nodes |> List.fold (fun acc n -> Map.add n.Id n acc) graph.Nodes }

    /// Add hyperedges to F.
    let addEdges (edges: Hyperedge list) (graph: SemanticGraph) : SemanticGraph =
        { graph with Edges = graph.Edges @ edges }

    /// Edges whose target is `id`: what produces or constrains this node.
    let edgesInto (id: NodeId) (graph: SemanticGraph) : Hyperedge list =
        graph.Edges |> List.filter (fun e -> e.Target = id)

    /// Edges in whose source set `id` appears: what this node produces or constrains.
    let edgesFrom (id: NodeId) (graph: SemanticGraph) : Hyperedge list =
        graph.Edges |> List.filter (fun e -> List.contains id e.Sources)

    /// Every obligation node, with its record, in NodeId order (deterministic
    /// for the ledger and for twin pairing).
    let obligations (graph: SemanticGraph) : (SemanticNode * ObligationInfo) list =
        graph.Nodes
        |> Map.toList
        |> List.choose (fun (_, n) ->
            match n.Kind with
            | SemanticKind.Obligation info -> Some (n, info)
            | _ -> None)

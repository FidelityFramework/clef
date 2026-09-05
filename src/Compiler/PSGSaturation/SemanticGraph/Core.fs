// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Core operations on SemanticGraph - creation, querying, saturation computation.
/// This module computes lazy coeffects like ModuleClassifications and SeqSaturation.
module Clef.Compiler.PSGSaturation.SemanticGraph.Core

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.SeqSaturation

//-------------------------------------------------------------------------
// SemanticGraph Module - Core Operations
//-------------------------------------------------------------------------

module SemanticGraph =
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

    // ═══════════════════════════════════════════════════════════════════════════
    // SEQ SATURATION - Extract state machine structure from SeqExpr nodes
    // ═══════════════════════════════════════════════════════════════════════════

    /// Check if a node is a literal boolean value
    let private isLiteralBool (nodes: Map<NodeId, SemanticNode>) (nodeId: NodeId) : bool option =
        match Map.tryFind nodeId nodes with
        | Some node ->
            match node.Kind with
            | SemanticKind.Literal (NativeLiteral.Bool b) -> Some b
            | _ -> None
        | None -> None

    /// Collect all Yield nodes in a subtree in document (pre-order) order
    let rec private collectYieldsInSubtree (nodes: Map<NodeId, SemanticNode>) (nodeId: NodeId) : (NodeId * NodeId) list =
        match Map.tryFind nodeId nodes with
        | None -> []
        | Some node ->
            match node.Kind with
            | SemanticKind.IfThenElse (condId, thenId, elseIdOpt) ->
                match isLiteralBool nodes condId with
                | Some false ->
                    match elseIdOpt with
                    | Some elseId -> collectYieldsInSubtree nodes elseId
                    | None -> []
                | Some true ->
                    collectYieldsInSubtree nodes thenId
                | None ->
                    let thenYields = collectYieldsInSubtree nodes thenId
                    let elseYields =
                        match elseIdOpt with
                        | Some elseId -> collectYieldsInSubtree nodes elseId
                        | None -> []
                    thenYields @ elseYields
            | SemanticKind.Yield valueId ->
                [(nodeId, valueId)]
            | _ ->
                node.Children
                |> List.collect (fun childId -> collectYieldsInSubtree nodes childId)

    /// Collect all mutable bindings in a subtree (internal state fields)
    let rec private collectMutableBindings (nodes: Map<NodeId, SemanticNode>) (nodeId: NodeId) (numCaptures: int) : SeqInternalStateField list =
        match Map.tryFind nodeId nodes with
        | None -> []
        | Some node ->
            let thisBinding =
                match node.Kind with
                | SemanticKind.Binding (name, isMutable, _, _) when isMutable ->
                    [{ Name = name; Type = node.Type; BindingId = node.Id; StructIndex = 0 }]  // Index set later
                | _ -> []
            let childBindings =
                node.Children
                |> List.collect (fun childId -> collectMutableBindings nodes childId numCaptures)
            thisBinding @ childBindings

    /// Check if a node is a WhileLoop
    let private isWhileLoop (nodes: Map<NodeId, SemanticNode>) (nodeId: NodeId) : (NodeId * NodeId) option =
        match Map.tryFind nodeId nodes with
        | Some node ->
            match node.Kind with
            | SemanticKind.WhileLoop (guardId, bodyId) -> Some (guardId, bodyId)
            | _ -> None
        | None -> None

    /// Check if a node is a Sequential
    let private isSequential (nodes: Map<NodeId, SemanticNode>) (nodeId: NodeId) : NodeId list option =
        match Map.tryFind nodeId nodes with
        | Some node ->
            match node.Kind with
            | SemanticKind.Sequential nodeIds -> Some nodeIds
            | _ -> None
        | None -> None

    /// Flatten nested Sequentials into a single list
    let rec private flattenSequentials (nodes: Map<NodeId, SemanticNode>) (nodeIds: NodeId list) : NodeId list =
        nodeIds
        |> List.collect (fun nodeId ->
            match isSequential nodes nodeId with
            | Some innerNodes -> flattenSequentials nodes innerNodes
            | None -> [nodeId])

    /// Check if a node is a conditional yield
    let private isConditionalYield (nodes: Map<NodeId, SemanticNode>) (nodeId: NodeId) : SeqConditionalYieldInfo option =
        let rec collectConditions (nId: NodeId) (accConditions: NodeId list) : (NodeId * NodeId list) option =
            match Map.tryFind nId nodes with
            | Some node ->
                match node.Kind with
                | SemanticKind.IfThenElse (condId, thenId, _) ->
                    let newConditions = accConditions @ [condId]
                    match Map.tryFind thenId nodes with
                    | Some thenNode ->
                        match thenNode.Kind with
                        | SemanticKind.IfThenElse _ ->
                            collectConditions thenId newConditions
                        | SemanticKind.Yield _ ->
                            Some (nId, newConditions)
                        | _ ->
                            let yields = collectYieldsInSubtree nodes thenId
                            if not (List.isEmpty yields) then Some (nId, newConditions) else None
                    | None -> None
                | _ -> None
            | None -> None
        match Map.tryFind nodeId nodes with
        | Some node ->
            match node.Kind with
            | SemanticKind.IfThenElse _ ->
                match collectConditions nodeId [] with
                | Some (outerIfId, conditions) ->
                    Some { IfNodeId = outerIfId; ConditionIds = conditions }
                | None -> None
            | _ -> None
        | None -> None

    /// Analyze body structure for a sequence expression
    let private analyzeBodyStructure (nodes: Map<NodeId, SemanticNode>) (bodyId: NodeId) (yields: (NodeId * NodeId) list) : SeqBodyKind =
        let actualBodyId =
            match Map.tryFind bodyId nodes with
            | Some node ->
                match node.Kind with
                | SemanticKind.Lambda(_, lambdaBodyId, _, _, _) -> lambdaBodyId
                | _ -> bodyId
            | None -> bodyId

        let rec findWhileInSequence (nodeList: NodeId list) (accInit: NodeId list) =
            match nodeList with
            | [] -> None
            | nodeId :: remaining ->
                match isWhileLoop nodes nodeId with
                | Some (guardId, whileBodyId) ->
                    Some (List.rev accInit, (nodeId, guardId, whileBodyId))
                | None ->
                    match isSequential nodes nodeId with
                    | Some nestedNodes ->
                        match findWhileInSequence nestedNodes (nodeId :: accInit) with
                        | Some result -> Some result
                        | None -> findWhileInSequence remaining (nodeId :: accInit)
                    | None ->
                        findWhileInSequence remaining (nodeId :: accInit)

        match isSequential nodes actualBodyId with
        | Some nodeList ->
            match findWhileInSequence nodeList [] with
            | Some (initExprs, (whileNodeId, conditionId, whileBodyId)) ->
                match isSequential nodes whileBodyId with
                | Some whileBodyNodes ->
                    let whileYields = collectYieldsInSubtree nodes whileBodyId
                    match whileYields with
                    | [(yieldNodeId, yieldValueId)] ->
                        let flattenedBody = flattenSequentials nodes whileBodyNodes
                        let rec splitAtYield (splitNodes: NodeId list) (pre: NodeId list) =
                            match splitNodes with
                            | [] -> (List.rev pre, [])
                            | nId :: rest ->
                                let nodeYields = collectYieldsInSubtree nodes nId
                                if not (List.isEmpty nodeYields) then
                                    (List.rev pre, rest)
                                else
                                    splitAtYield rest (nId :: pre)
                        let (preYield, postYield) = splitAtYield flattenedBody []
                        let conditionalYield = whileBodyNodes |> List.tryPick (fun nId -> isConditionalYield nodes nId)
                        SeqBodyKind.WhileBased {
                            InitExprs = initExprs
                            WhileNodeId = whileNodeId
                            ConditionId = conditionId
                            PreYieldExprs = preYield
                            YieldNodeId = yieldNodeId
                            YieldValueId = yieldValueId
                            PostYieldExprs = postYield
                            ConditionalYield = conditionalYield
                        }
                    | _ -> SeqBodyKind.Sequential yields
                | None ->
                    match Map.tryFind whileBodyId nodes with
                    | Some whileBodyNode ->
                        match whileBodyNode.Kind with
                        | SemanticKind.Yield valueId ->
                            SeqBodyKind.WhileBased {
                                InitExprs = initExprs
                                WhileNodeId = whileNodeId
                                ConditionId = conditionId
                                PreYieldExprs = []
                                YieldNodeId = whileBodyId
                                YieldValueId = valueId
                                PostYieldExprs = []
                                ConditionalYield = None
                            }
                        | SemanticKind.IfThenElse (condId, thenId, _) ->
                            let ifYields = collectYieldsInSubtree nodes thenId
                            match ifYields with
                            | [(yieldId, valueId)] ->
                                SeqBodyKind.WhileBased {
                                    InitExprs = initExprs
                                    WhileNodeId = whileNodeId
                                    ConditionId = conditionId
                                    PreYieldExprs = []
                                    YieldNodeId = yieldId
                                    YieldValueId = valueId
                                    PostYieldExprs = []
                                    ConditionalYield = Some { IfNodeId = whileBodyId; ConditionIds = [condId] }
                                }
                            | _ -> SeqBodyKind.Sequential yields
                        | _ -> SeqBodyKind.Sequential yields
                    | None -> SeqBodyKind.Sequential yields
            | None -> SeqBodyKind.Sequential yields
        | None ->
            match isWhileLoop nodes actualBodyId with
            | Some (conditionId, whileBodyId) ->
                let whileYields = collectYieldsInSubtree nodes whileBodyId
                match whileYields with
                | [(yieldNodeId, yieldValueId)] ->
                    SeqBodyKind.WhileBased {
                        InitExprs = []
                        WhileNodeId = actualBodyId
                        ConditionId = conditionId
                        PreYieldExprs = []
                        YieldNodeId = yieldNodeId
                        YieldValueId = yieldValueId
                        PostYieldExprs = []
                        ConditionalYield = None
                    }
                | _ -> SeqBodyKind.Sequential yields
            | None -> SeqBodyKind.Sequential yields

    /// Extract sequence saturation info for all SeqExpr nodes
    let private extractSeqSaturation (nodes: Map<NodeId, SemanticNode>) : Map<NodeId, SeqStateMachineInfo> =
        nodes
        |> Map.values
        |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.SeqExpr (bodyId, captures) ->
                let yields = collectYieldsInSubtree nodes bodyId
                let bodyKind = analyzeBodyStructure nodes bodyId yields
                let numCaptures = List.length captures
                let mutableBindings = collectMutableBindings nodes bodyId numCaptures
                let internalState =
                    mutableBindings
                    |> List.mapi (fun i field ->
                        { field with StructIndex = 3 + numCaptures + i })
                let elementType =
                    match node.Type with
                    | NativeType.TSeq elemTy -> elemTy
                    | _ -> NativeType.TError "Expected TSeq type for SeqExpr"
                Some (node.Id, {
                    OriginalSeqExprId = node.Id
                    BodyKind = bodyKind
                    Captures = captures
                    InternalState = internalState
                    ElementType = elementType
                })
            | _ -> None)
        |> Map.ofSeq

    /// Create lazy seq saturation coeffect from nodes
    let mkSeqSaturation (nodes: Map<NodeId, SemanticNode>) : Lazy<Map<NodeId, SeqStateMachineInfo>> =
        lazy (extractSeqSaturation nodes)

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
        SeqSaturation = lazy Map.empty
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
        SeqSaturation = lazy Map.empty
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

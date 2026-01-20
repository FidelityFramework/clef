// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Node builder for constructing SemanticNodes with proper type attachment.
module FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Builder

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Core

//-------------------------------------------------------------------------
// Node Builder
//-------------------------------------------------------------------------

/// Builder for creating semantic nodes with type attached
type NodeBuilder() =
    let mutable nodes = Map.empty<NodeId, SemanticNode>

    /// Create a new node and add it to the builder
    member _.Create(kind: SemanticKind, ty: NativeType, range: SourceRange,
                    ?srtp: WitnessResolution, ?arena: ArenaAffinity,
                    ?layout: TypeLayout, ?children: NodeId list,
                    ?parent: NodeId, ?emission: EmissionStrategy) : SemanticNode =
        let id = NodeId.fresh()
        let node = {
            Id = id
            Kind = kind
            Range = range
            Type = ty
            SRTPResolution = srtp
            ArenaAffinity = defaultArg arena ArenaAffinity.CurrentActor
            LayoutHint = layout
            Children = defaultArg children []
            Parent = parent
            Metadata = Map.empty
            IsReachable = true  // Default to reachable; soft-delete marks false
            EmissionStrategy = defaultArg emission EmissionStrategy.Inline
        }
        nodes <- Map.add id node nodes
        node

    /// Get all nodes created by this builder
    member _.Nodes = nodes

    /// Set parent on an existing node (for bidirectional parent-child links)
    /// ARCHITECTURAL NOTE: Child is created first, then parent. This method
    /// allows setting the parent after both are created.
    member _.SetParent(childId: NodeId, parentId: NodeId) =
        match Map.tryFind childId nodes with
        | Some node ->
            let updated = { node with Parent = Some parentId }
            nodes <- Map.add childId updated nodes
        | None -> ()  // Node not found (shouldn't happen)

    /// Set children on an existing node (for recursive bindings)
    /// PRD-13: Recursive bindings pre-create Binding nodes to get NodeIds,
    /// then set children after the Lambda is created.
    member _.SetChildren(nodeId: NodeId, children: NodeId list) =
        match Map.tryFind nodeId nodes with
        | Some node ->
            let updated = { node with Children = children }
            nodes <- Map.add nodeId updated nodes
        | None -> ()

    /// Set emission strategy on an existing node
    /// Used to mark Lambda/SeqExpr bodies as SeparateFunction after creation.
    member _.SetEmissionStrategy(nodeId: NodeId, strategy: EmissionStrategy) =
        match Map.tryFind nodeId nodes with
        | Some node ->
            let updated = { node with EmissionStrategy = strategy }
            nodes <- Map.add nodeId updated nodes
        | None -> ()

    /// Build the semantic graph
    member _.Build(entryPoints: NodeId list) : SemanticGraph =
        { Nodes = nodes
          EntryPoints = entryPoints
          Modules = Map.empty
          Types = SemanticGraph.mkTypesIndex nodes
          Platform = None
          ModuleClassifications = SemanticGraph.mkModuleClassifications nodes
          SeqSaturation = SemanticGraph.mkSeqSaturation nodes }

    /// Build the semantic graph with platform context
    member _.BuildWithPlatform(entryPoints: NodeId list, platform: PlatformContext) : SemanticGraph =
        { Nodes = nodes
          EntryPoints = entryPoints
          Modules = Map.empty
          Types = SemanticGraph.mkTypesIndex nodes
          Platform = Some platform
          ModuleClassifications = SemanticGraph.mkModuleClassifications nodes
          SeqSaturation = SemanticGraph.mkSeqSaturation nodes }

    /// Reset the builder
    member _.Reset() =
        nodes <- Map.empty
        NodeId.reset()

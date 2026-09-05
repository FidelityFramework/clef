// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Node builder for constructing SemanticNodes with proper type attachment.
module Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

//-------------------------------------------------------------------------
// Node Builder
//-------------------------------------------------------------------------

/// The implied children of a node: the structural projection of the single
/// edge table (Types.kindEdges).
///
/// ARCHITECTURAL PRINCIPLE: any NodeId referenced in a SemanticKind must be
/// reachable via children for the traversal algorithms (SSA assignment,
/// reachability) to work. That relation is now defined once, in `kindEdges`,
/// and this is its `EdgeClass.Structural` projection -- it cannot drift from
/// the reachability projection in Reachability.fs, because both read the same
/// table. Reference edges (a VarRef's definition) are deliberately excluded:
/// a definition is related to a reference, not contained by it.
let private extractImpliedChildren (target: NodeId) (kind: SemanticKind) : NodeId list =
    kindEdges target kind
    |> List.filter Hyperedge.isStructural
    |> List.map Hyperedge.soleSource

/// Builder for creating semantic nodes with type attached
type NodeBuilder() =
    let mutable nodes = Map.empty<NodeId, SemanticNode>

    /// Create a new node and add it to the builder.
    /// If children is not specified, it is auto-computed from the SemanticKind.
    /// If children IS specified, the implied children from SemanticKind are
    /// merged in to ensure structural integrity.
    member _.Create(kind: SemanticKind, ty: NativeType, range: SourceRange,
                    ?srtp: WitnessResolution, ?arena: ArenaAffinity,
                    ?layout: TypeLayout, ?children: NodeId list,
                    ?parent: NodeId, ?emission: EmissionStrategy) : SemanticNode =
        let id = NodeId.fresh()
        // Compute the final children list:
        // - If no children specified, use implied children from SemanticKind
        // - If children specified, merge with implied children (union, preserving order)
        let impliedChildren = extractImpliedChildren id kind
        let finalChildren =
            match children with
            | None -> impliedChildren
            | Some explicit ->
                // Merge: explicit first, then any implied that aren't already present
                let explicitSet = Set.ofList explicit
                let additional = impliedChildren |> List.filter (fun c -> not (Set.contains c explicitSet))
                explicit @ additional
        let node = {
            Id = id
            Kind = kind
            Range = range
            Type = ty
            SRTPResolution = srtp
            ArenaAffinity = defaultArg arena ArenaAffinity.CurrentActor
            LayoutHint = layout
            Children = finalChildren
            Parent = parent
            Metadata = Map.empty
            IsReachable = true  // Default to reachable; soft-delete marks false
            EmissionStrategy = defaultArg emission EmissionStrategy.Inline
            ValueRange = None   // written by RangeAnalysis at saturation
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

    /// Set the type of an existing node.
    /// Used to attach a generalized (TForall) type scheme to a top-level function binding
    /// after its body has been checked and the constraints so far have been solved.
    member _.SetType(nodeId: NodeId, ty: NativeType) =
        match Map.tryFind nodeId nodes with
        | Some node ->
            let updated = { node with Type = ty }
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

    /// Set metadata on an existing node and return the updated node
    /// PRD-13a: Used for tuple destructuring to store element binding info
    member _.SetMetadata(nodeId: NodeId, key: string, value: MetadataValue) : SemanticNode =
        match Map.tryFind nodeId nodes with
        | Some node ->
            let updated = { node with Metadata = Map.add key value node.Metadata }
            nodes <- Map.add nodeId updated nodes
            updated
        | None -> failwith ("Node not found: " + string (let (NodeId n) = nodeId in n))

    /// Build the semantic graph
    member _.Build(declRoots: (NodeId * DeclRoot) list) : SemanticGraph =
        { Nodes = nodes
          DeclarationRoots = declRoots
          Modules = Map.empty
          Types = SemanticGraph.mkTypesIndex nodes
          Platform = None
          ModuleClassifications = SemanticGraph.mkModuleClassifications nodes
          SeqSaturation = SemanticGraph.mkSeqSaturation nodes
          FieldRanges = lazy Map.empty
          ElementRanges = lazy Map.empty
          Edges = [] }

    /// Build the semantic graph with platform context
    member _.BuildWithPlatform(declRoots: (NodeId * DeclRoot) list, platform: PlatformContext) : SemanticGraph =
        { Nodes = nodes
          DeclarationRoots = declRoots
          Modules = Map.empty
          Types = SemanticGraph.mkTypesIndex nodes
          Platform = Some platform
          ModuleClassifications = SemanticGraph.mkModuleClassifications nodes
          SeqSaturation = SemanticGraph.mkSeqSaturation nodes
          FieldRanges = lazy Map.empty
          ElementRanges = lazy Map.empty
          Edges = [] }

    /// Reset the builder
    member _.Reset() =
        nodes <- Map.empty
        NodeId.reset()

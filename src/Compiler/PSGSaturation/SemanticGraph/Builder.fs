// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Node builder for constructing SemanticNodes with proper type attachment.
module Clef.Compiler.PSGSaturation.SemanticGraph.Builder

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

//-------------------------------------------------------------------------
// Node Builder
//-------------------------------------------------------------------------

/// Extract NodeIds that are structurally embedded in a SemanticKind.
/// These are the "implied children" - nodes referenced by the kind that
/// should be traversable via the children field.
///
/// ARCHITECTURAL PRINCIPLE (January 2026):
/// This function ensures structural integrity of the PSG. Any NodeId
/// referenced in a SemanticKind must be reachable via children for
/// traversal algorithms (SSA assignment, reachability, etc.) to work.
let private extractImpliedChildren (kind: SemanticKind) : NodeId list =
    match kind with
    | SemanticKind.Application (func, args) -> func :: args
    | SemanticKind.Lambda (params', body, _, _, _) ->
        // Parameters have NodeIds (third element of tuple) + body
        let paramIds = params' |> List.map (fun (_, _, nodeId) -> nodeId)
        paramIds @ [body]
    | SemanticKind.Match (scrutinee, cases) ->
        let caseNodeIds = cases |> List.collect (fun c ->
            let guardAndBody = match c.Guard with Some g -> [g; c.Body] | None -> [c.Body]
            c.PatternBindings @ guardAndBody)
        scrutinee :: caseNodeIds
    | SemanticKind.CaseElimination (scrutinee, arms) ->
        scrutinee :: (arms |> List.collect (fun arm ->
            arm.Bindings
            @ (match arm.Guard with Some g -> [g] | None -> [])
            @ [arm.Body]))
    | SemanticKind.Sequential nodes -> nodes
    | SemanticKind.WhileLoop (guard, body) -> [guard; body]
    | SemanticKind.ForLoop (_, start, finish, _, body) -> [start; finish; body]
    | SemanticKind.ForEach (_, collection, body) -> [collection; body]
    | SemanticKind.IfThenElse (guard, thenB, elseB) ->
        guard :: thenB :: (Option.toList elseB)
    | SemanticKind.TryWith (body, handler) -> [body; handler]
    | SemanticKind.TryFinally (body, cleanup) -> [body; cleanup]
    | SemanticKind.RecordExpr (fields, copyFrom) ->
        let fieldIds = fields |> List.map snd
        (Option.toList copyFrom) @ fieldIds
    | SemanticKind.UnionCase (_, _, payload) -> Option.toList payload
    | SemanticKind.DUGetTag (duValue, _) -> [duValue]
    | SemanticKind.DUEliminate (duValue, _, _, _) -> [duValue]
    | SemanticKind.DUConstruct (_, _, payload, arenaHint) ->
        (Option.toList payload) @ (Option.toList arenaHint)
    | SemanticKind.TupleExpr elements -> elements
    | SemanticKind.ArrayExpr elements -> elements
    | SemanticKind.ListExpr elements -> elements
    | SemanticKind.FieldGet (expr, _) -> [expr]
    | SemanticKind.FieldSet (expr, _, value) -> [expr; value]
    | SemanticKind.IndexGet (expr, index) -> [expr; index]
    | SemanticKind.IndexSet (expr, index, value) -> [expr; index; value]
    | SemanticKind.NamedIndexedPropertySet (expr, _, index, value) -> [expr; index; value]
    | SemanticKind.TypeAnnotation (expr, _) -> [expr]
    | SemanticKind.Upcast (expr, _) -> [expr]
    | SemanticKind.Downcast (expr, _) -> [expr]
    | SemanticKind.TypeTest (expr, _) -> [expr]
    | SemanticKind.AddressOf (expr, _) -> [expr]
    | SemanticKind.Deref expr -> [expr]
    | SemanticKind.Set (target, value) -> [target; value]
    | SemanticKind.TraitCall (_, _, arg) -> [arg]
    | SemanticKind.Quote (expr, _) -> [expr]
    | SemanticKind.ObjectExpr (_, members) -> members
    | SemanticKind.ModuleDef (_, members) -> members
    | SemanticKind.TypeDef (_, _, members) -> members
    | SemanticKind.MemberDef (_, _, body) -> Option.toList body
    | SemanticKind.LazyExpr (body, _) -> [body]
    | SemanticKind.LazyForce lazyValue -> [lazyValue]
    | SemanticKind.SeqExpr (body, _) -> [body]
    | SemanticKind.Yield value -> [value]
    | SemanticKind.YieldBang seq -> [seq]
    | SemanticKind.TupleGet (tuple, _) -> [tuple]
    // Leaf nodes with no embedded NodeIds
    | SemanticKind.Binding _ | SemanticKind.Literal _ | SemanticKind.VarRef _
    | SemanticKind.PlatformBinding _ | SemanticKind.Intrinsic _
    | SemanticKind.PatternBinding _ | SemanticKind.Error _
    | SemanticKind.InterpolatedString _ -> []

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
        let impliedChildren = extractImpliedChildren kind
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
          SeqSaturation = SemanticGraph.mkSeqSaturation nodes }

    /// Build the semantic graph with platform context
    member _.BuildWithPlatform(declRoots: (NodeId * DeclRoot) list, platform: PlatformContext) : SemanticGraph =
        { Nodes = nodes
          DeclarationRoots = declRoots
          Modules = Map.empty
          Types = SemanticGraph.mkTypesIndex nodes
          Platform = Some platform
          ModuleClassifications = SemanticGraph.mkModuleClassifications nodes
          SeqSaturation = SemanticGraph.mkSeqSaturation nodes }

    /// Reset the builder
    member _.Reset() =
        nodes <- Map.empty
        NodeId.reset()

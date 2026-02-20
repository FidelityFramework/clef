// SPDX-License-Identifier: MIT

/// Fold-In pass: integrates a RecipeSet into a PSG, producing a fresh PSG.
/// 
/// This is a single-pass traversal that builds a new graph where:
/// - Nodes with recipes → recipe's NewNodes included, original excluded
/// - Nodes without recipes → included with updated child references
/// 
/// The original PSG is not mutated; a fresh PSG is built.
/// 
/// See: psg_elaboration_fold_architecture.md (Serena memory)
module Clef.Compiler.Nanopass.FoldIn

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.Nanopass.Recipe

//=============================================================================
// REFERENCE UPDATE HELPERS
//=============================================================================

/// Update a NodeId reference using the replacement map
let private updateRef (replacementMap: Map<NodeId, NodeId>) (nodeId: NodeId) : NodeId =
    match Map.tryFind nodeId replacementMap with
    | Some replacement -> replacement
    | None -> nodeId

/// Update all NodeId references in a SemanticKind
let private updateKindRefs (replacementMap: Map<NodeId, NodeId>) (kind: SemanticKind) : SemanticKind =
    let update = updateRef replacementMap
    match kind with
    | SemanticKind.Application (funcId, args) ->
        SemanticKind.Application (update funcId, List.map update args)
    | SemanticKind.Lambda (params', body, captures, enclosing, ctx) ->
        let updatedParams = params' |> List.map (fun (name, ty, nodeId) -> (name, ty, update nodeId))
        SemanticKind.Lambda (updatedParams, update body, captures, enclosing, ctx)
    | SemanticKind.IfThenElse (guard, thenBr, elseBrOpt) ->
        SemanticKind.IfThenElse (update guard, update thenBr, Option.map update elseBrOpt)
    | SemanticKind.Sequential nodes ->
        SemanticKind.Sequential (List.map update nodes)
    | SemanticKind.WhileLoop (guard, body) ->
        SemanticKind.WhileLoop (update guard, update body)
    | SemanticKind.ForLoop (var, start, finish, isUp, body) ->
        SemanticKind.ForLoop (var, update start, update finish, isUp, update body)
    | SemanticKind.ForEach (var, coll, body) ->
        SemanticKind.ForEach (var, update coll, update body)
    | SemanticKind.TryWith (body, handler) ->
        SemanticKind.TryWith (update body, update handler)
    | SemanticKind.TryFinally (body, cleanup) ->
        SemanticKind.TryFinally (update body, update cleanup)
    | SemanticKind.LazyExpr (body, captures) ->
        SemanticKind.LazyExpr (update body, captures)
    | SemanticKind.SeqExpr (body, captures) ->
        SemanticKind.SeqExpr (update body, captures)
    | SemanticKind.Match (scrutinee, cases) ->
        let updatedCases = cases |> List.map (fun case ->
            { case with 
                Guard = Option.map update case.Guard
                Body = update case.Body
                PatternBindings = List.map update case.PatternBindings })
        SemanticKind.Match (update scrutinee, updatedCases)
    | SemanticKind.CaseElimination (scrutinee, arms) ->
        let updatedArms = arms |> List.map (fun arm ->
            { arm with
                Bindings = List.map update arm.Bindings
                Guard = Option.map update arm.Guard
                Body = update arm.Body })
        SemanticKind.CaseElimination (update scrutinee, updatedArms)
    | SemanticKind.RecordExpr (fields, copyFrom) ->
        let updatedFields = fields |> List.map (fun (name, nodeId) -> (name, update nodeId))
        SemanticKind.RecordExpr (updatedFields, Option.map update copyFrom)
    | SemanticKind.UnionCase (name, idx, payload) ->
        SemanticKind.UnionCase (name, idx, Option.map update payload)
    // DU Operations (January 2026)
    | SemanticKind.DUGetTag (duValue, duType) ->
        SemanticKind.DUGetTag (update duValue, duType)
    | SemanticKind.DUEliminate (duValue, caseIdx, caseName, payloadType) ->
        SemanticKind.DUEliminate (update duValue, caseIdx, caseName, payloadType)
    | SemanticKind.DUConstruct (caseName, caseIdx, payload, arenaHint) ->
        SemanticKind.DUConstruct (caseName, caseIdx, Option.map update payload, Option.map update arenaHint)
    | SemanticKind.TupleExpr elements ->
        SemanticKind.TupleExpr (List.map update elements)
    | SemanticKind.ArrayExpr elements ->
        SemanticKind.ArrayExpr (List.map update elements)
    | SemanticKind.ListExpr elements ->
        SemanticKind.ListExpr (List.map update elements)
    | SemanticKind.FieldGet (expr, fieldName) ->
        SemanticKind.FieldGet (update expr, fieldName)
    | SemanticKind.FieldSet (expr, fieldName, value) ->
        SemanticKind.FieldSet (update expr, fieldName, update value)
    | SemanticKind.IndexGet (expr, index) ->
        SemanticKind.IndexGet (update expr, update index)
    | SemanticKind.IndexSet (expr, index, value) ->
        SemanticKind.IndexSet (update expr, update index, update value)
    | SemanticKind.NamedIndexedPropertySet (expr, propName, index, value) ->
        SemanticKind.NamedIndexedPropertySet (update expr, propName, update index, update value)
    | SemanticKind.TypeAnnotation (expr, ty) ->
        SemanticKind.TypeAnnotation (update expr, ty)
    | SemanticKind.Upcast (expr, ty) ->
        SemanticKind.Upcast (update expr, ty)
    | SemanticKind.Downcast (expr, ty) ->
        SemanticKind.Downcast (update expr, ty)
    | SemanticKind.TypeTest (expr, ty) ->
        SemanticKind.TypeTest (update expr, ty)
    | SemanticKind.AddressOf (expr, isByref) ->
        SemanticKind.AddressOf (update expr, isByref)
    | SemanticKind.Deref expr ->
        SemanticKind.Deref (update expr)
    | SemanticKind.Set (target, value) ->
        SemanticKind.Set (update target, update value)
    | SemanticKind.Quote (expr, isTyped) ->
        SemanticKind.Quote (update expr, isTyped)
    | SemanticKind.ObjectExpr (interfaceType, members) ->
        SemanticKind.ObjectExpr (interfaceType, List.map update members)
    | SemanticKind.ModuleDef (name, members) ->
        SemanticKind.ModuleDef (name, List.map update members)
    | SemanticKind.TypeDef (name, kind, members) ->
        SemanticKind.TypeDef (name, kind, List.map update members)
    | SemanticKind.MemberDef (name, kind, body) ->
        SemanticKind.MemberDef (name, kind, Option.map update body)
    | SemanticKind.InterpolatedString parts ->
        let updatedParts = parts |> List.map (function
            | InterpolatedPart.ExprPart nodeId -> InterpolatedPart.ExprPart (update nodeId)
            | other -> other)
        SemanticKind.InterpolatedString updatedParts
    | SemanticKind.LazyForce lazyValue ->
        SemanticKind.LazyForce (update lazyValue)
    | SemanticKind.Yield value ->
        SemanticKind.Yield (update value)
    | SemanticKind.YieldBang seq ->
        SemanticKind.YieldBang (update seq)
    | SemanticKind.TupleGet (tuple, index) ->
        SemanticKind.TupleGet (update tuple, index)
    | SemanticKind.TraitCall (memberName, types, arg) ->
        SemanticKind.TraitCall (memberName, types, update arg)
    // Leaf nodes - no references to update
    | SemanticKind.Binding _ 
    | SemanticKind.Literal _
    | SemanticKind.VarRef _
    | SemanticKind.PlatformBinding _
    | SemanticKind.Intrinsic _
    | SemanticKind.PatternBinding _
    | SemanticKind.Error _ -> kind

/// Update all NodeId references in a node's Children list
let private updateChildRefs (replacementMap: Map<NodeId, NodeId>) (children: NodeId list) : NodeId list =
    children |> List.map (updateRef replacementMap)


//=============================================================================
// FOLD-IN PASS
//=============================================================================

/// Fold a RecipeSet into a PSG, producing a fresh PSG.
///
/// This is Pass 2 (Intrinsic Fold-In) or Pass 4 (Saturation Fold-In).
let foldIn (recipeSet: RecipeSet) (graph: SemanticGraph) : SemanticGraph =
    let replacementMap = recipeSet.ReplacementMap

    // Collect all new nodes from recipes AND update their cross-recipe references.
    // This is critical for recipe collision: when Recipe A creates nodes referencing
    // nodes that Recipe B replaces, A's nodes need their references updated.
    let newNodesFromRecipes =
        recipeSet.Recipes
        |> Map.toSeq |> Seq.map snd
        |> Seq.collect (fun r -> r.NewNodes)
        |> Seq.map (fun n ->
            // Update references in recipe-created nodes
            let updatedKind = updateKindRefs replacementMap n.Kind
            let updatedChildren = updateChildRefs replacementMap n.Children
            let updatedNode = { n with Kind = updatedKind; Children = updatedChildren }
            n.Id, updatedNode)
        |> Map.ofSeq

    // Build the new nodes map:
    // 1. Add new nodes from recipes
    // 2. For existing nodes: include if not being replaced, with updated references
    // 3. If a new node exists at the same NodeId, the new node wins (in-place replacement)
    let newNodes =
        graph.Nodes
        |> Map.fold (fun acc nodeId node ->
            if RecipeSet.hasRecipe nodeId recipeSet then
                // This node is being replaced - don't include it
                acc
            elif Map.containsKey nodeId acc then
                // A new node already exists at this ID (e.g., Binding replacing PatternBinding)
                // Keep the new node - it has the proper value source
                acc
            else
                // Update references and include
                let updatedKind = updateKindRefs replacementMap node.Kind
                let updatedChildren = updateChildRefs replacementMap node.Children
                let updatedParent = node.Parent |> Option.map (updateRef replacementMap)
                let updatedNode =
                    { node with
                        Kind = updatedKind
                        Children = updatedChildren
                        Parent = updatedParent }
                Map.add nodeId updatedNode acc
        ) newNodesFromRecipes

    //=========================================================================
    // PARENT EDGE LINKAGE
    //=========================================================================
    // Recipe-created nodes have Parent = None. We now establish Parent edges
    // based on Children relationships, making the graph fully traversable.
    //
    // For each node, we look at its Children and set each child's Parent to
    // point back to this node.
    //=========================================================================
    let nodesWithParents =
        newNodes
        |> Map.fold (fun acc parentId parentNode ->
            parentNode.Children
            |> List.fold (fun acc' childId ->
                match Map.tryFind childId acc' with
                | Some (childNode: SemanticNode) ->
                    let updatedChild: SemanticNode = { childNode with Parent = Some parentId }
                    Map.add childId updatedChild acc'
                | None -> acc'
            ) acc
        ) newNodes
    
    // Update declaration roots if any were replaced
    let updatedDeclRoots =
        graph.DeclarationRoots |> List.map (fun (id, root) -> (updateRef replacementMap id, root))

    // Update module mappings
    let updatedModules =
        graph.Modules
        |> Map.map (fun _path nodeIds -> nodeIds |> List.map (updateRef replacementMap))

    // Build fresh graph
    let resultGraph = {
        Nodes = nodesWithParents
        DeclarationRoots = updatedDeclRoots
        Modules = updatedModules
        Types = SemanticGraph.mkTypesIndex nodesWithParents
        Platform = graph.Platform
        ModuleClassifications = SemanticGraph.mkModuleClassifications nodesWithParents
        SeqSaturation = SemanticGraph.mkSeqSaturation nodesWithParents
    }

    // NOTE: Reachability validation removed (Feb 2026)
    // Rationale: Two-pass reachability architecture
    //   - First pass marks what to transform (efficiency)
    //   - FoldIn applies transformations (trusts recipe creation)
    //   - Final pass re-establishes truth after transformations (source of truth)
    // Mid-flight validation created paradox: two definitions of "reachable"
    //   - PSG marks module bodies as reachable (151 nodes)
    //   - Children traversal from entry only reaches 30 nodes
    // Solution: Trust recipe creation, validate once at end

    resultGraph

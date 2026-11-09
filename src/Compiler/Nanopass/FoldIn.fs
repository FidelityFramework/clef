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
// REFERENCE IDENTITY REWRITING
//=============================================================================

/// Update a NodeId reference using the replacement map
let private updateRef (replacementMap: Map<NodeId, NodeId>) (nodeId: NodeId) : NodeId =
    match Map.tryFind nodeId replacementMap with
    | Some replacement -> replacement
    | None -> nodeId

let private remapSchemeReferences replacements metadata =
    metadata |> Map.map (fun key value ->
        match value with
        | MetadataValue.NodeId id when key = SchemeMetadata.Definition || key = SchemeMetadata.ImplementationDeclaration ->
            MetadataValue.NodeId(updateRef replacements id)
        | _ -> value)

/// Redirect semantic references by identity, including resolved definitions and
/// capture sources. Recipes may use the same operation with a scope-local map;
/// it does not change types, capture modes, provenance ranges or graph topology.
let remapKindReferences (replacementMap: Map<NodeId, NodeId>) (kind: SemanticKind) : SemanticKind =
    let update = updateRef replacementMap
    let updateCaptures captures =
        captures |> List.map (fun capture ->
            { capture with SourceNodeId = Option.map update capture.SourceNodeId })
    match kind with
    | SemanticKind.Application (funcId, args) ->
        SemanticKind.Application (update funcId, List.map update args)
    | SemanticKind.Lambda (params', body, captures, enclosing, ctx) ->
        let updatedParams = params' |> List.map (fun (name, ty, nodeId) -> (name, ty, update nodeId))
        SemanticKind.Lambda (updatedParams, update body, updateCaptures captures, enclosing, ctx)
    | SemanticKind.VarRef (name, definition) ->
        SemanticKind.VarRef (name, Option.map update definition)
    | SemanticKind.IfThenElse (guard, thenBr, elseBrOpt) ->
        SemanticKind.IfThenElse (update guard, update thenBr, Option.map update elseBrOpt)
    | SemanticKind.Require(condition, diagnostic) -> SemanticKind.Require(update condition, diagnostic)
    | SemanticKind.Sequential nodes ->
        SemanticKind.Sequential (List.map update nodes)
    | SemanticKind.WhileLoop (guard, body) ->
        SemanticKind.WhileLoop (update guard, update body)
    | SemanticKind.ContinuationDispatch (selector, cases, otherwise) ->
        SemanticKind.ContinuationDispatch (update selector, cases |> List.map (fun (state, body) -> state, update body), update otherwise)
    | SemanticKind.AggregateStorage source -> SemanticKind.AggregateStorage (update source)
    | SemanticKind.DUInitialize (destination, name, index, payload) -> SemanticKind.DUInitialize (update destination, name, index, Option.map update payload)
    | SemanticKind.FrameRead (frame, slot) -> SemanticKind.FrameRead (update frame, update slot)
    | SemanticKind.FrameBorrow (frame, slot) -> SemanticKind.FrameBorrow (update frame, update slot)
    | SemanticKind.FrameWrite (frame, slot, value) -> SemanticKind.FrameWrite (update frame, update slot, update value)
    | SemanticKind.ContinuationStorage owner -> SemanticKind.ContinuationStorage (update owner)
    | SemanticKind.ContinuationAllocate owner -> SemanticKind.ContinuationAllocate (update owner)
    | SemanticKind.ClosureValue (implementation, environment) -> SemanticKind.ClosureValue (update implementation, update environment)
    | SemanticKind.EnvironmentCreate (owner, initializers) ->
        SemanticKind.EnvironmentCreate (update owner, initializers |> List.map (fun (slot, value) -> update slot, update value))
    | SemanticKind.EnvironmentAllocate owner -> SemanticKind.EnvironmentAllocate(update owner)
    | SemanticKind.EnvironmentReference value -> SemanticKind.EnvironmentReference (update value)
    | SemanticKind.EnvironmentRead (environment, slot) -> SemanticKind.EnvironmentRead (update environment, update slot)
    | SemanticKind.EnvironmentBorrow (environment, slot) -> SemanticKind.EnvironmentBorrow (update environment, update slot)
    | SemanticKind.EnvironmentWrite (environment, slot, value) -> SemanticKind.EnvironmentWrite (update environment, update slot, update value)
    | SemanticKind.ForLoop (var, start, finish, isUp, body) ->
        SemanticKind.ForLoop (var, update start, update finish, isUp, update body)
    | SemanticKind.ForEach (var, formal, coll, body) ->
        SemanticKind.ForEach (var, update formal, update coll, update body)
    | SemanticKind.TryWith (body, handler) ->
        SemanticKind.TryWith (update body, update handler)
    | SemanticKind.TryFinally (body, cleanup) ->
        SemanticKind.TryFinally (update body, update cleanup)
    | SemanticKind.LazyExpr (body, captures) ->
        SemanticKind.LazyExpr (update body, updateCaptures captures)
    | SemanticKind.LazyForce value -> SemanticKind.LazyForce(update value)
    | SemanticKind.EagerExpr operand -> SemanticKind.EagerExpr(update operand)
    | SemanticKind.LazyValue (thunk, environment) -> SemanticKind.LazyValue(update thunk, update environment)
    | SemanticKind.LazyEnvironment (owner, initializers) ->
        SemanticKind.LazyEnvironment(update owner, initializers |> List.map (fun (slot, value) -> update slot, update value))
    | SemanticKind.LazyEnvironmentReference value -> SemanticKind.LazyEnvironmentReference(update value)
    | SemanticKind.LazyAllocate owner -> SemanticKind.LazyAllocate(update owner)
    | SemanticKind.LazyRead (environment, slot) -> SemanticKind.LazyRead(update environment, update slot)
    | SemanticKind.LazyBorrow (environment, slot) -> SemanticKind.LazyBorrow(update environment, update slot)
    | SemanticKind.LazyWrite (environment, slot, value) -> SemanticKind.LazyWrite(update environment, update slot, update value)
    | SemanticKind.SeqExpr (body, captures) ->
        SemanticKind.SeqExpr (update body, updateCaptures captures)
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
    | SemanticKind.ArrayAllocate count -> SemanticKind.ArrayAllocate(update count)
    | SemanticKind.ListExpr elements ->
        SemanticKind.ListExpr (List.map update elements)
    | SemanticKind.FieldGet (expr, fieldName) ->
        SemanticKind.FieldGet (update expr, fieldName)
    | SemanticKind.StringByteBorrow source -> SemanticKind.StringByteBorrow(update source)
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
    | SemanticKind.CellAddress binding -> SemanticKind.CellAddress(update binding)
    | SemanticKind.ElementAddress(buffer, index) -> SemanticKind.ElementAddress(update buffer, update index)
    | SemanticKind.FieldAddress(receiver, field) -> SemanticKind.FieldAddress(update receiver, field)
    | SemanticKind.Reborrow source -> SemanticKind.Reborrow(update source)
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
    | SemanticKind.PlatformBinding _
    | SemanticKind.Intrinsic _
    | SemanticKind.PatternBinding _
    | SemanticKind.Obligation _
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
let private parentLinkedMaps =
    System.Runtime.CompilerServices.ConditionalWeakTable<Map<NodeId, SemanticNode>, obj>()
let private linkedSentinel = obj()

let foldIn (recipeSet: RecipeSet) (graph: SemanticGraph) : SemanticGraph =
    let replacementMap = recipeSet.ReplacementMap
    let nonIdentityReplacements = replacementMap |> Map.filter (fun k v -> k <> v)
    let hasNonIdentity = not nonIdentityReplacements.IsEmpty
    let alreadyParentLinked, _ = parentLinkedMaps.TryGetValue(graph.Nodes)
    let isIdentityFoldIn =
        recipeSet.Recipes.IsEmpty && not hasNonIdentity && alreadyParentLinked &&
        not graph.FieldRanges.IsValueCreated && graph.RangeContextFacts.IsNone && not graph.ElementRanges.IsValueCreated &&
        not graph.Layouts.IsValueCreated && graph.StaticStringPool.IsNone && graph.LiteralStorage.IsEmpty &&
        not graph.Escaping.IsValueCreated && not graph.Codata.IsValueCreated &&
        graph.WitnessProvenance.IsNone && graph.SequenceRangeProvenance.IsNone
    if isIdentityFoldIn then graph
    else
    let historical (edge: Hyperedge) =
        edge.Class = EdgeClass.Provenance &&
        match edge.Role with
        | EdgeRole.SchemeSpecialization | EdgeRole.OrdinaryBindingDemandHistory _ -> true
        | _ -> false
    // Historical derivations have two identity domains: their sources are
    // immutable snapshot identities; their target names current execution.
    // Retaining the former never adds declaration roots or live execution.
    let candidateHistoryIds =
        let set = System.Collections.Generic.HashSet<NodeId>()
        for KeyValue(id, r) in recipeSet.Recipes do
            set.Add id |> ignore
            for n in r.NewNodes do set.Add n.Id |> ignore
        set
    let historicalParticipants =
        if candidateHistoryIds.Count = 0 then Set.empty
        else
            let mutable found = Set.empty
            for edge in graph.Edges do
                if historical edge then
                    for s in edge.Sources do
                        if candidateHistoryIds.Contains s then
                            found <- Set.add s found
            found
    let preserveHistory id metadata =
        match graph.Nodes.TryFind id with
        | Some original when historicalParticipants.Contains id ->
            match original.Metadata.TryFind SchemeMetadata.Specialization with
            | Some (MetadataValue.Specialization _ as value) -> metadata |> Map.add SchemeMetadata.Specialization value
            | _ -> metadata
        | _ -> metadata

    // Collect all new nodes from recipes AND update their cross-recipe references.
    // This is critical for recipe collision: when Recipe A creates nodes referencing
    // nodes that Recipe B replaces, A's nodes need their references updated.
    let newNodesFromRecipes =
        recipeSet.Recipes
        |> Map.toSeq |> Seq.map snd
        |> Seq.collect (fun r -> r.NewNodes)
        |> Seq.map (fun n ->
            if hasNonIdentity then
                let updatedKind = remapKindReferences nonIdentityReplacements n.Kind
                let updatedChildren = updateChildRefs nonIdentityReplacements n.Children
                let updatedNode = { n with Kind = updatedKind; Children = updatedChildren
                                           Metadata = remapSchemeReferences nonIdentityReplacements n.Metadata |> Map.remove SchemeMetadata.HistoricalOnly |> preserveHistory n.Id }
                n.Id, updatedNode
            else
                let inheritedParent =
                    match n.Parent with
                    | Some _ as p -> p
                    | None ->
                        match graph.Nodes.TryFind n.Id |> Option.bind _.Parent with
                        | Some p when not (RecipeSet.hasRecipe p recipeSet) -> Some p
                        | _ -> None
                let updatedNode = { n with Parent = inheritedParent; Metadata = n.Metadata |> Map.remove SchemeMetadata.HistoricalOnly |> preserveHistory n.Id }
                n.Id, updatedNode)
        |> Map.ofSeq

    // Build the new nodes map:
    // 1. Add new nodes from recipes
    // 2. For existing nodes: include if not being replaced, with updated references
    // 3. If a new node exists at the same NodeId, the new node wins (in-place replacement)
    let newNodes =
        if not hasNonIdentity then
            let afterRemovals =
                recipeSet.Recipes
                |> Map.fold (fun acc nodeId _ ->
                    if historicalParticipants.Contains nodeId && not (Map.containsKey nodeId newNodesFromRecipes) then
                        match Map.tryFind nodeId acc with
                        | Some node ->
                            Map.add nodeId { node with IsReachable = false; Metadata = node.Metadata.Add(SchemeMetadata.HistoricalOnly, MetadataValue.Bool true) } acc
                        | None -> acc
                    else
                        Map.remove nodeId acc) graph.Nodes
            newNodesFromRecipes
            |> Map.fold (fun acc id node -> Map.add id node acc) afterRemovals
        else
            graph.Nodes
            |> Map.fold (fun acc nodeId node ->
                if RecipeSet.hasRecipe nodeId recipeSet then
                    // Historical participants survive replacement, with their
                    // original snapshot metadata and no executable reachability.
                    if historicalParticipants.Contains nodeId && not (Map.containsKey nodeId acc) then
                        Map.add nodeId { node with IsReachable = false; Metadata = node.Metadata.Add(SchemeMetadata.HistoricalOnly, MetadataValue.Bool true) } acc
                    else acc
                elif Map.containsKey nodeId acc then
                    // A new node already exists at this ID (e.g., Binding replacing PatternBinding)
                    // Keep the new node - it has the proper value source
                    acc
                else
                    // Update references and include
                    let updatedKind = remapKindReferences nonIdentityReplacements node.Kind
                    let updatedChildren = updateChildRefs nonIdentityReplacements node.Children
                    let updatedParent = node.Parent |> Option.map (updateRef nonIdentityReplacements)
                    let updatedNode =
                        { node with
                            Kind = updatedKind
                            Children = updatedChildren
                            Metadata = remapSchemeReferences nonIdentityReplacements node.Metadata
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
    // Module membership is lexical, while a startup spine may execute the
    // same declaration. Preserve lexical symbol/source identity independently
    // of the structural execution edges used for activation analysis.
    let touchesModuleDef =
        (recipeSet.Recipes |> Map.exists (fun id _ ->
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.ModuleDef _ } -> true
            | _ -> false))
        || (newNodesFromRecipes.Values |> Seq.exists (fun n ->
            match n.Kind with
            | SemanticKind.ModuleDef _ -> true
            | _ -> false))
    let canIncrementalParentLink =
        not hasNonIdentity && alreadyParentLinked && not touchesModuleDef
    let nodesWithParents =
        if canIncrementalParentLink then
            newNodesFromRecipes
            |> Map.fold (fun acc parentId parentNode ->
                (match parentNode.Metadata.TryFind SchemeMetadata.HistoricalOnly with
                 | Some(MetadataValue.Bool true) -> []
                 | _ -> parentNode.Children)
                |> List.fold (fun acc' childId ->
                    match Map.tryFind childId acc' with
                    | Some (childNode: SemanticNode) ->
                        let keepLexicalModuleParent =
                            match childNode.Parent with
                            | Some existingParentId ->
                                match Map.tryFind existingParentId acc' with
                                | Some existingParent ->
                                    match existingParent.Metadata.TryFind SchemeMetadata.HistoricalOnly, existingParent.Kind with
                                    | Some(MetadataValue.Bool true), _ -> false
                                    | _, SemanticKind.ModuleDef(_, members) -> List.contains childId members
                                    | _ -> false
                                | None -> false
                            | None -> false
                        let targetParent = if keepLexicalModuleParent then childNode.Parent.Value else parentId
                        if childNode.Parent = Some targetParent then acc'
                        else
                            let updatedChild: SemanticNode = { childNode with Parent = Some targetParent }
                            Map.add childId updatedChild acc'
                    | None -> acc'
                ) acc
            ) newNodes
        else
            let lexicalParents =
                newNodes.Values |> Seq.collect (fun node ->
                    match node.Metadata.TryFind SchemeMetadata.HistoricalOnly, node.Kind with
                    | Some(MetadataValue.Bool true), _ -> Seq.empty
                    | _, SemanticKind.ModuleDef(_, members) -> members |> Seq.map (fun memberId -> memberId, node.Id)
                    | _ -> Seq.empty) |> Map.ofSeq
            newNodes
            |> Map.fold (fun acc parentId parentNode ->
                (match parentNode.Metadata.TryFind SchemeMetadata.HistoricalOnly with
                 | Some(MetadataValue.Bool true) -> []
                 | _ -> parentNode.Children)
                |> List.fold (fun acc' childId ->
                    match Map.tryFind childId acc' with
                    | Some (childNode: SemanticNode) ->
                        let lexicalParent = lexicalParents.TryFind childId |> Option.defaultValue parentId
                        if childNode.Parent = Some lexicalParent then acc'
                        else
                            let updatedChild: SemanticNode = { childNode with Parent = Some lexicalParent }
                            Map.add childId updatedChild acc'
                    | None -> acc'
                ) acc
            ) newNodes
    parentLinkedMaps.AddOrUpdate(nodesWithParents, linkedSentinel)
    
    // Update declaration roots if any were replaced
    let updatedDeclRoots =
        if not hasNonIdentity then graph.DeclarationRoots
        else graph.DeclarationRoots |> List.map (fun (id, root) -> (updateRef nonIdentityReplacements id, root))

    // Update module mappings
    let updatedModules =
        if not hasNonIdentity then graph.Modules
        else
            graph.Modules
            |> Map.map (fun _path nodeIds -> nodeIds |> List.map (updateRef nonIdentityReplacements))

    let recipeNewEdges = recipeSet.Recipes.Values |> Seq.collect _.NewEdges |> Seq.toList
    // Build fresh graph
    let resultGraph =
      {
        Nodes = nodesWithParents
        DeclarationRoots = updatedDeclRoots
        Modules = updatedModules
        Types = SemanticGraph.mkTypesIndex nodesWithParents
        Platform = graph.Platform
        ModuleClassifications = SemanticGraph.mkModuleClassifications nodesWithParents
        // Fold-in runs before the range pass; the pass fills this on the final graph.
        FieldRanges = lazy Map.empty
        RangeContextFacts = None
        ElementRanges = lazy Map.empty
        Layouts = lazy Map.empty
        StaticStringPool = None
        LiteralStorage = Map.empty
        Escaping = lazy Map.empty
        Codata = lazy Codata.empty
        // Current incidence follows replacements. Historical sources do not:
        // rewriting them would silently turn "original" into "replacement".
        Edges =
            if not hasNonIdentity then
                if recipeNewEdges.IsEmpty then graph.Edges else graph.Edges @ recipeNewEdges
            else
                (graph.Edges @ recipeNewEdges)
                |> List.map (fun e ->
                    { e with
                        Role =
                            match e.Role with
                            | EdgeRole.StringCheckedConstruction construction when not(historical e) ->
                                let current = updateRef nonIdentityReplacements
                                EdgeRole.StringCheckedConstruction
                                    { construction with Owner=current construction.Owner;Input=current construction.Input
                                                        Snapshot=current construction.Snapshot;Length=current construction.Length
                                                        Validation=current construction.Validation;Decision=current construction.Decision
                                                        Text=current construction.Text;Success=current construction.Success
                                                        Failure=current construction.Failure;Retirement=current construction.Retirement
                                                        Returned=construction.Returned |> Option.map(fun life ->
                                                            {life with Application=current life.Application;Callee=current life.Callee;Declaration=current life.Declaration
                                                                       Implementation=current life.Implementation;Argument=current life.Argument;Formal=current life.Formal
                                                                       Body=current life.Body;Caller=current life.Caller;Actual=current life.Actual;Elimination=current life.Elimination
                                                                       SomeUse=current life.SomeUse;NoneUse=current life.NoneUse
                                                                       SomeBackingRetirement=current life.SomeBackingRetirement;SomeCarrierRetirement=current life.SomeCarrierRetirement
                                                                       NoneCarrierRetirement=current life.NoneCarrierRetirement;Uses=List.map current life.Uses
                                                                       Platform=current life.Platform;Space=current life.Space;Capacity=current life.Capacity}) }
                            | role -> role
                        Sources =
                            if historical e then e.Sources
                            else e.Sources |> List.map (updateRef nonIdentityReplacements)
                        Target = updateRef nonIdentityReplacements e.Target })
        WitnessProvenance = None
        SequenceRangeProvenance = None
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

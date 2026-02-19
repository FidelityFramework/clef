// SPDX-License-Identifier: MIT

/// Baker Saturation - Pass 3 (Fan-Out) and Pass 4 (Fold-In)
///
/// Baker saturation decomposes higher-order functions and language features
/// to primitive structures that Alex can witness directly.
///
/// Decomposition categories:
/// - HOF decomposition: List.map → recursive traversal
/// - Match expressions: Match → IfThenElse decision tree
/// - Seq expressions: seq { } → state machine (handled by SeqRecipes)
/// - Lazy expressions: lazy x → thunk structure (handled by LazyRecipes)
///
/// See: docs/PSG_Elaboration_Fold_Architecture.md
/// See: docs/Baker_Saturation_Architecture.md
module Clef.Compiler.Nanopass.BakerSaturation

open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.Nanopass.Recipe
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.ShadowAST

// Import existing recipe modules from Baker
module ListRecipes = Clef.Compiler.Baker.Recipes.ListRecipes
module MapRecipes = Clef.Compiler.Baker.Recipes.MapRecipes
module SetRecipes = Clef.Compiler.Baker.Recipes.SetRecipes
module OptionRecipes = Clef.Compiler.Baker.Recipes.OptionRecipes
module SeqRecipes = Clef.Compiler.Baker.Recipes.SeqRecipes
module StringRecipes = Clef.Compiler.Baker.Recipes.StringRecipes
module MatchRecipes = Clef.Compiler.Baker.Recipes.MatchRecipes
module NativePtrRecipes = Clef.Compiler.Baker.Recipes.NativePtrRecipes

//-------------------------------------------------------------------------
// Type Extraction Helpers (from HOFDecomposition)
//-------------------------------------------------------------------------

let private extractListElementType (ty: NativeType) : NativeType option =
    match ty with
    | NativeType.TList elemTy -> Some elemTy
    | _ -> None

let private extractMapTypes (ty: NativeType) : (NativeType * NativeType) option =
    match ty with
    | NativeType.TMap (keyTy, valTy) -> Some (keyTy, valTy)
    | _ -> None

let private extractSetElementType (ty: NativeType) : NativeType option =
    match ty with
    | NativeType.TSet elemTy -> Some elemTy
    | _ -> None

let private extractOptionInnerType (ty: NativeType) : NativeType option =
    match ty with
    | NativeType.TApp (tycon, [innerTy]) when tycon = Types.optionTyCon -> Some innerTy
    | NativeType.TApp (tycon, [innerTy]) when tycon = Types.voptionTyCon -> Some innerTy
    | _ -> None

let private extractSeqElementType (ty: NativeType) : NativeType option =
    match ty with
    | NativeType.TSeq elemTy -> Some elemTy
    | _ -> None

//-------------------------------------------------------------------------
// Decomposition Decision Logic (from HOFDecomposition)
//-------------------------------------------------------------------------

let private shouldDecomposeIntrinsic (info: IntrinsicInfo) : bool =
    match info.Module, info.Operation with
    // List HOFs
    | IntrinsicModule.List, "map" -> true
    | IntrinsicModule.List, "fold" -> true
    | IntrinsicModule.List, "filter" -> true
    | IntrinsicModule.List, "exists" -> true
    | IntrinsicModule.List, "forall" -> true
    | IntrinsicModule.List, "length" -> true
    | IntrinsicModule.List, "rev" -> true
    | IntrinsicModule.List, "append" -> true
    | IntrinsicModule.List, "collect" -> true
    | IntrinsicModule.List, "contains" -> true
    | IntrinsicModule.List, "tryPick" -> true
    | IntrinsicModule.List, "minBy" -> true
    | IntrinsicModule.List, "max" -> true
    | IntrinsicModule.List, "forall2" -> true
    | IntrinsicModule.List, "sumBy" -> true
    // Map HOFs
    | IntrinsicModule.Map, "toList" -> true
    | IntrinsicModule.Map, "toSeq" -> true
    | IntrinsicModule.Map, "tryFind" -> true
    | IntrinsicModule.Map, "add" -> true
    | IntrinsicModule.Map, "containsKey" -> true
    | IntrinsicModule.Map, "keys" -> true
    | IntrinsicModule.Map, "values" -> true
    | IntrinsicModule.Map, "forall" -> true
    // Set HOFs
    | IntrinsicModule.Set, "add" -> true
    | IntrinsicModule.Set, "contains" -> true
    | IntrinsicModule.Set, "remove" -> true
    | IntrinsicModule.Set, "union" -> true
    | IntrinsicModule.Set, "intersect" -> true
    | IntrinsicModule.Set, "difference" -> true
    // Option HOFs
    | IntrinsicModule.Option, "map" -> true
    | IntrinsicModule.Option, "bind" -> true
    | IntrinsicModule.Option, "filter" -> true
    // Seq HOFs - Producers
    | IntrinsicModule.Seq, "map" -> true
    | IntrinsicModule.Seq, "filter" -> true
    | IntrinsicModule.Seq, "collect" -> true
    | IntrinsicModule.Seq, "append" -> true
    // Seq HOFs - Consumers
    | IntrinsicModule.Seq, "toList" -> true
    | IntrinsicModule.Seq, "toArray" -> true
    | IntrinsicModule.Seq, "fold" -> true
    | IntrinsicModule.Seq, "tryPick" -> true
    | IntrinsicModule.Seq, "max" -> true
    | IntrinsicModule.Seq, "min" -> true
    | IntrinsicModule.Seq, "minBy" -> true
    | IntrinsicModule.Seq, "maxBy" -> true
    | IntrinsicModule.Seq, "exists" -> true
    | IntrinsicModule.Seq, "forall" -> true
    | IntrinsicModule.Seq, "length" -> true
    | IntrinsicModule.Seq, "isEmpty" -> true
    | IntrinsicModule.Seq, "head" -> true
    | IntrinsicModule.Seq, "tryHead" -> true
    // Primitives - Alex witnesses directly
    | IntrinsicModule.List, ("empty" | "isEmpty" | "head" | "tail" | "cons") -> false
    | IntrinsicModule.Map, ("empty" | "isEmpty") -> false
    | IntrinsicModule.Set, ("empty" | "isEmpty") -> false
    | IntrinsicModule.Option, ("isSome" | "isNone" | "get" | "defaultValue" | "some" | "none") -> false
    | IntrinsicModule.Seq, "empty" -> false
    | IntrinsicModule.Seq, "getEnumerator" -> false
    // String operations
    | IntrinsicModule.String, "concat2" -> true
    // NativePtr operations - transform to MemRef (F# semantics → MLIR semantics)
    | IntrinsicModule.NativePtr, "stackalloc" -> true
    | IntrinsicModule.NativePtr, "read" -> true
    | IntrinsicModule.NativePtr, "write" -> true
    | IntrinsicModule.NativePtr, "add" -> true
    | IntrinsicModule.NativePtr, "copy" -> true
    // Everything else
    | _ -> false

//-------------------------------------------------------------------------
// Pass 3: Saturation Fan-Out (Recipe Creation)
//-------------------------------------------------------------------------

/// Determine if a node needs Baker saturation (basic check for fan-out predicate).
/// Note: For Applications, we do a preliminary check here; createSaturationRecipe
/// will do the full check with graph access.
let private needsSaturationBasic (node: SemanticNode) : bool =
    match node.Kind with
    | SemanticKind.Match _ -> true
    | SemanticKind.UnionCase _ -> true  // DU construction needs lowering to DUConstruct
    | SemanticKind.Application _ -> true  // May or may not need decomposition, checked in recipe creation
    | _ -> false

/// Apply the appropriate recipe for an HOF intrinsic
let private applyIntrinsicRecipe
    (graph: SemanticGraph)
    (ctx: Context)
    (info: IntrinsicInfo)
    (args: NodeId list)
    (returnType: NativeType)
    : Result option =

    match info.Module with
    | IntrinsicModule.List ->
        let listArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun n -> n.Type)
            |> Option.bind extractListElementType

        match listArgType with
        | Some elemType ->
            let outputElemType = extractListElementType returnType
            let stateType =
                if info.Operation = "fold" then
                    args |> List.tryItem 1
                    |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
                    |> Option.map (fun n -> n.Type)
                else None
            ListRecipes.tryDecompose ctx info.Operation args elemType outputElemType stateType
        | None -> None

    | IntrinsicModule.Map ->
        let mapArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun n -> n.Type)
            |> Option.bind extractMapTypes

        match mapArgType with
        | Some (keyType, valueType) ->
            MapRecipes.tryDecompose ctx info.Operation args keyType valueType
        | None -> None

    | IntrinsicModule.Set ->
        let setArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun n -> n.Type)
            |> Option.bind extractSetElementType

        match setArgType with
        | Some elemType ->
            SetRecipes.tryDecompose ctx info.Operation args elemType
        | None -> None

    | IntrinsicModule.Option ->
        let optionArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun n -> n.Type)
            |> Option.bind extractOptionInnerType

        match optionArgType with
        | Some innerType ->
            let outputType = extractOptionInnerType returnType
            OptionRecipes.tryDecompose ctx info.Operation args innerType outputType
        | None -> None

    | IntrinsicModule.Seq ->
        let seqArgType =
            args
            |> List.tryLast
            |> Option.bind (fun argId -> SemanticGraph.tryGetNode argId graph)
            |> Option.map (fun n -> n.Type)
            |> Option.bind extractSeqElementType

        match seqArgType with
        | Some elemType ->
            let outputElemType = extractSeqElementType returnType
            // SeqRecipes takes stateType as 6th parameter (for fold), not graph
            let stateType = None  // Seq doesn't use stateType currently
            SeqRecipes.tryDecompose ctx info.Operation args elemType outputElemType stateType
        | None -> None

    | IntrinsicModule.String ->
        // String operations decompose to memory primitives
        StringRecipes.tryDecompose ctx info.Operation args returnType (Some returnType)

    | IntrinsicModule.NativePtr ->
        // NativePtr operations transform to MemRef intrinsics (F# semantics → MLIR semantics)
        // This is the CRITICAL transformation that eliminates NativePtr from MiddleEnd
        NativePtrRecipes.tryTransform info.Operation args returnType ctx.SourceRange ctx graph

    | _ -> None

/// Convert a Baker Result to a Nanopass Recipe
let private toRecipe (originalNodeId: NodeId) (source: string) (result: Result) : Recipe =
    {
        OriginalNodeId = originalNodeId
        NewNodes = result.NewNodes @ result.AuxFunctions
        ReplacementRootId = result.ResultNodeId
        ElaborationKind = ElaborationKind.Baker
        ElaborationSource = source
    }

/// Create a saturation recipe for a node.
/// RecipeCreator signature: SemanticNode -> SemanticGraph -> RecipeCreationResult
let private createSaturationRecipe (node: SemanticNode) (graph: SemanticGraph) : RecipeCreationResult =
    match node.Kind with
    | SemanticKind.Application (funcNodeId, argNodeIds) ->
        match SemanticGraph.tryGetNode funcNodeId graph with
        | Some funcNode ->
            // Unwrap TypeAnnotation for generic intrinsics (e.g., NativePtr.stackalloc<'T>)
            let unwrappedKind =
                match funcNode.Kind with
                | SemanticKind.TypeAnnotation (innerNodeId, _) ->
                    match SemanticGraph.tryGetNode innerNodeId graph with
                    | Some innerNode -> innerNode.Kind
                    | None -> funcNode.Kind
                | _ -> funcNode.Kind

            match unwrappedKind with
            | SemanticKind.Intrinsic info when shouldDecomposeIntrinsic info ->
                let hofName = sprintf "%A.%s" info.Module info.Operation
                let ctx = mkContext node.Range Types.unitType graph.Platform hofName node.Id

                match applyIntrinsicRecipe graph ctx info argNodeIds node.Type with
                | Some result ->
                    RecipeCreated (toRecipe node.Id hofName result)
                | None ->
                    CreationFailed (
                        sprintf "applyIntrinsicRecipe returned None for %s" hofName,
                        Map.ofList [
                            ("operation", hofName)
                            ("nodeId", string (NodeId.value node.Id))
                            ("argCount", string (List.length argNodeIds))
                        ]
                    )
            | SemanticKind.Intrinsic info ->
                NotApplicable (sprintf "Intrinsic %A.%s does not need decomposition" info.Module info.Operation)
            | _ ->
                NotApplicable "Function node is not an Intrinsic"
        | None ->
            CreationFailed (
                sprintf "Function node %d not found in graph" (NodeId.value funcNodeId),
                Map.ofList [("funcId", string (NodeId.value funcNodeId))]
            )

    | SemanticKind.Match (scrutineeId, cases) ->
        let ctx = mkContext node.Range node.Type graph.Platform "Match" node.Id
        // Tuple matches require nested tag extraction (multiple DU scrutinees).
        // Use enrichMatch (CaseElimination) for single-DU matches;
        // fall back to decomposeMatch (IfThenElse chain) for tuple matches.
        let isTupleMatch =
            match SemanticGraph.tryGetNode scrutineeId graph with
            | Some scrutineeNode ->
                match scrutineeNode.Kind with
                | SemanticKind.TupleExpr _ -> true
                | _ -> false
            | None -> false
        let result =
            if isTupleMatch then
                MatchRecipes.decomposeMatch ctx scrutineeId cases node.Type
            else
                MatchRecipes.enrichMatch ctx scrutineeId cases node.Type
        RecipeCreated (toRecipe node.Id "Match" result)

    | SemanticKind.UnionCase (caseName, caseIndex, payload) ->
        // Transform UnionCase to DUConstruct (lowered form for Alex)
        // DUConstruct adds arenaHint parameter (None = stack allocation)
        //
        // ARCHITECTURAL NOTE (February 2026): No Bits coercion.
        // Each DU case stores its native type directly into the byte-level memref.
        // memref.reinterpret_cast in Alex handles typed access at the MLIR level.
        // The "homogeneous payload slot" concept is eliminated — float stays float,
        // int stays int. Type fidelity preserved through to hardware backends.
        let ctx = mkContext node.Range node.Type graph.Platform "UnionCase" node.Id

        let newKind = SemanticKind.DUConstruct (caseName, caseIndex, payload, None)
        let newNode =
            { Id = NodeId.fresh()
              Kind = newKind
              Range = node.Range
              Type = node.Type
              SRTPResolution = node.SRTPResolution
              ArenaAffinity = node.ArenaAffinity
              LayoutHint = node.LayoutHint
              Children = match payload with Some id -> [id] | None -> []
              Parent = None
              Metadata = node.Metadata
              IsReachable = true
              EmissionStrategy = node.EmissionStrategy }
            |> markBaker "UnionCase" ctx.ExpansionId
        let result = mkResultNoShadow [newNode] newNode.Id []
        RecipeCreated (toRecipe node.Id "UnionCase" result)

    | _ ->
        NotApplicable "Node kind does not need saturation"

/// Run Pass 3: Saturation Fan-Out
/// Identifies nodes needing saturation and creates recipes in parallel.
let fanOut (graph: SemanticGraph) : RecipeSet =
    FanOut.fanOut "Saturation" needsSaturationBasic createSaturationRecipe graph

//-------------------------------------------------------------------------
// Pass 4: Saturation Fold-In
//-------------------------------------------------------------------------

/// Run Pass 4: Saturation Fold-In
/// Builds fresh PSG with saturation structures applied.
/// Uses generic FoldIn - the recipes from Pass 3 drive the transformation.
let foldIn (recipeSet: RecipeSet) (graph: SemanticGraph) : SemanticGraph =
    FoldIn.foldIn recipeSet graph

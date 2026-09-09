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

// Import existing recipe modules from Baker
module ListRecipes = Clef.Compiler.Baker.Recipes.ListRecipes
module MapRecipes = Clef.Compiler.Baker.Recipes.MapRecipes
module SetRecipes = Clef.Compiler.Baker.Recipes.SetRecipes
module OptionRecipes = Clef.Compiler.Baker.Recipes.OptionRecipes
module SeqRecipes = Clef.Compiler.Baker.Recipes.SeqRecipes
module StringRecipes = Clef.Compiler.Baker.Recipes.StringRecipes
module NumericRecipes = Clef.Compiler.Baker.Recipes.NumericRecipes
module MatchRecipes = Clef.Compiler.Baker.Recipes.MatchRecipes

/// A native callback is a declaration reference, not a closure value. Preserve
/// its edge for function-pointer settlement instead of eta-expanding it.
let private isNativeCallbackArgument (graph: SemanticGraph) (node: SemanticNode) =
    let rec parentUse child parent =
        match SemanticGraph.tryGetNode parent graph with
        | Some { Kind = SemanticKind.TypeAnnotation _; Parent = Some next } -> parentUse parent next
        | Some { Kind = SemanticKind.Application (fn, [arg]) } when arg = child ->
            match SemanticGraph.tryGetNode fn graph with
            | Some { Kind = SemanticKind.Intrinsic info } -> info.Module = IntrinsicModule.FnPtr && info.Operation = "ofFunction"
            | _ -> false
        | _ -> false
    node.Parent |> Option.exists (parentUse node.Id)

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
    // Library schemes (design (c); Dimensional_Range_Design.md §5): compare-and-select and the
    // rounding functions decompose; truncate, sqrt, atan2 and the transcendentals are atomic.
    | IntrinsicModule.Math, ("abs" | "sign" | "min" | "max" | "clamp" | "floor" | "ceiling" | "round") -> true
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
    | SemanticKind.Lambda(_, _, captures, _, LambdaContext.RegularClosure)
        when List.isEmpty captures -> true  // Zero-capture lambda may need closure pair (checked in recipe)
    | SemanticKind.VarRef (_, Some _) -> true  // A named function in value position is elaborated (checked in recipe)
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

    | IntrinsicModule.Math ->
        // The library schemes decompose over the arguments' resolved types (the operand's
        // carrier and dimension type its literals) and the application's result type.
        let argTypes =
            args |> List.choose (fun argId -> SemanticGraph.tryGetNode argId graph |> Option.map (fun n -> n.Type))
        if List.length argTypes = List.length args then
            NumericRecipes.tryDecompose ctx info.Operation args argTypes returnType
        else None

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
            // Unwrap TypeAnnotation for generic intrinsics (e.g., Array.zeroCreate<'T>)
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
                            "operation", hofName
                            "nodeId", string (NodeId.value node.Id)
                            "argCount", string (List.length argNodeIds)
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
              EmissionStrategy = node.EmissionStrategy
              ValueRange = None }
            |> markBaker "UnionCase" ctx.ExpansionId
        let result = mkResultNoShadow [newNode] newNode.Id []
        RecipeCreated (toRecipe node.Id "UnionCase" result)

    | SemanticKind.Lambda(params', body, captures, enclosing, context) when List.isEmpty captures ->
        // Anonymous function expressions are values in bindings, fields, branches and
        // returns as well as arguments. Named declarations remain direct functions.
        // When a lambda is passed as an argument, it needs closure pair construction
        // ({code_ptr, null_env}) even with zero captures, for uniform calling convention.
        //
        // This is a DMM decision: the compiler constructs the closure pair on behalf of
        // the developer. The developer writes `(fun x -> x * 2)` and the compiler
        // handles the value representation.
        let isInValuePosition =
            node.Metadata |> Map.tryFind ClosureMetadata.LambdaExpression = Some (MetadataValue.Bool true) ||
            match node.Parent with
            | Some parentId ->
                match SemanticGraph.tryGetNode parentId graph with
                | Some parentNode ->
                    match parentNode.Kind with
                    | SemanticKind.Application(_, args) ->
                        // Lambda is an argument to a function application
                        List.contains node.Id args
                    | _ -> false
                | None -> false
            | None -> false

        if isInValuePosition && not (isNativeCallbackArgument graph node) then
            let ctx = mkContext node.Range node.Type graph.Platform "Lambda" node.Id
            // Enrichment: create a new Lambda node identical to the original
            // but with ClosureMetadata marking it for closure pair construction.
            let enrichedNode =
                { Id = NodeId.fresh()
                  Kind = SemanticKind.Lambda(params', body, captures, enclosing, context)
                  Range = node.Range
                  Type = node.Type
                  SRTPResolution = node.SRTPResolution
                  ArenaAffinity = node.ArenaAffinity
                  LayoutHint = node.LayoutHint
                  Children = node.Children
                  Parent = None
                  Metadata =
                      node.Metadata
                      |> Map.add ClosureMetadata.RequiresClosurePair (MetadataValue.Bool true)
                  IsReachable = true
                  EmissionStrategy = node.EmissionStrategy
                  ValueRange = None }
                |> markBaker "Lambda" ctx.ExpansionId
            let result = mkResultNoShadow [enrichedNode] enrichedNode.Id []
            RecipeCreated (toRecipe node.Id "Lambda" result)
        else
            NotApplicable "Zero-capture lambda not in value position"

    | SemanticKind.VarRef (name, Some defId) ->
        // A named, capture-free declaration in value position needs a closure pair.
        // A reference to an existing function value already denotes a pair and must be
        // evaluated here, especially when it reads a mutable slot. Elaborating that
        // reference into a forwarding lambda would change snapshot semantics.
        // Capturing named declarations require a separate promotion plan.
        let definitionArity =
            match SemanticGraph.tryGetNode defId graph with
            | Some { Kind = SemanticKind.Binding (_, false, _, _); Children = lambdaId :: _ } ->
                match SemanticGraph.tryGetNode lambdaId graph with
                | Some ({ Kind = SemanticKind.Lambda (params', _, captures, _, _) } as lambda)
                    when List.isEmpty captures &&
                         Map.tryFind ClosureMetadata.LambdaExpression lambda.Metadata <> Some (MetadataValue.Bool true) &&
                         Map.tryFind ClosureMetadata.RequiresClosurePair lambda.Metadata <> Some (MetadataValue.Bool true) ->
                    Some params'.Length
                | _ -> None
            | _ -> None
        let inCallPosition =
            let isFuncChildOf (childId: NodeId) (parentId: NodeId) =
                match SemanticGraph.tryGetNode parentId graph with
                | Some { Kind = SemanticKind.Application (funcId, _) } -> funcId = childId
                | _ -> false
            match node.Parent with
            | Some parentId ->
                isFuncChildOf node.Id parentId ||
                match SemanticGraph.tryGetNode parentId graph with
                 | Some { Kind = SemanticKind.TypeAnnotation _; Parent = Some grandId } -> isFuncChildOf parentId grandId
                 | _ -> false
            | None -> true  // no parent: not a use
        // A field of a [<HardwareModule>] binding's Design record (Step = step) is a declaration
        // read structurally by the witness (hw.instance of the named module), not a closure.
        let rec inHardwareModuleDeclaration (nodeId: NodeId) =
            match SemanticGraph.tryGetNode nodeId graph with
            | Some { Kind = SemanticKind.Binding (_, _, _, Some DeclRoot.HardwareModule) } -> true
            | Some { Kind = SemanticKind.Binding _ } -> false
            | Some { Kind = SemanticKind.Lambda _ } -> false
            | Some { Parent = Some parentId } -> inHardwareModuleDeclaration parentId
            | _ -> false
        let rec resolved (ty: NativeType) =
            match ty with
            | NativeType.TVar tv ->
                match Clef.Compiler.NativeTypedTree.UnionFind.find tv with
                | _, Some bound -> resolved bound
                | _ -> ty
            | _ -> ty
        match definitionArity with
        | None ->
            NotApplicable "Reference is not to a capture-free named function"
        | Some _ when inCallPosition || isNativeCallbackArgument graph node ->
            NotApplicable "Function reference in call position"
        | Some _ when node.Parent |> Option.map inHardwareModuleDeclaration |> Option.defaultValue false ->
            NotApplicable "Declaration field of a hardware module Design"
        | Some arity ->
            match resolved node.Type with
            | NativeType.TFun _ as funcType ->
                let ctx = mkContext node.Range funcType graph.Platform "FunctionValue" node.Id
                let mk (kind: SemanticKind) (ty: NativeType) (children: NodeId list) : SemanticNode =
                    { Id = NodeId.fresh()
                      Kind = kind
                      Range = node.Range
                      Type = ty
                      SRTPResolution = node.SRTPResolution
                      ArenaAffinity = node.ArenaAffinity
                      LayoutHint = node.LayoutHint
                      Children = children
                      Parent = None
                      Metadata = Map.empty
                      IsReachable = true
                      EmissionStrategy = node.EmissionStrategy
                      ValueRange = None }
                    |> markBaker "FunctionValue" ctx.ExpansionId
                // One parameter per currying level of the reference's type
                let rec parameters (ty: NativeType) (acc: (string * NativeType * SemanticNode) list) (i: int) =
                    match resolved ty with
                    | NativeType.TFun (domainTy, rangeTy) ->
                        let paramName = sprintf "_eta%d" i
                        parameters rangeTy ((paramName, domainTy, mk (SemanticKind.PatternBinding paramName) domainTy []) :: acc) (i + 1)
                    | _ -> List.rev acc
                let parameterNodes = parameters funcType [] 0
                let lambdaParams = parameterNodes |> List.map (fun (paramName, domainTy, param) -> (paramName, domainTy, param.Id))
                let paramRefs =
                    parameterNodes |> List.map (fun (paramName, domainTy, param) -> mk (SemanticKind.VarRef (paramName, Some param.Id)) domainTy [])
                // The type after applying k arguments
                let rec typeAfter (ty: NativeType) (k: int) =
                    if k = 0 then resolved ty
                    else
                        match resolved ty with
                        | NativeType.TFun (_, rangeTy) -> typeAfter rangeTy (k - 1)
                        | other -> other
                // The body: a direct call saturating the definition's arity (the flat application
                // every direct call is), then one application per remaining currying level
                // when that declaration returns another function.
                let funcRef = mk (SemanticKind.VarRef (name, Some defId)) funcType []
                let direct = min arity paramRefs.Length
                let directArgs = paramRefs |> List.take direct |> List.map (fun r -> r.Id)
                let call = mk (SemanticKind.Application (funcRef.Id, directArgs)) (typeAfter funcType direct) (funcRef.Id :: directArgs)
                let applications =
                    paramRefs |> List.skip direct
                    |> List.fold (fun (apps: SemanticNode list) (r: SemanticNode) ->
                        let prev = List.last apps
                        apps @ [ mk (SemanticKind.Application (prev.Id, [r.Id])) (typeAfter prev.Type 1) [prev.Id; r.Id] ]) [call]
                // The outermost application is the lambda's body, its own function
                let body = { List.last applications with EmissionStrategy = EmissionStrategy.SeparateFunction 0 }
                let applications = (applications |> List.take (applications.Length - 1)) @ [body]
                // The enclosing function's name, as the checker records it for a written lambda
                let rec enclosingName (nodeId: NodeId) =
                    match SemanticGraph.tryGetNode nodeId graph with
                    | Some { Kind = SemanticKind.Lambda _; Parent = Some bindingId } ->
                        match SemanticGraph.tryGetNode bindingId graph with
                        | Some { Kind = SemanticKind.Binding (bindingName, _, _, _) } -> Some bindingName
                        | _ -> None
                    | Some { Kind = SemanticKind.Lambda _ } -> None
                    | Some { Parent = Some parentId } -> enclosingName parentId
                    | _ -> None
                let enclosing = node.Parent |> Option.bind enclosingName
                let paramIds = lambdaParams |> List.map (fun (_, _, id) -> id)
                let lambda0 = mk (SemanticKind.Lambda (lambdaParams, body.Id, [], enclosing, LambdaContext.RegularClosure)) funcType (paramIds @ [body.Id])
                let lambda = { lambda0 with Metadata = lambda0.Metadata |> Map.add ClosureMetadata.RequiresClosurePair (MetadataValue.Bool true) }
                let paramBindings = parameterNodes |> List.map (fun (_, _, param) -> param)
                let result = mkResultNoShadow (paramBindings @ paramRefs @ [funcRef] @ applications @ [lambda]) lambda.Id []
                RecipeCreated (toRecipe node.Id "FunctionValue" result)
            | _ ->
                NotApplicable "Function reference without a function type"

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

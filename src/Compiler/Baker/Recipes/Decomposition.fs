// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker Decomposition - Types and helpers for HOF decomposition to primitives.
///
/// ARCHITECTURAL PRINCIPLES:
/// - Recipes describe HOW to decompose higher-order operations to primitives
/// - Decomposition creates NEW PSG nodes representing the algorithm
/// - Alex witnesses the primitives; Baker creates the structure
///
/// PSG TRANSFORMATION MODEL:
/// - Input: Application node with HOF intrinsic (e.g., List.map)
/// - Output: New PSG structure using primitives (isEmpty, head, tail, cons, etc.)
/// - Original node is replaced/enriched with decomposed structure
///
/// SHADOW TRACKING (for editing transparency):
/// - Each expansion produces both PSG nodes AND a ShadowTree
/// - ShadowTree provides semantic view of synthesized code for tooling
/// - Developer can see "code I wrote" vs "compiler-saturated" at design time
///
/// See: docs/fidelity/fncs-specification.md Part 14
/// See: Serena memory "baker_shadow_ast_architecture"
module FSharp.Native.Compiler.Baker.Recipes.Decomposition

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Baker.ShadowAST

//-------------------------------------------------------------------------
// Metadata Keys for Expanded Nodes
//-------------------------------------------------------------------------

/// Metadata key indicating this node was expanded by Baker
[<Literal>]
let MetadataKey_BakerExpanded = "BakerExpanded"

/// Metadata key storing the original HOF name (e.g., "List.map")
[<Literal>]
let MetadataKey_ExpandedFrom = "ExpandedFrom"

/// Metadata key storing the expansion ID (links related nodes)
[<Literal>]
let MetadataKey_ExpansionId = "ExpansionId"

//-------------------------------------------------------------------------
// Node ID Generation
//-------------------------------------------------------------------------

/// Thread-safe expansion ID counter
let private nextExpansionId = ref 0

/// Generate a fresh expansion ID for grouping related expanded nodes
let freshExpansionId () : int =
    System.Threading.Interlocked.Increment(nextExpansionId)

//-------------------------------------------------------------------------
// Decomposition Context
//-------------------------------------------------------------------------

/// Context for decomposition operations.
/// Carries both PSG construction state and ShadowBuilder for parallel construction.
type Context = {
    /// Source range for generated nodes (inherited from original node)
    SourceRange: SourceRange
    /// Type of elements for the collection
    ElementType: NativeType
    /// Platform context
    Platform: PlatformContext option
    /// Original HOF name for metadata
    OriginalHOF: string
    /// Unique expansion ID for this decomposition
    ExpansionId: int
    /// The inspiring node that triggered this expansion
    InspiringNode: NodeId
    /// Shadow builder for constructing the shadow tree alongside PSG
    ShadowBuilder: ShadowBuilder
}

/// Create a decomposition context with parallel shadow construction
let mkContext 
    (range: SourceRange) 
    (elemType: NativeType) 
    (platform: PlatformContext option)
    (hofName: string)
    (inspiringNode: NodeId) : Context =
    let provenance = Provenance.create inspiringNode range hofName
    { SourceRange = range
      ElementType = elemType
      Platform = platform
      OriginalHOF = hofName
      ExpansionId = freshExpansionId ()
      InspiringNode = inspiringNode
      ShadowBuilder = ShadowBuilder(provenance) }

/// Create a nested context (for expansions within expansions)
let mkNestedContext (parent: Context) (hofName: string) : Context =
    let nestedProvenance = Provenance.nested parent.ShadowBuilder.Provenance hofName
    { parent with
        OriginalHOF = hofName
        ExpansionId = freshExpansionId ()
        ShadowBuilder = ShadowBuilder(nestedProvenance) }

/// Add Baker expansion metadata to a node
let markAsExpanded (ctx: Context) (node: SemanticNode) : SemanticNode =
    let metadata = 
        node.Metadata
        |> Map.add MetadataKey_BakerExpanded (MetadataValue.Bool true)
        |> Map.add MetadataKey_ExpandedFrom (MetadataValue.String ctx.OriginalHOF)
        |> Map.add MetadataKey_ExpansionId (MetadataValue.Int ctx.ExpansionId)
    { node with Metadata = metadata }

/// Create a base node with expansion metadata
let mkExpandedNode (ctx: Context) (kind: SemanticKind) (ty: NativeType) : SemanticNode =
    let id = NodeId.fresh()
    { Id = id
      Kind = kind
      Range = ctx.SourceRange  // Inherit source range for debugging
      Type = ty
      SRTPResolution = None
      ArenaAffinity = ArenaAffinity.CurrentActor
      LayoutHint = None
      Children = []
      Parent = None
      Metadata = 
        Map.empty
        |> Map.add MetadataKey_BakerExpanded (MetadataValue.Bool true)
        |> Map.add MetadataKey_ExpandedFrom (MetadataValue.String ctx.OriginalHOF)
        |> Map.add MetadataKey_ExpansionId (MetadataValue.Int ctx.ExpansionId)
      IsReachable = true
      EmissionStrategy = EmissionStrategy.Inline }

//-------------------------------------------------------------------------
// Decomposition Result
//-------------------------------------------------------------------------

/// Result of a decomposition - includes both PSG nodes and shadow tree
type Result = {
    /// New nodes created by decomposition
    NewNodes: SemanticNode list
    /// The "root" node ID that represents the result
    ResultNodeId: NodeId
    /// Auxiliary function definitions (recursive helpers, etc.)
    AuxFunctions: SemanticNode list
    /// Shadow tree for tooling transparency (None if shadow not built)
    ShadowTree: ShadowTree option
}

/// Empty decomposition result (identity transformation, no shadow)
let emptyResult nodeId : Result = {
    NewNodes = []
    ResultNodeId = nodeId
    AuxFunctions = []
    ShadowTree = None
}

/// Create result with shadow tree from context
let mkResult 
    (nodes: SemanticNode list) 
    (rootId: NodeId) 
    (auxFns: SemanticNode list)
    (rootShadowId: ShadowId)
    (semantic: SemanticShadow)
    (ctx: Context) : Result =
    let shadow = ctx.ShadowBuilder.Build(rootShadowId, semantic)
    { NewNodes = nodes
      ResultNodeId = rootId
      AuxFunctions = auxFns
      ShadowTree = Some shadow }

/// Create result without shadow (for operations that don't need transparency)
let mkResultNoShadow 
    (nodes: SemanticNode list) 
    (rootId: NodeId) 
    (auxFns: SemanticNode list) : Result =
    { NewNodes = nodes
      ResultNodeId = rootId
      AuxFunctions = auxFns
      ShadowTree = None }

/// Check if a node is a Baker-expanded node
let isExpandedNode (node: SemanticNode) : bool =
    match Map.tryFind MetadataKey_BakerExpanded node.Metadata with
    | Some (MetadataValue.Bool true) -> true
    | _ -> false

/// Get the original HOF name for an expanded node
let getExpandedFrom (node: SemanticNode) : string option =
    match Map.tryFind MetadataKey_ExpandedFrom node.Metadata with
    | Some (MetadataValue.String name) -> Some name
    | _ -> None

//-------------------------------------------------------------------------
// Shadow Building Helpers
//-------------------------------------------------------------------------

/// Helper: Create a primitive call shadow (e.g., List.isEmpty)
let shadowPrimitive (ctx: Context) (modName: string) (opName: string) (psgNode: SemanticNode) : ShadowId =
    ctx.ShadowBuilder.Primitive(modName, opName, psgNode.Id, psgNode.Type)

/// Helper: Create an application shadow
let shadowApp (ctx: Context) (func: ShadowRef) (args: ShadowRef list) (psgNode: SemanticNode) : ShadowId =
    ctx.ShadowBuilder.App(func, args, psgNode.Id, psgNode.Type)

/// Helper: Create an if-then-else shadow
let shadowIfThenElse (ctx: Context) (guard: ShadowRef) (thenBr: ShadowRef) (elseBr: ShadowRef) (psgNode: SemanticNode) : ShadowId =
    ctx.ShadowBuilder.IfThenElse(guard, thenBr, elseBr, psgNode.Id, psgNode.Type)

/// Helper: Create a let binding shadow
let shadowLet (ctx: Context) (name: string) (value: ShadowRef) (body: ShadowRef) (isRec: bool) (psgNode: SemanticNode) : ShadowId =
    ctx.ShadowBuilder.Let(name, value, body, isRec, psgNode.Id, psgNode.Type)

/// Helper: Create a literal shadow (empty, none, etc.)
let shadowLiteral (ctx: Context) (desc: string) (psgNode: SemanticNode) : ShadowId =
    ctx.ShadowBuilder.Literal(desc, psgNode.Id, psgNode.Type)

/// Helper: Create a variable reference shadow
let shadowVar (ctx: Context) (name: string) (psgNode: SemanticNode) : ShadowId =
    ctx.ShadowBuilder.Var(name, psgNode.Id, psgNode.Type)

/// Helper: Wrap a real PSG node as a shadow reference
let shadowReal (nodeId: NodeId) : ShadowRef = ShadowRef.Real nodeId

/// Helper: Wrap a shadow ID as a shadow reference
let shadowSynthetic (shadowId: ShadowId) : ShadowRef = ShadowRef.Synthetic shadowId

/// Helper: Create a RecursivePatternShadow semantic description
let mkRecursivePatternSemantic
    (operation: string)
    (baseCase: string)
    (recursiveCase: string)
    (sourceRefs: Map<string, NodeId>) : SemanticShadow =
    SemanticShadow.RecursivePattern {
        Operation = operation
        BaseCase = baseCase
        RecursiveCase = recursiveCase
        SourceRefs = sourceRefs
    }

/// Helper: Create a TransformShadow semantic description
let mkTransformSemantic
    (operation: string)
    (input: ShadowRef)
    (mapper: ShadowRef)
    (description: string) : SemanticShadow =
    SemanticShadow.Transform {
        Operation = operation
        Input = input
        Mapper = mapper
        Description = description
    }

//-------------------------------------------------------------------------
// PSG Node Construction Helpers
//-------------------------------------------------------------------------
// These helpers create actual PSG nodes for recursive decomposition.
// Used to replace placeholder Error nodes with real recursive structures.

/// Create an Intrinsic node for a collection primitive
let mkIntrinsicNode
    (ctx: Context)
    (intrModule: IntrinsicModule)
    (operation: string)
    (ty: NativeType) : SemanticNode =

    let info = {
        Module = intrModule
        Operation = operation
        Category = IntrinsicCategory.Pure  // Collection primitives are pure
        FullName = sprintf "%A.%s" intrModule operation
    }
    mkExpandedNode ctx (SemanticKind.Intrinsic info) ty

/// Create an Application node (function call)
let mkApplicationNode
    (ctx: Context)
    (funcNodeId: NodeId)
    (argNodeIds: NodeId list)
    (resultType: NativeType) : SemanticNode =

    mkExpandedNode ctx (SemanticKind.Application (funcNodeId, argNodeIds)) resultType

/// Create a VarRef node (variable reference)
let mkVarRefNode
    (ctx: Context)
    (name: string)
    (definitionNodeId: NodeId option)
    (ty: NativeType) : SemanticNode =

    mkExpandedNode ctx (SemanticKind.VarRef (name, definitionNodeId)) ty

/// Create a Binding node (let binding)
let mkBindingNode
    (ctx: Context)
    (name: string)
    (isMutable: bool)
    (isRecursive: bool)
    (valueNodeId: NodeId)
    (ty: NativeType) : SemanticNode =

    let node = mkExpandedNode ctx (SemanticKind.Binding (name, isMutable, isRecursive, false)) ty
    // Note: Children will be set by the caller (valueNodeId and body if let-in)
    { node with Children = [valueNodeId] }

/// Create a Lambda node
let mkLambdaNode
    (ctx: Context)
    (parameters: (string * NativeType * NodeId) list)
    (bodyNodeId: NodeId)
    (captures: CaptureInfo list)
    (enclosingFunction: string option)
    (lambdaContext: LambdaContext)
    (returnType: NativeType) : SemanticNode =

    // Build the full function type: param1 -> param2 -> ... -> returnType
    let funcType =
        parameters
        |> List.foldBack (fun (_, paramTy, _) acc -> NativeType.TFun (paramTy, acc))
        <| returnType

    let kind = SemanticKind.Lambda (parameters, bodyNodeId, captures, enclosingFunction, lambdaContext)
    let node = mkExpandedNode ctx kind funcType
    { node with Children = [bodyNodeId] }

/// Create an IfThenElse node
let mkIfThenElseNode
    (ctx: Context)
    (guardNodeId: NodeId)
    (thenNodeId: NodeId)
    (elseNodeIdOpt: NodeId option)
    (resultType: NativeType) : SemanticNode =

    let kind = SemanticKind.IfThenElse (guardNodeId, thenNodeId, elseNodeIdOpt)
    let node = mkExpandedNode ctx kind resultType
    let children =
        match elseNodeIdOpt with
        | Some elseId -> [guardNodeId; thenNodeId; elseId]
        | None -> [guardNodeId; thenNodeId]
    { node with Children = children }

/// Create an empty collection intrinsic call (List.empty, Map.empty, Set.empty)
/// Note: Empty collections are represented as intrinsic calls, not null literals
/// at the PSG level. Alex witnesses these to null pointers.
let mkEmptyCollectionNode
    (ctx: Context)
    (collModule: IntrinsicModule)
    (collType: NativeType) : SemanticNode =

    // Create the intrinsic node for empty
    let emptyIntrinsic = mkIntrinsicNode ctx collModule "empty" collType
    // Return just the intrinsic - it IS the empty value
    emptyIntrinsic

/// Create a Literal node for a boolean
let mkBoolLiteralNode (ctx: Context) (value: bool) : SemanticNode =
    mkExpandedNode ctx (SemanticKind.Literal (NativeLiteral.Bool value)) Types.boolType

/// Create a Literal node for an integer (int32)
let mkIntLiteralNode (ctx: Context) (value: int) : SemanticNode =
    mkExpandedNode ctx (SemanticKind.Literal (NativeLiteral.Int (int64 value, NTUKind.NTUint32))) Types.intType

/// Create a Literal node for an int64
let mkInt64LiteralNode (ctx: Context) (value: int64) : SemanticNode =
    mkExpandedNode ctx (SemanticKind.Literal (NativeLiteral.Int (value, NTUKind.NTUint64))) Types.int64Type

/// Create a Sequential node
let mkSequentialNode
    (ctx: Context)
    (nodeIds: NodeId list)
    (resultType: NativeType) : SemanticNode =

    let node = mkExpandedNode ctx (SemanticKind.Sequential nodeIds) resultType
    { node with Children = nodeIds }

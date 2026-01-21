// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker Primitives - Singleton PSG node builders wrapped in Recipe.
///
/// LAYER 1: "Raw Ingredients"
///
/// These are the atomic building blocks. Each primitive creates exactly one
/// PSG node (or a small fixed number). Patterns compose these into recursive
/// structures. Recipes compose patterns into complete algorithms.
///
/// ARCHITECTURAL ENFORCEMENT:
/// - Low-level node constructors are INTERNAL to this module
/// - Only Recipe-wrapped versions are PUBLIC
/// - Code outside Ingredients/ cannot bypass the Recipe abstraction
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
module FSharp.Native.Compiler.Baker.Ingredients.Primitives

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Baker.Ingredients.RecipeBuilder

//=============================================================================
// INTERNAL: Metadata Keys
//=============================================================================

[<Literal>]
let private MetadataKey_BakerExpanded = "BakerExpanded"

[<Literal>]
let private MetadataKey_ExpandedFrom = "ExpandedFrom"

[<Literal>]
let private MetadataKey_ExpansionId = "ExpansionId"

//=============================================================================
// INTERNAL: Low-level node construction
//=============================================================================

/// INTERNAL: Create a base node with expansion metadata
let internal mkNode (ctx: RecipeContext) (kind: SemanticKind) (ty: NativeType) : SemanticNode =
    let id = NodeId.fresh()
    { Id = id
      Kind = kind
      Range = ctx.SourceRange
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

/// INTERNAL: Create node and emit it
let internal createAndEmit (kind: SemanticKind) (ty: NativeType) : Recipe<NodeId> =
    recipe {
        let! ctx = getContext
        let node = mkNode ctx kind ty
        do! emitNode node
        return node.Id
    }

/// INTERNAL: Create node with children and emit
let internal createWithChildren (kind: SemanticKind) (ty: NativeType) (children: NodeId list) : Recipe<NodeId> =
    recipe {
        let! ctx = getContext
        let baseNode = mkNode ctx kind ty
        let node = { baseNode with Children = children }
        do! emitNode node
        return node.Id
    }

//=============================================================================
// LIST PRIMITIVES
//=============================================================================

/// Create an empty list: List.empty<'T>
/// Returns null pointer at runtime
let emptyList (elemType: NativeType) : Recipe<NodeId> =
    let listType = NativeType.TList elemType
    let info = {
        Module = IntrinsicModule.List
        Operation = "empty"
        Category = IntrinsicCategory.Pure
        FullName = "List.empty"
    }
    createAndEmit (SemanticKind.Intrinsic info) listType

/// Check if list is empty: List.isEmpty xs
let isEmpty (listNodeId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let listType = NativeType.TList elemType
    let funcType = NativeType.TFun (listType, Types.boolType)
    let info = {
        Module = IntrinsicModule.List
        Operation = "isEmpty"
        Category = IntrinsicCategory.Pure
        FullName = "List.isEmpty"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [listNodeId])) Types.boolType [funcId; listNodeId]
    }

/// Get head of list: List.head xs
let head (listNodeId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let listType = NativeType.TList elemType
    let funcType = NativeType.TFun (listType, elemType)
    let info = {
        Module = IntrinsicModule.List
        Operation = "head"
        Category = IntrinsicCategory.Pure
        FullName = "List.head"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [listNodeId])) elemType [funcId; listNodeId]
    }

/// Get tail of list: List.tail xs
let tail (listNodeId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let listType = NativeType.TList elemType
    let funcType = NativeType.TFun (listType, listType)
    let info = {
        Module = IntrinsicModule.List
        Operation = "tail"
        Category = IntrinsicCategory.Pure
        FullName = "List.tail"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [listNodeId])) listType [funcId; listNodeId]
    }

/// Prepend element to list: List.cons h t (or h :: t)
let cons (headNodeId: NodeId) (tailNodeId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let listType = NativeType.TList elemType
    let funcType = NativeType.TFun (elemType, NativeType.TFun (listType, listType))
    let info = {
        Module = IntrinsicModule.List
        Operation = "cons"
        Category = IntrinsicCategory.Pure
        FullName = "List.cons"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [headNodeId; tailNodeId])) listType [funcId; headNodeId; tailNodeId]
    }

//=============================================================================
// OPTION PRIMITIVES
//=============================================================================

/// Create None value: Option.none<'T>
let none (innerType: NativeType) : Recipe<NodeId> =
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [innerType])
    let info = {
        Module = IntrinsicModule.Option
        Operation = "none"
        Category = IntrinsicCategory.Pure
        FullName = "Option.none"
    }
    createAndEmit (SemanticKind.Intrinsic info) optionType

/// Create Some value: Option.some x
let some (valueNodeId: NodeId) (innerType: NativeType) : Recipe<NodeId> =
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [innerType])
    let funcType = NativeType.TFun (innerType, optionType)
    let info = {
        Module = IntrinsicModule.Option
        Operation = "some"
        Category = IntrinsicCategory.Pure
        FullName = "Option.some"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [valueNodeId])) optionType [funcId; valueNodeId]
    }

/// Check if option has value: Option.isSome x
let isSome (optionNodeId: NodeId) (innerType: NativeType) : Recipe<NodeId> =
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [innerType])
    let funcType = NativeType.TFun (optionType, Types.boolType)
    let info = {
        Module = IntrinsicModule.Option
        Operation = "isSome"
        Category = IntrinsicCategory.Pure
        FullName = "Option.isSome"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [optionNodeId])) Types.boolType [funcId; optionNodeId]
    }

/// Check if option is None: Option.isNone x
let isNone (optionNodeId: NodeId) (innerType: NativeType) : Recipe<NodeId> =
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [innerType])
    let funcType = NativeType.TFun (optionType, Types.boolType)
    let info = {
        Module = IntrinsicModule.Option
        Operation = "isNone"
        Category = IntrinsicCategory.Pure
        FullName = "Option.isNone"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [optionNodeId])) Types.boolType [funcId; optionNodeId]
    }

/// Get value from option: Option.get x (assumes Some)
let optionGet (optionNodeId: NodeId) (innerType: NativeType) : Recipe<NodeId> =
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [innerType])
    let funcType = NativeType.TFun (optionType, innerType)
    let info = {
        Module = IntrinsicModule.Option
        Operation = "get"
        Category = IntrinsicCategory.Pure
        FullName = "Option.get"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [optionNodeId])) innerType [funcId; optionNodeId]
    }

//=============================================================================
// STRUCTURAL PRIMITIVES
//=============================================================================

/// Create a function application node
let app (funcNodeId: NodeId) (argNodeIds: NodeId list) (resultType: NativeType) : Recipe<NodeId> =
    createWithChildren (SemanticKind.Application (funcNodeId, argNodeIds)) resultType (funcNodeId :: argNodeIds)

/// Create a single-argument application
let app1 (funcNodeId: NodeId) (argNodeId: NodeId) (resultType: NativeType) : Recipe<NodeId> =
    app funcNodeId [argNodeId] resultType

/// Create a two-argument application
let app2 (funcNodeId: NodeId) (arg1: NodeId) (arg2: NodeId) (resultType: NativeType) : Recipe<NodeId> =
    app funcNodeId [arg1; arg2] resultType

/// Create an if-then-else node
let ifThenElse (guardId: NodeId) (thenId: NodeId) (elseId: NodeId) (resultType: NativeType) : Recipe<NodeId> =
    createWithChildren 
        (SemanticKind.IfThenElse (guardId, thenId, Some elseId)) 
        resultType 
        [guardId; thenId; elseId]

/// Create a variable reference
let varRef (name: string) (defNodeId: NodeId option) (ty: NativeType) : Recipe<NodeId> =
    createAndEmit (SemanticKind.VarRef (name, defNodeId)) ty

/// Create a pattern binding (parameter in lambda)
let patternBinding (name: string) (ty: NativeType) : Recipe<NodeId> =
    createAndEmit (SemanticKind.PatternBinding name) ty

/// Create a let binding (non-recursive)
let letBind (name: string) (valueNodeId: NodeId) (ty: NativeType) : Recipe<NodeId> =
    recipe {
        let kind = SemanticKind.Binding (name, false, false, false)
        let! nodeId = createWithChildren kind ty [valueNodeId]
        do! bindVariable name nodeId ty
        return nodeId
    }

/// Create a recursive let binding
let letRecBind (name: string) (valueNodeId: NodeId) (ty: NativeType) : Recipe<NodeId> =
    recipe {
        let kind = SemanticKind.Binding (name, false, true, false)
        let! nodeId = createWithChildren kind ty [valueNodeId]
        do! bindVariable name nodeId ty
        return nodeId
    }

/// Create a lambda node
let lambda 
    (parameters: (string * NativeType) list) 
    (bodyBuilder: NodeId list -> Recipe<NodeId>)
    (returnType: NativeType) 
    : Recipe<NodeId> =
    recipe {
        // Create parameter binding nodes
        let! paramNodes = 
            parameters 
            |> List.map (fun (name, ty) -> 
                recipe {
                    let! paramId = patternBinding name ty
                    do! bindVariable name paramId ty
                    return (name, ty, paramId)
                })
            |> sequence
        
        // Build the body with parameters in scope
        let paramIds = paramNodes |> List.map (fun (_, _, id) -> id)
        let! bodyId = bodyBuilder paramIds
        
        // Compute the full function type
        let funcType =
            parameters
            |> List.foldBack (fun (_, paramTy) acc -> NativeType.TFun (paramTy, acc))
            <| returnType
        
        // Create the lambda node
        let kind = SemanticKind.Lambda (paramNodes, bodyId, [], None, LambdaContext.RegularClosure)
        return! createWithChildren kind funcType [bodyId]
    }

//=============================================================================
// LITERAL PRIMITIVES
//=============================================================================

/// Create a boolean literal
let boolLit (value: bool) : Recipe<NodeId> =
    createAndEmit (SemanticKind.Literal (NativeLiteral.Bool value)) Types.boolType

/// Create an int32 literal
let intLit (value: int) : Recipe<NodeId> =
    createAndEmit (SemanticKind.Literal (NativeLiteral.Int (int64 value, NTUKind.NTUint32))) Types.intType

/// Create an int64 literal
let int64Lit (value: int64) : Recipe<NodeId> =
    createAndEmit (SemanticKind.Literal (NativeLiteral.Int (value, NTUKind.NTUint64))) Types.int64Type

//=============================================================================
// OPERATOR PRIMITIVES
//=============================================================================

/// Create equality comparison: a = b
let eq (leftId: NodeId) (rightId: NodeId) (operandType: NativeType) : Recipe<NodeId> =
    let funcType = NativeType.TFun (operandType, NativeType.TFun (operandType, Types.boolType))
    let info = {
        Module = IntrinsicModule.Operators
        Operation = "op_Equality"
        Category = IntrinsicCategory.Pure
        FullName = "op_Equality"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! app2 funcId leftId rightId Types.boolType
    }

/// Create less-than comparison: a < b
let lt (leftId: NodeId) (rightId: NodeId) (operandType: NativeType) : Recipe<NodeId> =
    let funcType = NativeType.TFun (operandType, NativeType.TFun (operandType, Types.boolType))
    let info = {
        Module = IntrinsicModule.Operators
        Operation = "op_LessThan"
        Category = IntrinsicCategory.Pure
        FullName = "op_LessThan"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! app2 funcId leftId rightId Types.boolType
    }

/// Create greater-than comparison: a > b
let gt (leftId: NodeId) (rightId: NodeId) (operandType: NativeType) : Recipe<NodeId> =
    let funcType = NativeType.TFun (operandType, NativeType.TFun (operandType, Types.boolType))
    let info = {
        Module = IntrinsicModule.Operators
        Operation = "op_GreaterThan"
        Category = IntrinsicCategory.Pure
        FullName = "op_GreaterThan"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! app2 funcId leftId rightId Types.boolType
    }

/// Create addition: a + b
let add (leftId: NodeId) (rightId: NodeId) (numType: NativeType) : Recipe<NodeId> =
    let funcType = NativeType.TFun (numType, NativeType.TFun (numType, numType))
    let info = {
        Module = IntrinsicModule.Operators
        Operation = "op_Addition"
        Category = IntrinsicCategory.Pure
        FullName = "op_Addition"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! app2 funcId leftId rightId numType
    }

//=============================================================================
// COMPOSITE PRIMITIVES (built from other primitives)
//=============================================================================

/// Conditional cons: if cond then h :: t else t
/// Used in filter-style operations
let guardCons (condId: NodeId) (headId: NodeId) (tailId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    recipe {
        let! consResult = cons headId tailId elemType
        return! ifThenElse condId consResult tailId (NativeType.TList elemType)
    }

/// Short-circuit OR: if a then true else b
let orElse (leftId: NodeId) (rightId: NodeId) : Recipe<NodeId> =
    recipe {
        let! trueVal = boolLit true
        return! ifThenElse leftId trueVal rightId Types.boolType
    }

/// Short-circuit AND: if a then b else false
let andAlso (leftId: NodeId) (rightId: NodeId) : Recipe<NodeId> =
    recipe {
        let! falseVal = boolLit false
        return! ifThenElse leftId rightId falseVal Types.boolType
    }

/// Boolean NOT: if a then false else true
let not' (valueId: NodeId) : Recipe<NodeId> =
    recipe {
        let! trueVal = boolLit true
        let! falseVal = boolLit false
        return! ifThenElse valueId falseVal trueVal Types.boolType
    }


//=============================================================================
// MAP PRIMITIVES (AVL Tree)
//=============================================================================

/// Create an empty map: Map.empty<'K,'V>
/// Returns null pointer at runtime
let emptyMap (keyType: NativeType) (valueType: NativeType) : Recipe<NodeId> =
    let mapType = NativeType.TMap (keyType, valueType)
    let info = {
        Module = IntrinsicModule.Map
        Operation = "empty"
        Category = IntrinsicCategory.Pure
        FullName = "Map.empty"
    }
    createAndEmit (SemanticKind.Intrinsic info) mapType

/// Check if map is empty: Map.isEmpty m
let mapIsEmpty (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : Recipe<NodeId> =
    let mapType = NativeType.TMap (keyType, valueType)
    let funcType = NativeType.TFun (mapType, Types.boolType)
    let info = {
        Module = IntrinsicModule.Map
        Operation = "isEmpty"
        Category = IntrinsicCategory.Pure
        FullName = "Map.isEmpty"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [mapNodeId])) Types.boolType [funcId; mapNodeId]
    }

/// Create a map node: Map.node key value left right
/// This creates an AVL tree node (leaf or internal node)
let mapNode (keyId: NodeId) (valueId: NodeId) (leftId: NodeId) (rightId: NodeId) (keyType: NativeType) (valueType: NativeType) : Recipe<NodeId> =
    let mapType = NativeType.TMap (keyType, valueType)
    let funcType = NativeType.TFun (keyType, NativeType.TFun (valueType, NativeType.TFun (mapType, NativeType.TFun (mapType, mapType))))
    let info = {
        Module = IntrinsicModule.Map
        Operation = "node"
        Category = IntrinsicCategory.Pure
        FullName = "Map.node"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [keyId; valueId; leftId; rightId])) mapType [funcId; keyId; valueId; leftId; rightId]
    }

/// Get key from map node: Map.key node
let mapKey (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : Recipe<NodeId> =
    let mapType = NativeType.TMap (keyType, valueType)
    let funcType = NativeType.TFun (mapType, keyType)
    let info = {
        Module = IntrinsicModule.Map
        Operation = "key"
        Category = IntrinsicCategory.Pure
        FullName = "Map.key"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [mapNodeId])) keyType [funcId; mapNodeId]
    }

/// Get value from map node: Map.value node
let mapValue (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : Recipe<NodeId> =
    let mapType = NativeType.TMap (keyType, valueType)
    let funcType = NativeType.TFun (mapType, valueType)
    let info = {
        Module = IntrinsicModule.Map
        Operation = "value"
        Category = IntrinsicCategory.Pure
        FullName = "Map.value"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [mapNodeId])) valueType [funcId; mapNodeId]
    }

/// Get left subtree: Map.left node
let mapLeft (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : Recipe<NodeId> =
    let mapType = NativeType.TMap (keyType, valueType)
    let funcType = NativeType.TFun (mapType, mapType)
    let info = {
        Module = IntrinsicModule.Map
        Operation = "left"
        Category = IntrinsicCategory.Pure
        FullName = "Map.left"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [mapNodeId])) mapType [funcId; mapNodeId]
    }

/// Get right subtree: Map.right node
let mapRight (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : Recipe<NodeId> =
    let mapType = NativeType.TMap (keyType, valueType)
    let funcType = NativeType.TFun (mapType, mapType)
    let info = {
        Module = IntrinsicModule.Map
        Operation = "right"
        Category = IntrinsicCategory.Pure
        FullName = "Map.right"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [mapNodeId])) mapType [funcId; mapNodeId]
    }

/// Get height of map node: Map.height node
let mapHeight (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : Recipe<NodeId> =
    let mapType = NativeType.TMap (keyType, valueType)
    let funcType = NativeType.TFun (mapType, Types.intType)
    let info = {
        Module = IntrinsicModule.Map
        Operation = "height"
        Category = IntrinsicCategory.Pure
        FullName = "Map.height"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [mapNodeId])) Types.intType [funcId; mapNodeId]
    }

//=============================================================================
// SET PRIMITIVES (AVL Tree)
//=============================================================================

/// Create an empty set: Set.empty<'T>
/// Returns null pointer at runtime
let emptySet (elemType: NativeType) : Recipe<NodeId> =
    let setType = NativeType.TSet elemType
    let info = {
        Module = IntrinsicModule.Set
        Operation = "empty"
        Category = IntrinsicCategory.Pure
        FullName = "Set.empty"
    }
    createAndEmit (SemanticKind.Intrinsic info) setType

/// Check if set is empty: Set.isEmpty s
let setIsEmpty (setNodeId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let setType = NativeType.TSet elemType
    let funcType = NativeType.TFun (setType, Types.boolType)
    let info = {
        Module = IntrinsicModule.Set
        Operation = "isEmpty"
        Category = IntrinsicCategory.Pure
        FullName = "Set.isEmpty"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [setNodeId])) Types.boolType [funcId; setNodeId]
    }

/// Create a set node: Set.node value left right
let setNode (valueId: NodeId) (leftId: NodeId) (rightId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let setType = NativeType.TSet elemType
    let funcType = NativeType.TFun (elemType, NativeType.TFun (setType, NativeType.TFun (setType, setType)))
    let info = {
        Module = IntrinsicModule.Set
        Operation = "node"
        Category = IntrinsicCategory.Pure
        FullName = "Set.node"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [valueId; leftId; rightId])) setType [funcId; valueId; leftId; rightId]
    }

/// Get value from set node: Set.value node
let setValue (setNodeId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let setType = NativeType.TSet elemType
    let funcType = NativeType.TFun (setType, elemType)
    let info = {
        Module = IntrinsicModule.Set
        Operation = "value"
        Category = IntrinsicCategory.Pure
        FullName = "Set.value"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [setNodeId])) elemType [funcId; setNodeId]
    }

/// Get left subtree: Set.left node
let setLeft (setNodeId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let setType = NativeType.TSet elemType
    let funcType = NativeType.TFun (setType, setType)
    let info = {
        Module = IntrinsicModule.Set
        Operation = "left"
        Category = IntrinsicCategory.Pure
        FullName = "Set.left"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [setNodeId])) setType [funcId; setNodeId]
    }

/// Get right subtree: Set.right node
let setRight (setNodeId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let setType = NativeType.TSet elemType
    let funcType = NativeType.TFun (setType, setType)
    let info = {
        Module = IntrinsicModule.Set
        Operation = "right"
        Category = IntrinsicCategory.Pure
        FullName = "Set.right"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [setNodeId])) setType [funcId; setNodeId]
    }

/// Get height of set node: Set.height node
let setHeight (setNodeId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let setType = NativeType.TSet elemType
    let funcType = NativeType.TFun (setType, Types.intType)
    let info = {
        Module = IntrinsicModule.Set
        Operation = "height"
        Category = IntrinsicCategory.Pure
        FullName = "Set.height"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! createWithChildren (SemanticKind.Application (funcId, [setNodeId])) Types.intType [funcId; setNodeId]
    }

//=============================================================================
// COMPARISON PRIMITIVES
//=============================================================================

/// Compare two values: compare a b returns -1, 0, or 1
let compareTo (leftId: NodeId) (rightId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    let funcType = NativeType.TFun (elemType, NativeType.TFun (elemType, Types.intType))
    let info = {
        Module = IntrinsicModule.Operators
        Operation = "compare"
        Category = IntrinsicCategory.Pure
        FullName = "compare"
    }
    recipe {
        let! funcId = createAndEmit (SemanticKind.Intrinsic info) funcType
        return! app2 funcId leftId rightId Types.intType
    }

/// Check if comparison result indicates less than (< 0)
let compareIsLess (compareResultId: NodeId) : Recipe<NodeId> =
    recipe {
        let! zero = intLit 0
        return! lt compareResultId zero Types.intType
    }

/// Check if comparison result indicates equality (= 0)
let compareIsEqual (compareResultId: NodeId) : Recipe<NodeId> =
    recipe {
        let! zero = intLit 0
        return! eq compareResultId zero Types.intType
    }

/// Check if comparison result indicates greater than (> 0)
let compareIsGreater (compareResultId: NodeId) : Recipe<NodeId> =
    recipe {
        let! zero = intLit 0
        return! gt compareResultId zero Types.intType
    }

//=============================================================================
// SEQ PRIMITIVES (PRD-15/16 - Lazy Sequences)
//=============================================================================

/// Create a seq expression: seq { body }
/// The body should contain Yield/YieldBang nodes
let seqExpr (bodyId: NodeId) (captures: CaptureInfo list) (elemType: NativeType) : Recipe<NodeId> =
    let seqType = NativeType.TSeq elemType
    createWithChildren (SemanticKind.SeqExpr (bodyId, captures)) seqType [bodyId]

/// Yield a single value in a seq expression
let yield' (valueId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    createWithChildren (SemanticKind.Yield valueId) elemType [valueId]

/// Yield all values from a nested seq (yield!)
/// Used to compose/flatten nested sequences
let yieldBang (seqId: NodeId) (elemType: NativeType) : Recipe<NodeId> =
    createWithChildren (SemanticKind.YieldBang seqId) elemType [seqId]

/// Create an empty seq: Seq.empty<'T>
let emptySeq (elemType: NativeType) : Recipe<NodeId> =
    let seqType = NativeType.TSeq elemType
    let info = {
        Module = IntrinsicModule.Seq
        Operation = "empty"
        Category = IntrinsicCategory.Pure
        FullName = "Seq.empty"
    }
    createAndEmit (SemanticKind.Intrinsic info) seqType

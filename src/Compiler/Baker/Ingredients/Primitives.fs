// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Baker Primitives - Singleton PSG node builders using XParsec-style combinators.
///
/// LAYER 1: "Raw Ingredients"
///
/// These are the atomic building blocks. Each primitive creates exactly one
/// PSG node (or a small fixed number). Patterns compose these into recursive
/// structures. Recipes compose patterns into complete algorithms.
///
/// ARCHITECTURAL ENFORCEMENT:
/// - Low-level node constructors are INTERNAL to this module
/// - Only SaturationParser-wrapped versions are PUBLIC
/// - Code outside Ingredients/ cannot bypass the combinator abstraction
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
module Clef.Compiler.Baker.Ingredients.Primitives

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.Baker.Ingredients.SaturationCombinators

// Re-export saturation CE for convenient use in this module and dependents
let saturation = SaturationCombinators.saturation

//=============================================================================
// INTERNAL: Node construction (minimal helpers - just the base node builder)
//=============================================================================

/// Create a base node with expansion metadata. Returns node ready for emission.
let internal mkNode (state: SaturationState) (kind: SemanticKind) (ty: NativeType) (children: NodeId list) : SemanticNode =
    let baseNode =
        { Id = NodeId.fresh()
          Kind = kind
          Range = state.SourceRange
          Type = ty
          SRTPResolution = None
          ArenaAffinity = ArenaAffinity.CurrentActor
          LayoutHint = None
          Children = children
          Parent = None
          Metadata = Map.empty
          IsReachable = true
          EmissionStrategy = EmissionStrategy.Inline }
    markBaker state.OriginalHOF state.ExpansionId baseNode

/// Create a node at a SPECIFIC NodeId (for replacing PatternBindings in-place)
let internal mkNodeAt (state: SaturationState) (nodeId: NodeId) (kind: SemanticKind) (ty: NativeType) (children: NodeId list) : SemanticNode =
    let baseNode =
        { Id = nodeId
          Kind = kind
          Range = state.SourceRange
          Type = ty
          SRTPResolution = None
          ArenaAffinity = ArenaAffinity.CurrentActor
          LayoutHint = None
          Children = children
          Parent = None
          Metadata = Map.empty
          IsReachable = true
          EmissionStrategy = EmissionStrategy.Inline }
    markBaker state.OriginalHOF state.ExpansionId baseNode

//=============================================================================
// CONVENIENCE COMBINATORS: Node creation + emission
//=============================================================================

/// Create a node with children and emit it. Returns the node ID.
let createWithChildren (kind: SemanticKind) (ty: NativeType) (children: NodeId list) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state kind ty children
        do! emit node
        return node.Id
    }

/// Create a node without children and emit it. Returns the node ID.
let createAndEmit (kind: SemanticKind) (ty: NativeType) : SaturationParser<NodeId> =
    createWithChildren kind ty []

//=============================================================================
// LIST PRIMITIVES
//=============================================================================

/// Create an empty list: List.empty<'T>
let emptyList (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let listType = NativeType.TList elemType
        let info = { Module = IntrinsicModule.List; Operation = "empty"; Category = IntrinsicCategory.Pure; FullName = "List.empty" }
        let node = mkNode state (SemanticKind.Intrinsic info) listType []
        do! emit node
        return node.Id
    }

/// Check if list is empty: List.isEmpty xs
let isEmpty (listNodeId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let listType = NativeType.TList elemType
        let funcType = NativeType.TFun (listType, Types.boolType)
        let info = { Module = IntrinsicModule.List; Operation = "isEmpty"; Category = IntrinsicCategory.Pure; FullName = "List.isEmpty" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [listNodeId])) Types.boolType [funcNode.Id; listNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get head of list: List.head xs
let head (listNodeId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let listType = NativeType.TList elemType
        let funcType = NativeType.TFun (listType, elemType)
        let info = { Module = IntrinsicModule.List; Operation = "head"; Category = IntrinsicCategory.Pure; FullName = "List.head" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [listNodeId])) elemType [funcNode.Id; listNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get tail of list: List.tail xs
let tail (listNodeId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let listType = NativeType.TList elemType
        let funcType = NativeType.TFun (listType, listType)
        let info = { Module = IntrinsicModule.List; Operation = "tail"; Category = IntrinsicCategory.Pure; FullName = "List.tail" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [listNodeId])) listType [funcNode.Id; listNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Prepend element to list: List.cons h t (or h :: t)
let cons (headNodeId: NodeId) (tailNodeId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let listType = NativeType.TList elemType
        let funcType = NativeType.TFun (elemType, NativeType.TFun (listType, listType))
        let info = { Module = IntrinsicModule.List; Operation = "cons"; Category = IntrinsicCategory.Pure; FullName = "List.cons" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [headNodeId; tailNodeId])) listType [funcNode.Id; headNodeId; tailNodeId]
        do! emit appNode
        return appNode.Id
    }

//=============================================================================
// OPTION PRIMITIVES
//=============================================================================

/// Create None value: Option.none<'T>
let none (innerType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let optionType = NativeType.TApp (Types.optionTyCon, [innerType])
        let info = { Module = IntrinsicModule.Option; Operation = "none"; Category = IntrinsicCategory.Pure; FullName = "Option.none" }
        let node = mkNode state (SemanticKind.Intrinsic info) optionType []
        do! emit node
        return node.Id
    }

/// Create Some value: Option.some x
let some (valueNodeId: NodeId) (innerType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let optionType = NativeType.TApp (Types.optionTyCon, [innerType])
        let funcType = NativeType.TFun (innerType, optionType)
        let info = { Module = IntrinsicModule.Option; Operation = "some"; Category = IntrinsicCategory.Pure; FullName = "Option.some" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [valueNodeId])) optionType [funcNode.Id; valueNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Check if option has value: Option.isSome x
let isSome (optionNodeId: NodeId) (innerType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let optionType = NativeType.TApp (Types.optionTyCon, [innerType])
        let funcType = NativeType.TFun (optionType, Types.boolType)
        let info = { Module = IntrinsicModule.Option; Operation = "isSome"; Category = IntrinsicCategory.Pure; FullName = "Option.isSome" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [optionNodeId])) Types.boolType [funcNode.Id; optionNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Check if option is None: Option.isNone x
let isNone (optionNodeId: NodeId) (innerType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let optionType = NativeType.TApp (Types.optionTyCon, [innerType])
        let funcType = NativeType.TFun (optionType, Types.boolType)
        let info = { Module = IntrinsicModule.Option; Operation = "isNone"; Category = IntrinsicCategory.Pure; FullName = "Option.isNone" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [optionNodeId])) Types.boolType [funcNode.Id; optionNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get value from option: Option.get x (assumes Some)
let optionGet (optionNodeId: NodeId) (innerType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let optionType = NativeType.TApp (Types.optionTyCon, [innerType])
        let funcType = NativeType.TFun (optionType, innerType)
        let info = { Module = IntrinsicModule.Option; Operation = "get"; Category = IntrinsicCategory.Pure; FullName = "Option.get" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [optionNodeId])) innerType [funcNode.Id; optionNodeId]
        do! emit appNode
        return appNode.Id
    }

//=============================================================================
// STRUCTURAL PRIMITIVES
//=============================================================================

/// Create a function application node
let app (funcNodeId: NodeId) (argNodeIds: NodeId list) (resultType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Application (funcNodeId, argNodeIds)) resultType (funcNodeId :: argNodeIds)
        do! emit node
        return node.Id
    }

/// Create a single-argument application
let app1 (funcNodeId: NodeId) (argNodeId: NodeId) (resultType: NativeType) : SaturationParser<NodeId> =
    app funcNodeId [argNodeId] resultType

/// Create a two-argument application
let app2 (funcNodeId: NodeId) (arg1: NodeId) (arg2: NodeId) (resultType: NativeType) : SaturationParser<NodeId> =
    app funcNodeId [arg1; arg2] resultType

/// Create an if-then-else node
let ifThenElse (guardId: NodeId) (thenId: NodeId) (elseId: NodeId) (resultType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.IfThenElse (guardId, thenId, Some elseId)) resultType [guardId; thenId; elseId]
        do! emit node
        return node.Id
    }

/// Create a variable reference
let varRef (name: string) (defNodeId: NodeId option) (ty: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.VarRef (name, defNodeId)) ty []
        do! emit node
        return node.Id
    }

/// Create a pattern binding (parameter in lambda)
let patternBinding (name: string) (ty: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.PatternBinding name) ty []
        do! emit node
        return node.Id
    }

/// Create a let binding (non-recursive)
let letBind (name: string) (valueNodeId: NodeId) (ty: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let kind = SemanticKind.Binding (name, false, false, None)
        let node = mkNode state kind ty [valueNodeId]
        do! emit node
        do! withBinding name node.Id ty
        return node.Id
    }

/// Create a let binding at a SPECIFIC NodeId (for DU saturation).
/// This replaces an existing PatternBinding in-place, keeping the same NodeId
/// so VarRefs continue to resolve correctly.
let letBindAt (targetNodeId: NodeId) (name: string) (valueNodeId: NodeId) (ty: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let kind = SemanticKind.Binding (name, false, false, None)
        let node = mkNodeAt state targetNodeId kind ty [valueNodeId]
        do! emit node
        do! withBinding name targetNodeId ty
        return targetNodeId
    }

/// Create a recursive let binding
let letRecBind (name: string) (valueNodeId: NodeId) (ty: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let kind = SemanticKind.Binding (name, false, true, None)
        let node = mkNode state kind ty [valueNodeId]
        do! emit node
        do! withBinding name node.Id ty
        return node.Id
    }

/// Create a lambda node
let lambda
    (parameters: (string * NativeType) list)
    (bodyBuilder: NodeId list -> SaturationParser<NodeId>)
    (returnType: NativeType)
    : SaturationParser<NodeId> =
    saturation {
        // Create parameter binding nodes
        let rec createParams plist acc =
            saturation {
                match plist with
                | [] -> return List.rev acc
                | (name, ty) :: rest ->
                    let! paramState = getUserState
                    let paramNode = mkNode paramState (SemanticKind.PatternBinding name) ty []
                    do! emit paramNode
                    do! withBinding name paramNode.Id ty
                    let! remaining = createParams rest ((name, ty, paramNode.Id) :: acc)
                    return remaining
            }

        let! paramNodes = createParams parameters []
        let paramIds = paramNodes |> List.map (fun (_, _, id) -> id)

        // Build the body with parameters in scope
        let! bodyId = bodyBuilder paramIds

        // Compute the full function type
        let funcType =
            parameters
            |> List.foldBack (fun (_, paramTy) acc -> NativeType.TFun (paramTy, acc))
            <| returnType

        // Create the lambda node
        let! finalState = getUserState
        let kind = SemanticKind.Lambda (paramNodes, bodyId, [], None, LambdaContext.RegularClosure)
        let lambdaNode = mkNode finalState kind funcType [bodyId]
        do! emit lambdaNode
        return lambdaNode.Id
    }

//=============================================================================
// LITERAL PRIMITIVES
//=============================================================================

/// Create a boolean literal
let boolLit (value: bool) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Literal (NativeLiteral.Bool value)) Types.boolType []
        do! emit node
        return node.Id
    }

/// Create an int32 literal
let intLit (value: int) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Literal (NativeLiteral.Int (int64 value, NTUKind.NTUint (NTUWidth.Fixed 32)))) Types.intType []
        do! emit node
        return node.Id
    }

/// Create an int64 literal
let int64Lit (value: int64) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Literal (NativeLiteral.Int (value, NTUKind.NTUint (NTUWidth.Fixed 64)))) Types.int64Type []
        do! emit node
        return node.Id
    }

//=============================================================================
// OPERATOR PRIMITIVES
//=============================================================================

/// Create equality comparison: a = b
let eq (leftId: NodeId) (rightId: NodeId) (operandType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let funcType = NativeType.TFun (operandType, NativeType.TFun (operandType, Types.boolType))
        let info = { Module = IntrinsicModule.Operators; Operation = "op_Equality"; Category = IntrinsicCategory.Pure; FullName = "op_Equality" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [leftId; rightId])) Types.boolType [funcNode.Id; leftId; rightId]
        do! emit appNode
        return appNode.Id
    }

/// Create less-than comparison: a < b
let lt (leftId: NodeId) (rightId: NodeId) (operandType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let funcType = NativeType.TFun (operandType, NativeType.TFun (operandType, Types.boolType))
        let info = { Module = IntrinsicModule.Operators; Operation = "op_LessThan"; Category = IntrinsicCategory.Pure; FullName = "op_LessThan" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [leftId; rightId])) Types.boolType [funcNode.Id; leftId; rightId]
        do! emit appNode
        return appNode.Id
    }

/// Create greater-than comparison: a > b
let gt (leftId: NodeId) (rightId: NodeId) (operandType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let funcType = NativeType.TFun (operandType, NativeType.TFun (operandType, Types.boolType))
        let info = { Module = IntrinsicModule.Operators; Operation = "op_GreaterThan"; Category = IntrinsicCategory.Pure; FullName = "op_GreaterThan" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [leftId; rightId])) Types.boolType [funcNode.Id; leftId; rightId]
        do! emit appNode
        return appNode.Id
    }

/// Create addition: a + b
let add (leftId: NodeId) (rightId: NodeId) (numType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let funcType = NativeType.TFun (numType, NativeType.TFun (numType, numType))
        let info = { Module = IntrinsicModule.Operators; Operation = "op_Addition"; Category = IntrinsicCategory.Pure; FullName = "op_Addition" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [leftId; rightId])) numType [funcNode.Id; leftId; rightId]
        do! emit appNode
        return appNode.Id
    }

//=============================================================================
// COMPOSITE PRIMITIVES (built from other primitives)
//=============================================================================

/// Conditional cons: if cond then h :: t else t
/// Used in filter-style operations
let guardCons (condId: NodeId) (headId: NodeId) (tailId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! consResult = cons headId tailId elemType
        let! result = ifThenElse condId consResult tailId (NativeType.TList elemType)
        return result
    }

/// Short-circuit OR: if a then true else b
let orElse (leftId: NodeId) (rightId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! trueVal = boolLit true
        let! result = ifThenElse leftId trueVal rightId Types.boolType
        return result
    }

/// Short-circuit AND: if a then b else false
let andAlso (leftId: NodeId) (rightId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! falseVal = boolLit false
        let! result = ifThenElse leftId rightId falseVal Types.boolType
        return result
    }

/// Boolean NOT: if a then false else true
let not' (valueId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! trueVal = boolLit true
        let! falseVal = boolLit false
        let! result = ifThenElse valueId falseVal trueVal Types.boolType
        return result
    }

//=============================================================================
// MAP PRIMITIVES (AVL Tree)
//=============================================================================

/// Create an empty map: Map.empty<'K,'V>
let emptyMap (keyType: NativeType) (valueType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let mapType = NativeType.TMap (keyType, valueType)
        let info = { Module = IntrinsicModule.Map; Operation = "empty"; Category = IntrinsicCategory.Pure; FullName = "Map.empty" }
        let node = mkNode state (SemanticKind.Intrinsic info) mapType []
        do! emit node
        return node.Id
    }

/// Check if map is empty: Map.isEmpty m
let mapIsEmpty (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let mapType = NativeType.TMap (keyType, valueType)
        let funcType = NativeType.TFun (mapType, Types.boolType)
        let info = { Module = IntrinsicModule.Map; Operation = "isEmpty"; Category = IntrinsicCategory.Pure; FullName = "Map.isEmpty" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [mapNodeId])) Types.boolType [funcNode.Id; mapNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Create a map node: Map.node key value left right
let mapNode (keyId: NodeId) (valueId: NodeId) (leftId: NodeId) (rightId: NodeId) (keyType: NativeType) (valueType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let mapType = NativeType.TMap (keyType, valueType)
        let funcType = NativeType.TFun (keyType, NativeType.TFun (valueType, NativeType.TFun (mapType, NativeType.TFun (mapType, mapType))))
        let info = { Module = IntrinsicModule.Map; Operation = "node"; Category = IntrinsicCategory.Pure; FullName = "Map.node" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [keyId; valueId; leftId; rightId])) mapType [funcNode.Id; keyId; valueId; leftId; rightId]
        do! emit appNode
        return appNode.Id
    }

/// Get key from map node: Map.key node
let mapKey (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let mapType = NativeType.TMap (keyType, valueType)
        let funcType = NativeType.TFun (mapType, keyType)
        let info = { Module = IntrinsicModule.Map; Operation = "key"; Category = IntrinsicCategory.Pure; FullName = "Map.key" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [mapNodeId])) keyType [funcNode.Id; mapNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get value from map node: Map.value node
let mapValue (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let mapType = NativeType.TMap (keyType, valueType)
        let funcType = NativeType.TFun (mapType, valueType)
        let info = { Module = IntrinsicModule.Map; Operation = "value"; Category = IntrinsicCategory.Pure; FullName = "Map.value" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [mapNodeId])) valueType [funcNode.Id; mapNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get left subtree: Map.left node
let mapLeft (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let mapType = NativeType.TMap (keyType, valueType)
        let funcType = NativeType.TFun (mapType, mapType)
        let info = { Module = IntrinsicModule.Map; Operation = "left"; Category = IntrinsicCategory.Pure; FullName = "Map.left" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [mapNodeId])) mapType [funcNode.Id; mapNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get right subtree: Map.right node
let mapRight (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let mapType = NativeType.TMap (keyType, valueType)
        let funcType = NativeType.TFun (mapType, mapType)
        let info = { Module = IntrinsicModule.Map; Operation = "right"; Category = IntrinsicCategory.Pure; FullName = "Map.right" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [mapNodeId])) mapType [funcNode.Id; mapNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get height of map node: Map.height node
let mapHeight (mapNodeId: NodeId) (keyType: NativeType) (valueType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let mapType = NativeType.TMap (keyType, valueType)
        let funcType = NativeType.TFun (mapType, Types.intType)
        let info = { Module = IntrinsicModule.Map; Operation = "height"; Category = IntrinsicCategory.Pure; FullName = "Map.height" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [mapNodeId])) Types.intType [funcNode.Id; mapNodeId]
        do! emit appNode
        return appNode.Id
    }

//=============================================================================
// SET PRIMITIVES (AVL Tree)
//=============================================================================

/// Create an empty set: Set.empty<'T>
let emptySet (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let setType = NativeType.TSet elemType
        let info = { Module = IntrinsicModule.Set; Operation = "empty"; Category = IntrinsicCategory.Pure; FullName = "Set.empty" }
        let node = mkNode state (SemanticKind.Intrinsic info) setType []
        do! emit node
        return node.Id
    }

/// Check if set is empty: Set.isEmpty s
let setIsEmpty (setNodeId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let setType = NativeType.TSet elemType
        let funcType = NativeType.TFun (setType, Types.boolType)
        let info = { Module = IntrinsicModule.Set; Operation = "isEmpty"; Category = IntrinsicCategory.Pure; FullName = "Set.isEmpty" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [setNodeId])) Types.boolType [funcNode.Id; setNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Create a set node: Set.node value left right
let setNode (valueId: NodeId) (leftId: NodeId) (rightId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let setType = NativeType.TSet elemType
        let funcType = NativeType.TFun (elemType, NativeType.TFun (setType, NativeType.TFun (setType, setType)))
        let info = { Module = IntrinsicModule.Set; Operation = "node"; Category = IntrinsicCategory.Pure; FullName = "Set.node" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [valueId; leftId; rightId])) setType [funcNode.Id; valueId; leftId; rightId]
        do! emit appNode
        return appNode.Id
    }

/// Get value from set node: Set.value node
let setValue (setNodeId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let setType = NativeType.TSet elemType
        let funcType = NativeType.TFun (setType, elemType)
        let info = { Module = IntrinsicModule.Set; Operation = "value"; Category = IntrinsicCategory.Pure; FullName = "Set.value" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [setNodeId])) elemType [funcNode.Id; setNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get left subtree: Set.left node
let setLeft (setNodeId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let setType = NativeType.TSet elemType
        let funcType = NativeType.TFun (setType, setType)
        let info = { Module = IntrinsicModule.Set; Operation = "left"; Category = IntrinsicCategory.Pure; FullName = "Set.left" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [setNodeId])) setType [funcNode.Id; setNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get right subtree: Set.right node
let setRight (setNodeId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let setType = NativeType.TSet elemType
        let funcType = NativeType.TFun (setType, setType)
        let info = { Module = IntrinsicModule.Set; Operation = "right"; Category = IntrinsicCategory.Pure; FullName = "Set.right" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [setNodeId])) setType [funcNode.Id; setNodeId]
        do! emit appNode
        return appNode.Id
    }

/// Get height of set node: Set.height node
let setHeight (setNodeId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let setType = NativeType.TSet elemType
        let funcType = NativeType.TFun (setType, Types.intType)
        let info = { Module = IntrinsicModule.Set; Operation = "height"; Category = IntrinsicCategory.Pure; FullName = "Set.height" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [setNodeId])) Types.intType [funcNode.Id; setNodeId]
        do! emit appNode
        return appNode.Id
    }

//=============================================================================
// COMPARISON PRIMITIVES
//=============================================================================

/// Compare two values: compare a b returns -1, 0, or 1
let compareTo (leftId: NodeId) (rightId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let funcType = NativeType.TFun (elemType, NativeType.TFun (elemType, Types.intType))
        let info = { Module = IntrinsicModule.Operators; Operation = "compare"; Category = IntrinsicCategory.Pure; FullName = "compare" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [leftId; rightId])) Types.intType [funcNode.Id; leftId; rightId]
        do! emit appNode
        return appNode.Id
    }

/// Check if comparison result indicates less than (< 0)
let compareIsLess (compareResultId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! zero = intLit 0
        let! result = lt compareResultId zero Types.intType
        return result
    }

/// Check if comparison result indicates equality (= 0)
let compareIsEqual (compareResultId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! zero = intLit 0
        let! result = eq compareResultId zero Types.intType
        return result
    }

/// Check if comparison result indicates greater than (> 0)
let compareIsGreater (compareResultId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! zero = intLit 0
        let! result = gt compareResultId zero Types.intType
        return result
    }

//=============================================================================
// SEQ PRIMITIVES (PRD-15/16 - Lazy Sequences)
//=============================================================================

/// Create a seq expression: seq { body }
/// The body should contain Yield/YieldBang nodes
let seqExpr (bodyId: NodeId) (captures: CaptureInfo list) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let seqType = NativeType.TSeq elemType
        let node = mkNode state (SemanticKind.SeqExpr (bodyId, captures)) seqType [bodyId]
        do! emit node
        return node.Id
    }

/// Yield a single value in a seq expression
let yield' (valueId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Yield valueId) elemType [valueId]
        do! emit node
        return node.Id
    }

/// Yield all values from a nested seq (yield!)
/// Used to compose/flatten nested sequences
let yieldBang (seqId: NodeId) (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.YieldBang seqId) elemType [seqId]
        do! emit node
        return node.Id
    }

/// Create an empty seq: Seq.empty<'T>
let emptySeq (elemType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let seqType = NativeType.TSeq elemType
        let info = { Module = IntrinsicModule.Seq; Operation = "empty"; Category = IntrinsicCategory.Pure; FullName = "Seq.empty" }
        let node = mkNode state (SemanticKind.Intrinsic info) seqType []
        do! emit node
        return node.Id
    }

//=============================================================================
// UNION/DISCRIMINATED UNION PRIMITIVES
//=============================================================================

/// Extract a field from a struct/record/union by name
/// Used for pattern matching to extract tag and payload
let fieldGet (exprId: NodeId) (fieldName: string) (fieldType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.FieldGet (exprId, fieldName)) fieldType [exprId]
        do! emit node
        return node.Id
    }

//-----------------------------------------------------------------------------
// Discriminated Union Operations (Pointer-based, Type-safe)
//-----------------------------------------------------------------------------

/// Extract the tag (discriminator) from a discriminated union value.
/// Uses DUGetTag for proper pointer-based DU handling.
let duGetTag (unionId: NodeId) (unionType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.DUGetTag (unionId, unionType)) Types.int8Type [unionId]
        do! emit node
        return node.Id
    }

/// Type-safe payload extraction from a discriminated union via case eliminator.
/// This generates a DUEliminate node that:
/// 1. Bitcasts the DU pointer to the case-specific struct pointer type
/// 2. Loads and extracts the payload with the correct type
let duEliminate (unionId: NodeId) (caseName: string) (caseIndex: int) (payloadType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.DUEliminate (unionId, caseIndex, caseName, payloadType)) payloadType [unionId]
        do! emit node
        return node.Id
    }

/// Construct a discriminated union value in an arena.
let duConstruct (caseName: string) (caseIndex: int) (payload: NodeId option) (arenaHint: NodeId option) (resultType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let children =
            match payload, arenaHint with
            | Some p, Some a -> [p; a]
            | Some p, None -> [p]
            | None, Some a -> [a]
            | None, None -> []
        let node = mkNode state (SemanticKind.DUConstruct (caseName, caseIndex, payload, arenaHint)) resultType children
        do! emit node
        return node.Id
    }

//-----------------------------------------------------------------------------
// Legacy Tag Extraction (delegates to fieldGet)
//-----------------------------------------------------------------------------

/// Extract the tag (discriminator) from a discriminated union value.
/// DEPRECATED: Use duGetTag with explicit union type for new code.
let extractTag (unionId: NodeId) : SaturationParser<NodeId> =
    fieldGet unionId "Tag" Types.int8Type

/// Extract payload field at a specific index from a discriminated union.
/// DEPRECATED: Use duEliminate with explicit case info for new code.
let extractPayloadField (unionId: NodeId) (index: int) (fieldType: NativeType) : SaturationParser<NodeId> =
    let fieldName = sprintf "Item%d" (index + 1)  // F# uses 1-based naming
    fieldGet unionId fieldName fieldType

/// Create an i8 literal (used for tag constants)
let int8Lit (value: int) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Literal (NativeLiteral.Int (int64 value, NTUKind.NTUint (NTUWidth.Fixed 8)))) Types.int8Type []
        do! emit node
        return node.Id
    }

/// Compare two values for equality, returning bool
/// Used for tag comparison in pattern matching
let compareEq (leftId: NodeId) (rightId: NodeId) (operandType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let funcType = NativeType.TFun (operandType, NativeType.TFun (operandType, Types.boolType))
        let info = { Module = IntrinsicModule.Operators; Operation = "op_Equality"; Category = IntrinsicCategory.Comparison; FullName = "op_Equality" }
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [leftId; rightId])) Types.boolType [funcNode.Id; leftId; rightId]
        do! emit appNode
        return appNode.Id
    }

/// Compare tag value against expected tag index
/// Returns true if scrutinee's tag equals expected
let compareTagEq (scrutineeId: NodeId) (expectedTag: int) : SaturationParser<NodeId> =
    saturation {
        let! actualTagId = extractTag scrutineeId
        let! expectedTagId = int8Lit expectedTag
        let! result = compareEq actualTagId expectedTagId Types.int8Type
        return result
    }

/// Create a union case value (union construction)
let unionCase (caseName: string) (caseIndex: int) (payload: NodeId option) (unionType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let children = match payload with Some p -> [p] | None -> []
        let node = mkNode state (SemanticKind.UnionCase (caseName, caseIndex, payload)) unionType children
        do! emit node
        return node.Id
    }

//=============================================================================
// ARENA ALLOCATION COMBINATORS (F-02: Arena Allocation)
//=============================================================================

/// Create arena: Arena.create<'lifetime>(sizeBytes)
/// Allocates stack-based arena buffer.
/// Returns Arena<'lifetime> (memref<N x i8> in MLIR).
let arenaCreate (sizeBytesId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState

        // Arena.create<'lifetime>: int -> Arena<'lifetime>
        // Arena is nativeint (memref pointer) in our memref-based implementation
        let arenaType = Types.nintType

        let funcType = NativeType.TFun(Types.intType, arenaType)
        let info = { Module = IntrinsicModule.Arena; Operation = "create"; Category = IntrinsicCategory.Memory; FullName = "Arena.create" }

        // Create intrinsic node
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode

        // Apply to size argument
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [sizeBytesId])) arenaType [funcNode.Id; sizeBytesId]
        do! emit appNode

        return appNode.Id
    }

/// Allocate from arena: Arena.alloc(arena byref, sizeBytes)
/// Bump-pointer allocation from arena.
/// Returns nativeint pointer to allocated memory.
let arenaAlloc (arenaRefId: NodeId) (sizeBytesId: NodeId) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState

        // Arena.alloc: Arena<'lifetime> byref -> int -> nativeint
        // Arena is nativeint (memref pointer) in our memref-based implementation
        let arenaType = Types.nintType

        let funcType =
            NativeType.TFun(
                NativeType.TByref(arenaType, ByrefKind.InOut),
                NativeType.TFun(Types.intType, Types.nintType))
        let info = { Module = IntrinsicModule.Arena; Operation = "alloc"; Category = IntrinsicCategory.Memory; FullName = "Arena.alloc" }

        // Create intrinsic node
        let funcNode = mkNode state (SemanticKind.Intrinsic info) funcType []
        do! emit funcNode

        // Apply to arena byref and size arguments
        let! state' = getUserState
        let appNode = mkNode state' (SemanticKind.Application (funcNode.Id, [arenaRefId; sizeBytesId])) Types.nintType [funcNode.Id; arenaRefId; sizeBytesId]
        do! emit appNode

        return appNode.Id
    }

/// Build record/struct with fields: { field1 = value1; field2 = value2 }
/// General-purpose combinator for struct/record creation.
/// Creates a RecordExpr node with specified field bindings.
let buildRecord (fields: (string * NodeId) list) (recordType: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let childIds = fields |> List.map snd
        let node = mkNode state (SemanticKind.RecordExpr (fields, None)) recordType childIds
        do! emit node
        return node.Id
    }

/// Build record/struct with prerequisite nodes that must be witnessed first.
/// Used when side-effecting operations (e.g., memcpy) must execute before record creation.
/// Prerequisites establish control-flow dependencies via Children edges.
let buildRecordWithPrereqs
    (fields: (string * NodeId) list)
    (prereqs: NodeId list)
    (recordType: NativeType)
    : SaturationParser<NodeId> =
    saturation {
        let! state = getUserState
        let fieldIds = fields |> List.map snd
        // Prerequisites first (control flow), then field values (data flow)
        let childIds = prereqs @ fieldIds
        let node = mkNode state (SemanticKind.RecordExpr (fields, None)) recordType childIds
        do! emit node
        return node.Id
    }

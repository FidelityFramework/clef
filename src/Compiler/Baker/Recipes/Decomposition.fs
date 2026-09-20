// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Baker recipe context and graph expansion result contracts.
/// Node construction and expansion provenance belong to saturation ingredients;
/// recipes return the resulting nodes and any synthesized declarations here.
module Clef.Compiler.Baker.Recipes.Decomposition

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration

/// Source and platform facts supplied to a recipe's saturation state.
type Context = {
    /// Source range inherited by generated nodes.
    SourceRange: SourceRange
    /// Checked collection element type.
    ElementType: NativeType
    Platform: PlatformContext option
    /// Source operation and expansion identity retained as provenance.
    OriginalHOF: string
    ExpansionId: int
    InspiringNode: NodeId
}

let mkContext
    (range: SourceRange)
    (elemType: NativeType)
    (platform: PlatformContext option)
    (hofName: string)
    (inspiringNode: NodeId) : Context =
    { SourceRange = range
      ElementType = elemType
      Platform = platform
      OriginalHOF = hofName
      ExpansionId = freshId()
      InspiringNode = inspiringNode }

/// Graph structure to fold into the source operation.
type Result = {
    NewNodes: SemanticNode list
    ResultNodeId: NodeId
    /// Synthesized declarations retained by the decomposition.
    AuxFunctions: SemanticNode list
}

/// Create the graph-only expansion consumed by recipe fold-in.
let mkResultNoShadow
    (nodes: SemanticNode list)
    (rootId: NodeId)
    (auxFns: SemanticNode list) : Result =
    { NewNodes = nodes
      ResultNodeId = rootId
      AuxFunctions = auxFns }

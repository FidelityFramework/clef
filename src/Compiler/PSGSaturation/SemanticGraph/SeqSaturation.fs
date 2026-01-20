// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Sequence State Machine Types - Analysis results from seq expression saturation.
/// These types represent the saturated form of seq expressions, extracted during
/// PSG saturation phase by analyzing the structure of SeqExpr bodies.
///
/// NANOPASS: This module contains coeffect types computed during saturation.
/// The extraction functions that compute these values are in SemanticGraph.fs.
module FSharp.Native.Compiler.PSGSaturation.SemanticGraph.SeqSaturation

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes

/// Information about an internal mutable binding in a seq body.
/// These become fields in the seq struct (after captures).
/// PSG SATURATION: This structure is populated during saturation phase.
type SeqInternalStateField = {
    /// Name of the mutable variable
    Name: string
    /// Type of the variable
    Type: NativeType
    /// NodeId of the original Binding node
    BindingId: NodeId
    /// Index in the seq struct (3 + numCaptures + index)
    StructIndex: int
}

/// Information about conditional yields (if inside while).
/// Supports nested conditionals: if A then if B then yield x → ConditionIds = [A; B]
type SeqConditionalYieldInfo = {
    /// NodeId of the outermost IfThenElse
    IfNodeId: NodeId
    /// NodeIds of all conditions (for nested ifs, multiple conditions ANDed together)
    ConditionIds: NodeId list
}

/// Structure of a while-based sequence body.
/// seq { <init>; while <cond> do <before-yield>; yield <value>; <post-yield> }
/// PSG SATURATION: These node references point to existing PSG nodes.
type SeqWhileBodyInfo = {
    /// NodeIds of expressions before the while loop (initialization)
    InitExprs: NodeId list
    /// NodeId of the WhileLoop node
    WhileNodeId: NodeId
    /// NodeId of the while condition
    ConditionId: NodeId
    /// NodeIds of expressions before the yield (inside while body)
    PreYieldExprs: NodeId list
    /// The single yield point (while-based seqs have one yield per while)
    YieldNodeId: NodeId
    /// NodeId of the value expression being yielded
    YieldValueId: NodeId
    /// NodeIds of expressions after the yield (inside while body)
    PostYieldExprs: NodeId list
    /// Whether there's a conditional around the yield (if x then yield y)
    ConditionalYield: SeqConditionalYieldInfo option
}

/// The kind of sequence body structure.
/// Determined during PSG saturation from analysis of seq body.
[<RequireQualifiedAccess>]
type SeqBodyKind =
    /// Sequential yields: seq { yield 1; yield 2; yield 3 }
    /// Each yield gets its own state (0 -> 1 -> 2 -> ... -> -1)
    | Sequential of yields: (NodeId * NodeId) list  // (YieldNodeId, ValueNodeId) pairs
    /// While-based: seq { while cond do yield x }
    /// Two-state model (state 0 = init, state 1 = post-yield)
    | WhileBased of SeqWhileBodyInfo

/// Information about a sequence expression's state machine structure.
/// PSG SATURATION: This is the saturated form of SeqExpr.
/// Created during saturation phase by analyzing the SeqExpr body.
type SeqStateMachineInfo = {
    /// Original SeqExpr node this was saturated from
    OriginalSeqExprId: NodeId
    /// Body structure (sequential vs while-based)
    BodyKind: SeqBodyKind
    /// Variables captured from enclosing scope
    Captures: CaptureInfo list
    /// Internal mutable state fields (let mutable inside seq body)
    InternalState: SeqInternalStateField list
    /// Element type being yielded
    ElementType: NativeType
}

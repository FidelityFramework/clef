// SPDX-License-Identifier: MIT
/// Writable address exposure is distinct from an ordinary scalar value read.
/// Owners provide their checked cell identity; this ingredient infers no alias.
module Clef.Compiler.Baker.Ingredients.SourceStorageBorrows

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let takesAddress (readCell: NodeId -> bool) (isCell: NodeId -> bool) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.AddressOf(value, _) -> readCell value
    | SemanticKind.CellAddress source -> isCell source
    | _ -> false

type SlotBorrow = Environment | Frame | Lazy

/// Logical slot operands have provenance incidence rather than ordinary use
/// edges, so a complete writable-borrow census must inspect these typed kinds.
let trySlot (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.EnvironmentBorrow(_, slot) -> Some(slot, SlotBorrow.Environment)
    | SemanticKind.FrameBorrow(_, slot) -> Some(slot, SlotBorrow.Frame)
    | SemanticKind.LazyBorrow(_, slot) -> Some(slot, SlotBorrow.Lazy)
    | _ -> None

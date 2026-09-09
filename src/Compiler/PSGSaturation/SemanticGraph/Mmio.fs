/// The read width is a hardware boundary, independent of the use's range.
module Clef.Compiler.PSGSaturation.SemanticGraph.Mmio
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

let operation (graph: SemanticGraph) id =
    match SemanticGraph.tryGetNode id graph with
    | Some { Kind = SemanticKind.Application (fn, args) } ->
        match valueOf graph fn with
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Mmio; Operation = op } } -> Some (op, args)
        | _ -> None
    | _ -> None

let numericBoundary graph id : DeclaredParameter option =
    match operation graph id with
    | Some (op, _) ->
        match op with
        | "read8" | "read16" | "read32" ->
            let bits = int (op.Substring(4))
            Some { Node = id; Name = "Mmio." + op; Bits = bits; Range = ValueRange.unsignedOf bits }
        | _ -> None
    | _ -> None

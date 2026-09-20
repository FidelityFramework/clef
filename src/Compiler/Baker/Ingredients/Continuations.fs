// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Typed continuation ingredients consume settled frame residence and source
/// slot identities. Range-bearing reads and constants preserve those facts
/// during runtime graph construction after range analysis.
module Clef.Compiler.Baker.Ingredients.Continuations

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

/// Continuation nodes use the shared PSG emission ingredient.
let create = createWithChildren

let index (value: int) =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Literal (NativeLiteral.Int(int64 value, NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Pointer)))) Types.nintType []
        let node = { node with ValueRange = Some (ValueRange.bounded (bigint value) (bigint value)) }
        do! emit node
        return node.Id
    }

let integer (value: int) =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.Literal (NativeLiteral.Int(int64 value, NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register)))) Types.intType []
        let node = { node with ValueRange = Some (ValueRange.bounded (bigint value) (bigint value)) }
        do! emit node
        return node.Id
    }

let mutableBinding name value ty = create (SemanticKind.Binding(name, true, false, None)) ty [value]

let assign binding name ty value =
    saturation {
        let! target = varRef name (Some binding) ty
        return! create (SemanticKind.Set(target, value)) Types.unitType [target; value]
    }

let read frame (slot: SemanticNode) =
    saturation {
        let! state = getUserState
        let node = mkNode state (SemanticKind.FrameRead(frame, slot.Id)) slot.Type [frame]
        do! emit { node with ValueRange = slot.ValueRange }
        return node.Id
    }

let write frame slot value = create (SemanticKind.FrameWrite(frame, slot, value)) Types.unitType [frame; value]

let block actions ty = create (SemanticKind.Sequential actions) ty actions

let dispatch selector cases otherwise =
    create (SemanticKind.ContinuationDispatch(selector, cases, otherwise)) Types.unitType
        (selector :: (cases |> List.map snd) @ [otherwise])

let rec collect make = function
    | [] -> saturation { return [] }
    | item :: rest -> saturation {
        let! value = make item
        let! values = collect make rest
        return value :: values
      }

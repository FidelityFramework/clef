// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Complete native Option structure for Baker recipes. These ingredients emit
/// the typed DU operations in this firing; no generated Option intrinsic needs
/// another saturation pass. Payload extraction requires its selected Some path.
module Clef.Compiler.Baker.Ingredients.Options

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

let typeOf innerType = NativeType.TApp(Types.optionTyCon, [innerType])

let caseTest optionNodeId innerType caseIndex =
    saturation {
        let! tag = duGetTag optionNodeId (typeOf innerType)
        let! expected = int8Lit caseIndex
        // Native Option has exactly None=0 and Some=1. These local facts
        // belong to construction, including firings after range analysis.
        do! updateUserState (fun state ->
            let nodes =
                state.EmittedNodes |> List.map (fun node ->
                    if node.Id = tag then
                        { node with ValueRange = Some (ValueRange.bounded 0I 1I) }
                    elif node.Id = expected then
                        { node with ValueRange = Some (ValueRange.bounded (bigint caseIndex) (bigint caseIndex)) }
                    else node)
            { state with EmittedNodes = nodes })
        return! compareEq tag expected Types.int8Type
    }

let hasValue optionNodeId innerType = caseTest optionNodeId innerType 1

let value optionNodeId innerType = duEliminate optionNodeId "Some" 1 innerType

let some valueNodeId innerType = duConstruct "Some" 1 (Some valueNodeId) None (typeOf innerType)

let none innerType = duConstruct "None" 0 None None (typeOf innerType)

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

let private noneOrdinal = 0
let private someOrdinal = 1

/// The same canonical source cases used by construction and elimination.
/// This says nothing about the foreign representation of null.
let cases ty =
    match Clef.Compiler.NativeTypedTree.UnionFind.applySubst ty with
    | NativeType.TApp(constructor, [inner]) when constructor = Types.optionTyCon ->
        Some [noneOrdinal, "None", None; someOrdinal, "Some", Some inner]
    | _ -> None

let caseTest optionNodeId innerType caseIndex =
    saturation {
        let! tag = duGetTag optionNodeId (typeOf innerType)
        let! expected = tagLiteral caseIndex
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
        return! compareEq tag expected Types.intType
    }

let hasValue optionNodeId innerType = caseTest optionNodeId innerType someOrdinal

let value optionNodeId innerType = duEliminate optionNodeId "Some" someOrdinal innerType

let some valueNodeId innerType = duConstruct "Some" someOrdinal (Some valueNodeId) None (typeOf innerType)

let none innerType = duConstruct "None" noneOrdinal None None (typeOf innerType)

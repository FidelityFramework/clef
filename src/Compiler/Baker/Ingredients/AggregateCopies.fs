// SPDX-License-Identifier: MIT
/// Copy the selected scalar Option case into already owned storage. None never
/// demands a payload; the complete copy relation is retained with its branches.
module Clef.Compiler.Baker.Ingredients.AggregateCopies

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
module C = Clef.Compiler.Baker.Ingredients.Continuations
module O = Clef.Compiler.Baker.Ingredients.Options

let initialize destination name index payload =
    C.create (SemanticKind.DUInitialize(destination, name, index, payload)) Types.unitType
        (destination :: Option.toList payload)

let option source destination inner = saturation {
    let! selected = O.hasValue source inner
    let! value = O.value source inner
    // This transport is also minted after RangeAnalysis. Carry its ordinary
    // conservative DU-read transfer, not the capacity of the physical slot.
    // The existing core integer carrier rule handles an unobservable range;
    // no finite numeric proof or payload narrowing is manufactured here.
    let payloadRange =
        match Types.tryGetNTUKind inner with
        | Some (NTUKind.NTUint _ | NTUKind.NTUuint _) -> Some ValueRange.Unbounded
        | Some NTUKind.NTUbool -> Some ValueRange.boolean
        | Some NTUKind.NTUchar -> Some ValueRange.codePoint
        | _ -> None
    do! updateUserState (fun state ->
        let nodes = state.EmittedNodes |> List.map (fun node ->
            if node.Id = value then { node with ValueRange = payloadRange }
            elif node.Id = selected then { node with ValueRange = Some ValueRange.boolean }
            else node)
        { state with EmittedNodes = nodes })
    let! some = initialize destination "Some" 1 (Some value)
    let! none = initialize destination "None" 0 None
    let! branch = C.create (SemanticKind.IfThenElse(selected, some, Some none)) Types.unitType [selected; some; none]
    // Both cases write the same owned destination. Its address/view must be
    // established before selecting a case, so each branch has that value in
    // scope. Only the Some branch demands the payload extraction.
    let! copy = C.create (SemanticKind.Sequential [source; destination; branch]) Types.unitType [source; destination; branch]
    return copy, {
        Sources = [source; destination; selected; value; some; none]
        Target = branch; Class = EdgeClass.Provenance; Role = EdgeRole.AggregateCopy; Ordinal = 0 }
}

let result source destination resultType okType errorType okRange errorRange = saturation {
    let! tag = duGetTag source resultType
    let! expected = tagLiteral 0
    let! selected = compareEq tag expected Types.intType
    let! okValue = duEliminate source "Ok" 0 okType
    let! errorValue = duEliminate source "Error" 1 errorType
    let payloadRange ty =
        match Types.tryGetNTUKind ty with
        | Some (NTUKind.NTUint _ | NTUKind.NTUuint _) -> Some ValueRange.Unbounded
        | Some NTUKind.NTUbool -> Some ValueRange.boolean
        | Some NTUKind.NTUchar -> Some ValueRange.codePoint
        | _ -> None
    do! updateUserState (fun state ->
        let nodes = state.EmittedNodes |> List.map (fun node ->
            if node.Id = tag then { node with ValueRange = Some (ValueRange.bounded 0I 1I) }
            elif node.Id = expected then { node with ValueRange = Some (ValueRange.bounded 0I 0I) }
            elif node.Id = selected then { node with ValueRange = Some ValueRange.boolean }
            elif node.Id = okValue then { node with ValueRange = okRange |> Option.orElseWith (fun () -> payloadRange okType) }
            elif node.Id = errorValue then { node with ValueRange = errorRange |> Option.orElseWith (fun () -> payloadRange errorType) }
            else node)
        { state with EmittedNodes = nodes })
    let! ok = initialize destination "Ok" 0 (Some okValue)
    let! error = initialize destination "Error" 1 (Some errorValue)
    let! branch = C.create (SemanticKind.IfThenElse(selected, ok, Some error)) Types.unitType [selected; ok; error]
    let! copy = C.create (SemanticKind.Sequential [source; destination; branch]) Types.unitType [source; destination; branch]
    return copy, {
        Sources = [source; destination; selected; okValue; errorValue; ok; error]
        Target = branch; Class = EdgeClass.Provenance; Role = EdgeRole.AggregateCopy; Ordinal = 0 }
}

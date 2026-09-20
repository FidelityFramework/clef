// SPDX-License-Identifier: MIT
/// Copy the selected scalar Option case into already owned storage. None never
/// demands a payload; the complete copy relation is retained with its branches.
module Clef.Compiler.Baker.Ingredients.AggregateCopies

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
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

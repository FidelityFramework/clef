// SPDX-License-Identifier: MIT
/// Bounded owned aggregate transport. Admission reads the existing NTU union
/// placement; it neither invents a second size rule nor retains hidden pointers.
module Clef.Compiler.PSGSaturation.SemanticGraph.AggregateValues

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

/// Only a concrete Option with one scalar payload can be copied by the current
/// case-aware transport. Reference-bearing and nested aggregate payloads need
/// their own residence/copy contracts.
let scalarOption (graph: SemanticGraph) ty =
    let ty = applySubst ty
    match ty with
    | NativeType.TApp(constructor, [inner]) when constructor.Name = "option" && Set.isEmpty (freeTypeVars ty) ->
        match graph.Layouts.Value.TryFind (formatType ty) with
        | Some (SettledLayout.Union(["None", None; "Some", Some payload], _, Some bytes, Some alignment))
            when bytes > 0 && alignment > 0 && (alignment &&& (alignment - 1)) = 0 ->
            match Types.tryGetNTUKind inner, payload with
            | Some (NTUKind.NTUint _ | NTUKind.NTUuint _), SettledSlot.Integer _
            | Some (NTUKind.NTUfloat _ | NTUKind.NTUposit _), SettledSlot.Real _
            | Some NTUKind.NTUbool, SettledSlot.Bool
            | Some NTUKind.NTUchar, SettledSlot.Char
            | Some NTUKind.NTUunit, SettledSlot.Unit -> Some(inner, bytes, alignment)
            | _ -> None
        | _ -> None
    | _ -> None

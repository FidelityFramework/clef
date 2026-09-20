// SPDX-License-Identifier: MIT
/// Ordinary typed startup calls. The source entry remains an ordinary callable;
/// only the generated activation owns once-before-entry initialization.
module Clef.Compiler.Baker.Ingredients.ProgramInitialization

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
module C = Clef.Compiler.Baker.Ingredients.Continuations

let forwardedCall (source: SemanticNode) parameters resultType = saturation {
    let! formals = parameters |> C.collect (fun (name, ty, _) -> saturation {
        let! formal = patternBinding name ty
        return name, ty, formal
    })
    let! arguments = formals |> C.collect (fun (name, ty, formal) -> varRef name (Some formal) ty)
    let name = match source.Kind with SemanticKind.Binding(name, _, _, _) -> name | _ -> invalidOp "Startup requires a source declaration."
    let! callee = varRef name (Some source.Id) source.Type
    let! call = C.create (SemanticKind.Application(callee, arguments)) resultType (callee :: arguments)
    return formals, call
}

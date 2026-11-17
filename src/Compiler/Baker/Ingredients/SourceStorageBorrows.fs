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

/// Values derived from source-owned borrowed storage, shared by boundary lifetime
/// settlement and async suspension refusal. This traversal grants no residence.
let derivedValues (graph: SemanticGraph) (isTupleAccessor: NodeId -> bool) (seeds: NodeId list) =
    let derived = System.Collections.Generic.HashSet<NodeId>()
    let add id = derived.Add id |> ignore
    seeds |> List.iter add
    let rec bindingTargets seen id =
        if Set.contains id seen then [] else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some t) } -> t :: bindingTargets seen t
        | Some { Kind = SemanticKind.CellAddress b } -> b :: bindingTargets seen b
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
        | Some { Kind = SemanticKind.EagerExpr inner }
        | Some { Kind = SemanticKind.Deref inner }
        | Some { Kind = SemanticKind.Reborrow inner } -> bindingTargets seen inner
        | _ -> []
    let mutable changed = true
    while changed do
        changed <- false
        for node in graph.Nodes.Values do
            if node.IsReachable then
                let before = derived.Count
                match node.Kind with
                | SemanticKind.TypeAnnotation(inner, _)
                | SemanticKind.EagerExpr inner
                | SemanticKind.StringByteBorrow inner
                | SemanticKind.Reborrow inner
                | SemanticKind.Deref inner
                | SemanticKind.AddressOf(inner, _)
                | SemanticKind.TupleGet(inner, _)
                | SemanticKind.FieldGet(inner, _)
                | SemanticKind.DUEliminate(inner, _, _, _)
                | SemanticKind.UnionCase(_, _, Some inner)
                | SemanticKind.DUConstruct(_, _, Some inner, _) ->
                    if derived.Contains inner then add node.Id
                | SemanticKind.VarRef(_, Some targetId) ->
                    if derived.Contains targetId then add node.Id
                | SemanticKind.Binding _ ->
                    if node.Children |> List.exists derived.Contains then add node.Id
                | SemanticKind.TupleExpr elements ->
                    if elements |> List.exists derived.Contains then add node.Id
                | SemanticKind.RecordExpr(fields, copyFrom) ->
                    if (fields |> List.exists (snd >> derived.Contains)) || (copyFrom |> Option.exists derived.Contains) then
                        add node.Id
                | SemanticKind.Application(callee, args) ->
                    match graph.Nodes.TryFind callee with
                    | Some { Kind = SemanticKind.Intrinsic info }
                        when info.Module = IntrinsicModule.Array &&
                             not args.IsEmpty &&
                             (info.FullName = "ReadOnlyView.ofArray" || info.FullName = "ReadOnlyView.ofString" || info.FullName = "ReadOnlyView.slice") ->
                        if derived.Contains args.Head then add node.Id
                    | _ when args.Length = 1 && isTupleAccessor callee ->
                        if derived.Contains args.Head then add node.Id
                    | _ -> ()
                | SemanticKind.Set(target, rhs)
                | SemanticKind.FieldSet(target, _, rhs) ->
                    if derived.Contains rhs then
                        for t in bindingTargets Set.empty target do add t
                | SemanticKind.Sequential items when not items.IsEmpty ->
                    if derived.Contains (List.last items) then add node.Id
                | SemanticKind.IfThenElse(_, t, e) ->
                    if derived.Contains t || (e |> Option.exists derived.Contains) then add node.Id
                | SemanticKind.Match(scrutinee, cases) ->
                    if derived.Contains scrutinee then
                        for c in cases do
                            for pb in c.PatternBindings do add pb
                    if cases |> List.exists (fun c -> derived.Contains c.Body) then add node.Id
                | SemanticKind.CaseElimination(scrutinee, arms) ->
                    if derived.Contains scrutinee then
                        for arm in arms do
                            for b in arm.Bindings do add b
                    if arms |> List.exists (fun a -> derived.Contains a.Body) then add node.Id
                | SemanticKind.TryWith(body, handler) ->
                    if derived.Contains body || derived.Contains handler then add node.Id
                | SemanticKind.TryFinally(body, _) ->
                    if derived.Contains body then add node.Id
                | _ -> ()
                if derived.Count > before then changed <- true
    Set.ofSeq derived

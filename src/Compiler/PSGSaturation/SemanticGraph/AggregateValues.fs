// SPDX-License-Identifier: MIT
/// Bounded owned aggregate transport. Admission reads the existing NTU union
/// placement; it neither invents a second size rule nor retains hidden pointers.
module Clef.Compiler.PSGSaturation.SemanticGraph.AggregateValues

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let private scalarPayload ty slot =
    match Types.tryGetNTUKind ty, slot with
    | Some (NTUKind.NTUint _ | NTUKind.NTUuint _), SettledSlot.Integer _
    | Some (NTUKind.NTUfloat _ | NTUKind.NTUposit _), SettledSlot.Real _
    | Some NTUKind.NTUbool, SettledSlot.Bool
    | Some NTUKind.NTUchar, SettledSlot.Char
    | Some NTUKind.NTUunit, SettledSlot.Unit -> true
    | _ -> false

/// Only a concrete Option with one scalar payload can be copied by the current
/// case-aware transport. Reference-bearing and nested aggregate payloads need
/// their own residence/copy contracts.
let scalarOption (graph: SemanticGraph) ty =
    let ty = applySubst ty
    match ty with
    | NativeType.TApp(constructor, [inner]) when constructor.Name = "option" && Set.isEmpty (freeTypeVars ty) ->
        match graph.Layouts.Value.TryFind (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty) with
        | Some (SettledLayout.Union(["None", None; "Some", Some payload], _, Some bytes, Some alignment))
            when bytes > 0 && alignment > 0 && (alignment &&& (alignment - 1)) = 0 ->
            if scalarPayload inner payload then Some(inner, bytes, alignment) else None
        | _ -> None
    | _ -> None


/// Result transport owns both alternatives and copies only the selected case.
let scalarResult (graph: SemanticGraph) ty =
    let ty = applySubst ty
    match ty with
    | NativeType.TApp(constructor, [ok; error])
        when Clef.Compiler.NativeTypedTree.TypeIdentities.constructor constructor =
                 Clef.Compiler.NativeTypedTree.TypeIdentities.constructor Clef.Compiler.NativeTypedTree.Expressions.Types.resultTycon
             && Set.isEmpty (freeTypeVars ty) ->
        match graph.Layouts.Value.TryFind (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty) with
        | Some (SettledLayout.Union(["Ok", Some okSlot; "Error", Some errorSlot], _, Some bytes, Some alignment))
            when bytes > 0 && alignment > 0 && (alignment &&& (alignment - 1)) = 0
                 && scalarPayload ok okSlot && scalarPayload error errorSlot -> Some(ok, error, bytes, alignment)
        | _ -> None
    | _ -> None

let scalarLayout graph ty =
    match scalarOption graph ty with
    | Some(_, bytes, alignment) -> Some(bytes, alignment)
    | None -> scalarResult graph ty |> Option.map (fun (_, _, bytes, alignment) -> bytes, alignment)

/// The complete selected-case write account shared by placement and storage
/// readers. A provenance row alone never authorizes an aggregate store.
let selectedCopy (graph: SemanticGraph) (edge: Hyperedge) =
    let node id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
    let sameType left right = applySubst left = applySubst right
    let guarded source ty selected ordinal =
        match node selected with
        | Some { Kind = SemanticKind.Application(callee, [tag; expected]) } ->
            match node callee, node tag, node expected with
            | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Operators; Operation = "op_Equality" } },
              Some { Kind = SemanticKind.DUGetTag(actual, actualType) },
              Some { Kind = SemanticKind.Literal(NativeLiteral.Int(value, _)) } ->
                actual = source && sameType actualType ty && value = int64 ordinal
            | _ -> false
        | _ -> false
    let payload source ty value ordinal name =
        match node value with
        | Some { Kind = SemanticKind.DUEliminate(actual, tag, caseName, payloadType); Type = actualType; Children = [child] } ->
            actual = source && child = source && tag = ordinal && caseName = name
            && sameType payloadType ty && sameType actualType ty
        | _ -> false
    let writes destination writer ordinal name value =
        match node writer with
        | Some { Kind = SemanticKind.DUInitialize(actual, caseName, tag, actualValue); Children = children } ->
            actual = destination && caseName = name && tag = ordinal && actualValue = value
            && children = destination :: Option.toList value
        | _ -> false
    let branch selected yes no =
        match node edge.Target with
        | Some { Kind = SemanticKind.IfThenElse(guard, actualYes, Some actualNo); Children = children } ->
            guard = selected && actualYes = yes && actualNo = no && children = [selected; yes; no]
        | _ -> false
    let validate source destination selected yes no check =
        match node source, node destination with
        | Some sourceNode, Some destinationNode when sameType sourceNode.Type destinationNode.Type
                                                        && branch selected yes no && check sourceNode.Type ->
            Some(source, destination, [yes; no], Set.ofList (edge.Target :: edge.Sources))
        | _ -> None
    match edge.Class, edge.Role, edge.Ordinal, edge.Sources with
    | EdgeClass.Provenance, EdgeRole.AggregateCopy, 0, [source; destination; selected; value; some; none] ->
        validate source destination selected some none (fun ty ->
            match applySubst ty with
            | NativeType.TApp(tc, [inner]) when tc = Types.optionTyCon ->
                guarded source ty selected 1 && payload source inner value 1 "Some"
                && writes destination some 1 "Some" (Some value) && writes destination none 0 "None" None
            | _ -> false)
    | EdgeClass.Provenance, EdgeRole.AggregateCopy, 0, [source; destination; selected; okValue; errorValue; ok; error] ->
        validate source destination selected ok error (fun ty ->
            match applySubst ty with
            | NativeType.TApp(tc, [okType; errorType]) when
                Clef.Compiler.NativeTypedTree.TypeIdentities.constructor tc =
                    Clef.Compiler.NativeTypedTree.TypeIdentities.constructor Clef.Compiler.NativeTypedTree.Expressions.Types.resultTycon ->
                guarded source ty selected 0 && payload source okType okValue 0 "Ok" && payload source errorType errorValue 1 "Error"
                && writes destination ok 0 "Ok" (Some okValue) && writes destination error 1 "Error" (Some errorValue)
            | _ -> false)
    | _ -> None

/// Scalar constructors consumed only through an exact selected-case copy are
/// activation-local temporaries. Every current value use must belong to the
/// immutable source path or to that copy's tag/payload reads.
let copiedTemporaries (graph: SemanticGraph) (incidence: seq<Hyperedge>) =
    let node id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
    let rec activation seen id =
        if Set.contains id seen then None else
        match node id with
        | Some { Kind = SemanticKind.Lambda _ } -> Some id
        | Some value -> value.Parent |> Option.bind (activation (Set.add id seen))
        | None -> None
    let rec sourcePath seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match node id with
        | Some value ->
            let children =
                match value.Kind with
                | SemanticKind.DUConstruct _ | SemanticKind.FrameRead _ | SemanticKind.Application _ -> Some []
                | SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _) -> Some [value]
                | SemanticKind.Binding(_, false, _, _) when value.Children.Length = 1 -> Some value.Children
                | SemanticKind.Sequential values -> List.tryLast values |> Option.map List.singleton
                | SemanticKind.IfThenElse(_, yes, Some no) -> Some [yes; no]
                | SemanticKind.CaseElimination(_, cases) -> Some(cases |> List.map _.Body)
                | _ -> None
            children |> Option.bind (fun children ->
                let paths = children |> List.map (sourcePath seen)
                if paths |> List.exists Option.isNone then None else
                let paths = List.choose (fun path -> path) paths
                let vertices = Set.add value.Id (paths |> List.map (fun (v, _, _) -> v) |> Set.unionMany)
                let links = Set.union (Set.ofList (children |> List.map (fun child -> child, value.Id)))
                                     (paths |> List.map (fun (_, e, _) -> e) |> Set.unionMany)
                let allocations =
                    match value.Kind with
                    | SemanticKind.DUConstruct _ -> Set.singleton value.Id
                    | _ -> paths |> List.map (fun (_, _, a) -> a) |> Set.unionMany
                Some(vertices, links, allocations))
        | None -> None
    let uses =
        Seq.append graph.Edges incidence
        |> Seq.filter (fun edge -> (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference) && (node edge.Target |> Option.isSome))
        |> Seq.collect (fun edge -> edge.Sources |> Seq.map (fun source -> source, edge.Target))
        |> Set.ofSeq
    graph.Edges |> List.choose (fun edge ->
        selectedCopy graph edge |> Option.bind (fun (source, _, _, _) ->
            match node source, sourcePath Set.empty source with
            | Some value, Some(vertices, links, allocations) when scalarLayout graph value.Type |> Option.isSome ->
                let reads = graph.Nodes.Values |> Seq.choose (fun value ->
                    match value.Kind with
                    | SemanticKind.DUGetTag(actual, _) when actual = source &&
                        (edge.Sources |> List.exists (fun selected ->
                            node selected |> Option.exists (fun guard -> List.contains value.Id guard.Children))) -> Some value.Id
                    | SemanticKind.DUEliminate(actual, _, _, _) when actual = source && List.contains value.Id edge.Sources -> Some value.Id
                    | _ -> None) |> Set.ofSeq
                let admitted (from, target) =
                    if not (vertices.Contains from) then true
                    elif links.Contains(from, target) || (from = source && reads.Contains target) then true
                    else
                        match node target with
                        | Some { Kind = SemanticKind.Sequential items } -> List.contains from items && List.tryLast items <> Some from
                        | _ -> false
                let activationLocal =
                    match activation Set.empty edge.Target with
                    | Some owner -> Set.union vertices reads |> Set.forall (fun id -> activation Set.empty id = Some owner)
                    | None -> false
                if activationLocal && not allocations.IsEmpty && Set.forall admitted uses then Some allocations else None
            | _ -> None)) |> Set.unionMany

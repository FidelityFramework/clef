// SPDX-License-Identifier: MIT
/// Early typed lazy formation contracts, shared by range/effect analysis,
/// layout, and the higher-level origin/memoization readers. No final Codata is
/// forced and no code identity substitutes for a runtime environment instance.
module Clef.Compiler.PSGSaturation.SemanticGraph.LazyContracts

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let environmentType = Types.mkArrayType Types.uint8Type

/// Formation is a schema: executing it twice creates two environments. An
/// alias follows its actual operand, never a cache selected by this schema id.
type Instance = {
    Formation: NodeId
    Thunk: NodeId
    ThunkBody: NodeId
    Environment: NodeId
    Formal: NodeId
    Computed: NodeId
    Cached: NodeId
    InitialComputed: NodeId
    ElementType: NativeType
    Captured: (NodeId * NodeId * bool) list
}

let private live (graph: SemanticGraph) id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
let private single = function [value] -> Some value | _ -> None
let private rows role (graph: SemanticGraph) target =
    graph.Edges |> List.filter (fun edge -> edge.Role = role && edge.Target = target)

/// The cache declaration has no initializer. Its type comes from the actual
/// body; only the computed bit and explicit captures are formation inputs.
let instance (graph: SemanticGraph) owner : Instance option =
    match rows EdgeRole.LazyInstance graph owner |> single, live graph owner with
    | Some { Class = EdgeClass.Provenance; Ordinal = 0
             Sources = [thunk; body; environment; formal; computed; cached; initial] },
      Some { Kind = SemanticKind.LazyValue(actualThunk, actualEnvironment); Type = NativeType.TLazy element }
        when actualThunk = thunk && actualEnvironment = environment ->
        match live graph thunk, live graph body, live graph environment, live graph formal,
              live graph computed, live graph cached, live graph initial with
        | Some { Kind = SemanticKind.Lambda([_, formalType, actualFormal], actualBody, [], _, LambdaContext.LazyThunk); Type = codeType },
          Some result,
          Some { Kind = SemanticKind.LazyEnvironment(actualOwner, initializers); Type = storageType },
          Some { Kind = SemanticKind.PatternBinding _; Type = actualFormalType },
          Some { Kind = SemanticKind.PatternBinding _; Type = computedType; Children = [] },
          Some { Kind = SemanticKind.PatternBinding _; Type = cachedType; Children = [] },
          Some { Kind = SemanticKind.Literal(NativeLiteral.Bool false); Type = initialType }
            when actualFormal = formal && actualBody = body && actualOwner = owner &&
                 applySubst formalType = environmentType && applySubst actualFormalType = environmentType &&
                 applySubst storageType = environmentType && applySubst codeType = NativeType.TFun(environmentType, element) &&
                 applySubst result.Type = element && applySubst cachedType = element &&
                 computedType = Types.boolType && initialType = Types.boolType && computed <> cached &&
                 List.tryHead initializers = Some(computed, initial) &&
                 not (initializers |> List.exists (fun (slot, _) -> slot = cached)) ->
            let captures = initializers |> List.skip 1
            let captureRows = graph.Edges |> List.filter (fun edge ->
                edge.Target = environment && match edge.Role with EdgeRole.LazyCapture _ -> true | _ -> false)
            let captured = captures |> List.mapi (fun ordinal (slot, value) ->
                match captureRows |> List.filter (fun edge -> edge.Ordinal = ordinal), live graph slot, live graph value with
                | [{ Class = EdgeClass.Provenance; Role = EdgeRole.LazyCapture mutableCell; Sources = [actual; source; input] }],
                  Some sourceNode, Some _ when actual = owner && source = slot && input = value &&
                                                     slot <> cached && slot <> computed ->
                    let initializerAgrees =
                        if slot = value then
                            mutableCell = (match sourceNode.Kind with SemanticKind.Binding(_, true, _, _) -> true | _ -> false)
                        else
                            // Forwarding needs the actual outer-instance slot
                            // relation and a chain rooted at this declaration.
                            // Equal value/byref types cannot prove that identity.
                            // Current formation recipes retain direct sources.
                            false
                    if initializerAgrees then Some(slot, value, mutableCell) else None
                | _ -> None)
            if captureRows.Length = captures.Length && List.forall Option.isSome captured &&
               (initializers |> List.map fst |> Set.ofList).Count = initializers.Length then
                Some { Formation = owner; Thunk = thunk; ThunkBody = body; Environment = environment; Formal = formal
                       Computed = computed; Cached = cached; InitialComputed = initial; ElementType = element
                       Captured = List.choose id captured }
            else None
        | _ -> None
    | _ -> None

let instances graph =
    // Full-platform graphs contain many unrelated declarations. Only actual
    // lazy formations need their incidence validated; do not scan all edges
    // once for every unrelated node merely to discover its kind afterward.
    graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        match node.Kind with
        | SemanticKind.LazyValue _ when node.IsReachable -> instance graph id |> Option.map (fun value -> id, value)
        | _ -> None) |> Map.ofList

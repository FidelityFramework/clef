// SPDX-License-Identifier: MIT
/// Complete finite callable value flow at ordinary argument, result and alias
/// boundaries. This is not a mutable-cell snapshot and does not select an
/// implementation or environment. Every leaf is an independently settled
/// callable occurrence; opaque alternatives remain explicit refusals.
module Clef.Compiler.PSGSaturation.SemanticGraph.CallableFlows

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Inputs = {
    Carriers: Map<NodeId, CallableCarrier>
    Joins: Map<NodeId, CallableJoin>
    Layouts: Map<NodeId, EnvironmentLayout>
    SequenceFlows: Map<NodeId, SequenceFlow>
    SequenceFamilies: Map<NodeId, SequenceFamily>
}
type Residual = { Occurrence: NodeId; Reason: string }
type private Step = { Inputs: NodeId list; Calls: CallableFlowCall list; Opaque: bool }
type private Facts = { Leaves: Set<NodeId>; Unknown: Set<NodeId> }

let private settleCore (inputs: Inputs) (graph: SemanticGraph) : Map<NodeId, CallableFlow> * Residual list =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let tracked = nodes |> Map.filter (fun _ node -> match applySubst node.Type with NativeType.TFun _ -> true | _ -> false)
    let resolution = CallableOrigins.resolve graph
    let ingress = CallableIngress.analyzeWith graph resolution
    let admitted id = CallableIngress.allowsOccurrence ingress id
    let exact id = inputs.Carriers.ContainsKey id && admitted id
    let callSite call (target: CallableOrigins.CallTarget) =
        { Call = call; Implementation = target.Lambda
          Parameters = target.Parameters |> List.map (fun (_, _, id) -> id)
          Arguments = target.Arguments; Result = target.Body }
    let noCall sources = { Inputs = sources; Calls = []; Opaque = false }
    let opaque = { Inputs = []; Calls = []; Opaque = true }
    let steps = tracked |> Map.map (fun id node ->
        if not (admitted id) then opaque
        elif exact id then noCall []
        elif inputs.Joins.ContainsKey id then opaque // mutable reads retain their own frontier contract
        else
            match node.Kind, node.Children with
            | SemanticKind.Binding(_, false, _, _), [value]
            | SemanticKind.VarRef(_, Some value), _
            | SemanticKind.TypeAnnotation(value, _), _ -> noCall [value]
            | SemanticKind.EagerExpr value, _ when ExplicitDemand.operand graph id = Some value -> noCall [value]
            | SemanticKind.Sequential values, _ ->
                List.tryLast values |> Option.map (fun value -> noCall [value]) |> Option.defaultValue opaque
            | SemanticKind.IfThenElse(_, yes, no), _ -> noCall (yes :: Option.toList no)
            | SemanticKind.Match(_, cases), _ -> noCall (cases |> List.map _.Body)
            | SemanticKind.CaseElimination(_, cases), _ -> noCall (cases |> List.map _.Body)
            | SemanticKind.PatternBinding _, _ ->
                let supplied = resolution.ParameterInputs.TryFind id |> Option.defaultValue []
                let selected = supplied |> List.map (fun (call, actual) ->
                    match resolution.Calls.TryFind call with
                    | Some resolved when resolved.Complete && not resolved.Targets.IsEmpty ->
                        let targets = resolved.Targets |> List.filter (fun target ->
                            target.Parameters.Length = target.Arguments.Length &&
                            (List.zip target.Parameters target.Arguments
                             |> List.exists (fun ((_, _, formal), argument) -> formal = id && argument = actual)))
                        if targets.IsEmpty then None else Some(actual, targets |> List.map (callSite call))
                    | _ -> None)
                if supplied.IsEmpty || List.exists Option.isNone selected then opaque
                else
                    let selected = List.choose (fun value -> value) selected
                    { Inputs = selected |> List.map fst |> List.distinct
                      Calls = selected |> List.collect snd |> List.distinct; Opaque = false }
            | SemanticKind.Application _, _ ->
                match resolution.Calls.TryFind id with
                | Some resolved when resolved.Complete && not resolved.Targets.IsEmpty ->
                    { Inputs = resolved.Targets |> List.map _.Body |> List.distinct
                      Calls = resolved.Targets |> List.map (callSite id); Opaque = false }
                | _ -> opaque
            | SemanticKind.EnvironmentRead(environment, slot), _ ->
                ClosureEnvironments.tryEnvironmentOwner graph environment
                |> Option.bind (ClosureEnvironments.capturedInitializers graph)
                |> Option.bind (fun captures ->
                    match captures |> List.filter (fun (source, _, _) -> source = slot) with
                    | [_, value, false] -> Some(noCall [value])
                    | _ -> None)
                |> Option.defaultValue opaque
            | _ -> opaque)
    let empty = { Leaves = Set.empty; Unknown = Set.empty }
    let union left right = { Leaves = Set.union left.Leaves right.Leaves; Unknown = Set.union left.Unknown right.Unknown }
    let mutable facts = tracked |> Map.map (fun id _ ->
        if exact id then { empty with Leaves = Set.singleton id }
        elif steps[id].Opaque then { empty with Unknown = Set.singleton id }
        else empty)
    let propagate () =
        let mutable changed = true
        while changed do
            changed <- false
            for KeyValue(id, step) in steps do
                if not (exact id) then
                    let next = step.Inputs |> List.fold (fun found source ->
                        let value = facts.TryFind source |> Option.defaultValue { empty with Unknown = Set.singleton source }
                        union found value) facts[id]
                    if next <> facts[id] then
                        facts <- facts.Add(id, next)
                        changed <- true
    propagate ()
    // A constructor-free cycle is not an empty but complete callable family.
    facts <- facts |> Map.map (fun id value ->
        if value.Leaves.IsEmpty && value.Unknown.IsEmpty then { value with Unknown = Set.singleton id } else value)
    propagate ()
    let environmentBytes (carrier: CallableCarrier) =
        match carrier.Environment with
        | None -> Some None
        | Some environment ->
            inputs.Layouts.TryFind environment.Owner
            |> Option.filter (fun layout -> layout.Formal = environment.Formal && layout.Implementation = carrier.Implementation && layout.Bytes > 0)
            |> Option.map (fun layout -> Some layout.Bytes)
    let rawEnvironment id =
        inputs.Layouts.Values |> Seq.tryPick (fun layout -> if layout.Formal = id then Some layout.Bytes else None)
    let sequenceFamily id =
        inputs.SequenceFlows.TryFind id |> Option.bind (fun flow ->
            if not flow.Unknown.IsEmpty || flow.Owners.IsEmpty then None else
            match inputs.SequenceFamilies.Values |> Seq.filter (fun family ->
                family.Participants.Contains id && Set.isSubset flow.Owners (family.Members |> Map.keys |> Set.ofSeq)) |> Seq.toList with
            | [family] -> Some(flow, family)
            | _ -> None)
    let alternatives id =
        facts.TryFind id |> Option.bind (fun value ->
            if value.Unknown.IsEmpty && not value.Leaves.IsEmpty then Some(Set.toList value.Leaves) else None)
    let lazyOwner = lazy (LazyValues.tryOwner graph)
    let rec sameShape seen left right =
        match left, right with
        | CallableValueShape.Data left, CallableValueShape.Data right ->
            match nodes.TryFind left, nodes.TryFind right with
            | Some left, Some right when applySubst left.Type = applySubst right.Type ->
                match rawEnvironment left.Id, rawEnvironment right.Id with
                | Some left, Some right -> left = right
                | None, None ->
                    match Types.tryGetNTUKind (applySubst left.Type) with
                    | Some (NTUKind.NTUint _ | NTUKind.NTUuint _) ->
                        let width = RangeAnalysis.heldWidth graph left.Id
                        width.IsSome && width = RangeAnalysis.heldWidth graph right.Id
                    | _ -> true
                | _ -> false
            | _ -> false
        | CallableValueShape.Lazy left, CallableValueShape.Lazy right ->
            match lazyOwner.Value left, lazyOwner.Value right with
            | Some left, Some right when left = right -> LazyContracts.instance graph left |> Option.isSome
            | _ -> false
        | CallableValueShape.Sequence left, CallableValueShape.Sequence right ->
            match sequenceFamily left, sequenceFamily right with
            | Some(left, leftFamily), Some(right, rightFamily) ->
                leftFamily.Identity = rightFamily.Identity && left.IsEnumerator = right.IsEnumerator &&
                applySubst left.ElementType = applySubst right.ElementType
            | _ -> false
        | CallableValueShape.Callable left, CallableValueShape.Callable right ->
            if Set.contains (left, right) seen then false else
            match alternatives left, alternatives right with
            | Some lefts, Some rights ->
                lefts |> List.forall (fun left -> rights |> List.forall (fun right ->
                    sameBoundary (Set.add (left, right) seen) inputs.Carriers[left] inputs.Carriers[right]))
            | _ -> false
        | _ -> false
    and sameBoundary seen (left: CallableCarrier) (right: CallableCarrier) =
        applySubst left.SourceType = applySubst right.SourceType &&
        environmentBytes left = environmentBytes right && (environmentBytes left).IsSome &&
        left.ParameterShapes.Length = right.ParameterShapes.Length &&
        List.forall2 (sameShape seen) left.ParameterShapes right.ParameterShapes &&
        sameShape seen left.ResultShape right.ResultShape
    let proof root =
        let rec visit seen id =
            if Set.contains id seen || exact id then seen else
            let seen = Set.add id seen
            match steps.TryFind id with
            | Some step -> List.fold visit seen step.Inputs
            | None -> seen
        let participants = visit Set.empty root
        let dependencies = participants |> Set.toList |> List.map (fun id -> id, steps[id].Inputs) |> Map.ofList
        let calls = participants |> Set.toList |> List.collect (fun id -> steps[id].Calls) |> List.distinct |> List.sort
        dependencies, calls
    let mutable residuals = []
    let flows = facts |> Map.toList |> List.choose (fun (id, value) ->
        if exact id || inputs.Joins.ContainsKey id || not value.Unknown.IsEmpty || value.Leaves.IsEmpty then None else
        let alternatives = Set.toList value.Leaves
        let first = inputs.Carriers[alternatives.Head]
        if applySubst (CallableCarriers.sourceType tracked[id]) <> applySubst first.SourceType ||
           not (alternatives |> List.forall (fun alternative -> sameBoundary Set.empty first inputs.Carriers[alternative])) then
            residuals <- { Occurrence = id; Reason = "Every callable alternative must share its actual source type, parameter, result and environment convention." } :: residuals
            None
        else
            let dependencies, calls = proof id
            Some(id, { Occurrence = id; SourceType = CallableCarriers.sourceType tracked[id]
                       Alternatives = alternatives; Dependencies = dependencies; Calls = calls })) |> Map.ofList
    flows, List.rev residuals

let settle inputs graph =
    if inputs.Carriers.IsEmpty then Map.empty, [] else settleCore inputs graph

let private validationCache =
    System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, Map<NodeId, CallableFlow>>()

/// Re-read actual participants on the current immutable graph revision. Old
/// codata cannot hide an added opaque actual, changed body or redirected alias.
let validate (graph: SemanticGraph) (expected: CallableFlow) =
    let flows = validationCache.GetValue(graph, fun graph ->
        let codata = graph.Codata.Value
        let carriers, _ = CallableCarriers.settle
                            { Layouts = codata.EnvironmentLayouts; Origins = ClosureEnvironments.origins graph
                              Known = ClosureEnvironments.knownCallables graph } graph
        let joins = MutableCallableStorage.settle carriers codata.EnvironmentLayouts graph
        settle { Carriers = carriers; Joins = joins.Joins; Layouts = codata.EnvironmentLayouts
                 SequenceFlows = codata.SequenceFlows; SequenceFamilies = codata.SequenceFamilies } graph |> fst)
    flows.TryFind expected.Occurrence = Some expected

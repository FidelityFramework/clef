// SPDX-License-Identifier: MIT
/// Explicit lazy formation and memoization use ordinary Baker ingredients.
/// The force algorithm is graph structure, never an Alex-side reconstruction.
module Clef.Compiler.Baker.Recipes.LazyRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Baker.Recipes.Decomposition
module Lazy = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues
module C = Clef.Compiler.Baker.Ingredients.Continuations

type Expansion = { Structure: Result; Edges: Hyperedge list }

let private finish (graph: SemanticGraph) root nodes evidence =
    let key (edge: Hyperedge) = edge.Target, edge.Class, edge.Role, edge.Ordinal, edge.Sources
    let old = nodes |> List.choose (fun node -> graph.Nodes.TryFind node.Id)
              |> List.collect structuralIncidence |> List.map key |> Set.ofList
    { Structure = mkResultNoShadow nodes root []
      Edges = (graph.Edges |> List.filter (fun edge -> not (old.Contains (key edge))))
              @ (nodes |> List.collect structuralIncidence) @ evidence }

let formation (ctx: Context) (graph: SemanticGraph) (plan: Lazy.Plan) : Expansion =
    let owner, thunk = plan.Source, plan.Thunk
    let element = graph.Nodes[plan.Body].Type
    let state = SaturationState.create ctx.SourceRange ctx.OriginalHOF ctx.ExpansionId owner.Id graph.Platform
    let references = ResizeArray<Hyperedge>()
    let outcome, nodes = run state (saturation {
        let! formal = patternBinding "__lazy_environment" Lazy.environmentType
        let! computed = patternBinding "__lazy_computed" Types.boolType
        let! cached = patternBinding "__lazy_cached" element
        let! initial = boolLit false
        let initializers = (computed, initial) :: (plan.Captures |> List.map (fun capture -> capture.SourceNodeId.Value, capture.SourceNodeId.Value))
        // Captured declarations remain references. Formation never traverses a
        // captured binding's computation or evaluates the deferred thunk body.
        let! environment = C.create (SemanticKind.LazyEnvironment(owner.Id, initializers)) Lazy.environmentType [initial]
        let captures = plan.Captures |> List.map (fun capture -> capture.SourceNodeId.Value, capture) |> Map.ofList
        let rec within seen id =
            if Set.contains id seen then seen else
            match graph.Nodes.TryFind id with
            | None -> seen
            | Some node ->
                let seen = Set.add id seen
                match node.Kind with
                | SemanticKind.Lambda _ | SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ | SemanticKind.LazyValue _ -> seen
                | _ -> List.fold within seen node.Children
        let bodyNodes = within Set.empty plan.Body
        let destinations = bodyNodes |> Set.toList |> List.choose (fun id ->
            match graph.Nodes[id].Kind with SemanticKind.Set(target, _) -> Some target | _ -> None) |> Set.ofList
        let sourceOf id =
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.VarRef(_, Some source) } when captures.ContainsKey source -> Some source
            | _ -> None
        for id in bodyNodes do
            let node = graph.Nodes[id]
            match node.Kind with
            | SemanticKind.VarRef(_, Some source) when captures.ContainsKey source && not (destinations.Contains id) ->
                let! environment = varRef "__lazy_environment" (Some formal) Lazy.environmentType
                do! enrich node (SemanticKind.LazyRead(environment, source)) node.Type [environment] node.EmissionStrategy false
                references.Add { Sources = [owner.Id; source]; Target = node.Id
                                 Class = EdgeClass.Provenance; Role = EdgeRole.CaptureReferenceOrigin; Ordinal = 0 }
                do! preturn ()
            | SemanticKind.Set(target, value) when sourceOf target |> Option.exists (fun source -> captures[source].IsMutable) ->
                let source = (sourceOf target).Value
                let! environment = varRef "__lazy_environment" (Some formal) Lazy.environmentType
                do! enrich node (SemanticKind.LazyWrite(environment, source, value)) node.Type [environment; value] node.EmissionStrategy false
            | _ -> do! preturn ()
        let enclosing = match thunk.Kind with SemanticKind.Lambda(_, _, _, enclosing, _) -> enclosing | _ -> None
        let codeType = NativeType.TFun(Lazy.environmentType, element)
        do! enrich thunk (SemanticKind.Lambda(["__lazy_environment", Lazy.environmentType, formal], plan.Body, [], enclosing, LambdaContext.LazyThunk))
                        codeType [formal; plan.Body] thunk.EmissionStrategy false
        do! enrich owner (SemanticKind.LazyValue(thunk.Id, environment)) owner.Type [thunk.Id; environment] owner.EmissionStrategy false
        return formal, computed, cached, initial, environment
    })
    match outcome with
    | Matched(formal, computed, cached, initial, environment) ->
        let instance =
            { Class = EdgeClass.Provenance; Role = EdgeRole.LazyInstance; Ordinal = 0; Target = owner.Id
              Sources = [thunk.Id; plan.Body; environment; formal; computed; cached; initial] }
        let captures = plan.Captures |> List.mapi (fun ordinal capture ->
            let source = capture.SourceNodeId.Value
            { Class = EdgeClass.Provenance; Role = EdgeRole.LazyCapture capture.IsMutable; Ordinal = ordinal
              Sources = [owner.Id; source; source]; Target = environment })
        finish graph owner.Id nodes (instance :: captures @ List.ofSeq references)
    | NoMatch reason -> invalidOp ("Lazy formation saturation failed: " + reason)

/// One demanded force snapshots its actual environment once. The cold branch
/// computes once, stores that result, publishes computed=true, then yields the
/// same result. No default cache value is constructed or read on the cold path.
let force (ctx: Context) (graph: SemanticGraph) (source: SemanticNode) (contract: Lazy.Instance) : Expansion =
    let operand = match source.Kind with SemanticKind.LazyForce operand -> operand | _ -> invalidArg "source" "Lazy.force requires its source force occurrence."
    let state = SaturationState.create ctx.SourceRange ctx.OriginalHOF ctx.ExpansionId source.Id graph.Platform
    let outcome, nodes = run state (saturation {
        let! actualEnvironment = C.create (SemanticKind.LazyEnvironmentReference operand) Lazy.environmentType [operand]
        let! environmentBinding = letBind "__lazy_force_environment" actualEnvironment Lazy.environmentType
        let environmentRef () = varRef "__lazy_force_environment" (Some environmentBinding) Lazy.environmentType
        let! conditionEnvironment = environmentRef ()
        let! condition = C.create (SemanticKind.LazyRead(conditionEnvironment, contract.Computed)) Types.boolType [conditionEnvironment]
        let! cachedEnvironment = environmentRef ()
        let! cachedRead = C.create (SemanticKind.LazyRead(cachedEnvironment, contract.Cached)) contract.ElementType [cachedEnvironment]
        let! code = varRef "__lazy_thunk" (Some contract.Thunk) (NativeType.TFun(Lazy.environmentType, contract.ElementType))
        let! invocationEnvironment = environmentRef ()
        let! invocation = app code [invocationEnvironment] contract.ElementType
        let! resultBinding = letBind "__lazy_first_result" invocation contract.ElementType
        let! storedResult = varRef "__lazy_first_result" (Some resultBinding) contract.ElementType
        let! storeEnvironment = environmentRef ()
        let! store = C.create (SemanticKind.LazyWrite(storeEnvironment, contract.Cached, storedResult)) Types.unitType [storeEnvironment; storedResult]
        let! published = boolLit true
        let! publishEnvironment = environmentRef ()
        let! publication = C.create (SemanticKind.LazyWrite(publishEnvironment, contract.Computed, published)) Types.unitType [publishEnvironment; published]
        let! result = varRef "__lazy_first_result" (Some resultBinding) contract.ElementType
        let! uncached = C.block [resultBinding; store; publication; result] contract.ElementType
        let! conditional = ifThenElse condition cachedRead uncached contract.ElementType
        do! enrich source (SemanticKind.Sequential [environmentBinding; conditional]) source.Type
                        [environmentBinding; conditional] source.EmissionStrategy false
        return environmentBinding, condition, cachedRead, invocation, resultBinding, store, publication, uncached, conditional
    })
    match outcome with
    | Matched(environmentBinding, condition, cachedRead, invocation, resultBinding, store, publication, uncached, conditional) ->
        let evidence =
            { Class = EdgeClass.Provenance; Role = EdgeRole.LazyMemoization; Ordinal = 0; Target = source.Id
              Sources = [contract.Formation; operand; environmentBinding; condition; cachedRead; invocation; resultBinding; store; publication; uncached; conditional] }
        finish graph source.Id nodes [evidence]
    | NoMatch reason -> invalidOp ("Lazy force saturation failed: " + reason)

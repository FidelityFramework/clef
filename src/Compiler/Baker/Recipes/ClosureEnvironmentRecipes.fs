// SPDX-License-Identifier: MIT
/// Materialize the selected known callable form through ordinary typed graph
/// values, explicit capture access and direct applications with a real formal.
module Clef.Compiler.Baker.Recipes.ClosureEnvironmentRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Baker.Recipes.Decomposition
module C = Clef.Compiler.Baker.Ingredients.Continuations

type Expansion = { Structure: Result; Edges: Hyperedge list }

let materialize (ctx: Context) (graph: SemanticGraph) (plan: Plan) : Expansion =
    let source = plan.Source
    let state = SaturationState.create { source.Range with End = source.Range.Start }
                    ctx.OriginalHOF ctx.ExpansionId source.Id graph.Platform
    let formations = ResizeArray<Hyperedge>()
    let outcome, nodes = run state (saturation {
        let parameters, body, enclosing, context =
            match source.Kind with
            | SemanticKind.Lambda(parameters, body, _, enclosing, context) -> parameters, body, enclosing, context
            | _ -> invalidOp "An environment plan must identify a source Lambda."
        let! formal = patternBinding "__closure_environment" environmentType
        let implementation = NodeId.fresh()
        let binding = NodeId.fresh()
        let implementationType = NativeType.TFun(environmentType, source.Type)
        let initializers = plan.Captures |> List.map (fun capture -> capture.SourceNodeId.Value, capture.SourceNodeId.Value)
        let! environment = C.create (SemanticKind.EnvironmentCreate(source.Id, initializers)) environmentType []
        let captures = plan.Captures |> List.map (fun capture -> capture.SourceNodeId.Value, capture) |> Map.ofList
        let rec within seen id =
            if Set.contains id seen then seen else
            match graph.Nodes.TryFind id with
            | Some node ->
                let seen = Set.add id seen
                match node.Kind with
                | SemanticKind.SeqExpr _ | SemanticKind.Lambda _ | SemanticKind.LazyExpr _ -> seen
                | _ -> List.fold within seen node.Children
            | None -> seen
        let bodyNodes = within Set.empty body
        let sourceOf id =
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.VarRef(_, Some declaration) } when captures.ContainsKey declaration -> Some declaration
            | _ -> None
        for id in bodyNodes do
            let node = graph.Nodes[id]
            match node.Kind with
            | SemanticKind.SeqExpr(generator, nested) when nested |> List.exists (fun capture -> capture.SourceNodeId |> Option.exists captures.ContainsKey) ->
                let! initializers = nested |> C.collect (fun capture -> saturation {
                    let declaration = capture.SourceNodeId.Value
                    if captures.ContainsKey declaration then
                        let! env = varRef "__closure_environment" (Some formal) environmentType
                        let kind, ty =
                            if capture.IsMutable then SemanticKind.EnvironmentBorrow(env, declaration), NativeType.TByref(capture.Type, ByrefKind.InOut)
                            else SemanticKind.EnvironmentRead(env, declaration), capture.Type
                        let! value = C.create kind ty [env]
                        return declaration, value, capture.IsMutable
                    else return declaration, declaration, capture.IsMutable
                })
                let! child = C.create (SemanticKind.SeqExpr(generator, nested)) node.Type [generator]
                let eager = initializers |> List.choose (fun (slot, value, _) -> if slot = value then None else Some value)
                do! enrich node (SemanticKind.Sequential(eager @ [child])) node.Type (eager @ [child]) node.EmissionStrategy false
                formations.Add { Sources = [source.Id; implementation; formal]; Target = child
                                 Class = EdgeClass.Provenance; Role = EdgeRole.SequenceCaptureFormation; Ordinal = 0 }
                initializers |> List.iteri (fun ordinal (slot, value, mutableCell) ->
                    formations.Add { Sources = [slot; value]; Target = child; Class = EdgeClass.Provenance
                                     Role = EdgeRole.SequenceCaptureInitializer mutableCell; Ordinal = ordinal })
                do! preturn ()
            | SemanticKind.VarRef(_, Some declaration) when captures.ContainsKey declaration ->
                let! env = varRef "__closure_environment" (Some formal) environmentType
                do! enrich node (SemanticKind.EnvironmentRead(env, declaration)) node.Type [env] node.EmissionStrategy false
            | SemanticKind.Set(target, value) when sourceOf target |> Option.exists (fun declaration -> captures[declaration].IsMutable) ->
                let declaration = (sourceOf target).Value
                let! env = varRef "__closure_environment" (Some formal) environmentType
                do! enrich node (SemanticKind.EnvironmentWrite(env, declaration, value)) node.Type [env; value] node.EmissionStrategy false
            | _ -> do! preturn ()
        let implementationNode =
            { source with Id = implementation
                          Kind = SemanticKind.Lambda(("__closure_environment", environmentType, formal) :: parameters, body, [], enclosing, context)
                          Type = implementationType; Range = { source.Range with End = source.Range.Start }
                          Children = formal :: (parameters |> List.map (fun (_, _, id) -> id)) @ [body]
                          Parent = Some binding
                          Metadata = source.Metadata.Remove(ClosureMetadata.RequiresClosurePair).Remove(ClosureMetadata.LambdaExpression)
                                         .Add(ClosureMetadata.SourceSignature, MetadataValue.Type source.Type) }
        do! emit implementationNode
        let name = sprintf "__closure_environment_impl_%d" (NodeId.value source.Id)
        let codeBinding =
            { implementationNode with Id = binding; Kind = SemanticKind.Binding(name, false, false, None)
                                      Children = [implementation]; Parent = None }
        do! emit codeBinding
        do! enrich source (SemanticKind.ClosureValue(implementation, environment)) source.Type
                        [implementation; environment] source.EmissionStrategy false
        for callId in plan.Calls do
            let call = graph.Nodes[callId]
            match call.Kind with
            | SemanticKind.Application(callee, arguments) ->
                let! actualEnvironment = C.create (SemanticKind.EnvironmentReference callee) environmentType [callee]
                let! functionRef = varRef name (Some binding) implementationType
                do! enrich call (SemanticKind.Application(functionRef, actualEnvironment :: arguments)) call.Type
                        (functionRef :: actualEnvironment :: arguments) call.EmissionStrategy false
            | _ -> invalidOp "A known callable call plan must identify an Application."
        return environment, implementation, formal
    })
    match outcome with
    | Matched(environment, implementation, formal) ->
        let key (edge: Hyperedge) = edge.Target, edge.Class, edge.Role, edge.Ordinal, edge.Sources
        let replaced = nodes |> List.choose (fun node -> graph.Nodes.TryFind node.Id)
                       |> List.collect structuralIncidence |> List.map key |> Set.ofList
        let captures = plan.Captures |> List.mapi (fun ordinal capture ->
            let declaration = capture.SourceNodeId.Value
            { Sources = [source.Id; declaration; declaration]; Target = environment
              Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentCapture capture.IsMutable; Ordinal = ordinal })
        let signature = { Sources = [source.Id; implementation]; Target = formal
                          Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentFormal; Ordinal = 0 }
        { Structure = mkResultNoShadow nodes source.Id []
          Edges = (graph.Edges |> List.filter (fun edge -> not (replaced.Contains (key edge))))
                  @ (nodes |> List.collect structuralIncidence) @ captures @ [signature] @ List.ofSeq formations }
    | NoMatch reason -> invalidOp ("Closure environment saturation failed: " + reason)

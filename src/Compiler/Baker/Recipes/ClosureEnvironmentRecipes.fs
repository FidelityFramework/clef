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

/// A stateless callable is plain named code. Immutable aliases carry no
/// environment value, so deferred uses name the declaration directly rather
/// than allocating a zero-byte environment or retaining a spurious slot.
let private plain (ctx: Context) (graph: SemanticGraph) (plan: Plan) : Expansion =
    let source = plan.Source
    let read = tryImplementation graph
    let sourceDeclaration = trySourceDeclaration graph
    let resolution = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
    let ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyzeWith graph resolution
    // Code identity is not demand authority. In particular, an immutable
    // binding may contain a factory call that returns this stateless lambda.
    // Redirecting its reads to code would erase the demanded factory occurrence.
    // Only transparent immutable references to this original leaf can disappear.
    let rec leafAlias seen id =
        if id = source.Id then true
        elif Set.contains id seen then false
        else
            let seen = Set.add id seen
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _) } -> leafAlias seen value
            | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> leafAlias seen value
            | Some { Kind = SemanticKind.PatternBinding _ } ->
                let supplied = resolution.ParameterInputs.TryFind id |> Option.defaultValue []
                not supplied.IsEmpty &&
                (supplied |> List.forall (fun (call, actual) ->
                    match resolution.Calls.TryFind call with
                    | Some invocation when invocation.Complete && not invocation.Unknown &&
                                           not invocation.Targets.IsEmpty ->
                        let selected = invocation.Targets |> List.filter (fun target ->
                            target.Parameters.Length = target.Arguments.Length &&
                            (List.zip target.Parameters target.Arguments |> List.exists (fun ((_, _, formal), argument) ->
                                formal = id && argument = actual)))
                        not selected.IsEmpty && leafAlias seen actual
                    | _ -> false))
            | _ -> false
    let referenceOrigins = ResizeArray<Hyperedge>()
    let aliases = graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        if node.IsReachable && read id = Some source.Id && leafAlias Set.empty id &&
           Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence ingress id
        then Some id else None) |> Set.ofList
    let implementation, binding = NodeId.fresh(), NodeId.fresh()
    let name = sprintf "__closure_code_%d" (NodeId.value source.Id)
    let state = SaturationState.create { source.Range with End = source.Range.Start }
                    ctx.OriginalHOF ctx.ExpansionId source.Id graph.Platform
    let result, nodes = run state (saturation {
        let code =
            { source with Id = implementation; Parent = Some binding
                          Range = { source.Range with End = source.Range.Start }
                          Metadata = source.Metadata.Remove(ClosureMetadata.RequiresClosurePair).Remove(ClosureMetadata.LambdaExpression)
                                        .Add(ClosureMetadata.SourceSignature, MetadataValue.Type source.Type) }
        do! emit code
        do! emit { code with Id = binding; Kind = SemanticKind.Binding(name, false, false, None); Children = [implementation]; Parent = None }
        do! enrich source (SemanticKind.VarRef(name, Some binding)) source.Type [] source.EmissionStrategy false
        for node in graph.Nodes.Values do
            if node.IsReachable && node.Id <> source.Id then
                let trim captures = captures |> List.filter (fun capture ->
                    capture.IsMutable || not (capture.SourceNodeId |> Option.exists aliases.Contains))
                match node.Kind with
                | SemanticKind.VarRef(sourceName, Some declaration)
                    when aliases.Contains declaration &&
                         Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence ingress node.Id ->
                    let original = sourceDeclaration node.Id |> Option.defaultValue declaration
                    referenceOrigins.Add {
                        Sources = [original; binding]; Target = node.Id
                        Class = EdgeClass.Provenance; Role = EdgeRole.CallableReferenceOrigin; Ordinal = 0 }
                    do! enrich node (SemanticKind.VarRef(sourceName, Some binding)) node.Type [] node.EmissionStrategy false
                | SemanticKind.Lambda(parameters, body, captures, enclosing, context) when trim captures <> captures ->
                    do! enrich node (SemanticKind.Lambda(parameters, body, trim captures, enclosing, context)) node.Type node.Children node.EmissionStrategy false
                | SemanticKind.SeqExpr(generator, captures) when trim captures <> captures ->
                    do! enrich node (SemanticKind.SeqExpr(generator, trim captures)) node.Type node.Children node.EmissionStrategy false
                | _ -> do! preturn ()
            else do! preturn ()
        // Plain promotion changes code identity, not the actual parameter
        // boundary. Keep each existing application and its callee evaluation:
        // aliases above now resolve to this code, and effectful callee expressions
        // retain their own ordered children. No second invocation is constructed.
        return source.Id
    })
    match result with
    | Matched _ ->
        let key (edge: Hyperedge) = edge.Target, edge.Class, edge.Role, edge.Ordinal, edge.Sources
        let replaced = nodes |> List.choose (fun node -> graph.Nodes.TryFind node.Id)
                       |> List.collect structuralIncidence |> List.map key |> Set.ofList
        let references = referenceOrigins |> Seq.map _.Target |> Set.ofSeq
        { Structure = mkResultNoShadow nodes source.Id []
          Edges = (graph.Edges |> List.filter (fun edge ->
                      not (replaced.Contains (key edge)) &&
                      not (edge.Role = EdgeRole.CallableReferenceOrigin && references.Contains edge.Target)))
                  @ (nodes |> List.collect structuralIncidence) @ List.ofSeq referenceOrigins }
    | NoMatch reason -> invalidOp ("Plain callable saturation failed: " + reason)

let materialize (ctx: Context) (graph: SemanticGraph) (plan: Plan) : Expansion =
    if plan.Captures.IsEmpty then plain ctx graph plan else
    let source = plan.Source
    let state = SaturationState.create { source.Range with End = source.Range.Start }
                    ctx.OriginalHOF ctx.ExpansionId source.Id graph.Platform
    let formations = ResizeArray<Hyperedge>()
    let forwarded = ResizeArray<NodeId * Hyperedge list>()
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
            | SemanticKind.EnvironmentCreate(owner, _) ->
                // A nested closure keeps its original slot identities. Its
                // formation reads this activation's environment values/cells;
                // it never reevaluates the outer source declarations.
                match capturedInitializers graph owner with
                | Some initializers when initializers |> List.exists (fun (slot, value, _) -> slot = value && captures.ContainsKey slot) ->
                    let! initializers = initializers |> C.collect (fun (slot, value, mutableCell) -> saturation {
                        if slot = value && captures.ContainsKey slot then
                            let capture = captures[slot]
                            let! env = varRef "__closure_environment" (Some formal) environmentType
                            let kind, ty =
                                if mutableCell then SemanticKind.EnvironmentBorrow(env, slot), NativeType.TByref(capture.Type, ByrefKind.InOut)
                                else SemanticKind.EnvironmentRead(env, slot), capture.Type
                            let! held = C.create kind ty [env]
                            return slot, held, mutableCell
                        else return slot, value, mutableCell
                    })
                    let eager = initializers |> List.choose (fun (slot, value, _) ->
                        if slot <> value && captures.ContainsKey slot then Some value else None)
                    let children = List.distinct (node.Children @ eager)
                    do! enrich node (SemanticKind.EnvironmentCreate(owner, initializers |> List.map (fun (slot, value, _) -> slot, value)))
                                    node.Type children node.EmissionStrategy false
                    let rows = initializers |> List.mapi (fun ordinal (slot, value, mutableCell) ->
                        { Sources = [owner; slot; value]; Target = node.Id; Class = EdgeClass.Provenance
                          Role = EdgeRole.EnvironmentCapture mutableCell; Ordinal = ordinal })
                    forwarded.Add(node.Id, rows)
                    do! preturn ()
                | _ -> do! preturn ()
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
                formations.Add { Sources = [source.Id; declaration]; Target = node.Id
                                 Class = EdgeClass.Provenance; Role = EdgeRole.CaptureReferenceOrigin; Ordinal = 0 }
                do! preturn ()
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
        let forwarded = Map.ofSeq forwarded
        { Structure = mkResultNoShadow nodes source.Id []
          Edges = (graph.Edges |> List.filter (fun edge ->
                    not (replaced.Contains (key edge)) &&
                    not (forwarded.ContainsKey edge.Target && (match edge.Role with EdgeRole.EnvironmentCapture _ -> true | _ -> false))))
                  @ (nodes |> List.collect structuralIncidence) @ captures @ [signature] @ List.ofSeq formations
                  @ (forwarded |> Map.toList |> List.collect snd) }
    | NoMatch reason -> invalidOp ("Closure environment saturation failed: " + reason)

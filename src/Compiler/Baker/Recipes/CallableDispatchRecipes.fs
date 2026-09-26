// SPDX-License-Identifier: MIT
/// Construct a real source dispatcher closure. Its immutable tag is captured
/// at the original formation frontier; callback bodies remain deferred.
module Clef.Compiler.Baker.Recipes.CallableDispatchRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.CallableDispatch
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Baker.Recipes.Decomposition

type Expansion = { Structure: Result; Edges: Hyperedge list }

let materialize (ctx: Context) (graph: SemanticGraph) (plan: Plan) =
    let source = plan.Formal
    let state = SaturationState.create source.Range ctx.OriginalHOF ctx.ExpansionId source.Id graph.Platform
    let outcome, nodes = run state (saturation {
        do! emit source
        let! tag = patternBinding "__callable_alternative" Types.intType
        let capture = { Name = "__callable_alternative"; Type = Types.intType; IsMutable = false; SourceNodeId = Some tag }
        let parameters, resultType =
            match plan.Members.Head.Implementation.Kind with
            | SemanticKind.Lambda(parameters, body, _, _, _) ->
                parameters |> List.map (fun (name, ty, _) -> name, ty), graph.Nodes[body].Type
            | _ -> invalidOp "A dispatch member must retain its actual declared Lambda."
        let! dispatcher = closure parameters [capture] None (fun arguments captures ->
            let rec branch ordinal members = saturation {
                match members with
                | [] -> return! fail (XParsec.ErrorType.Message "A source dispatcher has no alternatives.")
                | memberValue :: rest ->
                    let name = match memberValue.Declaration.Kind with SemanticKind.Binding(name, _, _, _) -> name | _ -> invalidOp "Missing code declaration."
                    let! callee = varRef name (Some memberValue.Declaration.Id) source.Type
                    let! invocation = app callee arguments resultType
                    if rest.IsEmpty then return invocation else
                    let! literal = intLit ordinal
                    let! matches = eq captures.Head literal Types.intType
                    let! next = branch (ordinal + 1) rest
                    return! ifThenElse matches invocation next resultType
            }
            branch 0 plan.Members) resultType
        let factoryType = NativeType.TFun(Types.intType, source.Type)
        let! factory = createWithChildren
                           (SemanticKind.Lambda(["__callable_alternative", Types.intType, tag], dispatcher, [], None, LambdaContext.RegularClosure))
                           factoryType [tag; dispatcher]
        let name = sprintf "__callable_dispatch_%d" (NodeId.value source.Id)
        let! declaration = letBind name factory factoryType
        do! updateUserState (fun state ->
            let updated =
                state.EmittedNodes |> List.map (fun node ->
                    if node.Id = factory then { node with Parent = Some declaration }
                    elif node.Id = tag || node.Id = dispatcher then { node with Parent = Some factory }
                    else node)
            { state with EmittedNodes = updated })
        // Ordinary argument identities survive. Only the stateless callback
        // reference is represented by a factory that captures its proved tag.
        for actual in plan.Actuals do
            let! literal = intLit actual.Member
            let! callee = varRef name (Some declaration) factoryType
            let! formed = app callee [literal] source.Type
            match actual.Call.Kind with
            | SemanticKind.Application(functionValue, arguments) ->
                let arguments = arguments |> List.mapi (fun ordinal value -> if ordinal = actual.Position then formed else value)
                do! enrich actual.Call (SemanticKind.Application(functionValue, arguments)) actual.Call.Type
                           (functionValue :: arguments) actual.Call.EmissionStrategy false
            | _ -> return! fail (XParsec.ErrorType.Message "A source dispatch frontier is not an Application.")
        return source.Id
    })
    match outcome with
    | Matched root ->
        let key (edge: Hyperedge) = edge.Target, edge.Class, edge.Role, edge.Ordinal, edge.Sources
        let replaced = nodes |> List.choose (fun node -> graph.Nodes.TryFind node.Id)
                       |> List.collect structuralIncidence |> List.map key |> Set.ofList
        { Structure = mkResultNoShadow nodes root []
          Edges = (graph.Edges |> List.filter (fun edge -> not (replaced.Contains(key edge)))) @ (nodes |> List.collect structuralIncidence) }
    | NoMatch reason -> invalidOp ("Callable dispatch saturation failed: " + reason)

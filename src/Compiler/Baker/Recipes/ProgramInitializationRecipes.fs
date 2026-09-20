// SPDX-License-Identifier: MIT
/// Ordered program initialization is a Baker graph recipe. Declaration IDs,
/// lexical membership and source-entry callability survive the new activation.
module Clef.Compiler.Baker.Recipes.ProgramInitializationRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Recipes.Decomposition
module C = Clef.Compiler.Baker.Ingredients.Continuations
module P = Clef.Compiler.Baker.Ingredients.ProgramInitialization
module Facts = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization

type ExistingStartup = { Nodes: SemanticNode list; Binding: NodeId; Call: NodeId }
type Expansion = { Nodes: SemanticNode list; Edges: Hyperedge list; EntryBinding: NodeId }

let materialize (ctx: Context) (graph: SemanticGraph) (source: SemanticNode) selected unitActivations (existing: ExistingStartup option) =
    let parameters, sourceBody =
        match graph.Nodes[source.Children.Head].Kind with
        | SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure) -> parameters, body
        | _ -> invalidOp "Startup requires an ordinary captureless source entry."
    let sourceLambda = source.Children.Head
    let modules = graph.Nodes.Values |> Seq.choose (fun node ->
        match node.Kind with SemanticKind.ModuleDef(_, members) -> Some(node, members) | _ -> None) |> Seq.toList
    let owner id = modules |> List.choose (fun (node, members) -> if List.contains id members then Some node.Id else None)
                   |> function [moduleId] -> moduleId | _ -> invalidOp "A startup initializer requires one lexical module declaration."
    let state = SaturationState.create { source.Range with End = source.Range.Start } ctx.OriginalHOF ctx.ExpansionId source.Id graph.Platform
    let outcome, emitted = run state (saturation {
        let! initializers = selected |> C.collect (fun id -> saturation {
            let node = graph.Nodes[id]
            match node.Kind, node.Children with
            | SemanticKind.Binding _, [value] -> return id, id, value, owner id, node.Type <> Types.unitType
            | SemanticKind.Binding _, _ -> return invalidOp "A runtime initializer must have exactly one value."
            | _ ->
                let! discard = C.create (SemanticKind.Binding(sprintf "__program_effect_%d" (NodeId.value id), false, false, None)) node.Type [id]
                return id, discard, id, owner id, false
        })
        let! entryBinding, entryLambda, call, symbol, entryType, formals, tail =
            match existing with
            | Some startup -> saturation {
                let binding = startup.Nodes |> List.find (fun node -> node.Id = startup.Binding)
                let lambda = startup.Nodes |> List.find (fun node -> node.Id = binding.Children.Head)
                let formals, body = match lambda.Kind with SemanticKind.Lambda(ps, body, [], _, _) -> ps, body | _ -> invalidOp "Malformed platform startup Lambda."
                let symbol = match binding.Kind with SemanticKind.Binding(name, _, _, _) -> name | _ -> invalidOp "Malformed platform startup declaration."
                for node in startup.Nodes do do! emit node
                return binding.Id, lambda.Id, startup.Call, symbol, binding.Type, formals, [body]
              }
            | None -> saturation {
                let! formals, call = P.forwardedCall source parameters graph.Nodes[sourceBody].Type
                return NodeId.fresh(), NodeId.fresh(), call, "main", source.Type, formals, [call]
              }
        let ids = initializers |> List.map (fun (_, binding, _, _, _) -> binding)
        let resultType = match existing with Some _ -> Types.unitType | None -> graph.Nodes[sourceBody].Type
        let! spine = C.block (ids @ tail) resultType
        let! state = getUserState
        let lambda = mkNode state (SemanticKind.Lambda(formals, spine, [], Some symbol, LambdaContext.RegularClosure)) entryType
                            ((formals |> List.map (fun (_, _, formal) -> formal)) @ [spine])
        do! emit { lambda with Id = entryLambda; Parent = Some entryBinding; EmissionStrategy = EmissionStrategy.SeparateFunction 0 }
        let binding = mkNode state (SemanticKind.Binding("__clef_program_entry", false, false, Some DeclRoot.EntryPoint)) entryType [entryLambda]
        do! emit { binding with Id = entryBinding; EmissionStrategy = EmissionStrategy.SeparateFunction 0;
                               Metadata = binding.Metadata.Add(Facts.EntrySymbol, MetadataValue.String symbol) }
        let sourceKind = match source.Kind with SemanticKind.Binding(name, mutableValue, recursive, _) -> SemanticKind.Binding(name, mutableValue, recursive, None) | _ -> source.Kind
        do! emit { source with Kind = sourceKind }
        for moduleNode, members in modules do
            let replaced = members |> List.map (fun memberId ->
                initializers |> List.tryFind (fun (original, _, _, _, _) -> original = memberId)
                |> Option.map (fun (_, binding, _, _, _) -> binding) |> Option.defaultValue memberId)
            let name = match moduleNode.Kind with SemanticKind.ModuleDef(name, _) -> name | _ -> ""
            do! emit { moduleNode with Kind = SemanticKind.ModuleDef(name, replaced); Children = [] }
        return entryBinding, entryLambda, spine, call, initializers
    })
    match outcome with
    | NoMatch reason -> invalidOp ("Program initialization recipe failed: " + reason)
    | Matched(entry, activation, spine, call, initializers) ->
        let edge role ordinal sources target = { Sources = sources; Target = target; Class = EdgeClass.Provenance; Role = role; Ordinal = ordinal }
        let rows = initializers |> List.mapi (fun ordinal (_, binding, value, moduleId, isValue) ->
            edge EdgeRole.ProgramInitializer ordinal [moduleId; binding; value; activation] spine
            :: (if isValue then [edge EdgeRole.ProgramValueIntent ordinal [activation; spine; value] binding] else [])) |> List.concat
        let origins = initializers |> List.choose (fun (original, binding, _, moduleId, _) ->
            if original = binding then None else Some(edge EdgeRole.EnrichedWith 0 [moduleId; original] binding))
        let units = unitActivations |> List.mapi (fun ordinal (moduleId, premises) ->
            edge EdgeRole.ProgramUnitActivation ordinal (List.distinct (activation :: source.Id :: premises)) moduleId)
        { Nodes = emitted; EntryBinding = entry
          Edges = edge EdgeRole.ProgramInitialization 0 [entry; source.Id; sourceLambda; sourceBody; activation] spine
                  :: edge EdgeRole.ProgramEntryCall 0 [entry; source.Id; sourceLambda; activation] call :: rows @ origins @ units }

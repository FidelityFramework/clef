// SPDX-License-Identifier: MIT
/// Lazy source algorithms are elaborated through the normal recipe fold.
/// This source contract precedes typed layout and residence settlement and is
/// independently executable in component tests.
module Clef.Compiler.Nanopass.LazyElaboration

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Nanopass.Recipe
module Lazy = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues
module Recipes = Clef.Compiler.Baker.Recipes.LazyRecipes

let private fold name (source: SemanticNode) (expanded: Recipes.Expansion) graph =
    let create (_: SemanticNode) _ =
        RecipeCreated { OriginalNodeId = source.Id; NewNodes = expanded.Structure.NewNodes
                        ReplacementRootId = source.Id; ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = name }
    let folded = FoldIn.foldIn (FanOut.fanOut name (fun node -> node.Id = source.Id) create graph) graph
    { folded with Edges = expanded.Edges }

let rec formations (graph: SemanticGraph) =
    match Lazy.plans graph |> List.tryHead with
    | None -> graph
    | Some plan ->
        let name = "Lazy.formation"
        let context = mkContext plan.Source.Range plan.Source.Type graph.Platform name plan.Source.Id
        let expanded = Recipes.formation context graph plan
        formations (fold name plan.Source expanded graph)

let rec forces (graph: SemanticGraph) =
    let ownerOf = Lazy.tryOwner graph
    let next = graph.Nodes.Values |> Seq.tryPick (fun node ->
        match node.Kind with
        | SemanticKind.LazyForce operand when node.IsReachable ->
            ownerOf operand |> Option.bind (Lazy.instance graph) |> Option.map (fun contract -> node, contract)
        | _ -> None)
    match next with
    | None -> graph
    | Some(source, contract) ->
        let name = "Lazy.force"
        let context = mkContext source.Range source.Type graph.Platform name source.Id
        let expanded = Recipes.force context graph source contract
        forces (fold name source expanded graph)

let normalize (graph: SemanticGraph) =
    let present = graph.Nodes.Values |> Seq.exists (fun node ->
        node.IsReachable && match node.Kind with SemanticKind.LazyExpr _ | SemanticKind.LazyForce _ -> true | _ -> false)
    if not present then graph else
    let rewritten = graph |> formations |> forces
    // Replaced Set targets are retained source nodes, but no longer executable
    // operands of LazyWrite. Refresh liveness at this owning rewrite boundary,
    // rather than depending on an unrelated later string/sequence recipe.
    // Open library graphs have no executable roots to authorize that cut.
    if rewritten.DeclarationRoots.IsEmpty then rewritten
    else Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable rewritten

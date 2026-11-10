// SPDX-License-Identifier: MIT
/// Retire this boundary owner's previous firing, then fold its replacement.
module Clef.Compiler.Nanopass.BoundarySettlement

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.Baker.Ingredients.Obligations
module Ingredients = Clef.Compiler.Baker.Ingredients.Boundaries
module Recipes = Clef.Compiler.Baker.Recipes.BoundaryRecipes

let private retract graph =
    let retired = graph.Nodes |> Map.fold (fun ids id node -> if Ingredients.ownedNode node then Set.add id ids else ids) Set.empty
    let retiredNames =
        retired |> Seq.choose (fun id ->
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.Obligation info } -> Some info.Id
            | _ -> None) |> Set.ofSeq
    let graph = ObligationElaboration.retireAnchors retired graph
    let nodes = graph.Nodes |> Map.filter (fun id _ -> not (retired.Contains id))
    let edges = graph.Edges |> List.filter (fun edge ->
        let boundary = match edge.Role with EdgeRole.BoundaryDeclaration _ -> false | _ -> edge.Class = EdgeClass.Boundary
        not boundary && not (retired.Contains edge.Target) && not (edge.Sources |> List.exists retired.Contains))
    let retracted = { graph with Nodes = nodes; Edges = edges } |> SemanticGraph.invalidateWitness
    if retiredNames.IsEmpty || retracted.Codata.Value.CallableAggregateDependencies.IsEmpty then
        retracted, false
    else
        let facts = retracted.Codata.Value
        let mutable changed = false
        let updatedDeps =
            facts.CallableAggregateDependencies
            |> Map.map (fun _ account ->
                let sources =
                    account.Sources
                    |> List.map (fun source ->
                        match retracted.Nodes.TryFind source.Node with
                        | Some { Metadata = meta } ->
                            let currentAnchors =
                                match meta.TryFind ObligationMetadata.Anchors with
                                | Some(MetadataValue.StringList names) -> names
                                | _ -> []
                            let stripped = source.Anchors |> List.filter (fun name -> not (retiredNames.Contains name) || List.contains name currentAnchors)
                            if stripped <> source.Anchors then
                                changed <- true
                                { source with Anchors = stripped }
                            else source
                        | None -> source)
                let claims =
                    account.Claims |> List.filter (fun (id, _) -> not (retired.Contains id))
                if claims.Length <> account.Claims.Length then changed <- true
                { account with Sources = sources; Claims = claims })
        if not changed then retracted, false
        else
            { retracted with Codata = lazy { facts with CallableAggregateDependencies = updatedDeps } }
            |> SemanticGraph.invalidateWitness,
            true

let elaborate = Recipes.elaborate
let foldIn (enrichment: Enrichment) graph =
    ObligationElaboration.foldIn enrichment graph

let private normalizeCore graph =
    let retained = Ingredients.RetainedBoundaryNodes.capture graph
    let retracted, hadBoundaryAggregateAnchors = retract graph
    let working = BoundaryDeclarations.normalize retracted
    let folded = foldIn (Recipes.elaborateWithRetained retained working) working
    if hadBoundaryAggregateAnchors then
        fst (CallableAggregateSettlement.renewAccounts folded)
    else
        folded

let normalize graph =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> normalizeCore graph)

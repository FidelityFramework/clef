// SPDX-License-Identifier: MIT
/// One forward source fold for callable component rows and their data placement.
/// Scalar/range owners retain their proofs under the checked representation
/// renewal. Source diagnostics remain tied to demanded occurrences.
module Clef.Compiler.Nanopass.CallableAggregateSettlement

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module Recipe = Clef.Compiler.Baker.Recipes.CallableAggregateRecipes
module Representation = Clef.Compiler.Baker.Recipes.NumericRepresentationRecipes
module Graph = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph

let private refusal site reason : Recipe.Residual =
    { Occurrence = site; Code = "CCS8414"; Reason = reason }

let private current (graph: SemanticGraph) =
    let facts = graph.Codata.Value
    Recipe.settle (Origins.resolveCallableBranches graph)
        { Carriers = facts.CallableCarriers; Contracts = facts.CallableContracts
          Flows = facts.CallableFlows; Joins = facts.CallableJoins
          PreviousSlots = facts.CallableAggregateSlots } graph

let normalize (graph: SemanticGraph) =
    let rows = current graph
    let facts = graph.Codata.Value
    let codata =
        { facts with CallableAggregateSlots = rows.Slots; CallableAggregateValues = rows.Values
                     CallableAggregateDependencies = rows.Dependencies }
    let authored =
        { graph with Codata = lazy codata }
        |> Graph.invalidateWitness
    match Representation.renewAggregateStorage authored with
    | Ok settled -> settled, rows.Residuals
    | Error failures ->
        let residuals = failures |> List.choose (fun failure ->
            failure.Occurrence |> Option.orElseWith (fun () -> rows.Values |> Map.keys |> Seq.tryHead)
            |> Option.map (fun site -> refusal site failure.Reason))
        authored, rows.Residuals @ residuals

/// Later obligation owners can add proof annotations without changing the
/// callable formation. Recheck the semantic rows against the current graph
/// before minting its final dependency account. A changed row is a refusal,
/// never a repaired witness/publication receipt.
let renewAccounts (graph: SemanticGraph) =
    let facts = graph.Codata.Value
    let expected = current graph
    let expectedSites = expected.Values |> Map.keys |> Set.ofSeq
    let accountSites = expected.Dependencies |> Map.keys |> Set.ofSeq
    let missingAccounts = Set.difference expectedSites accountSites
    if expected.Slots <> facts.CallableAggregateSlots || expected.Values <> facts.CallableAggregateValues then
        let sites = Set.union (facts.CallableAggregateValues |> Map.keys |> Set.ofSeq)
                              expectedSites
        let failures = sites |> Set.toList |> List.map (fun site ->
            refusal site "Callable aggregate formation or contract changed after placement; its owning source fold must settle it again.")
        Graph.invalidateWitness graph, expected.Residuals @ failures
    elif not (Set.isEmpty missingAccounts) || not (Set.isSubset accountSites expectedSites) then
        let sites = Set.union missingAccounts (Set.difference accountSites expectedSites)
        let failures = sites |> Set.toList |> List.map (fun site ->
            refusal site "Every callable aggregate occurrence requires its own current dependency account; incomplete accounts cannot renew placement.")
        Graph.invalidateWitness graph, expected.Residuals @ failures
    elif expected.Dependencies = facts.CallableAggregateDependencies then
        graph, expected.Residuals
    else
        let refreshed =
            { graph with Codata = lazy { facts with CallableAggregateDependencies = expected.Dependencies } }
            |> Graph.invalidateWitness
        refreshed, expected.Residuals

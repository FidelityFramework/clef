// SPDX-License-Identifier: MIT
/// One forward source fold for callable component rows and their data placement.
/// Scalar/range owners retain their proofs under the checked representation
/// renewal. Source diagnostics remain tied to demanded occurrences.
module Clef.Compiler.Nanopass.CallableAggregateSettlement

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module Recipe = Clef.Compiler.Baker.Recipes.CallableAggregateRecipes
module Representation = Clef.Compiler.Baker.Recipes.NumericRepresentationRecipes
module Contract = Clef.Compiler.Baker.Recipes.CallableContractRecipes
module Graph = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph

let private refusal site reason : Recipe.Residual =
    { Occurrence = site; Code = "CCS8414"; Reason = reason }

let private inputs (facts: Codata) : Recipe.Inputs =
    { Carriers = facts.CallableCarriers; Contracts = facts.CallableContracts
      Flows = facts.CallableFlows; Joins = facts.CallableJoins
      PreviousSlots = facts.CallableAggregateSlots }

let private current (graph: SemanticGraph) =
    Recipe.settle (Origins.resolveCallableBranches graph) (inputs graph.Codata.Value) graph

let private rowsOf (facts: Codata) : Recipe.Settlement =
    { Slots = facts.CallableAggregateSlots; Values = facts.CallableAggregateValues
      Dependencies = facts.CallableAggregateDependencies; Residuals = [] }

let private install (rows: Recipe.Settlement) (graph: SemanticGraph) =
    let facts = graph.Codata.Value
    if rows.Slots = facts.CallableAggregateSlots && rows.Values = facts.CallableAggregateValues &&
       rows.Dependencies = facts.CallableAggregateDependencies then graph else
    let codata =
        { facts with CallableAggregateSlots = rows.Slots; CallableAggregateValues = rows.Values
                     CallableAggregateDependencies = rows.Dependencies }
    { graph with Codata = lazy codata } |> Graph.invalidateWitness

let private overlay previous replacements =
    replacements |> Map.fold (fun table key value ->
        if (table |> Map.tryFind key) = Some value then table else table |> Map.add key value) previous

/// All slots of an aggregate type advance together. A receiving dependency is
/// induced only by a stored carrier's physical parameters/result, not by its
/// containing aggregate occurrence. This is a finite graph inventory, not a
/// retry of origin analysis or the compiler pipeline.
let private dependencies (types: Set<TypeIdentity>) (graph: SemanticGraph) (work: Recipe.WorkGroup list) =
    let rec included identity =
        let own = if types.Contains identity then Set.singleton identity else Set.empty
        let children =
            match identity with
            | TypeIdentity.Application(_, arguments) | TypeIdentity.Tuple(_, arguments) -> arguments
            | TypeIdentity.AnonymousRecord(_, fields) -> List.map snd fields
            | TypeIdentity.Union(_, cases) -> cases |> List.collect (fun (_, _, fields) -> List.map snd fields)
            | TypeIdentity.Function(argument, result) | TypeIdentity.Map(argument, result) -> [argument; result]
            | TypeIdentity.Forall(_, value) | TypeIdentity.Byref(_, value) | TypeIdentity.NativePointer value
            | TypeIdentity.Lazy value | TypeIdentity.Sequence value | TypeIdentity.Enumerator value
            | TypeIdentity.List value | TypeIdentity.Set value -> [value]
            | _ -> []
        children |> List.fold (fun found child -> Set.union found (included child)) own
    let carriers = graph.Codata.Value.CallableCarriers
    types |> Seq.map (fun aggregateType ->
        let required =
            work |> List.filter (fun group -> group.AggregateType = aggregateType)
            |> List.collect (fun group -> Recipe.receivingTypes graph carriers group |> Set.toList)
            |> List.fold (fun found identity -> Set.union found (included identity)) Set.empty
        aggregateType, required) |> Map.ofSeq

let private mergeFrontier (types: Set<TypeIdentity>) (selected: Recipe.Settlement) (held: Recipe.Settlement) =
    let removedSlots = held.Slots |> Map.toSeq |> Seq.choose (fun (identity, slot) ->
        if types.Contains slot.AggregateType then Some identity else None) |> Set.ofSeq
    let retainedSlots = held.Slots |> Map.filter (fun identity _ -> not (removedSlots.Contains identity))
    let retainedValues =
        held.Values |> Map.map (fun _ values -> values |> List.filter (fun value -> not (removedSlots.Contains value.Slot)))
        |> Map.filter (fun _ values -> not values.IsEmpty)
    let values = selected.Values |> Map.fold (fun values site rows ->
        let combined = (values |> Map.tryFind site |> Option.defaultValue []) @ rows |> List.sortBy _.Slot
        values |> Map.add site combined) retainedValues
    let slots = overlay retainedSlots selected.Slots
    let values = if values = held.Values then held.Values else values
    let slots = if slots = held.Slots then held.Slots else slots
    { Slots = slots; Values = values
      Dependencies = held.Dependencies |> Map.filter (fun site _ -> values.ContainsKey site)
      Residuals = selected.Residuals } : Recipe.Settlement

let normalize (graph: SemanticGraph) =
    let work = Recipe.prepareWork (Origins.resolveCallableBranches graph) graph
    let types =
        Set.union (work |> List.map _.AggregateType |> Set.ofList)
                  (graph.Codata.Value.CallableAggregateSlots.Values |> Seq.map _.AggregateType |> Set.ofSeq)
    let required = dependencies types graph work
    let mutable remaining = types
    let mutable settled = graph
    let residuals = ResizeArray<Recipe.Residual>()
    // A frontier consumes at least one remaining type. Its slots are folded
    // once and placement is called once per dependency depth, never per slot.
    while not remaining.IsEmpty do
        let ready = remaining |> Set.filter (fun key -> Set.intersect required[key] remaining |> Set.isEmpty)
        if ready.IsEmpty then
            let queued = work |> List.filter (fun group -> remaining.Contains group.AggregateType)
            for group in queued do
                for site, _, _ in group.Rows do
                    residuals.Add(refusal site "Callable aggregate receiving types form a cycle; an explicit source-owned recursive receiving convention is required.")
            let empty : Recipe.Settlement = { Slots = Map.empty; Values = Map.empty; Dependencies = Map.empty; Residuals = [] }
            settled <- install (mergeFrontier remaining empty (rowsOf settled.Codata.Value)) settled
            remaining <- Set.empty
        else
            let selected = work |> List.filter (fun group -> ready.Contains group.AggregateType)
            let facts = settled.Codata.Value
            let authored = Recipe.settleWork selected (inputs facts) settled
            let merged = mergeFrontier ready authored (rowsOf facts)
            let accountSites =
                merged.Values |> Map.toSeq |> Seq.choose (fun (site, rows) ->
                    if rows |> List.exists (fun row -> ready.Contains merged.Slots[row.Slot].AggregateType) then Some site else None)
                |> Set.ofSeq
            let accounted = Recipe.authorAccounts accountSites (inputs facts) settled merged
            residuals.AddRange accounted.Residuals
            settled <- install accounted settled
            match Representation.renewAggregateTypes ready settled with
            | Error failures ->
                let fallback = selected |> List.collect _.Rows |> List.tryHead |> Option.map (fun (site, _, _) -> site)
                for failure in failures do
                    match failure.Occurrence |> Option.orElse fallback with
                    | Some site -> residuals.Add(refusal site failure.Reason)
                    | None -> ()
            | Ok(placed, changes) ->
                let facts = placed.Codata.Value
                let contracts, carriers = Contract.renewForSites placed facts.EnvironmentLayouts changes facts.CallableContracts facts.CallableCarriers
                let storage = Clef.Compiler.Baker.Ingredients.CallableContracts.refreshStorage carriers facts.MutableCallableStorage
                settled <-
                    if contracts = facts.CallableContracts && carriers = facts.CallableCarriers && storage = facts.MutableCallableStorage then placed
                    else
                        let codata = { facts with CallableContracts = contracts; CallableCarriers = carriers; MutableCallableStorage = storage }
                        { placed with Codata = lazy codata } |> Graph.invalidateWitness
            remaining <- Set.difference remaining ready
    // No intermediate queued account can escape the owner. Check complete
    // final merged tables after every receiving convention has advanced.
    let facts = settled.Codata.Value
    let rows = rowsOf facts
    let final = Recipe.authorAccounts (rows.Values |> Map.keys |> Set.ofSeq) (inputs facts) settled rows
    residuals.AddRange final.Residuals
    install final settled, residuals |> Seq.distinct |> Seq.toList

/// Later obligation owners can add proof annotations without changing the
/// callable formation. Recheck the semantic rows against the current graph
/// before minting its final dependency account. A changed row is a refusal,
/// never a repaired witness/publication receipt.
let renewAccounts (graph: SemanticGraph) =
    let facts = graph.Codata.Value
    let expected = current graph
    let expectedSites = expected.Values |> Map.keys |> Set.ofSeq
    let authoredSites = expected.Dependencies |> Map.keys |> Set.ofSeq
    let heldSites = facts.CallableAggregateDependencies |> Map.keys |> Set.ofSeq
    let missingAccounts = Set.union (Set.difference expectedSites authoredSites) (Set.difference expectedSites heldSites)
    let extraAccounts = Set.difference heldSites expectedSites
    if expected.Slots <> facts.CallableAggregateSlots || expected.Values <> facts.CallableAggregateValues then
        let sites = Set.union (facts.CallableAggregateValues |> Map.keys |> Set.ofSeq) expectedSites
        let failures = sites |> Set.toList |> List.map (fun site ->
            refusal site "Callable aggregate formation or contract changed after placement; its owning source fold must settle it again.")
        Graph.invalidateWitness graph, expected.Residuals @ failures
    elif not missingAccounts.IsEmpty || not extraAccounts.IsEmpty then
        let sites = Set.union missingAccounts extraAccounts
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

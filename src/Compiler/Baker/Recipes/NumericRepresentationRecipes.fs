// SPDX-License-Identifier: MIT
/// Renew aggregate representation rows after their source component fold.
/// Existing scalar selections and finite-cell/sequence proof accounts are
/// checked before the update and retained byte-for-byte. No range pass is run.
module Clef.Compiler.Baker.Recipes.NumericRepresentationRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Numeric = Clef.Compiler.Baker.Ingredients.NumericValues
module Representations = Clef.Compiler.Baker.Ingredients.ValueRepresentations
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Publication = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication
module Graph = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph

let renewAggregateStorage (graph: SemanticGraph) =
    let affected = graph.Codata.Value.CallableAggregateSlots.Values |> Seq.map _.AggregateType |> Set.ofSeq
    if affected.IsEmpty then Ok(graph, Set.empty) else
    // The old account is still in the graph. Validate it while its layout is
    // current, before the owning component step changes any representation.
    Publication.project graph |> Result.bind (fun _ ->
        let domains = graph.Edges |> List.choose (fun edge ->
            match edge.Role with EdgeRole.NumericDomain domain -> Some(edge, domain) | _ -> None)
        match domains with
        | [held, domain] ->
            let placed = Placement.settle graph.Platform graph
            let rec depends identity =
                affected.Contains identity ||
                match identity with
                | TypeIdentity.Application(_, arguments) | TypeIdentity.Tuple(_, arguments) -> List.exists depends arguments
                | TypeIdentity.AnonymousRecord(_, fields) -> fields |> List.exists (snd >> depends)
                | TypeIdentity.Union(_, cases) -> cases |> List.exists (fun (_, _, fields) -> List.exists (snd >> depends) fields)
                | TypeIdentity.Function(argument, result) | TypeIdentity.Map(argument, result) -> depends argument || depends result
                | TypeIdentity.Forall(_, value) | TypeIdentity.Byref(_, value) | TypeIdentity.NativePointer value
                | TypeIdentity.Lazy value | TypeIdentity.Sequence value | TypeIdentity.Enumerator value
                | TypeIdentity.List value | TypeIdentity.Set value -> depends value
                | _ -> false
            let keys left right = Set.union (left |> Map.keys |> Set.ofSeq) (right |> Map.keys |> Set.ofSeq)
            let layoutChanges = keys domain.Layouts placed.Layouts.Value |> Set.filter (fun key ->
                domain.Layouts.TryFind key <> placed.Layouts.Value.TryFind key)
            let occurrences, types = Representations.settle placed domain.Values domain.Elements domain.ElementTypes domain.DeclaredScalars
            let occurrenceChanges = keys domain.OccurrenceRepresentations occurrences |> Set.filter (fun id ->
                domain.OccurrenceRepresentations.TryFind id <> occurrences.TryFind id)
            let typeChanges = keys domain.TypeRepresentations types |> Set.filter (fun key ->
                domain.TypeRepresentations.TryFind key <> types.TryFind key)
            let changesAdmitted =
                (layoutChanges |> Set.forall depends) && (typeChanges |> Set.forall depends) &&
                (occurrenceChanges |> Set.forall (fun id -> domain.SourceTypes.TryFind id |> Option.exists depends))
            let scalarUnchanged = domain.Values |> List.forall (fun carrier ->
                occurrences.TryFind carrier.Site = domain.OccurrenceRepresentations.TryFind carrier.Site)
            if not changesAdmitted || not scalarUnchanged || Numeric.premises placed <> domain.Premises then
                Error [{ Occurrence = Some held.Target; Participants = occurrenceChanges
                         Reason = "Callable aggregate placement changed a non-aggregate source premise or scalar representation; its owning recipe must settle that change." }]
            else
                let renewed = { domain with Layouts = placed.Layouts.Value
                                            OccurrenceRepresentations = occurrences; TypeRepresentations = types }
                let edges = placed.Edges |> List.map (fun edge ->
                    match edge.Role with
                    | EdgeRole.NumericDomain _ -> Numeric.domainRow held.Target renewed
                    | _ -> edge)
                let updated =
                    { placed with Edges = edges }
                    |> Graph.invalidateWitness
                // The ordinary numeric reader remains the acceptance rule.
                Publication.project updated |> Result.map (fun _ -> updated, occurrenceChanges)
        | _ -> Error [{ Occurrence = None; Participants = Set.empty
                        Reason = "Aggregate representation renewal requires one current numeric account." }])

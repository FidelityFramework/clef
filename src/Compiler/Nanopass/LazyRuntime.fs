// SPDX-License-Identifier: MIT
/// Settle explicit lazy storage after its source algorithm and complete uses.
/// Placement supplies exact typed fields; residence supplies each allocation's
/// authority. Neither relation alone admits a native lazy instance.
module Clef.Compiler.Nanopass.LazyRuntime

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Ingredients.Obligations
module Lazy = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues
module Residence = Clef.Compiler.PSGSaturation.SemanticGraph.LazyResidence
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Proof = Clef.Compiler.Baker.Recipes.ContinuationObligationRecipes

type Settlement = {
    Layouts: Map<NodeId, LazyLayout>
    Origins: Map<NodeId, NodeId>
    Destinations: Map<NodeId, NodeId>
    Residences: Map<NodeId, EscapeKind>
    Diagnostics: Diagnostic list
}

let private slots (graph: SemanticGraph) (fields: Placement.ContinuationField list) : ContinuationSlot list =
    fields |> List.map (fun field ->
        { Source = field.Source; ValueType = graph.Nodes[field.Source].Type
          Field = field.Field; Holds = field.Holds
          IsCapture = field.Role = Placement.ContinuationRole.Capture })

let private participants (contract: Lazy.Instance) (residence: Residence.Reading) captureUses =
    [contract.Formation; contract.Thunk; contract.ThunkBody; contract.Environment; contract.Formal
     contract.Computed; contract.Cached; contract.InitialComputed]
    @ (contract.Captured |> List.collect (fun (slot, value, _) -> [slot; value]))
    @ (residence.Evidence |> List.filter (fun edge -> edge.Target = contract.Formation) |> List.collect _.Sources)
    @ (captureUses |> Map.tryFind contract.Formation |> Option.defaultValue [])
    |> List.distinct

let private admittedOwner (graph: SemanticGraph) (residence: Residence.Reading) owner =
    let allocations =
        graph.Nodes.Values
        |> Seq.choose (fun node ->
            if not node.IsReachable then None else
            match node.Kind with
            | SemanticKind.LazyEnvironment(actual, _) when actual = owner && not (residence.Destinations.ContainsKey node.Id) -> Some node.Id
            | SemanticKind.LazyAllocate actual when actual = owner -> Some node.Id
            | _ -> None)
        |> Seq.toList
    not allocations.IsEmpty && allocations |> List.forall residence.Sites.ContainsKey

/// Recheck a carried layout against the current typed instance, placement,
/// complete-use proof and resident obligation. A stale Codata entry is never
/// permission to retain old offsets, a cache initializer or another instance.
let validate (graph: SemanticGraph) (layout: LazyLayout) =
    let memoization = Lazy.settle graph
    let residence = Residence.analyze graph
    match memoization.Instances.TryFind layout.Owner with
    | Some contract when memoization.Residuals.IsEmpty && admittedOwner graph residence layout.Owner ->
        match Placement.placeLazyEnvironment graph layout.Owner with
        | Ok (SettledLayout.Record(_, Some bytes, Some alignment), fields) ->
            let actualSlots = slots graph fields
            let expected = participants contract residence memoization.CaptureUses @ layout.Obligations |> List.distinct
            let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyLayout && edge.Target = layout.Owner)
            let resident =
                match rows with
                | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = sources }] -> sources = expected
                | _ -> false
            let obligation =
                match layout.Obligations with
                | [id] ->
                    match graph.Nodes.TryFind id with
                    | Some { Kind = SemanticKind.Obligation info } ->
                        match info.Body with
                        | ObligationBody.ContinuationLayout(actual, extent, align) ->
                            actual = (actualSlots |> List.map (fun slot -> slot.Field.Offset.Value, slot.Field.Size.Value, slot.Field.Align.Value)) &&
                            extent = bytes && align = alignment
                        | _ -> false
                    | _ -> false
                | _ -> false
            resident && obligation && layout.Thunk = contract.Thunk && layout.Formal = contract.Formal &&
            layout.Computed = contract.Computed && layout.Cached = contract.Cached &&
            layout.Slots = actualSlots && layout.Bytes = bytes && layout.Alignment = alignment
        | _ -> false
    | _ -> false

/// Retire only this settlement's obligations and any joints which depend on
/// them. Source formation/destination relations remain available for another
/// settlement when their premises become admissible again.
let private removeOwnedProofs retainedObligations (graph: SemanticGraph) =
    let retiredObligations =
        graph.Edges
        |> List.filter (fun edge -> edge.Role = EdgeRole.LazyLayout)
        |> List.collect (fun edge ->
            edge.Sources |> List.choose (fun id ->
                match graph.Nodes.TryFind id with
                | Some { Kind = SemanticKind.Obligation info }
                    when info.Id = sprintf "lazy_%d_environment" (NodeId.value edge.Target) && not (Set.contains id retainedObligations) -> Some id
                | _ -> None))
        |> Set.ofList
    if retiredObligations.IsEmpty && not (graph.Edges |> List.exists (fun edge -> edge.Role = EdgeRole.LazyLayout || edge.Role = EdgeRole.LazyResidence)) then graph
    else
        { graph with
            Nodes = graph.Nodes |> Map.filter (fun id _ -> not (retiredObligations.Contains id))
            Edges = graph.Edges |> List.filter (fun edge ->
                edge.Role <> EdgeRole.LazyLayout && edge.Role <> EdgeRole.LazyResidence &&
                not (retiredObligations.Contains edge.Target) &&
                not (edge.Sources |> List.exists retiredObligations.Contains)) }

let private retract (graph: SemanticGraph) =
    let previousSites =
        graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyResidence)
        |> List.choose (fun edge -> List.tryHead edge.Sources) |> Set.ofList
    let clean = removeOwnedProofs Set.empty graph
    // Keep this lazy: a graph without explicit Lazy values must not force all
    // unrelated Codata merely to establish that there is no Lazy authority.
    let codata = lazy (
        let previous = graph.Codata.Value
        let sites = Set.union previousSites (previous.LazyOrigins |> Map.keys |> Set.ofSeq)
        { previous with LazyLayouts = Map.empty; LazyOrigins = Map.empty; LazyDestinations = Map.empty
                        Escapes = previous.Escapes |> Map.filter (fun site _ -> not (sites.Contains site)) })
    { clean with Codata = codata }

let settleWhenSourceAdmitted admitted (graph: SemanticGraph) =
    let empty = { Layouts = Map.empty; Origins = Map.empty; Destinations = Map.empty; Residences = Map.empty; Diagnostics = [] }
    let present =
        graph.Nodes.Values |> Seq.exists (fun node ->
            if not node.IsReachable then false else
            match node.Kind with
            | SemanticKind.LazyExpr _ | SemanticKind.LazyForce _ | SemanticKind.LazyValue _
            | SemanticKind.LazyEnvironment _ | SemanticKind.LazyAllocate _ -> true
            | _ -> false)
    if not admitted || graph.Platform.IsNone || not present then retract graph, empty else
    let memoization = Lazy.settle graph
    let residence = Residence.analyze graph
    let residual site related reason =
        { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8405"
          Message = "Lazy instance requires further settlement: " + reason
          Range = graph.Nodes[site].Range; RelatedNodes = site :: related
          Reachability = ReachabilityContext.Unknown }
    let errors =
        (memoization.Residuals |> List.map (fun pending -> residual pending.Site pending.Participants pending.Reason))
        @ (residence.Residuals |> List.map (fun pending -> residual pending.Site pending.Participants pending.Reason))
    let placed =
        memoization.Instances.Values
        |> Seq.choose (fun contract ->
            if not memoization.Residuals.IsEmpty || not (admittedOwner graph residence contract.Formation) then None else
            match Placement.placeLazyEnvironment graph contract.Formation with
            | Ok (SettledLayout.Record(_, Some bytes, Some alignment), fields) ->
                let fields = slots graph fields
                let layout obligations : LazyLayout =
                    { Owner = contract.Formation; Thunk = contract.Thunk; Formal = contract.Formal
                      Computed = contract.Computed; Cached = contract.Cached; Slots = fields
                      Bytes = bytes; Alignment = alignment; Obligations = obligations }
                let existing = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyLayout && edge.Target = contract.Formation)
                let oldObligations =
                    existing |> List.collect _.Sources |> List.choose (fun id ->
                        match graph.Nodes.TryFind id with
                        | Some { Kind = SemanticKind.Obligation info }
                            when info.Id = sprintf "lazy_%d_environment" (NodeId.value contract.Formation) -> Some id
                        | _ -> None) |> List.distinct
                let previous = layout oldObligations
                if validate graph previous then
                    Some(Ok(previous, { Enrichment.empty with NewEdges = existing }))
                else
                    let proof =
                        Proof.layout (NodeId.value contract.Formation) (sprintf "lazy_%d_environment" (NodeId.value contract.Formation))
                            graph.Nodes[contract.Formation]
                            (fields |> List.map (fun slot -> slot.Source, slot.Field.Offset.Value, slot.Field.Size.Value, slot.Field.Align.Value)) bytes alignment
                    let obligations = proof.NewNodes |> List.map _.Id
                    let dependencies = participants contract residence memoization.CaptureUses
                    let evidence = { Class = EdgeClass.Provenance; Role = EdgeRole.LazyLayout
                                     Sources = List.distinct (dependencies @ obligations); Target = contract.Formation; Ordinal = 0 }
                    let jointEdges =
                        proof.NewEdges |> List.map (fun edge ->
                            { edge with Sources = List.distinct (edge.Sources @ dependencies) })
                    let proof = { proof with NewEdges = evidence :: jointEdges }
                    Some (Ok(layout obligations, proof))
            | Result.Error reason -> Some (Result.Error(residual contract.Formation [] (sprintf "%A" reason)))
            | _ -> Some (Result.Error(residual contract.Formation [] "The declared platform did not settle an exact lazy extent and alignment.")))
        |> Seq.toList
    let layouts = placed |> List.choose (function Ok(layout, _) -> Some(layout.Owner, layout) | _ -> None) |> Map.ofList
    let retainedObligations = layouts.Values |> Seq.collect _.Obligations |> Set.ofSeq
    let proof = placed |> List.choose (function Ok(_, proof) -> Some proof | _ -> None) |> Enrichment.concat
    let clean = removeOwnedProofs retainedObligations graph
    let enriched = ObligationElaboration.foldIn { proof with NewEdges = proof.NewEdges @ residence.Evidence } clean
    let ownerOf = Lazy.tryOwner enriched
    let origins = enriched.Nodes |> Map.toList |> List.choose (fun (id, node) ->
        if not node.IsReachable then None else
        ownerOf id |> Option.filter layouts.ContainsKey |> Option.map (fun owner -> id, owner)) |> Map.ofList
    let reading =
        { Layouts = layouts; Origins = origins; Destinations = residence.Destinations; Residences = residence.Sites
          Diagnostics = errors @ (placed |> List.choose (function Result.Error diagnostic -> Some diagnostic | _ -> None)) }
    let previousSites = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyResidence) |> List.choose (fun edge -> List.tryHead edge.Sources) |> Set.ofList
    let codata = lazy (
        let previous = enriched.Codata.Value
        let retained = previous.Escapes |> Map.filter (fun site _ -> not (previousSites.Contains site))
        let escapes = residence.Sites |> Map.fold (fun facts site kind -> Map.add site kind facts) retained
        { previous with LazyLayouts = layouts; LazyOrigins = origins; LazyDestinations = residence.Destinations; Escapes = escapes })
    let graph = { enriched with Codata = codata }
    graph, reading

let settle graph = settleWhenSourceAdmitted true graph

let private programReadings = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, Map<NodeId, NodeId * NodeId>>()

/// The actual program-owned instance behind an immutable binding. A schema is
/// insufficient: a direct formation or exact caller destination must identify
/// one allocation, and current startup/storage authority must cover that site.
/// Consumers may name the already initialized global; they must not recreate
/// the formation, evaluate the initializer or substitute another factory call.
let programInstance (graph: SemanticGraph) binding =
    let read (graph: SemanticGraph) =
        let codata = graph.Codata.Value
        let residence = Residence.analyze graph
        let layouts = codata.LazyLayouts |> Map.filter (fun _ layout -> validate graph layout)
        let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
        let rec actual seen id =
            if Set.contains id seen then None else
            let seen = Set.add id seen
            match nodes.TryFind id with
            | Some { Type = NativeType.TLazy _; Kind = SemanticKind.LazyValue(_, environment) } when layouts.ContainsKey id ->
                if residence.Destinations.ContainsKey environment then None else Some(id, environment)
            | Some { Type = NativeType.TLazy _; Kind = SemanticKind.Application _ } ->
                let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyResultCall && edge.Target = id)
                match rows with
                | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [_; constructor; formal; allocation; _] }]
                    when residence.Destinations.TryFind constructor = Some formal ->
                    match nodes.TryFind allocation with
                    | Some { Kind = SemanticKind.LazyAllocate owner } when layouts.ContainsKey owner -> Some(owner, allocation)
                    | _ -> None
                | _ -> None
            | Some { Type = NativeType.TLazy _; Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> actual seen source
            | Some { Type = NativeType.TLazy _; Kind = SemanticKind.Binding(_, false, _, _); Children = [source] } -> actual seen source
            | Some { Type = NativeType.TLazy _; Kind = SemanticKind.EagerExpr source }
                when Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand.operand graph id = Some source -> actual seen source
            | Some { Type = NativeType.TLazy _; Kind = SemanticKind.Sequential values } -> List.tryLast values |> Option.bind (actual seen)
            | Some { Type = NativeType.TLazy _; Kind = SemanticKind.IfThenElse(_, left, Some right) } ->
                match actual seen left, actual seen right with
                | Some left, Some right when left = right -> Some left
                | _ -> None
            | _ -> None
        match Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read graph with
        | None -> Map.empty
        | Some plan ->
            plan.ValueBindings |> Set.toList |> List.choose (fun binding ->
                match nodes.TryFind binding, Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.tryValueAuthority graph binding with
                | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [initializer]; Type = NativeType.TLazy _ },
                  Some authority when authority.Initializer.Initializer = initializer ->
                    actual Set.empty initializer |> Option.bind (fun (owner, allocation) ->
                        if residence.Sites.TryFind allocation = Some EscapeKind.StaticLifetime &&
                           codata.Escapes.TryFind allocation = Some EscapeKind.StaticLifetime then
                            Some(binding, (owner, allocation))
                        else None)
                | _ -> None)
            |> Map.ofList
    programReadings.GetValue(graph, read).TryFind binding

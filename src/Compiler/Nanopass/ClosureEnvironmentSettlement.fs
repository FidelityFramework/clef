// SPDX-License-Identifier: MIT
/// Physical environment placement and its bounded-use residence are settled
/// before continuation frames capture their descriptors. Codata is never forced.
module Clef.Compiler.Nanopass.ClosureEnvironmentSettlement

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Ingredients.Obligations
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Residence = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence
module Proof = Clef.Compiler.Baker.Recipes.ContinuationObligationRecipes
module Program = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module Carriers = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers
module Demand = Clef.Compiler.PSGSaturation.SemanticGraph.ExplicitDemand
module ProgramStorageAuthority = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority

type Settlement = {
    Layouts: Map<NodeId, EnvironmentLayout>
    Destinations: Map<NodeId, NodeId>
    Residences: Map<NodeId, EscapeKind>
    Diagnostics: Diagnostic list
}

type ProgramInstance = {
    Carrier: CallableCarrier
    Allocation: NodeId option
    Participants: Set<NodeId>
}

/// All structural occurrences of a program allocation must belong to one
/// initializer. A nested/repeated activation cannot name one static instance.
let private programSites = ProgramStorageAuthority.candidates

let private programBacking graph (layout: EnvironmentLayout) site candidates =
    match candidates with
    | [binding, path] ->
        Program.tryValueAuthority graph binding |> Option.bind (fun authority ->
            let space = authority.Space
            let powerOfTwo value = value > 0 && (value &&& (value - 1)) = 0
            let extent = bigint layout.Bytes
            let granularity = bigint space.Granularity
            let covered =
                layout.Bytes > 0 && powerOfTwo layout.Alignment && powerOfTwo space.Alignment &&
                powerOfTwo space.Granularity && space.Alignment % layout.Alignment = 0 &&
                extent + ((granularity - extent % granularity) % granularity) <= bigint space.Capacity &&
                (Platform.read graph).Findings.IsEmpty
            // This is the individual object's capacity/alignment obligation.
            // No pooled offsets or aggregate image capacity follow from it.
            if not covered then None else
                let sources =
                    [site; binding; layout.Owner; layout.Implementation; layout.Formal] @
                    authority.Evidence.Sources @ path @ layout.Obligations @
                    (ProgramStorageAuthority.declarationInputs graph space.Node |> Set.toList) |> List.distinct
                Some { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentResidence
                       Sources = sources; Target = layout.Owner; Ordinal = 0 })
    | _ -> None

let settlePreparedWhenSourceAdmitted admitted destinations factoryCalls (graph: SemanticGraph) =
    let empty = { Layouts = Map.empty; Destinations = Map.empty; Residences = Map.empty; Diagnostics = [] }
    if not admitted || graph.Platform.IsNone then graph, empty else
    let residual site related reason =
        { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8403"
          Message = "Captured callable environment requires further settlement: " + reason
          Range = graph.Nodes[site].Range; RelatedNodes = site :: related
          Reachability = ReachabilityContext.Unknown }
    let residence = Residence.analyzeEnvironmentsPrepared graph destinations factoryCalls
    let residenceErrors = residence.Unresolved |> List.map (fun pending -> residual pending.Site [] (sprintf "%A" pending.Reason))
    let regionErrors = residence.Regions |> Map.toList |> List.map (fun (site, generator) ->
        residual site [generator] "A generator-local callback needs a settled owned environment region; activation-local backing storage cannot survive a suspension.")
    let placed = graph.Nodes.Values |> Seq.choose (fun owner ->
        match owner.Kind with
        | SemanticKind.ClosureValue(implementation, environment) when owner.IsReachable ->
            let captures = Environments.captures graph owner.Id
            let shape =
                match graph.Nodes.TryFind implementation, graph.Nodes.TryFind environment with
                | Some { Kind = SemanticKind.Lambda(parameters, _, [], _, _) },
                  Some { Kind = SemanticKind.EnvironmentCreate(actual, initializers) }
                    when actual = owner.Id && initializers.Length = captures.Length
                         && (List.map fst initializers = (captures |> List.choose _.SourceNodeId)) ->
                    let formals = graph.Edges |> List.choose (fun edge ->
                        if edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.EnvironmentFormal
                           && edge.Sources = [owner.Id; implementation]
                           && (parameters |> List.exists (fun (_, ty, formal) -> formal = edge.Target && ty = Environments.environmentType))
                        then Some edge.Target else None)
                    match formals with [formal] -> Some formal | _ -> None
                | _ -> None
            match shape with
            | None -> Some (Result.Error (residual owner.Id [implementation; environment] "Formation, exact capture incidence and the real environment formal disagree."))
            | Some formal ->
                match Placement.placeEnvironment graph captures with
                | Ok (SettledLayout.Record(_, Some bytes, Some alignment), fields) ->
                    let slots = fields |> List.map (fun (field: Placement.ContinuationField) ->
                        { Source = field.Source; ValueType = graph.Nodes[field.Source].Type
                          Field = field.Field; Holds = field.Holds; IsCapture = true })
                    let proof = Proof.layout (NodeId.value owner.Id) (sprintf "closure_%d_environment" (NodeId.value owner.Id)) owner
                                    (slots |> List.map (fun slot -> slot.Source, slot.Field.Offset.Value, slot.Field.Size.Value, slot.Field.Align.Value)) bytes alignment
                    let edges = proof.NewEdges |> List.map (fun edge -> { edge with Sources = List.distinct (edge.Sources @ [implementation; environment; formal]) })
                    let proof = { proof with NewEdges = edges }
                    let layout = { Owner = owner.Id; Implementation = implementation; Formal = formal
                                   Slots = slots; Bytes = bytes; Alignment = alignment
                                   Obligations = proof.NewNodes |> List.map _.Id }
                    Some (Ok(layout, proof))
                | Result.Error reason -> Some (Result.Error (residual owner.Id [] (sprintf "%A" reason)))
                | _ -> Some (Result.Error (residual owner.Id [] "The target did not settle an exact environment extent and alignment."))
        | _ -> None) |> Seq.toList
    let layouts = placed |> List.choose (function Ok(layout, _) -> Some(layout.Owner, layout) | _ -> None) |> Map.ofList
    let proofs = placed |> List.choose (function Ok(_, proof) -> Some proof | _ -> None) |> Enrichment.concat
    let programCandidates = programSites graph
    let programPlacements = residence.Sites |> Map.toList |> List.choose (fun (site, _) ->
        let candidates = programCandidates site
        if candidates.IsEmpty then None else
        let owner =
            match graph.Nodes[site].Kind with
            | SemanticKind.EnvironmentCreate(owner, _) | SemanticKind.EnvironmentAllocate owner -> Some owner
            | _ -> None
        let proof = owner |> Option.bind layouts.TryFind |> Option.bind (fun layout -> programBacking graph layout site candidates)
        Some(site, proof))
    let programErrors = programPlacements |> List.choose (fun (site, proof) ->
        if proof.IsSome then None else
        Some(residual site [] "Program callable storage requires one unrepeated initializer and declared writable space covering the settled environment."))
    let staticSites = programPlacements |> List.choose (fun (site, proof) -> proof |> Option.map (fun _ -> site)) |> Set.ofList
    let residences = residence.Sites |> Map.map (fun site kind -> if staticSites.Contains site then EscapeKind.StaticLifetime else kind)
    let proofs = { proofs with NewEdges = proofs.NewEdges @ residence.Evidence @ (programPlacements |> List.choose snd) }
    let graph = ObligationElaboration.foldIn proofs graph
    let destinations =
      graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Sources, graph.Nodes.TryFind edge.Target with
        | EdgeClass.Provenance, EdgeRole.EnvironmentResultDestination, [implementation; owner; formal],
          Some { Kind = SemanticKind.EnvironmentCreate(actual, _) } when actual = owner && layouts.ContainsKey owner ->
            match graph.Nodes.TryFind implementation with
            | Some { Kind = SemanticKind.Lambda(parameters, _, _, _, _) }
                when parameters |> List.exists (fun (_, ty, id) -> id = formal && ty = Environments.environmentType) -> Some(edge.Target, formal)
            | _ -> None
        | _ -> None) |> Map.ofList
    graph, { Layouts = layouts; Destinations = destinations; Residences = residences
             Diagnostics = residenceErrors @ regionErrors @ programErrors @ (placed |> List.choose (function Result.Error diagnostic -> Some diagnostic | _ -> None)) }

let settleWhenSourceAdmitted admitted graph = settlePreparedWhenSourceAdmitted admitted Map.empty Map.empty graph
let settle graph = settleWhenSourceAdmitted true graph

let private validLayout (graph: SemanticGraph) (layout: EnvironmentLayout) =
    match graph.Nodes.TryFind layout.Owner, Environments.capturedInitializers graph layout.Owner with
    | Some { Kind = SemanticKind.ClosureValue(implementation, environment); IsReachable = true }, Some captures
        when implementation = layout.Implementation ->
        match Placement.placeEnvironment graph (Environments.captures graph layout.Owner) with
        | Ok (SettledLayout.Record(_, Some bytes, Some alignment), fields) ->
            let slots: ContinuationSlot list = fields |> List.map (fun field ->
                { Source = field.Source; ValueType = graph.Nodes[field.Source].Type
                  Field = field.Field; Holds = field.Holds; IsCapture = true })
            let formalRows = graph.Edges |> List.filter (fun edge ->
                edge.Role = EdgeRole.EnvironmentFormal && edge.Sources |> List.contains layout.Owner)
            let formalAgrees =
                match formalRows, graph.Nodes.TryFind layout.Formal, graph.Nodes.TryFind implementation with
                | [{ Class = EdgeClass.Provenance; Sources = [owner; code]; Target = formal; Ordinal = 0 }],
                  Some { Kind = SemanticKind.PatternBinding _; IsReachable = true; Type = formalType },
                  Some { Kind = SemanticKind.Lambda(parameters, _, [], _, _); IsReachable = true }
                    when owner = layout.Owner && code = implementation && formal = layout.Formal &&
                         applySubst formalType = Environments.environmentType ->
                    parameters |> List.filter (fun (_, _, id) -> id = formal)
                    |> function [(_, ty, _)] -> applySubst ty = Environments.environmentType | _ -> false
                | _ -> false
            let expectedSources =
                (layout.Owner :: (slots |> List.map _.Source) |> List.distinct) @
                    [implementation; environment; layout.Formal] |> List.distinct
            let obligationAgrees =
                match layout.Obligations with
                | [id] ->
                    let constraints = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = id)
                    match graph.Nodes.TryFind id, constraints with
                    | Some { Kind = SemanticKind.Obligation info },
                      [{ Class = EdgeClass.Obligation; Sources = sources; Ordinal = 0 }] when sources = expectedSources ->
                        match info.Body with
                        | ObligationBody.ContinuationLayout(actual, extent, align) ->
                            actual = (slots |> List.map (fun slot -> slot.Field.Offset.Value, slot.Field.Size.Value, slot.Field.Align.Value)) &&
                            extent = bytes && align = alignment && info.Id = sprintf "closure_%d_environment" (NodeId.value layout.Owner)
                        | _ -> false
                    | _ -> false
                | _ -> false
            formalAgrees && obligationAgrees && layout.Slots = slots && layout.Bytes = bytes && layout.Alignment = alignment &&
            captures.Length = slots.Length && bytes > 0 && alignment > 0
        | _ -> false
    | _ -> false

let private programReadings = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, Map<NodeId, ProgramInstance>>()

/// Read the already initialized program instance. Carrier identity establishes
/// code and convention; exact formation/result-destination incidence establishes
/// the allocation. Neither may substitute for the other's evidence.
let programInstance (graph: SemanticGraph) binding : ProgramInstance option =
    let read (graph: SemanticGraph) =
        let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
        let codata = graph.Codata.Value
        let residence = Residence.analyzeEnvironments graph
        let candidates = programSites graph
        let layouts = codata.EnvironmentLayouts |> Map.filter (fun owner layout -> owner = layout.Owner && validLayout graph layout)
        let carriers, _ = Carriers.settle
                                { Layouts = layouts; Origins = Environments.origins graph; Known = Environments.knownCallables graph } graph
        let carrier id =
            match carriers.TryFind id, codata.CallableCarriers.TryFind id with
            | Some current, Some held when current = held -> Some current
            | _ -> None
        let sameType left right =
            match nodes.TryFind left, nodes.TryFind right with
            | Some left, Some right -> applySubst (Carriers.sourceType left) = applySubst (Carriers.sourceType right)
            | _ -> false
        let rec actual seen id =
            if Set.contains id seen then None else
            let seen = Set.add id seen
            let follow source =
                if not (sameType id source) then None else
                actual seen source |> Option.map (fun (implementation, allocation, participants) -> implementation, allocation, id :: participants)
            match nodes.TryFind id, carrier id with
            | Some node, Some current ->
                match node.Kind with
                | SemanticKind.VarRef(_, Some source) when node.Children.IsEmpty ->
                    match graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Definition && edge.Target = id) with
                    | [] -> follow source
                    | [{ Class = EdgeClass.Reference; Sources = [definition]; Ordinal = 0 }] when definition = source -> follow source
                    | _ -> None
                | SemanticKind.Binding(_, false, _, _) when node.Children.Length = 1 -> follow node.Children.Head
                | SemanticKind.TypeAnnotation(source, declared) when node.Children = [source] && applySubst declared = applySubst node.Type -> follow source
                | SemanticKind.EagerExpr source when Demand.operand graph id = Some source -> follow source
                | SemanticKind.Sequential values when node.Children = values -> List.tryLast values |> Option.bind follow
                | SemanticKind.IfThenElse(condition, yes, Some no) when node.Children = [condition; yes; no] ->
                    match actual seen yes, actual seen no with
                    | Some(left, allocation, participants), Some(right, other, dependencies) when left = right && allocation = other ->
                        Some(left, allocation, id :: condition :: (participants @ dependencies))
                    | _ -> None
                | _ when current.Environment.IsNone ->
                    Some(current.Implementation, None, [id; current.Implementation; current.Result] @ (current.Parameters |> List.map (fun (_, _, formal) -> formal)))
                | SemanticKind.ClosureValue(implementation, environment) ->
                    match current.Environment, nodes.TryFind environment with
                    | Some convention, Some { Kind = SemanticKind.EnvironmentCreate(owner, _) }
                        when convention.Owner = id && implementation = current.Implementation && owner = id &&
                             not (codata.EnvironmentDestinations.ContainsKey environment) && residence.Sites.ContainsKey environment ->
                        Some(implementation, Some environment, [id; implementation; environment; convention.Formal])
                    | _ -> None
                | SemanticKind.Application(callee, arguments) when node.Children = callee :: arguments ->
                    let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EnvironmentResultCall && edge.Target = id)
                    match rows, current.Environment with
                    | [{ Class = EdgeClass.Provenance; Sources = [factory; constructor; formal; allocation; destination]; Ordinal = 0 }], Some convention
                        when codata.EnvironmentDestinations.TryFind constructor = Some formal && residence.Sites.ContainsKey allocation ->
                        match nodes.TryFind constructor, nodes.TryFind allocation with
                        | Some { Kind = SemanticKind.EnvironmentCreate(owner, _) }, Some { Kind = SemanticKind.EnvironmentAllocate(actual) }
                            when owner = convention.Owner && actual = owner ->
                            let dependencies =
                                residence.Evidence |> List.filter (fun edge ->
                                    edge.Role = EdgeRole.EnvironmentResidence && edge.Target = owner && List.contains allocation edge.Sources)
                                |> List.collect _.Sources
                            if dependencies.IsEmpty then None else
                            Some(current.Implementation, Some allocation,
                                 [id; callee; factory; constructor; formal; allocation; destination] @ arguments @ dependencies)
                        | _ -> None
                    | _ -> None
                | _ -> None
            | _ -> None
        match Program.read graph with
        | None -> Map.empty
        | Some plan ->
            plan.ValueBindings |> Set.toList |> List.choose (fun binding ->
                match nodes.TryFind binding, Program.tryValueAuthority graph binding, carrier binding with
                | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [initializer] }, Some authority, Some held
                    when authority.Initializer.Initializer = initializer ->
                    actual Set.empty initializer |> Option.bind (fun (implementation, allocation, participants) ->
                        let backing =
                            match allocation, held.Environment with
                            | None, None -> Some []
                            | Some site, Some environment when codata.Escapes.TryFind site = Some EscapeKind.StaticLifetime && residence.Sites.ContainsKey site ->
                                layouts.TryFind environment.Owner |> Option.bind (fun layout ->
                                    programBacking graph layout site (candidates site) |> Option.bind (fun expected ->
                                        let rows = graph.Edges |> List.filter (fun edge ->
                                            edge.Class = expected.Class && edge.Role = expected.Role && edge.Target = expected.Target &&
                                            edge.Ordinal = expected.Ordinal && edge.Sources = expected.Sources)
                                        match rows with [row] -> Some row.Sources | _ -> None))
                            | _ -> None
                        backing |> Option.bind (fun backing ->
                            if implementation <> held.Implementation then None else
                            Some(binding, { Carrier = held; Allocation = allocation
                                            Participants = Set.ofList (binding :: (authority.Evidence.Sources @ participants @ backing)) })))
                | _ -> None)
            |> Map.ofList
    programReadings.GetValue(graph, read).TryFind binding

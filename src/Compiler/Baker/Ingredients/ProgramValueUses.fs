// SPDX-License-Identifier: MIT
/// Current source reads of runtime callable slots and their startup phases.
/// Phases order completed initializers before reads, not arbitrary lifetimes.
module Clef.Compiler.Baker.Ingredients.ProgramValueUses

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Program = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization
module Activation = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramActivation

type Reading = { Body: ObligationBody; Participants: Participant list; Missing: string list }

let private callable node =
    let rec loop ty =
        match applySubst ty with
        | NativeType.TFun _ -> true
        | NativeType.TForall(_, body) -> loop body
        | _ -> false
    node.IsReachable && loop node.Type

/// Retained intent supplies scope even when later authority/startup is missing.
let bindings (graph: SemanticGraph) =
    graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, graph.Nodes.TryFind edge.Target with
        | EdgeClass.Provenance, EdgeRole.ProgramValueIntent, Some node when callable node -> Some node.Id
        | _ -> None) |> List.distinct

let private occurrence group role ordinal node : Participant =
    { Node = node; Role = role; Ordinal = ordinal; Group = group }

let scope (graph: SemanticGraph) binding =
    occurrence binding ParticipantRole.InitializationBinding 0 binding ::
    (graph.Edges |> List.collect (fun edge ->
        match edge.Class, edge.Role, edge.Sources with
        | EdgeClass.Provenance, EdgeRole.ProgramValueIntent, [entry; spine; value] when edge.Target = binding ->
            [ occurrence binding ParticipantRole.InitializationEntry edge.Ordinal entry
              occurrence binding ParticipantRole.InitializationSpine edge.Ordinal spine
              occurrence binding ParticipantRole.InitializationValue edge.Ordinal value ]
        | _ -> []))

let read (graph: SemanticGraph) binding : Reading =
    let initial = scope graph binding
    let pending reasons participants = { Body = ObligationBody.Pending reasons; Participants = participants; Missing = reasons }
    match Program.read graph with
    | None -> pending ["The current startup plan is absent or inconsistent."] initial
    | Some plan ->
      match plan.Initializers |> List.filter (fun row -> row.Binding = binding && plan.ValueBindings.Contains binding) with
      | [initialization] ->
        let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
        let incidence = nodes.Values |> Seq.collect Closures.structuralIncidence |> Seq.toList
        let parents = incidence |> List.filter Hyperedge.isStructural
                      |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
                      |> List.groupBy fst |> Map.ofList |> Map.map (fun _ rows -> rows |> List.map snd)
        let activation = lazy (Activation.analyze graph)
        let references =
            incidence @ graph.Edges
            |> List.filter (fun edge ->
                edge.Class = EdgeClass.Reference && List.contains binding edge.Sources &&
                (nodes.ContainsKey edge.Target || not (graph.Nodes.ContainsKey edge.Target)))
            |> List.distinctBy (fun edge -> edge.Class, edge.Role, edge.Sources, edge.Target, edge.Ordinal)
        let reads, unsupported = references |> List.fold (fun (reads, unsupported) edge ->
            match nodes.TryFind edge.Target, edge.Role, edge.Sources with
            | Some { Kind = SemanticKind.ModuleDef(_, members) }, EdgeRole.Member, [source]
                when List.tryItem edge.Ordinal members = Some source -> reads, unsupported
            | Some { Kind = SemanticKind.VarRef(_, Some source); Children = [] }, EdgeRole.Definition, [actual]
                when source = binding && actual = binding && edge.Ordinal = 0 -> edge :: reads, unsupported
            | Some { Kind = SemanticKind.EnvironmentCreate(_, values) }, EdgeRole.EnvironmentInitializer, [actual]
                when actual = binding && (List.tryItem edge.Ordinal values |> Option.exists (snd >> (=) binding)) -> edge :: reads, unsupported
            | _ -> edge :: reads, sprintf "Unclassified reference to callable slot at node %d." (NodeId.value edge.Target) :: unsupported) ([], [])
        let participants = ResizeArray<Participant>(initial)
        // A binding executes at its retained startup position. Any other direct
        // structural use of that binding needs a value-reading contract; it may
        // not vanish merely because it bypasses a VarRef.
        let rec startupContainers seen id =
            if Set.contains id seen then seen else
            match nodes.TryFind id with
            | Some { Kind = SemanticKind.Sequential values } ->
                List.fold startupContainers (Set.add id seen) values
            | _ -> seen
        let containers = startupContainers Set.empty plan.Spine
        let directUses = incidence |> List.filter (fun edge ->
            Hyperedge.isStructural edge && List.contains binding edge.Sources &&
            not (edge.Role = EdgeRole.Element && edge.Sources = [binding] && containers.Contains edge.Target))
        let directMissing = directUses |> List.map (fun edge ->
            participants.Add(occurrence edge.Target ParticipantRole.InitializationUse edge.Ordinal edge.Target)
            participants.Add(occurrence edge.Target ParticipantRole.InitializationPremise edge.Ordinal binding)
            sprintf "Direct structural callable-slot use (%A) at node %d needs a reading contract." edge.Role (NodeId.value edge.Target))
        // Capture metadata is independent of kind-derived/reference incidence.
        // Its formation phase is not the invocation phase of a deferred body.
        let captureMissing = nodes.Values |> Seq.collect (fun node ->
            let captures =
                match node.Kind with
                | SemanticKind.Lambda(_, _, captures, _, _)
                | SemanticKind.SeqExpr(_, captures)
                | SemanticKind.LazyExpr(_, captures) -> captures
                | _ -> []
            captures |> List.mapi (fun ordinal capture -> ordinal, capture)
            |> List.choose (fun (ordinal, capture) ->
                match capture.SourceNodeId with
                | Some source when source <> binding -> None
                | source ->
                    participants.Add(occurrence node.Id ParticipantRole.InitializationUse ordinal node.Id)
                    match source with
                    | Some source ->
                        participants.Add(occurrence node.Id ParticipantRole.InitializationPremise ordinal source)
                        Some(sprintf "Residual callable-slot capture %d at node %d needs a formation-phase contract." ordinal (NodeId.value node.Id))
                    | None ->
                        // The census cannot exclude any slot until formation
                        // supplies identity. A capture's name is not authority.
                        Some(sprintf "Capture %d at node %d has unresolved source identity." ordinal (NodeId.value node.Id)))) |> Seq.toList
        // One direct premise per visited occurrence, not a list per ancestry path.
        let phasesFor useSite =
            let cache = System.Collections.Generic.Dictionary<NodeId, Result<Set<int * NodeId>, string list>>()
            let active = System.Collections.Generic.HashSet<NodeId>()
            let rec visit id =
                match cache.TryGetValue id with
                | true, result -> result
                | _ when not (active.Add id) -> Error [sprintf "Cyclic activation/structural path at node %d needs an admitted order contract." (NodeId.value id)]
                | _ ->
                    participants.Add(occurrence useSite ParticipantRole.InitializationScope 0 id)
                    let combine inputs =
                        inputs |> List.fold (fun accumulated next ->
                            match accumulated, visit next with
                            | Ok left, Ok right -> Ok(Set.union left right)
                            | Error left, Error right -> Error(left @ right)
                            | Error errors, _ | _, Error errors -> Error errors) (Ok Set.empty)
                    let roots = plan.Initializers |> List.filter (fun row -> row.Binding = id)
                    let result =
                        match roots, nodes.TryFind id with
                        | [row], Some _ -> Ok(Set.singleton (row.Ordinal, row.Binding))
                        | [], Some _ when id = plan.EntryCall -> Ok(Set.singleton (plan.Initializers.Length, plan.EntryCall))
                        | [], Some { Kind = SemanticKind.Lambda(_, _, _, _, LambdaContext.RegularClosure) } when id <> plan.EntryLambda ->
                            match Activation.coverage activation.Value plan.EntryLambda id with
                            | None -> Error [sprintf "Complete ordinary invocation scope is unavailable for node %d." (NodeId.value id)]
                            | Some coverage when not coverage.Dependencies.IsEmpty -> Error [sprintf "Deferred invocation scope for node %d needs a separate order contract." (NodeId.value id)]
                            | Some coverage ->
                                for edge in coverage.Evidence do
                                    edge.Sources |> List.iteri (fun ordinal source ->
                                        participants.Add(occurrence edge.Target ParticipantRole.InitializationPremise ordinal source))
                                let calls = coverage.Evidence |> List.choose (fun edge ->
                                    match edge.Role, edge.Sources with
                                    | EdgeRole.ProgramActivationCall, [_; caller; callee; implementation] when implementation = id ->
                                        participants.Add(occurrence edge.Target ParticipantRole.InitializationCaller 0 caller)
                                        participants.Add(occurrence edge.Target ParticipantRole.InitializationCallee 0 callee)
                                        Some edge.Target
                                    | _ -> None)
                                if calls.IsEmpty then Error [sprintf "No complete invocation supplies node %d's phase." (NodeId.value id)]
                                else combine calls
                        | [], Some { Kind = SemanticKind.Lambda _ | SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ } ->
                            Error [sprintf "Deferred or uncovered scope at node %d has no startup phase." (NodeId.value id)]
                        | [], Some _ ->
                            match parents.TryFind id with
                            | Some edges when not edges.IsEmpty ->
                                for edge in edges do participants.Add(occurrence id ParticipantRole.InitializationParent edge.Ordinal edge.Target)
                                edges |> List.map _.Target |> List.distinct |> combine
                            | _ -> Error [sprintf "Node %d is outside every supported startup/entry scope." (NodeId.value id)]
                        | _ -> Error [sprintf "Missing or ambiguous phase participant %d." (NodeId.value id)]
                    active.Remove id |> ignore
                    cache[id] <- result
                    result
            visit useSite
        let phases, missing =
            List.rev reads |> List.fold (fun (allPhases, missing) edge ->
                participants.Add(occurrence edge.Target ParticipantRole.InitializationUse edge.Ordinal edge.Target)
                match phasesFor edge.Target with
                | Error reasons -> allPhases, missing @ reasons
                | Ok phases ->
                    for phase, root in phases do participants.Add(occurrence edge.Target ParticipantRole.InitializationPhase phase root)
                    allPhases @ (phases |> Set.toList |> List.map fst), missing) ([], List.rev unsupported @ directMissing @ captureMissing)
        let current = List.ofSeq participants
        if missing.IsEmpty then
            { Body = ObligationBody.ProgramInitializationOrder(initialization.Ordinal, plan.Initializers.Length, phases)
              Participants = current; Missing = [] }
        else pending (List.distinct missing) current
      | _ -> pending ["The callable slot has no unique current initializer and value intent."] initial

/// Admission checks current source premises, never an earlier proof or history.
/// Solver discharge is a separate required stage for the complete proposition.
let current (graph: SemanticGraph) binding =
    let expected = read graph binding
    if not expected.Missing.IsEmpty then false else
    graph.Edges |> List.filter (fun edge ->
        match edge.Role with
        | EdgeRole.ProgramInitializationOrder participants ->
            participants |> List.exists (fun p -> p.Role = ParticipantRole.InitializationBinding && p.Node = binding && p.Group = binding)
        | _ -> false)
    |> function
       | [{ Class = EdgeClass.Provenance; Role = EdgeRole.ProgramInitializationOrder participants; Sources = sources; Target = target; Ordinal = 0 }]
            when participants = expected.Participants && sources = List.map _.Node participants ->
           match graph.Nodes.TryFind target, graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = target) with
           | Some { Kind = SemanticKind.Obligation info }, [{ Class = EdgeClass.Obligation; Sources = actual; Ordinal = 0 }] ->
               info.Body = expected.Body && actual = sources && info.Id = sprintf "program_binding_%d_initialization_order" (NodeId.value binding)
           | _ -> false
       | _ -> false

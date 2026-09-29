// SPDX-License-Identifier: MIT
/// Source execution ownership for program storage. This establishes one
/// unrepeated initializer and its declared writable space, not object layout
/// or whole-region capacity. Those have distinct owning contracts.
module Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Program = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization
module Closures = Clef.Compiler.Baker.Ingredients.Closures

let private readings = System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, NodeId -> (NodeId * NodeId list) list>()

/// Allocation proposals precede startup, uniqueness and space acceptance. Read
/// the initializer relation itself: an invalid startup plan must not erase it.
/// Walk each initializer once, including loops but excluding deferred bodies.
/// Keep only direct incidence, never a transitive path per allocation.
let environmentProposals (graph: SemanticGraph) =
    graph.Edges |> List.choose (fun edge ->
        match edge.Class, edge.Role, edge.Sources with
        | EdgeClass.Provenance, EdgeRole.ProgramInitializer, [_; binding; initializer; _] -> Some(binding, initializer)
        | _ -> None)
    |> List.distinct
    |> List.collect (fun (binding, initializer) ->
        let seen = System.Collections.Generic.HashSet<NodeId>()
        let pending = System.Collections.Generic.Stack<NodeId>()
        let proposals = ResizeArray<_>()
        pending.Push initializer
        while pending.Count > 0 do
            let id = pending.Pop()
            if seen.Add id then
                match graph.Nodes.TryFind id with
                | Some { IsReachable = true; Kind = SemanticKind.Lambda _ } -> ()
                | Some node when node.IsReachable ->
                    match node.Kind with
                    | SemanticKind.EnvironmentCreate _ | SemanticKind.EnvironmentAllocate _ ->
                        proposals.Add(id, (binding, initializer))
                    | _ -> ()
                    for edge in Closures.structuralIncidence node do
                        let delayed =
                            edge.Role = EdgeRole.Body &&
                            (match node.Kind with SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ -> true | _ -> false)
                        if Hyperedge.isStructural edge && not delayed then
                            for child in edge.Sources do pending.Push child
                | _ -> ()
        proposals |> Seq.toList)
    |> List.groupBy fst
    |> List.map (fun (site, rows) -> site, rows |> List.map snd |> List.distinct)
    |> Map.ofList

/// Every structural occurrence must reach the same source initializer without
/// crossing a function, loop or delayed body. Parent pointers are not authority.
let candidates (graph: SemanticGraph) =
    let read (graph: SemanticGraph) =
        let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
        let parents =
            nodes.Values |> Seq.collect Closures.structuralIncidence
            |> Seq.filter Hyperedge.isStructural
            |> Seq.collect (fun edge -> edge.Sources |> List.map (fun source -> source, (edge.Target, edge.Role)))
            |> Seq.groupBy fst
            |> Seq.map (fun (source, rows) -> source, rows |> Seq.map snd |> Seq.distinct |> Seq.toList)
            |> Map.ofSeq
        let path target site =
            // A shared suffix is checked once, not copied once per route to it.
            // State is local to this (site, initializer) query: false is active,
            // true is completed. An active backedge still rejects the whole
            // all-parent claim, even when another parent reaches the target.
            let states = System.Collections.Generic.Dictionary<NodeId, bool>()
            let pending = System.Collections.Generic.Stack<NodeId * bool>()
            let participants = ResizeArray<NodeId>()
            let mutable valid = true
            pending.Push(site, false)
            while valid && pending.Count > 0 do
                let id, leaving = pending.Pop()
                if leaving then states[id] <- true else
                match states.TryGetValue id with
                | true, complete -> if not complete then valid <- false
                | _ ->
                    match nodes.TryFind id with
                    | Some { Kind = SemanticKind.Lambda _ | SemanticKind.WhileLoop _ | SemanticKind.ForLoop _ | SemanticKind.ForEach _ } -> valid <- false
                    | Some _ when id = target ->
                        participants.Add id
                        states[id] <- true
                    | Some _ ->
                        match parents.TryFind id with
                        | Some enclosing when not enclosing.IsEmpty ->
                            participants.Add id
                            states[id] <- false
                            pending.Push(id, true)
                            // Reverse the stack insertion to retain the old
                            // traversal's first-occurrence dependency order.
                            for parent, role in List.rev enclosing do
                                let delayedBody =
                                    role = EdgeRole.Body &&
                                    (match nodes.TryFind parent with
                                     | Some { Kind = SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ } -> true
                                     | _ -> false)
                                if delayedBody then valid <- false
                                else pending.Push(parent, false)
                        | _ -> valid <- false
                    | None -> valid <- false
            if valid then Some(List.ofSeq participants) else None
        let rows =
            Program.read graph
            |> Option.map (fun plan -> plan.Initializers |> List.filter (fun row -> plan.ValueBindings.Contains row.Binding))
            |> Option.defaultValue []
        fun site -> rows |> List.choose (fun row ->
            path row.Initializer site |> Option.map (fun participants -> row.Binding, participants))
    readings.GetValue(graph, System.Runtime.CompilerServices.ConditionalWeakTable<SemanticGraph, NodeId -> (NodeId * NodeId list) list>.CreateValueCallback(fun current -> read current))

/// Keep declaration literals/aliases in the proof dependency set, not merely
/// the outer record whose unchanged identity could hide a capacity edit.
let declarationInputs (graph: SemanticGraph) root =
    let rec collect seen id =
        if Set.contains id seen then seen else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | None -> seen
        | Some node ->
            let inputs =
                Closures.structuralIncidence node
                |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
                |> List.collect _.Sources
            inputs |> List.fold collect seen
    collect Set.empty root

let authority (graph: SemanticGraph) site : (Program.ValueAuthority * Set<NodeId>) option =
    match candidates graph site with
    | [binding, path] ->
        Program.tryValueAuthority graph binding |> Option.map (fun authority ->
            authority,
            Set.union (Set.ofList (site :: binding :: (authority.Evidence.Sources @ path)))
                      (declarationInputs graph authority.Space.Node))
    | _ -> None

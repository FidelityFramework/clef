// SPDX-License-Identifier: MIT
/// Source-owned selection of already demanded bodies and their actual contexts.
/// Full semantic/premise validation remains with the existing source owners.
module Clef.Compiler.Baker.Recipes.WitnessScopeRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open System.Globalization
open System.Security.Cryptography
open System.Text

let private support =
    { Identity = "ccs:prepared-owner"
      Policy = WitnessScopeSupportPolicy.WholePreparedOwner }

/// Resource policy for the current source host, not a Clef semantic limit.
/// Paths count context alternatives across demanded bodies and the nonbody
/// module headers required to establish them. Frames count the sum of their
/// breadcrumb lengths. Compact stamped ports never copy dormant siblings.
type ScopeContextBudget = { MaxPaths: int64; MaxFrames: int64 }

type private SourceOccurrenceSlot = {
    Parent: NodeId
    Port: WitnessOccurrencePort
    Ordinal: int
    Extent: int
    Stamp: string
}

/// Bound interim explicit context-list construction without consulting CLR
/// memory heuristics. A host can supply another explicit policy through
/// projectWithBudget; exhaustion is a source diagnostic, never a partial plan.
let hostedContextBudget = { MaxPaths = 100_000L; MaxFrames = 1_000_000L }

/// A source membership stamp retains order and multiplicity. It grants no
/// revision or proof authority; Baker rechecks the complete owning domain.
let private portStamp parent port (slots: NodeId list) =
    let text = StringBuilder()
    let append (value: string) = text.Append(value.Length.ToString(CultureInfo.InvariantCulture)).Append(':').Append(value).Append(';') |> ignore
    append ((NodeId.value parent).ToString(CultureInfo.InvariantCulture))
    append (match port with WitnessOccurrencePort.StructuralChild -> "structural" | WitnessOccurrencePort.ModuleDeclaration -> "declaration")
    for id in slots do append ((NodeId.value id).ToString(CultureInfo.InvariantCulture))
    text.ToString() |> Encoding.UTF8.GetBytes |> SHA256.HashData |> System.Convert.ToHexString

let private metadataIdentities = function
    | MetadataValue.NodeId id -> [id]
    | MetadataValue.NodeIdList ids -> ids
    | _ -> []

let private historyIdentities = function
    | MetadataValue.Specialization trace ->
        [trace.SourceDeclaration; trace.SourceNode; trace.CloneDeclaration; trace.CloneNode]
        @ List.map fst trace.Requests
        @ trace.Input.Children @ Option.toList trace.Input.Parent
        @ trace.Output.Children @ Option.toList trace.Output.Parent
    | _ -> []

/// Select only the final source reachability marks. The recipe does not run a
/// second reachability algorithm or turn inactive dependencies into bodies.
let private projectPrepared (budget: ScopeContextBudget) (emission: WitnessEmissionProjection option) (graph: SemanticGraph) : Result<WitnessLiveScopePlan, WitnessProjectionFailure list> =
    let failures = ResizeArray<WitnessProjectionFailure>()
    let fail occurrence participants reason =
        failures.Add { Occurrence = occurrence; Participants = Set.ofList participants
                       Reason = "WitnessScopes: " + reason }
    if budget.MaxPaths < 0L || budget.MaxFrames < 0L then
        fail None [] "The source host supplied a negative occurrence-context resource budget."
    // Reachability also retains semantic type declarations for Baker's exact
    // nominal layout and mutable-field checks. Their settled consequences are
    // carried by Numeric.Layouts and Memory operations, not executable bodies.
    // Current proof citizens likewise have their separate typed claim account.
    // Keep the source reachability marks and complete owner premises intact.
    let bodies = graph.Nodes |> Map.filter (fun _ node ->
        node.IsReachable &&
        (match node.Kind with SemanticKind.Obligation _ | SemanticKind.TypeDef _ -> false | _ -> true))
    let incoming = System.Collections.Generic.Dictionary<NodeId, ResizeArray<SourceOccurrenceSlot>>()
    let neededModules = System.Collections.Generic.HashSet<NodeId>()
    let addSlots parent port (slots: NodeId list) =
        let extent, stamp = slots.Length, portStamp parent port slots
        slots |> List.iteri (fun ordinal child ->
            if not (graph.Nodes.ContainsKey child) then
                fail (Some parent) [parent; child] "An actual source slot references an absent node."
            elif bodies.ContainsKey child || neededModules.Contains child then
                let row =
                    { Parent = parent; Port = port; Ordinal = ordinal
                      Extent = extent; Stamp = stamp }
                match incoming.TryGetValue child with
                | true, rows -> rows.Add row
                | _ -> incoming.Add(child, ResizeArray [row]))
    // Canonical module inventory establishes declaration contexts. ModuleDef
    // membership can differ from Children after startup/declaration extraction.
    let modules = System.Collections.Generic.HashSet<NodeId>()
    let activeModules = System.Collections.Generic.HashSet<NodeId>()
    let moduleVisits = System.Collections.Generic.Stack<NodeId * bool>()
    for roots in graph.Modules.Values do
        for root in roots do moduleVisits.Push(root, false)
    while moduleVisits.Count <> 0 do
        let id, leaving = moduleVisits.Pop()
        if leaving then activeModules.Remove id |> ignore
        elif activeModules.Contains id then
            fail (Some id) (Seq.toList activeModules) "The current declaration inventory contains a cycle."
        elif not (graph.Nodes.ContainsKey id) then
            fail (Some id) [id] "The current module inventory references an absent node."
        else
            match graph.Nodes[id].Kind with
            | SemanticKind.ModuleDef(_, members) when modules.Add id ->
                activeModules.Add id |> ignore
                moduleVisits.Push(id, true)
                for memberId in List.rev members do
                    if not (graph.Nodes.ContainsKey memberId) then
                        fail (Some id) [id; memberId] "An actual source declaration slot references an absent node."
                    else
                        match graph.Nodes[memberId].Kind with
                        | SemanticKind.ModuleDef _ -> moduleVisits.Push(memberId, false)
                        | _ -> ()
            | _ -> ()

    // Full-owner membership is inspected conservatively, but inactive members
    // never receive occurrence records or copied prefix/suffix lists. Retain
    // only module ancestors of an actual live declaration as context headers.
    let moduleParents = System.Collections.Generic.Dictionary<NodeId, ResizeArray<NodeId>>()
    let pendingModules = System.Collections.Generic.Queue<NodeId>()
    let requireModule id = if neededModules.Add id then pendingModules.Enqueue id
    for id in modules do
        match graph.Nodes[id].Kind with
        | SemanticKind.ModuleDef(_, members) ->
            for memberId in members do
                if bodies.ContainsKey memberId then requireModule id
                if modules.Contains memberId then
                    match moduleParents.TryGetValue memberId with
                    | true, parents -> parents.Add id
                    | _ -> moduleParents.Add(memberId, ResizeArray [id])
        | _ -> ()
    while pendingModules.Count <> 0 do
        match moduleParents.TryGetValue(pendingModules.Dequeue()) with
        | true, parents -> for parent in parents do requireModule parent
        | _ -> ()
    // Only live execution parents establish execution paths. An inactive
    // rewritten application is historical evidence, never another live parent.
    for node in bodies.Values do addSlots node.Id WitnessOccurrencePort.StructuralChild node.Children
    for id in neededModules do
        match graph.Nodes[id].Kind with
        | SemanticKind.ModuleDef(_, members) -> addSlots id WitnessOccurrencePort.ModuleDeclaration members
        | _ -> ()

    // A small shared DAG can have exponentially many actual paths. Count the
    // complete alternatives and cumulative frames before allocating path
    // lists. Kahn ordering also avoids recursive host-stack growth. Counting
    // ports separately preserves aliases and repeated child identities at
    // different original ordinals.
    let contextNodes = System.Collections.Generic.HashSet<NodeId>(bodies.Keys)
    let outgoing = System.Collections.Generic.Dictionary<NodeId, ResizeArray<NodeId>>()
    for pair in incoming do
        contextNodes.Add pair.Key |> ignore
        for row in pair.Value do
            contextNodes.Add row.Parent |> ignore
            match outgoing.TryGetValue row.Parent with
            | true, children -> children.Add pair.Key
            | _ -> outgoing.Add(row.Parent, ResizeArray [pair.Key])
    let degrees = System.Collections.Generic.Dictionary<NodeId, int>()
    let counts = System.Collections.Generic.Dictionary<NodeId, int64 * int64>()
    let ready = System.Collections.Generic.Queue<NodeId>()
    let order = ResizeArray<NodeId>()
    let mutable totalPaths, totalFrames = 0L, 0L
    let addBounded occurrence name limit left right =
        if right > limit || left > limit - right then
            fail (Some occurrence) [occurrence]
                $"The source-host occurrence-context {name} budget ({limit}) was exceeded; no live scope was produced."
            None
        else Some (left + right)
    let account id =
        let paths, frames = counts[id]
        match addBounded id "path" budget.MaxPaths totalPaths paths,
              addBounded id "frame" budget.MaxFrames totalFrames frames with
        | Some nextPaths, Some nextFrames ->
            totalPaths <- nextPaths
            totalFrames <- nextFrames
            order.Add id
            ready.Enqueue id
        | _ -> ()
    if failures.Count = 0 then
        for id in contextNodes do
            let degree = match incoming.TryGetValue id with true, rows -> rows.Count | _ -> 0
            degrees.Add(id, degree)
            counts.Add(id, if degree = 0 then (1L, 0L) else (0L, 0L))
            if degree = 0 && failures.Count = 0 then account id
        while ready.Count <> 0 && failures.Count = 0 do
            let parent = ready.Dequeue()
            let parentPaths, parentFrames = counts[parent]
            match outgoing.TryGetValue parent with
            | false, _ -> ()
            | true, children ->
                for child in children do
                    if failures.Count = 0 then
                        let childPaths, childFrames = counts[child]
                        match addBounded child "path" budget.MaxPaths childPaths parentPaths,
                              addBounded child "frame" budget.MaxFrames parentFrames parentPaths with
                        | Some paths, Some addedFrames ->
                            match addBounded child "frame" budget.MaxFrames childFrames addedFrames with
                            | Some frames ->
                                counts[child] <- paths, frames
                                degrees[child] <- degrees[child] - 1
                                if degrees[child] = 0 then account child
                            | None -> ()
                        | _ -> ()
        if failures.Count = 0 && order.Count <> contextNodes.Count then
            fail None (contextNodes |> Seq.filter (fun id -> degrees[id] <> 0) |> Seq.toList)
                "A live occurrence context contains a structural cycle."
    let frames = System.Collections.Generic.Dictionary<NodeId, WitnessOccurrenceBreadcrumb list>()
    let contexts = System.Collections.Generic.Dictionary<NodeId, WitnessOccurrenceBreadcrumb list list>()
    if failures.Count = 0 then
        for pair in incoming do
            let rows = pair.Value |> Seq.map (fun row ->
                ({ Parent = row.Parent; Port = row.Port; Ordinal = row.Ordinal
                   Extent = row.Extent; Stamp = row.Stamp } : WitnessOccurrenceBreadcrumb)) |> Seq.toList
            frames.Add(pair.Key, rows)
        for id in order do
            let paths =
                match frames.TryGetValue id with
                | false, _ -> [[]]
                | true, rows ->
                    rows |> List.collect (fun row ->
                        contexts[row.Parent] |> List.map (fun rest -> row :: rest))
            contexts.Add(id, paths)
    let occurrences =
        (if failures.Count = 0 then bodies else Map.empty) |> Map.map (fun id node ->
            { Body = node
              Children = node.Children |> List.mapi (fun ordinal child ->
                  { Ordinal = ordinal
                    Traversal =
                        if bodies.ContainsKey child then WitnessChildTraversal.SourceLive child
                        else WitnessChildTraversal.SourceOmitted(support, child) })
              Contexts = contexts[id] })
    let contextIdentities =
        frames.Values |> Seq.collect id
        |> Seq.map _.Parent
        |> Set.ofSeq |> fun ids -> Set.difference ids (bodies.Keys |> Set.ofSeq)
    let history = bodies.Values |> Seq.collect (fun node -> node.Metadata.Values |> Seq.collect historyIdentities) |> Set.ofSeq
    let interfaces =
        bodies.Values |> Seq.collect (fun node ->
            let references = kindEdges node.Id node.Kind |> List.filter Hyperedge.isReference |> List.collect _.Sources
            references @ Option.toList node.Parent @ (node.Metadata.Values |> Seq.collect metadataIdentities |> Seq.toList))
        |> Set.ofSeq |> fun ids -> Set.difference ids (bodies.Keys |> Set.ofSeq)
    let ports =
        incoming |> Seq.collect (fun pair -> pair.Value |> Seq.map (fun row -> pair.Key, row))
        |> Seq.groupBy (fun (_, row) -> row.Parent, row.Port)
        |> Seq.map (fun (key, rows) ->
            let rows = Seq.toList rows
            let _, first = List.head rows
            key, { Extent = first.Extent; Stamp = first.Stamp
                   Positions = rows |> List.map (fun (child, row) -> row.Ordinal, child) |> Map.ofList }) |> Map.ofSeq
    let headers =
        Set.union contextIdentities (Set.ofSeq neededModules) |> Seq.map (fun parent ->
            let name =
                match graph.Nodes[parent].Kind with
                | SemanticKind.ModuleDef(name, _) -> name
                | _ ->
                    fail (Some parent) [parent] "A body-free context parent is not a source module container."
                    ""
            let headerPorts =
                ports |> Map.toSeq |> Seq.choose (fun ((owner, port), account) -> if owner = parent then Some(port, account) else None)
                |> Map.ofSeq
            parent, { Identity = parent; Name = name; Ports = headerPorts }) |> Map.ofSeq
    let bindingUses =
        bodies |> Map.toList |> List.choose (fun (site, node) ->
            match node.Kind with
            | SemanticKind.VarRef(referenceName, Some binding) ->
                match graph.Nodes.TryFind binding, emission with
                | None, _ ->
                    fail (Some site) [site; binding] "A live variable use references an absent binding."
                    None
                | _, None ->
                    fail (Some site) [site; binding] "A live variable use has no current source emission classification."
                    None
                | Some declaration, Some facts ->
                    let classification =
                        match declaration.Kind with
                        | SemanticKind.PatternBinding name -> Some(name, WitnessBindingClass.Formal)
                        | SemanticKind.Binding(name, mutableCell, _, _) ->
                            Some(name, if mutableCell then WitnessBindingClass.MutableCell else WitnessBindingClass.ImmutableValue)
                        | SemanticKind.Lambda(_, _, _, name, LambdaContext.LazyThunk)
                            when facts.Callable.Declarations.ContainsKey binding ->
                            Some(Option.defaultValue referenceName name, WitnessBindingClass.ImmutableValue)
                        | _ ->
                            fail (Some site) [site; binding] "A live variable use does not name a settled binding or formal declaration."
                            None
                    classification |> Option.map (fun (name, classification) ->
                        site, { Binding = binding; Name = name; Class = classification
                                IsProgramSlotIntent = facts.Storage.Startup |> Option.exists (fun startup -> startup.ValueBindings.Contains binding)
                                HasProgramSlotAuthority = facts.Storage.SlotAuthorities.Contains binding
                                IsFunctionBinding = facts.Callable.FunctionBindings.Contains binding
                                IsCallableDeclaration = facts.Callable.DefinitionOnlyBindings.Contains binding || facts.Callable.DefinitionOnlyLambdas.Contains binding
                                IsPartialApplication = graph.Codata.Value.Curry.PartialAppBindings.Contains binding })
            | SemanticKind.VarRef(_, None) ->
                fail (Some site) [site] "A live variable use has no settled binding identity."
                None
            | _ -> None) |> Map.ofList
    let entries = ResizeArray<WitnessSourceEntry>()
    let addEntry reason focus =
        let paths =
            match occurrences.TryFind focus with
            | Some row -> Some row.Contexts
            | None when reason = WitnessEntryReason.BoundaryScope && headers.ContainsKey focus -> Some contexts[focus]
            | _ -> None
        match paths with
        | Some paths ->
            for context in paths do
                let entry = { Focus = focus; Reason = reason; Context = context }
                if not (entries |> Seq.exists (fun held -> held.Focus = focus && held.Context = context)) then entries.Add entry
        | None -> ()
    for focus, _ in graph.DeclarationRoots do addEntry WitnessEntryReason.ExecutableRoot focus
    match emission with
    | Some facts ->
        let declared = Set.unionMany [facts.Callable.FunctionBindings; facts.Callable.DefinitionOnlyLambdas; facts.Storage.DefinitionOnlyThunks]
        for focus in declared do
            // A lambda contained by an admitted binding is witnessed there;
            // only a detached demanded declaration becomes an explicit entry.
            let structurallyContained =
                match incoming.TryGetValue focus with
                | true, rows -> rows |> Seq.exists (fun row -> row.Port = WitnessOccurrencePort.StructuralChild && bodies.ContainsKey row.Parent)
                | _ -> false
            if not structurallyContained then addEntry WitnessEntryReason.DetachedDefinition focus
        let boundaryOwners =
            Set.union (facts.Boundary.ByScope.Keys |> Set.ofSeq)
                      (facts.Boundary.IntrinsicWriteImports.Values |> Seq.map _.Scope |> Set.ofSeq)
        for focus in boundaryOwners do addEntry WitnessEntryReason.BoundaryScope focus
        for focus in Set.unionMany [facts.Spatial.CodeRoots; facts.Spatial.Required; facts.Spatial.ByScope.Keys |> Set.ofSeq] do
            addEntry WitnessEntryReason.SpatialRoot focus
    | None -> ()
    if failures.Count <> 0 then Error (List.ofSeq failures)
    else
        Ok { Occurrences = occurrences; Entries = List.ofSeq entries; ContextHeaders = headers; Ports = ports
             Contexts = contexts |> Seq.map (fun pair -> pair.Key, pair.Value) |> Map.ofSeq; BindingUses = bindingUses
             ContextIdentities = contextIdentities
             InterfaceIdentityCandidates = Set.difference interfaces history
             HistoricalIdentities = Set.difference history (bodies.Keys |> Set.ofSeq)
             Support = support }

let projectWithBudget budget (graph: SemanticGraph) = projectPrepared budget graph.Codata.Value.WitnessEmission graph
let projectWithEmission emission graph = projectPrepared hostedContextBudget (Some emission) graph
let project graph = projectWithBudget hostedContextBudget graph

/// Re-observation under the source owner. Bodies are the exact source records;
/// passive publication never compares/reconstructs source semantic values.
let matches (held: WitnessLiveScopePlan) (current: WitnessLiveScopePlan) =
    held.Support = current.Support && held.ContextIdentities = current.ContextIdentities &&
    held.Entries = current.Entries && held.ContextHeaders = current.ContextHeaders && held.Ports = current.Ports && held.Contexts = current.Contexts && held.BindingUses = current.BindingUses &&
    held.InterfaceIdentityCandidates = current.InterfaceIdentityCandidates && held.HistoricalIdentities = current.HistoricalIdentities &&
    (held.Occurrences.Keys |> Set.ofSeq) = (current.Occurrences.Keys |> Set.ofSeq) &&
    (held.Occurrences |> Map.forall (fun id row ->
        let actual = current.Occurrences[id]
        obj.ReferenceEquals(row.Body, actual.Body) && row.Children = actual.Children && row.Contexts = actual.Contexts))

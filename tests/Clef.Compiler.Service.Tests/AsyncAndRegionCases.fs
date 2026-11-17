namespace Clef.Compiler.Service.Tests

open System.Diagnostics
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Publication = Clef.Compiler.PSGSaturation.Publication.RevisionPublication
module Discharge = Clef.Compiler.Nanopass.ObligationDischarge

module private AsyncAndRegionFixture =
    let private byteState : NumericRepresentation =
        { Name = "uint8"; Capability = "native"; Family = "uint"; Bits = 8
          MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap" }

    let platform =
        { IntrinsicWriteFixture.platform with
            Representations = IntrinsicWriteFixture.platform.Representations.Add(byteState.Name, byteState) }

    /// The selected platform declares one region memory space: 4096-byte
    /// pages within a 1 MiB budget. Region capacity is read from it.
    let authority =
        IntrinsicWriteFixture.authority
            .Replace(
                "Representations = [| ",
                "Representations = [| { Name = \"uint8\"; Capability = \"native\"; Family = \"uint\"; Bits = 8; MinMagnitude = \"0\"; MaxMagnitude = \"255\"; Boundary = \"wrap\" }; ")
            .Replace(
                "let rodata =",
                "let regionPages = { Name = \"region\"; Kind = \"region\"; Capacity = 1048576; Alignment = 16; Granularity = 4096; Growth = \"up\"; Access = \"rw\"; Base = None }\nlet rodata =")
            .Replace("Spaces = [| rodata |]", "Spaces = [| rodata; regionPages |]")

    let checkRaw (name: string) (body: string) =
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwith (sprintf "Parse failed: %d errors" errors.Length)
        Clef.Compiler.NativeService.checkParsedInputsWithPlatform
            [ parse authority "write-authority.clef"; parse body (name + ".clef") ]
            (Some platform)

    let check (name: string) (body: string) =
        let result = checkRaw name body
        DimensionalCases.noErrors result
        result.Graph

    /// Publication alone. `wellFormed` states the integrity requirement.
    let publish (graph: SemanticGraph) =
        match Publication.publish graph with
        | Ok revision -> revision
        | Error failures ->
            failwith (sprintf "Publication refused: %d failures" failures.Length)

    let wellFormed (revision: Fidelity.PSG.Revision) =
        let violations = Fidelity.PSG.Integrity.check revision
        Assert.True(violations.IsEmpty, Fidelity.PSG.Integrity.describe violations)

    let clefId (Fidelity.PSG.NodeId value) = NodeId value
    let psgId (NodeId value) = Fidelity.PSG.NodeId value

    /// Discharge the exact settled claim the graph carries for a published
    /// obligation: the claim is read from its graph citizen, never re-encoded.
    let solveObligation (graph: SemanticGraph) (obligation: Fidelity.PSG.ObligationInfo) =
        let settled =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Obligation info when info.Id = obligation.Id -> Some info
                | _ -> None)
            |> Seq.distinct
            |> Seq.toList
        let info = Assert.Single(settled)
        let start = ProcessStartInfo("cvc5")
        start.ArgumentList.Add "--lang=smt2"
        start.ArgumentList.Add "--tlimit-per=2000"
        start.RedirectStandardInput <- true
        start.RedirectStandardOutput <- true
        start.RedirectStandardError <- true
        start.UseShellExecute <- false
        use solver = new Process(StartInfo = start)
        Assert.True(solver.Start())
        let output, errors = solver.StandardOutput.ReadToEndAsync(), solver.StandardError.ReadToEndAsync()
        solver.StandardInput.Write(Discharge.smtLib [ info ])
        solver.StandardInput.Close()
        if not (solver.WaitForExit 5000) then
            solver.Kill(true)
            failwith "cvc5 solver timed out"
        Assert.True(solver.ExitCode = 0, errors.GetAwaiter().GetResult())
        output.GetAwaiter().GetResult().Trim()

    /// The value-bearing participants of the published async and region rows.
    let valueParticipants (revision: Fidelity.PSG.Revision) : Fidelity.PSG.NodeId list =
        [ for row in revision.Codata.AsyncFormations.Values do
              yield row.Formation
              yield row.Body
              yield row.ResultStorage
              yield! row.CapturedBindings
          for row in revision.Codata.AsyncActivations.Values do
              yield row.Site
              yield row.Formation
              yield row.ResultTarget
              yield row.CompletionTarget
          for row in revision.Codata.AsyncSuspensions.Values do
              yield row.Site
              yield row.AwaitedSource
              yield! row.LiveSlots
              yield! row.InitializedSlots
              yield row.BindResumeTarget
              yield row.CompletionTarget
              for retention in row.SpanningRetentions do
                  yield retention.Binding
                  yield retention.BackingRegion
          for row in revision.Codata.AsyncOrchestrations.Values do
              yield row.Site
              yield! row.Children
              yield row.ResultStorage
          for row in revision.Codata.RegionAllocations.Values do
              yield row.Region
              yield! row.AllocatedValues
              for (_, release) in row.ScopeExitReleases do
                  yield release
          for row in revision.Codata.RegionCallPassings.Values do
              yield row.Site
              yield row.Call
              yield row.Region
              yield! row.CalleeReleases
          for row in revision.Codata.RegionCopyEndpoints.Values do
              yield row.Site
              yield row.EscapingValue
              yield row.SourceRegion
              yield row.SourceView
              yield! Option.toList row.DestinationRegion
              yield row.DestinationStorage ]
        |> List.distinct

    let private isFrameOperation (node: SemanticNode) =
        match node.Kind with
        | SemanticKind.ContinuationAllocate _ | SemanticKind.ContinuationStorage _
        | SemanticKind.FrameRead _ | SemanticKind.FrameWrite _ | SemanticKind.FrameBorrow _
        | SemanticKind.ContinuationDispatch _ -> true
        | _ -> false

    /// The frame identity a frame operand is published under.
    let private frameOf (revision: Fidelity.PSG.Revision) (operand: NodeId) =
        revision.Codata.SequenceOrigins.TryFind (psgId operand)
        |> Option.bind (fun owner -> revision.Codata.ContinuationFrames.TryFind owner)

    /// The Baker-elaborated continuation operations of every async frame: the
    /// allocation, every frame access addressed through it and every
    /// resumption dispatch selected by a read of the frame's state slot.
    let frameOperations (graph: SemanticGraph) (revision: Fidelity.PSG.Revision) : SemanticNode list =
        let frames = revision.Codata.AsyncFormations.Values |> Seq.map _.Frame |> Set.ofSeq
        graph.Nodes.Values
        |> Seq.filter (fun node ->
            node.IsReachable &&
            (match node.Kind with
             | SemanticKind.ContinuationAllocate owner -> frames.Contains (psgId owner)
             | SemanticKind.FrameRead(frame, _) | SemanticKind.FrameBorrow(frame, _) | SemanticKind.FrameWrite(frame, _, _) ->
                 frameOf revision frame |> Option.exists (fun row -> frames.Contains row.Owner)
             | SemanticKind.ContinuationDispatch(selector, _, _) ->
                 (match graph.Nodes[selector].Kind with
                  | SemanticKind.FrameRead(frame, _) -> frameOf revision frame |> Option.exists (fun row -> frames.Contains row.Owner)
                  | _ -> false)
             | _ -> false))
        |> Seq.sortBy (fun node -> NodeId.value node.Id)
        |> Seq.toList

    /// The continuation frame of every formation is explicit in its deferred
    /// callable: allocation, capture and state stores at entry, and for each
    /// suspension cut that resumes a computation the state transition, the
    /// stores of the retained locals and a resumption dispatch whose case
    /// region reloads every retained slot. Each operation names a slot of the
    /// published frame it is addressed through.
    let assertFrameElaboration (graph: SemanticGraph) (revision: Fidelity.PSG.Revision) =
        let operations = frameOperations graph revision
        let rec within (root: NodeId) (seen: Set<NodeId>) =
            if seen.Contains root then seen
            else graph.Nodes[root].Children |> List.fold (fun found child -> within child found) (seen.Add root)
        for formation in revision.Codata.AsyncFormations.Values do
            let frame = revision.Codata.ContinuationFrames[formation.Frame]
            let callable = graph.Nodes[clefId formation.Callable]
            let entry =
                match callable.Kind with
                | SemanticKind.Lambda(_, entry, _, _, _) -> graph.Nodes[entry]
                | _ -> failwith "The formation's callable is not a Lambda."
            let entryItems =
                match entry.Kind with
                | SemanticKind.Sequential items -> items
                | _ -> failwith "The deferred callable has no entry block."
            // Entry: the frame binding of this formation's allocation.
            let allocation =
                match graph.Nodes[List.head entryItems] with
                | { Kind = SemanticKind.Binding(_, false, _, _); Children = [ value ] } ->
                    (match graph.Nodes[value].Kind with
                     | SemanticKind.ContinuationAllocate owner when psgId owner = formation.Frame -> value
                     | _ -> failwith "The entry block does not allocate the formation's frame.")
                | _ -> failwith "The entry block does not begin with the frame binding."
            Assert.True(frame.Bytes > 0)
            Assert.Equal(Some Fidelity.PSG.EscapeKind.StackScoped, revision.Codata.Escapes.TryFind (psgId allocation))
            Assert.Equal(Some formation.Frame, revision.Codata.SequenceOrigins.TryFind (psgId allocation))
            let scope = within callable.Id Set.empty
            let own = operations |> List.filter (fun node -> scope.Contains node.Id)
            let writes =
                own |> List.choose (fun node ->
                    match node.Kind with
                    | SemanticKind.FrameWrite(_, slot, value) -> Some(node.Id, psgId slot, value)
                    | _ -> None)
            let reads =
                own |> List.choose (fun node ->
                    match node.Kind with
                    | SemanticKind.FrameRead(_, slot) -> Some(node.Id, psgId slot)
                    | _ -> None)
            let slots = frame.Slots |> List.map _.Source |> Set.ofList
            // Every access names a slot of the published frame.
            for (_, slot, _) in writes do Assert.Contains(slot, slots)
            for (_, slot) in reads do Assert.Contains(slot, slots)
            // The frame write is the only parent of the value it stores: no
            // block sequences that value a second time.
            for (id, _, value) in writes do
                let parents =
                    graph.Nodes.Values
                    |> Seq.filter (fun node -> node.IsReachable && List.contains value node.Children)
                    |> Seq.map _.Id
                    |> Seq.toList
                Assert.Equal<NodeId list>([ id ], parents)
                Assert.Equal(Some id, graph.Nodes[value].Parent)
            // Capture and state initialization at entry.
            Assert.Contains(frame.State, slots)
            for capture in formation.CapturedBindings do
                if slots.Contains capture then
                    Assert.Contains(writes, fun (id, slot, _) -> slot = capture && List.contains id entryItems)
            Assert.Contains(writes, fun (id, slot, _) -> slot = frame.State && List.contains id entryItems)
            Assert.Equal<(Fidelity.PSG.NodeId * Fidelity.PSG.NodeId) list>(
                writes |> List.filter (fun (id, slot, _) -> List.contains id entryItems && slot <> frame.State) |> List.map (fun (_, slot, value) -> slot, psgId value),
                frame.Initializers)
            let cuts = revision.Codata.AsyncSuspensions.Values |> Seq.filter (fun cut -> cut.Formation = formation.Formation) |> Seq.toList
            Assert.Equal<int list>(cuts |> List.map _.StateOrdinal |> List.sort, frame.ResumeStates)
            let dispatches =
                own |> List.choose (fun node ->
                    match node.Kind with
                    | SemanticKind.ContinuationDispatch(selector, cases, _) -> Some(node, selector, cases)
                    | _ -> None)
            for cut in cuts do
                // The state transition of the cut: a store of its ordinal.
                Assert.Contains(writes, fun (_, slot, value) ->
                    slot = frame.State &&
                    (match graph.Nodes[value].Kind with
                     | SemanticKind.Literal(NativeLiteral.Int(ordinal, _)) -> ordinal = int64 cut.StateOrdinal
                     | _ -> false))
                let resumed = dispatches |> List.filter (fun (_, _, cases) -> cases |> List.exists (fun (ordinal, _) -> ordinal = cut.StateOrdinal))
                let continues = revision.Nodes.ContainsKey cut.Continuation && cut.Continuation <> cut.CompletionTarget
                if continues then
                    let (_, selector, cases) = Assert.Single(resumed)
                    // The selector reads the state slot; the case region reloads
                    // every retained slot and holds the resumed computation.
                    Assert.Contains(reads, fun (id, slot) -> id = selector && slot = frame.State)
                    let region = cases |> List.find (fun (ordinal, _) -> ordinal = cut.StateOrdinal) |> snd
                    let regionNodes = within region Set.empty
                    Assert.Contains(clefId cut.Continuation, regionNodes)
                    for slot in cut.LiveSlots do
                        Assert.Contains(reads, fun (id, read) -> read = slot && regionNodes.Contains id)
                        Assert.Contains(writes, fun (id, written, _) -> written = slot && not (regionNodes.Contains id))
                else
                    Assert.Empty(resumed)
                    Assert.Empty(cut.LiveSlots)
        operations

    /// The operation a source array access guards: the access is the block of
    /// its operands, its bounds requirement and the guarded operation.
    let private guardedAccess (graph: SemanticGraph) (access: SemanticNode) =
        match access.Kind with
        | SemanticKind.Sequential items ->
            (match List.rev items with
             | operation :: required :: _ ->
                 (match graph.Nodes[required].Kind, graph.Nodes[operation].Kind with
                  | SemanticKind.Require _, (SemanticKind.IndexGet _ | SemanticKind.IndexSet _) -> graph.Nodes[operation]
                  | _ -> failwith "A source array access does not end with its bounds requirement and guarded operation.")
             | _ -> failwith "A source array access has no bounds requirement.")
        | _ -> failwith "A source array access is not elaborated with its bounds guard."

    /// The block of one orchestration's join: the binding of the join's
    /// result array, the guarded store of each child result and the value.
    let private joinBlock (graph: SemanticGraph) (row: Fidelity.PSG.AsyncOrchestration) =
        let parentOf (node: SemanticNode) =
            match node.Parent with
            | Some parent -> graph.Nodes[parent]
            | None -> failwith "An elaborated orchestration operation has no parent."
        let activations = row.Children |> List.map (fun child -> graph.Nodes[clefId child])
        // Each child activation is the stored value of one guarded store.
        let stores =
            activations |> List.map (fun activation ->
                match parentOf activation with
                | { Kind = SemanticKind.IndexSet(_, _, value) } as store when value = activation.Id -> store
                | _ -> failwith "A child activation is not the stored value of a result store.")
        let accesses = stores |> List.map parentOf
        for (access, store) in List.zip accesses stores do
            Assert.Equal(store.Id, (guardedAccess graph access).Id)
        match accesses |> List.map _.Parent |> List.distinct with
        | [ Some block ] -> graph.Nodes[block], activations, stores, accesses
        | _ -> failwith "The result stores of an orchestration do not share one block."

    /// The child array of an orchestration: the binding its site reads, the
    /// elements of the bound array expression and the block that sequences the
    /// binding.
    let private childArray (graph: SemanticGraph) (row: Fidelity.PSG.AsyncOrchestration) =
        let tasks =
            match graph.Nodes[clefId row.Site].Kind with
            | SemanticKind.Application(_, [ operand ]) ->
                (match graph.Nodes[operand].Kind with
                 | SemanticKind.VarRef(_, Some definition) -> graph.Nodes[definition]
                 | _ -> failwith "The orchestration's child array is not read through a binding.")
            | _ -> failwith "The orchestration site is not an application to its child array."
        let elements =
            match tasks.Children |> List.map (fun value -> graph.Nodes[value].Kind) with
            | [ SemanticKind.ArrayExpr elements ] -> elements
            | _ -> failwith "The child array's binding does not hold an array expression."
        let items =
            match tasks.Parent |> Option.map (fun block -> graph.Nodes[block].Kind) with
            | Some (SemanticKind.Sequential items) -> items
            | _ -> failwith "The child array's binding is not sequenced by a block."
        tasks, elements, items

    /// The Baker-elaborated operations of every orchestration (A-03): the
    /// binding of each child and the child array's reference to it, and the
    /// block that binds the join's result array with everything it holds
    /// except the orchestration the binding holds: each child activation
    /// with its activator and protocol anchors, the read of each child
    /// through its binding, and the guarded store of each result into the
    /// result array.
    let orchestrationOperations (graph: SemanticGraph) (revision: Fidelity.PSG.Revision) : SemanticNode list =
        let rec within (excluded: NodeId) (root: NodeId) (seen: Set<NodeId>) =
            if seen.Contains root || root = excluded then seen
            else graph.Nodes[root].Children |> List.fold (fun found child -> within excluded child found) (seen.Add root)
        [ for row in revision.Codata.AsyncOrchestrations.Values do
              let block, _, _, _ = joinBlock graph row
              let storage =
                  match block.Kind with
                  | SemanticKind.Sequential (results :: _) -> List.head graph.Nodes[results].Children
                  | _ -> failwith "The join block does not begin with the binding of the result array."
              yield! within storage block.Id Set.empty |> Set.toList |> List.map (fun id -> graph.Nodes[id])
              let _, elements, _ = childArray graph row
              for element in elements |> List.map (fun id -> graph.Nodes[id]) do
                  yield element
                  match element.Kind with
                  | SemanticKind.VarRef(_, Some binding) -> yield graph.Nodes[binding]
                  | _ -> () ]
        |> List.filter _.IsReachable
        |> List.distinctBy _.Id
        |> List.sortBy (fun node -> NodeId.value node.Id)

    /// The work items of every orchestration are explicit in the PSG. Each
    /// child computation is bound once, before the child array's binding, and
    /// is the array's element at its result ordinal. The join is a block that
    /// binds a constructed result array; each child activation applies an
    /// activator of its own to the child read through its binding, and its
    /// result is stored under a bounds guard into the result array at that
    /// ordinal, in result order. Each child activation has the activation row
    /// of its child's formation, and no reachable Async.RunSynchronously
    /// application is without an activation row.
    let assertOrchestrationElaboration (graph: SemanticGraph) (revision: Fidelity.PSG.Revision) =
        for node in graph.Nodes.Values do
            match node.Kind with
            | SemanticKind.Application(activator, _) when node.IsReachable ->
                match graph.Nodes[activator].Kind with
                | SemanticKind.Intrinsic info when info.FullName = "Async.RunSynchronously" ->
                    Assert.True(revision.Codata.AsyncActivations.ContainsKey (psgId node.Id),
                                sprintf "The Async.RunSynchronously application %d has no activation row." (NodeId.value node.Id))
                | _ -> ()
            | _ -> ()
        for row in revision.Codata.AsyncOrchestrations.Values do
            Assert.NotEmpty(row.Children)
            Assert.Equal(row.ResultCapacity, row.Children.Length)
            Assert.Equal<Fidelity.PSG.NodeId list>(row.Children, row.ResultOrdering |> List.sortBy fst |> List.map snd)
            for (before, after) in row.WorkDependencies do
                Assert.Contains(before, row.Children)
                Assert.Contains(after, row.Children)
            let tasks, elements, taskItems = childArray graph row
            Assert.Equal(row.Children.Length, elements.Length)
            // Result delivery: the guarded stores are the items of one block, in
            // result order, between the binding of the result array and the block's value.
            let block, activations, stores, accesses = joinBlock graph row
            Assert.True(block.IsReachable)
            let results, value =
                match block.Kind with
                | SemanticKind.Sequential (results :: rest) when List.length rest = accesses.Length + 1 ->
                    Assert.Equal<NodeId list>(accesses |> List.map _.Id, List.take accesses.Length rest)
                    graph.Nodes[results], graph.Nodes[List.last rest]
                | _ -> failwith "The join block is not the binding, the result stores and the value."
            // The binding holds the result storage of the orchestration: the
            // orchestration itself, with no activation applied to it.
            let storage =
                match results.Kind, results.Children with
                | SemanticKind.Binding(_, false, _, _), [ storage ] -> graph.Nodes[storage]
                | _ -> failwith "The join block does not begin with the binding of the result array."
            Assert.True(storage.IsReachable)
            Assert.Equal(clefId row.Site, storage.Id)
            Assert.Equal(Some results.Id, storage.Parent)
            Assert.True(match value.Kind with SemanticKind.VarRef(_, Some definition) -> definition = results.Id | _ -> false)
            let participants = row.Participants |> List.map _.Node
            Assert.Contains(psgId storage.Id, participants)
            Assert.Contains(psgId results.Id, participants)
            for (ordinal, (store, access)) in List.indexed (List.zip stores accesses) do
                Assert.Contains(psgId access.Id, participants)
                Assert.True(
                    (match store.Kind with
                     | SemanticKind.IndexSet(target, index, _) ->
                         (match graph.Nodes[target].Kind, graph.Nodes[index].Kind with
                          | SemanticKind.VarRef(_, Some definition), SemanticKind.Literal(NativeLiteral.Int(position, _)) ->
                              definition = results.Id && position = int64 ordinal
                          | _ -> false)
                     | _ -> false),
                    "A result store does not address the join's result array at its result ordinal.")
            for (ordinal, activation) in List.indexed activations do
                Assert.True(activation.IsReachable)
                let activator, computation =
                    match activation.Kind with
                    | SemanticKind.Application(activator, [ computation ]) -> graph.Nodes[activator], graph.Nodes[computation]
                    | _ -> failwith "A child work item is not an activation applied to its child."
                Assert.True(
                    (match activator.Kind with
                     | SemanticKind.Intrinsic info -> info.FullName = "Async.RunSynchronously"
                     | _ -> false),
                    "A child work item is not applied by an activation intrinsic.")
                Assert.Equal(Some activation.Id, activator.Parent)
                // The child is read through its own binding. That binding is
                // sequenced before the child array's binding, and the array's
                // element at the child's result ordinal is a reference to it.
                let child =
                    match computation.Kind with
                    | SemanticKind.VarRef(_, Some definition) -> graph.Nodes[definition]
                    | _ -> failwith "A child activation does not read its child through a binding."
                Assert.True(match child.Kind with SemanticKind.Binding(_, false, _, _) -> child.Children.Length = 1 | _ -> false)
                Assert.True(
                    (match graph.Nodes[List.item ordinal elements].Kind with
                     | SemanticKind.VarRef(_, Some definition) -> definition = child.Id
                     | _ -> false),
                    "The child array's element at the result ordinal is not a reference to the child's binding.")
                Assert.True(
                    (match List.tryFindIndex ((=) child.Id) taskItems, List.tryFindIndex ((=) tasks.Id) taskItems with
                     | Some bound, Some array -> bound < array
                     | _ -> false),
                    "A child's binding is not sequenced before the child array's binding.")
                Assert.Contains(psgId child.Id, participants)
                // The activation row of the child's formation, with the
                // result and completion targets of the child's own activator.
                let settled = revision.Codata.AsyncActivations[psgId activation.Id]
                Assert.True(revision.Codata.AsyncFormations.ContainsKey settled.Formation)
                Assert.Contains(clefId settled.ResultTarget, activator.Children)
                Assert.Contains(clefId settled.CompletionTarget, activator.Children)
                Assert.NotEmpty(settled.Obligations)

    /// The region lifecycle operations of the published region rows, from the
    /// creation of each region to its scope-exit releases: the creation, the
    /// allocated values, the call passings, the copy endpoints and the releases.
    let regionOperations (graph: SemanticGraph) (revision: Fidelity.PSG.Revision) : SemanticNode list =
        [ for row in revision.Codata.RegionAllocations.Values do
              yield row.Region
              yield! row.AllocatedValues
              for (_, release) in row.ScopeExitReleases do
                  yield release
          for row in revision.Codata.RegionCallPassings.Values do
              yield row.Site
              yield row.Call
              yield! row.CalleeReleases
          for row in revision.Codata.RegionCopyEndpoints.Values do
              yield row.Site
              yield row.DestinationStorage ]
        |> List.distinct
        |> List.map (fun id -> graph.Nodes[clefId id])
        |> List.filter _.IsReachable
        |> List.sortBy (fun node -> NodeId.value node.Id)

    /// Every value-bearing participant and every elaborated frame or
    /// orchestration operation has its settled alias target, value shape and
    /// occurrence representation in the revision, and an SSA assignment under
    /// both operating regimes.
    let assertSettledValues (graph: SemanticGraph) (revision: Fidelity.PSG.Revision) (operations: SemanticNode list) =
        let participants = valueParticipants revision @ (operations |> List.map (fun node -> psgId node.Id)) |> List.distinct
        Assert.NotEmpty(participants)
        let callable = revision.Emission.Callable
        for id in participants do
            Assert.True(revision.Nodes.ContainsKey id, sprintf "Participant %d is not an occurrence of the revision." (NodeId.value (clefId id)))
            Assert.True(callable.ValueShapes.ContainsKey id, sprintf "Participant %d has no settled value shape." (NodeId.value (clefId id)))
            Assert.True(revision.Emission.Numeric.OccurrenceRepresentations.ContainsKey id, sprintf "Participant %d has no settled occurrence representation." (NodeId.value (clefId id)))
            // The alias target is settled and is itself a settled endpoint.
            match callable.AliasTargets.TryFind id with
            | Some target -> Assert.Equal(Some target, callable.AliasTargets.TryFind target)
            | None -> Assert.Fail(sprintf "Participant %d has no settled alias target." (NodeId.value (clefId id)))
        // Full release regime: a single pass from the settled graph.
        let release = Clef.Compiler.Nanopass.SSAAssignment.normalize graph
        let releasePlan = release.Codata.Value.SSAAssignment.Value
        Assert.Equal<Map<NodeId, SSAId list>>(graph.Codata.Value.SSAAssignment.Value.Assignments, releasePlan.Assignments)
        for id in participants do
            Assert.True(releasePlan.Assignments.TryFind (clefId id) |> Option.exists (fun slots -> not slots.IsEmpty),
                        sprintf "Participant %d has no SSA assignment in the release regime." (NodeId.value (clefId id)))
        // Differential regime: the elaborated frame and orchestration
        // operations and the region lifecycle operations are the delta cone,
        // so every acceptance case re-assigns a non-empty cone. Occurrences
        // outside the cone keep their identities and their exact prior
        // assignments; every assignment in the cone is fresh and above every
        // prior one.
        let lifecycle = regionOperations graph revision
        let coneNodes = (operations @ lifecycle) |> List.distinctBy _.Id
        let cone = coneNodes |> List.map _.Id |> Set.ofList
        Assert.NotEmpty(cone)
        let every = graph.Nodes |> Map.keys |> Set.ofSeq
        let retained = Set.difference every cone
        let alignment = retained |> Seq.map (fun id -> id, id) |> Map.ofSeq
        let reconciled, plan = Clef.Compiler.Nanopass.SSAAssignment.reconcileAndAssign graph alignment retained graph
        let current (id: NodeId) = plan.NodeRemap[id]
        // The plan carries one high-water mark, NodeHighWater, and an SSA
        // value is SSAId(node, ordinal). The prior register high-water mark is
        // the highest node any prior SSA value names; the prior frame-slot
        // high-water mark is the highest node a prior SSA value of a frame
        // slot or frame access names.
        let registersOf (ids: seq<NodeId>) =
            ids |> Seq.collect (fun id -> releasePlan.Assignments[id]) |> Seq.map _.Node |> Seq.fold max 0
        let registerHighWater = registersOf releasePlan.Assignments.Keys
        let frameSlots =
            [ for frame in revision.Codata.ContinuationFrames.Values do
                  yield! frame.Slots |> List.map (fun slot -> clefId slot.Source)
              for node in graph.Nodes.Values do
                  match node.Kind with
                  | SemanticKind.FrameRead _ | SemanticKind.FrameWrite _ | SemanticKind.FrameBorrow _ -> yield node.Id
                  | _ -> () ]
            |> List.filter releasePlan.Assignments.ContainsKey
        let frameSlotHighWater = registersOf frameSlots
        Assert.True(frameSlotHighWater <= registerHighWater && registerHighWater <= releasePlan.NodeHighWater)
        let prior = releasePlan.Assignments |> Map.toSeq |> Seq.collect snd |> Set.ofSeq
        Assert.Equal<Set<NodeId>>(cone |> Set.map current, plan.ReassignedNodes)
        Assert.Equal<Set<NodeId>>(Set.difference (releasePlan.Assignments.Keys |> Set.ofSeq) cone, plan.RetainedNodes)
        Assert.Equal(releasePlan.NodeHighWater + cone.Count, plan.NodeHighWater)
        for id in plan.ReassignedNodes do
            let fresh = plan.Assignments[id]
            Assert.NotEmpty(fresh)
            for ssa in fresh do
                Assert.True(ssa.Node > registerHighWater && ssa.Node > frameSlotHighWater && ssa.Node > releasePlan.NodeHighWater,
                            sprintf "A re-assigned SSA value of node %d does not advance above the prior high-water marks." (NodeId.value id))
                Assert.False(prior.Contains ssa, sprintf "A re-assigned SSA value of node %d reuses a prior SSA value." (NodeId.value id))
        for id in plan.RetainedNodes do
            Assert.Equal(id, current id)
            Assert.Equal<SSAId list>(releasePlan.Assignments[id], plan.Assignments[id])
        for id in participants |> List.map clefId do
            Assert.True(plan.Assignments.TryFind (current id) |> Option.exists (fun slots -> not slots.IsEmpty),
                        sprintf "Participant %d has no SSA assignment in the differential regime." (NodeId.value id))
            if cone.Contains id then
                Assert.True(NodeId.value (current id) > releasePlan.NodeHighWater)
                Assert.Contains(current id, plan.ReassignedNodes)
            else
                Assert.Equal(id, current id)
                Assert.Equal<SSAId list>(releasePlan.Assignments[id], plan.Assignments[id])
                Assert.Contains(id, plan.RetainedNodes)
        // Def-use structure is preserved: every operand of a re-assigned
        // operation is the current identity of the operand it had.
        for operation in coneNodes do
            let moved = reconciled.Nodes[current operation.Id]
            let operands (node: SemanticNode) =
                match node.Kind with
                | SemanticKind.FrameRead(frame, slot) | SemanticKind.FrameBorrow(frame, slot) -> [ frame; slot ]
                | SemanticKind.FrameWrite(frame, slot, value) -> [ frame; slot; value ]
                | SemanticKind.ContinuationDispatch(selector, cases, otherwise) -> selector :: otherwise :: (cases |> List.map snd)
                | SemanticKind.ContinuationAllocate owner | SemanticKind.ContinuationStorage owner -> [ owner ]
                | _ -> node.Children
            Assert.Equal<NodeId list>(operation.Children |> List.map current, moved.Children)
            Assert.Equal<NodeId list>(operands operation |> List.map current, operands moved)
            for operand in operands moved do
                if reconciled.Nodes[operand].IsReachable then
                    Assert.True(plan.Assignments.ContainsKey operand, sprintf "Operand %d of a re-assigned operation has no SSA assignment." (NodeId.value operand))

    /// Every obligation of the published async, region and frame rows is a
    /// current claim of the revision and is discharged by cvc5.
    let assertDischarged (graph: SemanticGraph) (revision: Fidelity.PSG.Revision) =
        let obligations =
            [ for row in revision.Codata.AsyncFormations.Values do
                  yield! row.Obligations
                  yield! revision.Codata.ContinuationFrames[row.Frame].Obligations
              for row in revision.Codata.AsyncActivations.Values do yield! row.Obligations
              for row in revision.Codata.AsyncSuspensions.Values do
                  yield! row.Obligations
                  for retention in row.SpanningRetentions do yield retention.RetirementCheck
              for row in revision.Codata.AsyncOrchestrations.Values do yield! row.SynchronizationObligations
              for row in revision.Codata.RegionAllocations.Values do yield! row.Obligations
              for row in revision.Codata.RegionCallPassings.Values do yield! row.Obligations
              for row in revision.Codata.RegionCopyEndpoints.Values do yield row.EscapeDischargeObligation ]
            |> List.distinct
        Assert.NotEmpty(obligations)
        for id in obligations do
            let claim = revision.CurrentClaims[id]
            Assert.True(
                (match claim.Body with
                 | Fidelity.PSG.ObligationBody.ContinuationLayout _
                 | Fidelity.PSG.ObligationBody.CapacityFits _
                 | Fidelity.PSG.ObligationBody.BorrowedResultViewScope _ -> true
                 | _ -> false),
                sprintf "Obligation %s is not a layout, capacity or retention claim." claim.Id)
            Assert.Equal("unsat", solveObligation graph claim)

    /// The callable carrier settlement of async computation values (clef#163
    /// GA-C163-1). Every formation's value has the callable shape and a carrier
    /// with a settled contract. A formation that captures a binding has a
    /// closure value as its deferred callable, with a published environment
    /// layout; every call of its forming function is given a caller-owned
    /// environment by a factory result account, and every activation or
    /// suspension operand carries that call's environment. Returns the number
    /// of factory calls of each capturing formation.
    let assertCallableCarriers (graph: SemanticGraph) (revision: Fidelity.PSG.Revision) : (Fidelity.PSG.AsyncFormation * int) list =
        let callable = revision.Emission.Callable
        let settledContract (id: Fidelity.PSG.NodeId) =
            Assert.Equal(Some (Fidelity.PSG.CallableValueShape.Callable id), callable.ValueShapes.TryFind id)
            let carrier = callable.Carriers[id]
            match carrier.Contract with
            | Ok contract ->
                Assert.True(callable.Contracts.ContainsKey contract, sprintf "Carrier %d names a contract the revision does not hold." (NodeId.value (clefId id)))
                carrier, callable.Contracts[contract]
            | Error reason -> failwith (sprintf "Carrier %d has no settled contract: %s" (NodeId.value (clefId id)) reason)
        // The operand of every activation and of every suspension.
        let operands =
            [ for row in revision.Codata.AsyncActivations.Values do
                  match graph.Nodes[clefId row.Site].Kind with
                  | SemanticKind.Application(_, [ operand ]) -> yield psgId operand
                  | _ -> failwith "An activation site is not an application of one operand."
              for row in revision.Codata.AsyncSuspensions.Values do
                  yield row.AwaitedSource ]
            |> List.distinct
        [ for row in revision.Codata.AsyncFormations.Values do
              let formation = graph.Nodes[clefId row.Formation]
              let deferred = graph.Nodes[List.last formation.Children]
              let carrier, contract = settledContract row.Formation
              Assert.Equal(row.Callable, carrier.Implementation)
              Assert.Equal(row.Formation, carrier.Formation)
              // An immutable alias preserves the async formation frontier;
              // the deferred callable at the end of its block has another type.
              for alias in revision.Nodes.Values do
                  let aliasesFormation =
                      match alias.Kind with
                      | Fidelity.PSG.SemanticKind.Binding(_, false, _, _) -> alias.Children = [ row.Formation ]
                      | Fidelity.PSG.SemanticKind.VarRef(_, Some binding) ->
                          revision.Nodes.TryFind binding
                          |> Option.exists (fun bound -> bound.Children = [ row.Formation ])
                      | _ -> false
                  if aliasesFormation then
                      Assert.Equal(row.Formation, callable.Carriers[alias.Id].Formation)
              // The deferred callable's unused `_async_unit` formal is omitted
              // in both Ordinary.Parameters and the callable carrier.
              match graph.Nodes[clefId row.Callable].Kind with
              | SemanticKind.Lambda(parameters, _, _, _, _) ->
                  match parameters |> List.tryPick (fun (name, _, formal) -> if name = "_async_unit" then Some (psgId formal) else None) with
                  | Some unitFormal ->
                      let omittedFormals = revision.Emission.Ordinary.Parameters.TryFind row.Callable |> Option.defaultValue Set.empty
                      Assert.Contains(unitFormal, omittedFormals)
                      Assert.Contains(unitFormal, carrier.OmittedParameters)
                  | None -> failwith "The deferred callable of an async formation has no _async_unit parameter."
              | _ -> failwith "The deferred callable of an async formation is not a Lambda."
              match deferred.Kind, row.CapturedBindings with
              | SemanticKind.ClosureValue(code, environment), _ :: _ ->
                  Assert.Equal(row.Callable, psgId code)
                  let slots =
                      match graph.Nodes[environment].Kind with
                      | SemanticKind.EnvironmentCreate(owner, initializers) when owner = deferred.Id -> initializers |> List.map (fst >> psgId)
                      | _ -> failwith "The closure value of a capturing formation has no environment constructor of its own."
                  Assert.Equal<Set<Fidelity.PSG.NodeId>>(Set.ofList row.CapturedBindings, Set.ofList slots)
                  let layout = revision.Codata.EnvironmentLayouts[psgId deferred.Id]
                  Assert.Equal(psgId deferred.Id, layout.Owner)
                  Assert.Equal(row.Callable, layout.Implementation)
                  Assert.Equal(slots.Length, layout.Slots.Length)
                  Assert.Equal<Set<Fidelity.PSG.NodeId>>(Set.ofList slots, layout.Slots |> List.map _.Source |> Set.ofList)
                  Assert.True(layout.Slots |> List.forall _.IsCapture)
                  Assert.True(layout.Bytes > 0 && layout.Alignment > 0)
                  let convention : Fidelity.PSG.CallableEnvironment = { Owner = psgId deferred.Id; Formal = layout.Formal }
                  Assert.Equal(Some convention, carrier.Environment)
                  Assert.Equal(Some layout.Bytes, contract.EnvironmentBytes)
                  // The forming function returns the closure value into storage
                  // its caller allocates: one account and one allocation per call.
                  let accounts =
                      revision.Emission.Storage.EnvironmentFactoryResults.Values
                      |> Seq.filter (fun account -> account.Constructor = psgId environment)
                      |> Seq.toList
                  Assert.NotEmpty(accounts)
                  Assert.Equal(accounts.Length, accounts |> List.map _.Allocation |> List.distinct |> List.length)
                  for account in accounts do
                      Assert.Equal(Some account.Formal, revision.Codata.EnvironmentDestinations.TryFind (psgId environment))
                      Assert.Equal(formation.Parent, Some (clefId account.Factory))
                      Assert.True(
                          (match graph.Nodes[clefId account.Allocation].Kind with
                           | SemanticKind.EnvironmentAllocate owner -> owner = deferred.Id
                           | _ -> false),
                          "A factory call does not allocate the environment of the formation's closure value.")
                      Assert.True(
                          (match graph.Nodes[clefId account.Call].Kind with
                           | SemanticKind.Application(_, arguments) -> List.contains (clefId account.Destination) arguments
                           | _ -> false),
                          "A factory call is not applied to its environment destination.")
                      // The call site carries the code and this call's environment.
                      let site, siteContract = settledContract account.Call
                      Assert.Equal(row.Callable, site.Implementation)
                      Assert.Equal(Some convention, site.Environment)
                      Assert.Equal(Some account.Call, site.EnvironmentValue)
                      Assert.Equal(contract.Identity, siteContract.Identity)
                  // Every activation or suspension of this formation's value
                  // carries the environment of exactly one factory call, and
                  // every factory call reaches one.
                  let calls = accounts |> List.map _.Call |> Set.ofList
                  let consumed =
                      operands |> List.choose (fun operand ->
                          callable.Carriers.TryFind operand
                          |> Option.filter (fun held -> held.Implementation = row.Callable)
                          |> Option.map (fun _ ->
                              let held, heldContract = settledContract operand
                              Assert.Equal(Some convention, held.Environment)
                              Assert.Equal(contract.Identity, heldContract.Identity)
                              match held.EnvironmentValue with
                              | Some value ->
                                  Assert.Contains(value, calls)
                                  value
                              | None -> failwith "An operand of a capturing formation carries no environment value."))
                  Assert.Equal<Set<Fidelity.PSG.NodeId>>(calls, Set.ofList consumed)
                  yield row, accounts.Length
              | _, [] ->
                  // A formation without captures is code alone.
                  Assert.Equal(None, carrier.Environment)
                  Assert.Equal(None, carrier.EnvironmentValue)
                  Assert.Equal(None, contract.EnvironmentBytes)
              | _ ->
                  failwith (sprintf "The capturing formation %d has no closure value as its deferred callable." (NodeId.value formation.Id)) ]

    /// The complete Baker settlement of one acceptance case (clef#163).
    let assertBakerSettled (graph: SemanticGraph) (revision: Fidelity.PSG.Revision) =
        let operations = assertFrameElaboration graph revision
        assertOrchestrationElaboration graph revision
        for cut in revision.Codata.AsyncSuspensions.Values do
            Assert.True(revision.Codata.AsyncActivations.ContainsKey cut.Site,
                        sprintf "The settled AsyncSuspension cut %d has no AsyncActivation row." (NodeId.value (clefId cut.Site)))
        for KeyValue(site, activation) in revision.Codata.AsyncActivations do
            let formation = revision.Codata.AsyncFormations[activation.Formation]
            match graph.Nodes[clefId formation.Callable].Kind with
            | SemanticKind.Lambda(_, bodyId, _, _, _) ->
                let heldWidth id = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph id
                match heldWidth bodyId, heldWidth (clefId site) with
                | Some fromBits, Some toBits when fromBits <> toBits ->
                    let meets = revision.Codata.Meets.TryFind site |> Option.defaultValue []
                    Assert.Contains(meets, fun m -> m.Consumer = site && m.Operand = site && m.From = fromBits && m.To = toBits)
                | _ -> ()
            | _ -> ()
        assertSettledValues graph revision (operations @ orchestrationOperations graph revision)
        assertDischarged graph revision
        operations

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "AsyncAndRegion")>]
type AsyncAndRegionCases() =

    [<Fact>]
    member _.``A-01 (17_BasicAsync): deferred AsyncFormation is distinct from AsyncActivation and settles captures``() =
        let source = """
module BasicAsyncSample

let simpleAsync = async {
    return 42
}

let asyncWithCapture (x: int) = async {
    return x * 2
}

[<EntryPoint>]
let main _ =
    Console.writeln "=== Basic Async Test ==="

    Console.writeln "--- Simple Async ---"
    let v1 = Async.RunSynchronously simpleAsync
    Console.write "Result: "
    Console.writeln (Format.int v1)

    Console.writeln "--- Async with Capture ---"
    let v2 = Async.RunSynchronously (asyncWithCapture 21)
    Console.write "Result: "
    Console.writeln (Format.int v2)

    0
"""
        let graph = AsyncAndRegionFixture.check "17_BasicAsync" source
        let revision = AsyncAndRegionFixture.publish graph
        let operations = AsyncAndRegionFixture.assertBakerSettled graph revision
        // Neither formation has a suspension cut: each callable allocates its
        // frame and stores its captures and state, and dispatches nothing.
        Assert.Equal(2, operations |> List.filter (fun node -> match node.Kind with SemanticKind.ContinuationAllocate _ -> true | _ -> false) |> List.length)
        Assert.Equal(3, operations |> List.filter (fun node -> match node.Kind with SemanticKind.FrameWrite _ -> true | _ -> false) |> List.length)
        Assert.DoesNotContain(operations, fun node -> match node.Kind with SemanticKind.ContinuationDispatch _ | SemanticKind.FrameRead _ -> true | _ -> false)
        Assert.Equal(2, revision.Codata.AsyncFormations.Count)
        Assert.Equal(2, revision.Codata.AsyncActivations.Count)
        let capturedFormations =
            revision.Codata.AsyncFormations.Values
            |> Seq.filter (fun f -> not f.CapturedBindings.IsEmpty)
            |> Seq.toList
        Assert.Single(capturedFormations) |> ignore
        // `asyncWithCapture` captures `x`: its deferred callable is a closure
        // value, and the one call `asyncWithCapture 21` carries its code and a
        // caller-owned environment to the activation.
        let carried = AsyncAndRegionFixture.assertCallableCarriers graph revision
        Assert.Equal<int list>([ 1 ], carried |> List.map snd)
        for form in revision.Codata.AsyncFormations.Values do
            // Formation is deferred: the body belongs to a callable, not to
            // the formation's own evaluation. The callable's entry block
            // initializes the continuation frame and then evaluates the body.
            let callable = graph.Nodes[AsyncAndRegionFixture.clefId form.Callable]
            Assert.True(
                (match callable.Kind with
                 | SemanticKind.Lambda(_, entry, _, _, _) ->
                     (match graph.Nodes[entry].Kind with
                      | SemanticKind.Sequential items -> List.tryLast items = Some (AsyncAndRegionFixture.clefId form.Body)
                      | _ -> false)
                 | SemanticKind.ClosureValue _ -> true
                 | _ -> false),
                "The formation's callable must be a deferred Lambda whose entry block ends with the async body.")
            let owner = graph.Nodes[AsyncAndRegionFixture.clefId form.Formation]
            Assert.DoesNotContain(AsyncAndRegionFixture.clefId form.Body, owner.Children)
            for oblId in form.Obligations do
                Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])
        for act in revision.Codata.AsyncActivations.Values do
            Assert.NotEqual(act.Site, act.Formation)
            Assert.True(revision.Codata.AsyncFormations.ContainsKey act.Formation)
            for oblId in act.Obligations do
                Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])
        AsyncAndRegionFixture.wellFormed revision

    [<Fact>]
    member _.``A-02 (18_AsyncAwait): let! and do! populate AsyncSuspension rows, and a frame change invalidates its dependents``() =
        let template = """
module AsyncAwaitSample

let asyncAdd a b = async {
    return a + b
}

let composed = async {
    let! x = asyncAdd 10 20
    let! y = asyncAdd 1 5
    return RETURN_TAIL
}

let withDo = async {
    do! async { Console.writeln "Step 1" }
    do! async { Console.writeln "Step 2" }
    return 42
}

let spaced (seed: int) = async {
    let k = seed + 1
    let! a = asyncAdd 2 3
    Console.writeln "Between"
    return a + k
}

[<EntryPoint>]
let main _ =
    Console.writeln "=== Async Await Test ==="

    Console.writeln "--- Composed Async ---"
    let v1 = Async.RunSynchronously composed
    Console.write "Result: "
    Console.writeln (Format.int v1)

    Console.writeln "--- Async with do! ---"
    let v2 = Async.RunSynchronously withDo
    Console.write "Result: "
    Console.writeln (Format.int v2)

    Console.writeln "--- Spaced Async ---"
    let v3 = Async.RunSynchronously (spaced 4)
    Console.write "Result: "
    Console.writeln (Format.int v3)

    0
"""
        let source (tail: string) = template.Replace("RETURN_TAIL", tail)
        let graph = AsyncAndRegionFixture.check "18_AsyncAwait" (source "y")
        let revision = AsyncAndRegionFixture.publish graph
        let operations = AsyncAndRegionFixture.assertBakerSettled graph revision
        // Five cuts each resume a computation: five resumption dispatches,
        // each selected by a read of its frame's state slot.
        Assert.Equal(5, operations |> List.filter (fun node -> match node.Kind with SemanticKind.ContinuationDispatch _ -> true | _ -> false) |> List.length)
        Assert.Contains(operations, fun node -> match node.Kind with SemanticKind.FrameRead _ -> true | _ -> false)
        Assert.Contains(operations, fun node -> match node.Kind with SemanticKind.FrameWrite _ -> true | _ -> false)
        Assert.Equal(5, revision.Codata.AsyncSuspensions.Count)
        let ordinals =
            revision.Codata.AsyncSuspensions.Values
            |> Seq.map _.StateOrdinal
            |> Seq.sort
            |> Seq.toList
        Assert.Equal<int list>([0; 0; 0; 1; 1], ordinals)
        // `asyncAdd` captures `a` and `b` and is called three times, each call
        // awaited; `spaced` captures `seed` and is called once and activated.
        let carried = AsyncAndRegionFixture.assertCallableCarriers graph revision
        Assert.Equal<int list>([ 1; 3 ], carried |> List.map snd |> List.sort)
        Assert.Equal<int list>([ 1; 2 ], carried |> List.map (fun (row, _) -> row.CapturedBindings.Length) |> List.sort)
        for susp in revision.Codata.AsyncSuspensions.Values do
            Assert.True(susp.LiveSlots |> List.forall susp.InitializedSlots.Contains)
            for oblId in susp.Obligations do
                Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])

        // `k` is declared before the cut of `spaced` and read two statements
        // after it. It is live across the cut: stored into its frame slot
        // before the cut and reloaded in the cut's dispatch region, and its
        // read there names the reload.
        let isBindingOf (name: string) (slot: Fidelity.PSG.NodeId) =
            match graph.Nodes[AsyncAndRegionFixture.clefId slot].Kind with
            | SemanticKind.Binding(bound, _, _, _) -> bound = name
            | _ -> false
        let spacedCut =
            Assert.Single(revision.Codata.AsyncSuspensions.Values |> Seq.filter (fun cut -> cut.LiveSlots |> List.exists (isBindingOf "k")))
        let kSlot = AsyncAndRegionFixture.clefId (spacedCut.LiveSlots |> List.find (isBindingOf "k"))
        Assert.Contains(AsyncAndRegionFixture.psgId kSlot, spacedCut.InitializedSlots)
        Assert.Contains(revision.Codata.ContinuationFrames[spacedCut.Frame].Slots, fun slot -> slot.Source = AsyncAndRegionFixture.psgId kSlot)
        let rec inside (root: NodeId) (seen: Set<NodeId>) =
            if seen.Contains root then seen
            else graph.Nodes[root].Children |> List.fold (fun found child -> inside child found) (seen.Add root)
        let spacedRegion =
            operations |> List.pick (fun node ->
                match node.Kind with
                | SemanticKind.ContinuationDispatch(selector, [ (ordinal, region) ], _) when ordinal = spacedCut.StateOrdinal ->
                    (match graph.Nodes[selector].Kind with
                     | SemanticKind.FrameRead(_, state) when AsyncAndRegionFixture.psgId state = revision.Codata.ContinuationFrames[spacedCut.Frame].State ->
                         Some (inside region Set.empty)
                     | _ -> None)
                | _ -> None)
        let kStore = Assert.Single(operations |> List.filter (fun node -> match node.Kind with SemanticKind.FrameWrite(_, slot, _) -> slot = kSlot | _ -> false))
        Assert.DoesNotContain(kStore.Id, spacedRegion)
        let kReload = Assert.Single(operations |> List.filter (fun node -> match node.Kind with SemanticKind.FrameRead(_, slot) -> slot = kSlot | _ -> false))
        Assert.Contains(kReload.Id, spacedRegion)
        let kReloadBinding = graph.Nodes[kReload.Parent.Value]
        Assert.True(match kReloadBinding.Kind with SemanticKind.Binding(_, false, _, _) -> kReloadBinding.Children = [ kReload.Id ] | _ -> false)
        let readsIn (definition: NodeId) =
            spacedRegion |> Set.filter (fun id ->
                let node = graph.Nodes[id]
                node.IsReachable && (match node.Kind with SemanticKind.VarRef(_, Some target) -> target = definition | _ -> false))
        Assert.NotEmpty(readsIn kReloadBinding.Id)
        Assert.Empty(readsIn kSlot)

        // Keeping `x` live across the second cut changes the frame; the
        // dependent suspension liveness and its settled layout claim change.
        let changedGraph = AsyncAndRegionFixture.check "18_AsyncAwait_live" (source "x + y")
        let changed = AsyncAndRegionFixture.publish changedGraph
        let changedOperations = AsyncAndRegionFixture.assertBakerSettled changedGraph changed
        let secondCut (rev: Fidelity.PSG.Revision) =
            rev.Codata.AsyncSuspensions.Values
            |> Seq.filter (fun s -> s.StateOrdinal = 1)
            |> Seq.sortByDescending (fun s -> s.LiveSlots.Length)
            |> Seq.head
        let baseCut, changedCut = secondCut revision, secondCut changed
        Assert.Empty(baseCut.LiveSlots)
        Assert.Single(changedCut.LiveSlots) |> ignore
        let xSlotId = List.head changedCut.LiveSlots
        let firstCutOfComposed =
            changed.Codata.AsyncSuspensions.Values
            |> Seq.find (fun s -> s.Formation = changedCut.Formation && s.StateOrdinal = 0)
        Assert.DoesNotContain(xSlotId, firstCutOfComposed.InitializedSlots)
        Assert.Contains(xSlotId, changedCut.InitializedSlots)
        let changedOblId = List.head changedCut.Obligations
        let changedSources = changed.ObligationSources[changedOblId] |> List.concat
        Assert.Contains(changedCut.Frame, changedSources)
        Assert.Contains(xSlotId, changedSources)
        let baseFrame, changedFrame = revision.Codata.ContinuationFrames[baseCut.Frame], changed.Codata.ContinuationFrames[changedCut.Frame]
        // The frame gains the slot of `x`. Slot widths are selected from the
        // analysed ranges, so the padded byte extent need not grow; the frame's
        // settled layout claim changes with the slot set.
        Assert.DoesNotContain(baseFrame.Slots, fun slot -> slot.Source = xSlotId)
        Assert.Contains(changedFrame.Slots, fun slot -> slot.Source = xSlotId)
        Assert.Equal(baseFrame.Slots.Length + 1, changedFrame.Slots.Length)
        Assert.True(changedFrame.Bytes >= baseFrame.Bytes)
        Assert.NotEqual(revision.CurrentClaims[List.head baseFrame.Obligations].Body, changed.CurrentClaims[List.head changedFrame.Obligations].Body)
        let claimBody (rev: Fidelity.PSG.Revision) (cut: Fidelity.PSG.AsyncSuspension) = rev.CurrentClaims[List.head cut.Obligations].Body
        Assert.NotEqual(claimBody revision baseCut, claimBody changed changedCut)
        for oblId in changedCut.Obligations do
            Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation changedGraph changed.CurrentClaims[oblId])
        // `x` is stored before the second cut and reloaded in its resumed
        // computation; the read of `x` there names the reload, not the binding.
        let xSlot = AsyncAndRegionFixture.clefId xSlotId
        Assert.Contains(changedOperations, fun node -> match node.Kind with SemanticKind.FrameWrite(_, slot, _) -> slot = xSlot | _ -> false)
        let reload = changedOperations |> List.find (fun node -> match node.Kind with SemanticKind.FrameRead(_, slot) -> slot = xSlot | _ -> false)
        let reloadBinding = changedGraph.Nodes[reload.Parent.Value]
        Assert.True(match reloadBinding.Kind with SemanticKind.Binding(_, false, _, _) -> reloadBinding.Children = [ reload.Id ] | _ -> false)
        Assert.Contains(changedGraph.Nodes.Values, fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.VarRef(_, Some definition) -> definition = reloadBinding.Id | _ -> false))
        Assert.Equal(Some (AsyncAndRegionFixture.psgId reload.Id), changed.Emission.Callable.AliasTargets.TryFind (AsyncAndRegionFixture.psgId reloadBinding.Id))
        AsyncAndRegionFixture.wellFormed revision
        AsyncAndRegionFixture.wellFormed changed

    [<Fact>]
    member _.``A-02: a suspension cut outside a sequencing block is not settled and reports CCS8403``() =
        let source = """
module UnsequencedCut

let step = async { Console.writeln "Step" }

let gated (flag: bool) = async {
    if flag then
        do! step
    return 1
}

[<EntryPoint>]
let main _ =
    Console.writeln (Format.int (Async.RunSynchronously (gated true)))
    0
"""
        let result = AsyncAndRegionFixture.checkRaw "18_AsyncAwait_unsequenced" source
        let reported = result.Diagnostics |> List.map (fun d -> d.Code + ": " + d.Message) |> String.concat "\n"
        Assert.True(
            result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8403" && d.Message.Contains "is not sequenced by a block"),
            reported)

    [<Fact>]
    member _.``Farscape#220 (CCS8424 & CCS8425): refuses unretained view or invalidated region handle across suspension cut and admits retained region``() =
        let ccs8424Source = """
module BorrowedViewAcrossAwait

let step (x: int) = async { return x + 1 }

[<EntryPoint>]
let main _ =
    let work = async {
        let arr = [| 10; 20; 30 |]
        let view = ReadOnlyView.ofArray arr
        let! a = step 1
        let v0 = view.[0]
        return a + v0
    }
    Async.RunSynchronously work
"""
        let res8424 = AsyncAndRegionFixture.checkRaw "ccs8424" ccs8424Source
        Assert.Contains(res8424.Diagnostics, fun d -> d.Code = "CCS8424")

        let ccs8425Source = """
module InvalidatedRegionAcrossAwait

let step (x: int) = async { return x + 1 }

[<EntryPoint>]
let main _ =
    let work = async {
        let r = Region.create 4
        let buf = Region.alloc<int> r 4
        buf.[0] <- 10
        Region.release r
        let! a = step 1
        return a + buf.[0]
    }
    Async.RunSynchronously work
"""
        let res8425 = AsyncAndRegionFixture.checkRaw "ccs8425" ccs8425Source
        Assert.Contains(res8425.Diagnostics, fun d -> d.Code = "CCS8425")

        // Released after the resumption but before the post-resumption read.
        let ccs8425AfterResume = """
module ReleasedAfterResume

let step (x: int) = async { return x + 1 }

[<EntryPoint>]
let main _ =
    let work = async {
        let r = Region.create 4
        let buf = Region.alloc<int> r 4
        buf.[0] <- 10
        let! a = step 1
        Region.release r
        return a + buf.[0]
    }
    Async.RunSynchronously work
"""
        let resAfter = AsyncAndRegionFixture.checkRaw "ccs8425_after_resume" ccs8425AfterResume
        Assert.Contains(resAfter.Diagnostics, fun d -> d.Code = "CCS8425")

        let retainedSource = """
module RetainedRegionAcrossAwait

let step (x: int) = async { return x + 1 }

[<EntryPoint>]
let main _ =
    let work = async {
        let r = Region.create 4
        let buf = Region.alloc<int> r 4
        buf.[0] <- 10
        let! a = step 1
        let res = a + buf.[0]
        Region.release r
        return res
    }
    Async.RunSynchronously work
"""
        let graphRetained = AsyncAndRegionFixture.check "retained_region_await" retainedSource
        let revRetained = AsyncAndRegionFixture.publish graphRetained
        AsyncAndRegionFixture.assertBakerSettled graphRetained revRetained |> ignore
        let susp = Assert.Single(revRetained.Codata.AsyncSuspensions.Values)
        let retention = Assert.Single(susp.SpanningRetentions)
        Assert.NotEmpty(retention.InvalidatedBy)
        let reg = revRetained.Codata.RegionAllocations[retention.BackingRegion]
        Assert.True(retention.InvalidatedBy |> List.forall (fun release -> reg.ScopeExitReleases |> List.exists (fun (_, r) -> r = release)))
        Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graphRetained revRetained.CurrentClaims[retention.RetirementCheck])
        AsyncAndRegionFixture.wellFormed revRetained

    [<Fact>]
    member _.``A-03 (19_AsyncParallel & Async.Sequential): populates AsyncOrchestration with 5 children and iterates every result``() =
        let source = """
module AsyncParallelSample

let makeAsync (n: int) = async {
    Console.write "Computing "
    Console.writeln (Format.int n)
    return n * n
}

[<EntryPoint>]
let main _ =
    Console.writeln "=== Async Parallel Test ==="

    let tasks = [|
        makeAsync 1
        makeAsync 2
        makeAsync 3
        makeAsync 4
        makeAsync 5
    |]

    Console.writeln "--- Running Parallel ---"
    let results = Async.Parallel tasks |> Async.RunSynchronously

    Console.writeln "--- Results ---"
    for r in results do
        Console.writeln (Format.int r)

    let seqResults = Async.Sequential tasks |> Async.RunSynchronously
    for s in seqResults do
        Console.writeln (Format.int s)

    0
"""
        let graph = AsyncAndRegionFixture.check "19_AsyncParallel" source
        let revision = AsyncAndRegionFixture.publish graph
        AsyncAndRegionFixture.assertBakerSettled graph revision |> ignore
        Assert.Equal(2, revision.Codata.AsyncOrchestrations.Count)
        let parOrch =
            revision.Codata.AsyncOrchestrations.Values
            |> Seq.find (fun o -> o.Mode = Fidelity.PSG.AsyncOrchestrationMode.Parallel)
        Assert.Equal(5, parOrch.Children.Length)
        Assert.Equal(5, parOrch.ResultCapacity)
        Assert.True(parOrch.ElementStride > 0)
        Assert.Empty(parOrch.WorkDependencies)
        let seqOrch =
            revision.Codata.AsyncOrchestrations.Values
            |> Seq.find (fun o -> o.Mode = Fidelity.PSG.AsyncOrchestrationMode.Sequential)
        Assert.Equal(5, seqOrch.Children.Length)
        Assert.Equal(4, seqOrch.WorkDependencies.Length)
        let makeAsyncFormation = Assert.Single(revision.Codata.AsyncFormations.Values)
        // `makeAsync` captures `n`: each of its five calls has an environment
        // of its own, and the ten child activations carry those environments.
        let carried = AsyncAndRegionFixture.assertCallableCarriers graph revision
        Assert.Equal<int list>([ 5 ], carried |> List.map snd)
        // The value of an orchestration is the result storage its join binds:
        // it has no deferred callable and no callable shape.
        for row in revision.Codata.AsyncOrchestrations.Values do
            Assert.Equal(Some (Fidelity.PSG.CallableValueShape.Data row.Site), revision.Emission.Callable.ValueShapes.TryFind row.Site)
            Assert.False(revision.Emission.Callable.Carriers.ContainsKey row.Site)
        // The elaborated A-03 operations: the five children of `tasks` are
        // bound once; each orchestration's join is a block that binds the
        // orchestration's result storage as its result array, with five
        // explicit child activations, each an activation of `makeAsync`'s
        // formation applied to its child read through its binding, and five
        // guarded stores of their results into that result array.
        // `assertBakerSettled` checks their structure and settled tables.
        let orchestrated = AsyncAndRegionFixture.orchestrationOperations graph revision
        let count (select: SemanticNode -> bool) = orchestrated |> List.filter select |> List.length
        // Two join bindings and the five child bindings both orchestrations share.
        Assert.Equal(7, count (fun node -> match node.Kind with SemanticKind.Binding _ -> true | _ -> false))
        Assert.Equal(10, count (fun node -> match node.Kind with SemanticKind.IndexSet _ -> true | _ -> false))
        // One bounds requirement per result store.
        Assert.Equal(10, count (fun node -> match node.Kind with SemanticKind.Require _ -> true | _ -> false))
        Assert.Equal(10, count (fun node ->
            match node.Kind with
            | SemanticKind.Intrinsic info -> info.FullName = "Async.RunSynchronously"
            | _ -> false))
        Assert.Equal(10, revision.Codata.AsyncActivations.Count)
        Assert.Empty(Set.intersect (Set.ofList parOrch.Children) (Set.ofList seqOrch.Children))
        for child in parOrch.Children @ seqOrch.Children do
            Assert.Equal(makeAsyncFormation.Formation, revision.Codata.AsyncActivations[child].Formation)
        // Sequential work dependencies chain the child activations in result order.
        Assert.Equal<(Fidelity.PSG.NodeId * Fidelity.PSG.NodeId) list>(List.pairwise seqOrch.Children, seqOrch.WorkDependencies)
        for oblId in parOrch.SynchronizationObligations @ seqOrch.SynchronizationObligations do
            Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])
        // Each `for .. in` over a result array is a counted loop over all elements.
        let loops =
            graph.Nodes.Values
            |> Seq.filter (fun node -> node.IsReachable && (match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false))
            |> Seq.length
        Assert.True(loops >= 2, "Each array iteration must be a loop over every element.")
        AsyncAndRegionFixture.wellFormed revision

    [<Fact>]
    member _.``A-04 (20_BasicRegion): constructs one release on every exit path and refuses missing or excessive premises``() =
        let source = """
module BasicRegionSample

let processInRegion () =
    let region = Region.create 4
    let buffer = Region.alloc<int> region 100
    buffer.[0] <- 42
    let v = buffer.[0]
    v

let pick (flag: bool) =
    let region = Region.create 1
    let buf = Region.alloc<int> region 4
    buf.[0] <- 7
    let v = buf.[0]
    if flag then v else v + 1

[<EntryPoint>]
let main _ =
    let res = processInRegion ()
    Console.writeln (Format.int res)
    Console.writeln (Format.int (pick true))
    0
"""
        let graph = AsyncAndRegionFixture.check "20_BasicRegion" source
        let revision = AsyncAndRegionFixture.publish graph
        AsyncAndRegionFixture.assertBakerSettled graph revision |> ignore
        AsyncAndRegionFixture.wellFormed revision
        Assert.Equal(2, revision.Codata.RegionAllocations.Count)
        for reg in revision.Codata.RegionAllocations.Values do
            Assert.True(reg.Capacity >= reg.ByteExtent)
            Assert.True(reg.Capacity % 4096L = 0L)
            Assert.NotEmpty(reg.ScopeExitReleases)
            Assert.Equal(reg.ScopeExitPaths.Length, reg.ScopeExitReleases.Length)
            // Every constructed release is a real Region.release operation.
            for (_, release) in reg.ScopeExitReleases do
                let node = graph.Nodes[AsyncAndRegionFixture.clefId release]
                Assert.True(match node.Kind with SemanticKind.Application _ -> true | _ -> false)
            for oblId in reg.Obligations do
                Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[oblId])
        let twoExits = revision.Codata.RegionAllocations.Values |> Seq.find (fun reg -> reg.ScopeExitPaths.Length = 2)
        Assert.Equal(2, twoExits.ScopeExitReleases |> List.map snd |> List.distinct |> List.length)
        let large = revision.Codata.RegionAllocations.Values |> Seq.find (fun reg -> reg.ScopeExitPaths.Length = 1)
        Assert.Equal(16384L, large.Capacity)

        let negSource = """
module InvalidRegionAlloc

[<EntryPoint>]
let main _ =
    let r = Region.create 4
    let buf = Region.alloc<int> r 0
    Region.release r
    0
"""
        let negRes = AsyncAndRegionFixture.checkRaw "20_BasicRegion_neg" negSource
        Assert.Contains(negRes.Diagnostics, fun d -> d.Code = "CCS8405")

        let overSource = """
module OverCapacityRegion

let over () =
    let r = Region.create 1
    let buf = Region.alloc<int> r 1000
    buf.[0] <- 1
    let v = buf.[0]
    Region.release r
    v

[<EntryPoint>]
let main _ =
    Console.writeln (Format.int (over ()))
    0
"""
        let overRes = AsyncAndRegionFixture.checkRaw "20_BasicRegion_over" overSource
        Assert.Contains(overRes.Diagnostics, fun d -> d.Code = "CCS8405")

        let exitReadsSource = """
module ExitReadsRegion

let leaks () =
    let r = Region.create 1
    let b = Region.alloc<int> r 4
    b.[0] <- 1
    b.[0]

[<EntryPoint>]
let main _ =
    Console.writeln (Format.int (leaks ()))
    0
"""
        let exitRes = AsyncAndRegionFixture.checkRaw "20_BasicRegion_exit" exitReadsSource
        Assert.Contains(exitRes.Diagnostics, fun d -> d.Code = "CCS8405")

    [<Fact>]
    member _.``A-05 (21_RegionPassing): settles Borrowed RegionCallPassing for callees and refuses callee release``() =
        let source = """
module RegionPassingSample

let allocateAndFill (r: Region) (size: int) (value: int) =
    let buf = Region.alloc<int> r size
    buf.[0] <- value
    buf

let doubleValues (r: Region) (input: int array) (len: int) =
    let outBuf = Region.alloc<int> r len
    let v = input.[0]
    if v >= 0 && v <= 100 then
        outBuf.[0] <- v * 2
    else
        outBuf.[0] <- 0
    outBuf.[0]

[<EntryPoint>]
let main _ =
    let region = Region.create 4
    let data = allocateAndFill region 10 21
    let doubled = doubleValues region data 10
    Region.release region
    Console.writeln (Format.int doubled)
    0
"""
        let graph = AsyncAndRegionFixture.check "21_RegionPassing" source
        let revision = AsyncAndRegionFixture.publish graph
        AsyncAndRegionFixture.assertBakerSettled graph revision |> ignore
        AsyncAndRegionFixture.wellFormed revision
        let reg = Assert.Single(revision.Codata.RegionAllocations.Values)
        // Both callee allocations draw from the caller's region.
        Assert.True(reg.ByteExtent >= 160L)
        Assert.Equal(2, revision.Codata.RegionCallPassings.Count)
        for pass in revision.Codata.RegionCallPassings.Values do
            Assert.Equal(Fidelity.PSG.RegionOwnershipMode.Borrowed, pass.Mode)
            Assert.Empty(pass.CalleeReleases)
            Assert.True(pass.CalleeLifetimeDepth > pass.CallerLifetimeDepth)

        let negSource = """
module IllegalBorrowedRelease

let release2 (q: Region) =
    Region.release q

let badCallee (r: Region) =
    let alias = r
    release2 alias

[<EntryPoint>]
let main _ =
    let region = Region.create 4
    let b = Region.alloc<int> region 4
    b.[0] <- 1
    badCallee region
    0
"""
        let negRes = AsyncAndRegionFixture.checkRaw "21_RegionPassing_neg" negSource
        Assert.Contains(negRes.Diagnostics, fun d -> d.Code = "CCS8405")

    [<Fact>]
    member _.``A-06 (22_RegionEscape): settles CopyOut and CopyTo RegionCopyEndpoints and refuses uncopied region escapes``() =
        let source = """
module RegionEscapeSample

let processAndExtract (input: int array) =
    let region = Region.create 4
    let len = Array.length input
    let temp = Region.alloc<int> region len
    let v = input.[0]
    if v >= 0 && v <= 100 then
        temp.[0] <- v * v
    else
        temp.[0] <- 0
    let result = Region.copyOut<int> temp len
    Region.release region
    result

let copyBetweenRegions () =
    let dstRegion = Region.create 4
    let srcRegion = Region.create 4
    let temp = Region.alloc<int> srcRegion 4
    temp.[0] <- 99
    let copied = Region.copyTo<int> temp dstRegion 4
    Region.release srcRegion
    let v = copied.[0]
    Region.release dstRegion
    v

[<EntryPoint>]
let main _ =
    let src = [| 7; 8; 9 |]
    let outArr = processAndExtract src
    let v2 = copyBetweenRegions ()
    Console.writeln (Format.int (outArr.[0] + v2))
    0
"""
        let graph = AsyncAndRegionFixture.check "22_RegionEscape" source
        let revision = AsyncAndRegionFixture.publish graph
        AsyncAndRegionFixture.assertBakerSettled graph revision |> ignore
        AsyncAndRegionFixture.wellFormed revision
        Assert.Equal(2, revision.Codata.RegionCopyEndpoints.Count)
        let copyOutRow =
            revision.Codata.RegionCopyEndpoints.Values
            |> Seq.find (fun c -> c.Kind = Fidelity.PSG.RegionCopyKind.CopyOut)
        Assert.True(copyOutRow.DestinationRegion.IsNone)
        Assert.Equal(Some Fidelity.PSG.EscapeKind.EscapesViaReturn, revision.Codata.Escapes.TryFind copyOutRow.DestinationStorage)
        Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[copyOutRow.EscapeDischargeObligation])
        let copyToRow =
            revision.Codata.RegionCopyEndpoints.Values
            |> Seq.find (fun c -> c.Kind = Fidelity.PSG.RegionCopyKind.CopyTo)
        Assert.True(copyToRow.DestinationRegion.IsSome)
        Assert.Equal(32L, copyToRow.SourceByteExtent)
        Assert.Equal("unsat", AsyncAndRegionFixture.solveObligation graph revision.CurrentClaims[copyToRow.EscapeDischargeObligation])

        let negSource = """
module UncopiedRegionEscape

let dangerous (flag: bool) =
    let r = Region.create 4
    let data = Region.alloc<int> r 10
    data.[0] <- 42
    let other = [| 1 |]
    Region.release r
    if flag then data else other

[<EntryPoint>]
let main _ =
    let escaped = dangerous true
    0
"""
        let negRes = AsyncAndRegionFixture.checkRaw "22_RegionEscape_neg" negSource
        Assert.Contains(negRes.Diagnostics, fun d -> d.Code = "CCS8406")

        let overCopy = """
module OverCopy

let over () =
    let r = Region.create 1
    let temp = Region.alloc<int> r 4
    temp.[0] <- 1
    let result = Region.copyOut<int> temp 8
    Region.release r
    result

[<EntryPoint>]
let main _ =
    let a = over ()
    0
"""
        let overRes = AsyncAndRegionFixture.checkRaw "22_RegionEscape_over" overCopy
        Assert.Contains(overRes.Diagnostics, fun d -> d.Code = "CCS8405")

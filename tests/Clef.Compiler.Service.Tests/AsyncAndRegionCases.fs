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
                "let stack = { Name = \"stack\"; Kind = \"stack\"; Capacity = 4096; Alignment = 16; Granularity = 16; Growth = \"down\"; Access = \"rw\"; Base = None }\nlet regionPages = { Name = \"region\"; Kind = \"region\"; Capacity = 1048576; Alignment = 16; Granularity = 4096; Growth = \"up\"; Access = \"rw\"; Base = None }\nlet rodata =")
            .Replace("Spaces = [| rodata |]", "Spaces = [| rodata; stack; regionPages |]")

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

    let regionMemory (revision: Fidelity.PSG.Revision) =
        let memory = revision.Emission.Memory
        let at site =
            match memory.Operations.TryFind site with
            | Some(Fidelity.PSG.MemoryWitnessOperation.Region row) -> row
            | _ -> failwith (sprintf "Missing region memory operation at %d; required=%b; deferred=%b"
                           (let (Fidelity.PSG.NodeId n) = site in n) (memory.Required.Contains site)
                           (revision.Emission.Ordinary.DeferredOnly.Contains site))
        for region in revision.Codata.RegionAllocations.Values do
            let creation = at region.Region
            Assert.Equal(Fidelity.PSG.MemoryRegionKind.Create, creation.Kind)
            Assert.Equal(region.Capacity, creation.Capacity)
            for allocation in region.AllocatedValues do
                match revision.Nodes[allocation].Kind with
                | Fidelity.PSG.SemanticKind.Application _ ->
                    let operation = at allocation
                    Assert.Contains(operation.Kind, [Fidelity.PSG.MemoryRegionKind.Allocate; Fidelity.PSG.MemoryRegionKind.CopyTo])
                | _ -> ()
            for _, release in region.ScopeExitReleases do
                Assert.Equal(Fidelity.PSG.MemoryRegionKind.Release, (at release).Kind)
            // A valid source lifetime row cannot authorize changed geometry.
            let changed = { creation with Offset = creation.Capacity }
            let changedMemory = { memory with Operations = memory.Operations.Add(creation.Site, Fidelity.PSG.MemoryWitnessOperation.Region changed) }
            let tampered =
                { revision with Emission = { revision.Emission with Memory = changedMemory } }
            Assert.Contains(Fidelity.PSG.Integrity.check tampered, fun violation ->
                violation.Part.StartsWith("Emission.Memory.Operations.Region"))
            for _, release in region.ScopeExitReleases do
                let released = at release
                let changed = { released with Operand = Some region.Region }
                let changedMemory = { memory with Operations = memory.Operations.Add(release, Fidelity.PSG.MemoryWitnessOperation.Region changed) }
                let tampered =
                    { revision with Emission = { revision.Emission with Memory = changedMemory } }
                Assert.Contains(Fidelity.PSG.Integrity.check tampered, fun violation ->
                    violation.Part.StartsWith("Emission.Memory.Operations.Region"))
        for copy in revision.Codata.RegionCopyEndpoints.Values do
            let operation = at copy.Site
            Assert.Equal(Some copy.SourceView, operation.Source)
            Assert.Equal(
                (if copy.Kind=Fidelity.PSG.RegionCopyKind.CopyOut then Fidelity.PSG.MemoryRegionKind.CopyOut else Fidelity.PSG.MemoryRegionKind.CopyTo),
                operation.Kind)

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

    /// Identify the source array by its reference to the first activated child.
    let childArray (graph: SemanticGraph) (row: Fidelity.PSG.AsyncOrchestration) =
        let firstChild =
            match graph.Nodes[clefId (List.head row.Children)].Kind with
            | SemanticKind.Application(_, [ operand ]) ->
                match graph.Nodes[operand].Kind with
                | SemanticKind.VarRef(_, Some binding) -> binding
                | _ -> failwith "The first child activation does not read a binding."
            | _ -> failwith "The first child activation has no operand."
        let array, elements =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.ArrayExpr (first :: _ as elements) ->
                    match graph.Nodes[first].Kind with
                    | SemanticKind.VarRef(_, Some binding) when binding = firstChild -> Some(node, elements)
                    | _ -> None
                | _ -> None)
            |> Assert.Single
        let tasks =
            match array.Parent |> Option.map (fun parent -> graph.Nodes[parent]) with
            | Some ({ Kind = SemanticKind.Binding(_, false, _, _); Children = [ value ] } as binding) when value = array.Id -> binding
            | _ -> failwith "The child array is not held by an immutable binding."
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
            // The results binding owns the block containing the source marker
            // and the guarded allocation that the orchestration publishes.
            let storage =
                match results.Kind, results.Children with
                | SemanticKind.Binding(_, false, _, _), [ storage ] -> graph.Nodes[storage]
                | _ -> failwith "The join block does not begin with the binding of the result array."
            Assert.True(storage.IsReachable)
            match storage.Kind with
            | SemanticKind.Sequential [ marker; capacity; guarded ] ->
                Assert.Equal(clefId row.Site, marker)
                match graph.Nodes[guarded].Kind with
                | SemanticKind.Sequential [ requirement; allocation ] ->
                    Assert.True(match graph.Nodes[requirement].Kind with SemanticKind.Require _ -> true | _ -> false)
                    Assert.Equal(clefId row.ResultStorage, allocation)
                    match graph.Nodes[allocation].Kind with
                    | SemanticKind.ArrayAllocate count ->
                        Assert.True(match graph.Nodes[count].Kind with SemanticKind.VarRef(_, Some binding) -> binding = capacity | _ -> false)
                    | _ -> failwith "The published result storage does not allocate its bound capacity."
                | _ -> failwith "The result allocation is not guarded by its bounds requirement."
            | _ -> failwith "The result binding does not own the orchestration marker and guarded allocation."
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
        let reconciled, plan =
            match DimensionalCases.reconcileCheckedPhysical graph alignment retained graph with
            | Result.Ok result -> result
            | Result.Error failure -> failwithf "Expected checked SSA reconciliation: %A" failure
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

    static member private OrchestrationSource finalExpression =
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

"""
        source + "    " + finalExpression + "\n"

    [<Fact>]
    member _.``A-03: the child array binding is sequenced before the returned length after both joins``() =
        let graph = AsyncAndRegionCases.OrchestrationSource "Array.length tasks" |> AsyncAndRegionFixture.check "19_AsyncArrayConsumer"
        let revision = AsyncAndRegionFixture.publish graph
        Assert.Equal(2, revision.Codata.AsyncOrchestrations.Count)
        let tasks, _, items =
            revision.Codata.AsyncOrchestrations.Values |> Seq.map (AsyncAndRegionFixture.childArray graph)
            |> Seq.distinctBy (fun (binding, _, _) -> binding.Id) |> Assert.Single
        let read =
            graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Application(callee, [ argument ]) when node.IsReachable ->
                    match graph.Nodes[callee].Kind, graph.Nodes[argument].Kind with
                    | SemanticKind.Intrinsic info, SemanticKind.VarRef(_, Some definition) -> info.FullName = "Array.length" && definition = tasks.Id
                    | _ -> false
                | _ -> false)
            |> Assert.Single
        let rec blockItem (node: SemanticNode) =
            match node.Parent with
            | Some parent when Some parent = tasks.Parent -> node.Id
            | Some parent -> blockItem graph.Nodes[parent]
            | None -> failwith "The length read is outside the child array's block."
        Assert.Contains(tasks.Id, items)
        Assert.True(List.findIndex ((=) tasks.Id) items < List.findIndex ((=) (blockItem read)) items,
                    "The length read must follow its array binding in the block.")
        AsyncAndRegionFixture.assertOrchestrationElaboration graph revision

    [<Fact>]
    member _.``A-03 (19_AsyncParallel & Async.Sequential): populates AsyncOrchestration with 5 children and iterates every result``() =
        let graph = AsyncAndRegionCases.OrchestrationSource "0" |> AsyncAndRegionFixture.check "19_AsyncParallel"
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

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``A-04 (20_BasicRegion): constructs one release on every exit path and refuses missing or excessive premises``(annotated: bool) =
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
        let source =
            if annotated then
                source.Replace("let processInRegion () =", "let processInRegion () : int =")
                    .Replace("let pick (flag: bool) =", "let pick (flag: bool) : int =")
            else source
        let graph = AsyncAndRegionFixture.check "20_BasicRegion" source
        let revision = AsyncAndRegionFixture.publish graph
        AsyncAndRegionFixture.regionMemory revision
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
        AsyncAndRegionFixture.regionMemory revision
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

        let repeated = """
module RepeatedRegionReservation

let allocate (r: Region) =
    let buffer = Region.alloc<int> r 1
    buffer.[0] <- 10
    buffer

[<EntryPoint>]
let main _ =
    let r = Region.create 1
    let first = allocate r
    let second = allocate r
    first.[0] <- 20
    let value = second.[0]
    Region.release r
    Console.writeln (Format.int value)
    0
"""
        let repeatedResult = AsyncAndRegionFixture.checkRaw "21_RegionPassing_repeated" repeated
        Assert.Contains(repeatedResult.Diagnostics, fun d -> d.Code="CCS8405" && d.Message.Contains("repeatedly"))
        let indirect =
            repeated.Replace("let allocate (r: Region) =", "let invoke f r = f r\n\nlet allocate (r: Region) =")
                    .Replace("let second = allocate r", "let second = invoke allocate r")
        let indirectResult = AsyncAndRegionFixture.checkRaw "21_RegionPassing_indirect" indirect
        Assert.Contains(indirectResult.Diagnostics, fun d -> d.Code="CCS8405" && d.Message.Contains("repeatedly"))

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
        AsyncAndRegionFixture.regionMemory revision
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
        let copy =
            match revision.Emission.Memory.Operations[copyToRow.Site] with
            | Fidelity.PSG.MemoryWitnessOperation.Region operation -> operation
            | _ -> failwith "Missing reached copyTo memory witness."
        let destination = copy.Participants |> List.filter (fun p -> p.Role = Fidelity.PSG.ParticipantRole.RegionHandleOperand) |> Assert.Single
        let sourcePort = copy.Participants |> List.filter (fun p -> p.Role = Fidelity.PSG.ParticipantRole.RegionCopySource) |> Assert.Single
        Assert.Equal((copy.Operand, 1, copy.Site), (Some destination.Node, destination.Ordinal, destination.Group))
        Assert.Equal((copy.Source, 0, copy.Site), (Some sourcePort.Node, sourcePort.Ordinal, sourcePort.Group))
        let mutations =
            [ "operand ordinal", (fun (p: Fidelity.PSG.Participant) -> if p = destination then { p with Ordinal = 0 } else p)
              "operand group", (fun p -> if p = destination then { p with Group = destination.Node } else p)
              "operand roles", (fun p -> if p = destination then { p with Role = sourcePort.Role }
                                         elif p = sourcePort then { p with Role = destination.Role } else p)
              "proof ordinals", (fun p -> if p.Role = Fidelity.PSG.ParticipantRole.RegionProof && p.Ordinal < 2 then { p with Ordinal = 1 - p.Ordinal } else p) ]
        let nodeIds (entries: Fidelity.PSG.Participant list) = entries |> List.map _.Node |> List.sort
        let refusals changed reason =
            let memory = revision.Emission.Memory
            let changedMemory = { memory with Operations = memory.Operations.Add(copy.Site, Fidelity.PSG.MemoryWitnessOperation.Region changed) }
            let revised = { revision with Emission = { revision.Emission with Memory = changedMemory } }
            Fidelity.PSG.Integrity.check revised |> List.filter (fun violation -> violation.Node = Some copy.Site && violation.Reason = reason)
        let results = mutations |> List.map (fun (name, mutate) ->
            let changed = List.map mutate copy.Participants
            Assert.Equal<Fidelity.PSG.NodeId list>(nodeIds copy.Participants, nodeIds changed)
            name, refusals { copy with Participants = changed } "Region participants differ from the reached source ports, ownership groups or ordered obligations." |> List.length)
        Assert.Equal<(string * int) list>(mutations |> List.map (fun (name, _) -> name, 1), results)
        let inventedCopy = { destination with Node = copy.Site; Role = Fidelity.PSG.ParticipantRole.RegionCopyOwner; Ordinal = 0; Group = copy.Site }
        let forgedRows = copy.Participants |> List.collect (fun p ->
            if p.Role = Fidelity.PSG.ParticipantRole.RegionStorageSpace then [p; inventedCopy] else [p])
        Assert.Equal<Set<Fidelity.PSG.NodeId>>(Set.ofList (nodeIds copy.Participants), Set.ofList (nodeIds forgedRows))
        Assert.Single(refusals { copy with CopyOwner = Some copy.Site; Participants = forgedRows } "Region memory operands differ from their exact source application.") |> ignore
        let swappedClaims =
            match copy.Obligations with layout :: capacity :: rest -> capacity :: layout :: rest | _ -> failwith "Missing the copy layout and capacity claims."
        let coherentRoles =
            copy.Participants |> List.map (fun p ->
                if p.Role = Fidelity.PSG.ParticipantRole.RegionProof then { p with Node = swappedClaims[p.Ordinal] } else p)
        Assert.Equal<Fidelity.PSG.NodeId list>(nodeIds copy.Participants, nodeIds coherentRoles)
        Assert.Single(refusals { copy with Obligations = swappedClaims; Participants = coherentRoles } "Region storage lacks its exact ordered layout, capacity or source obligations.") |> ignore
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

    [<Fact>]
    member _.``PSG #40 ReadOnlyArrayView typed participants reject same-ID role, ordinal, and group swaps``() =
        let source = """
module ReadOnlyViewParticipants

[<EntryPoint>]
let main _ =
    let arr = [| 10; 20; 30 |]
    let view = ReadOnlyView.ofArray arr
    let v0 = view.[0]
    if v0 = 10 then 0 else 1
"""
        let graph = AsyncAndRegionFixture.check "psg40_ro_view" source
        let revision = AsyncAndRegionFixture.publish graph
        AsyncAndRegionFixture.wellFormed revision
        let view =
            revision.Emission.Memory.Operations.Values
            |> Seq.choose (function Fidelity.PSG.MemoryWitnessOperation.ReadOnlyArrayView row -> Some row | _ -> None)
            |> Assert.Single
        let siteP = view.Participants |> List.filter (fun p -> p.Role = Fidelity.PSG.ParticipantRole.Site) |> Assert.Single
        let calleeP = view.Participants |> List.filter (fun p -> p.Role = Fidelity.PSG.ParticipantRole.ReadOnlyViewCallee) |> Assert.Single
        let sourceP = view.Participants |> List.filter (fun p -> p.Role = Fidelity.PSG.ParticipantRole.ReadOnlyViewArraySource) |> Assert.Single
        Assert.Equal(3, view.Participants.Length)
        Assert.Equal((view.Site, 0, view.Site), (siteP.Node, siteP.Ordinal, siteP.Group))
        Assert.Equal((0, view.Site), (calleeP.Ordinal, calleeP.Group))
        Assert.Equal((view.Source, 0, view.Site), (sourceP.Node, sourceP.Ordinal, sourceP.Group))
        let nodeIds (entries: Fidelity.PSG.Participant list) = entries |> List.map _.Node |> List.sort
        let reason = "The read-only array view differs from its exact source operand or descriptor carriers."
        let mutations =
            [ "site/callee swap", (fun (p: Fidelity.PSG.Participant) ->
                if p = siteP then { p with Node = calleeP.Node }
                elif p = calleeP then { p with Node = siteP.Node } else p)
              "callee/source role swap", (fun p ->
                if p = calleeP then { p with Role = sourceP.Role }
                elif p = sourceP then { p with Role = calleeP.Role } else p)
              "source ordinal", (fun p -> if p = sourceP then { p with Ordinal = 1 } else p)
              "source group", (fun p -> if p = sourceP then { p with Group = sourceP.Node } else p) ]
        for name, mutate in mutations do
            let changed = List.map mutate view.Participants
            Assert.Equal<Fidelity.PSG.NodeId list>(nodeIds view.Participants, nodeIds changed)
            let memory = revision.Emission.Memory
            let changedMemory = { memory with Operations = memory.Operations.Add(view.Site, Fidelity.PSG.MemoryWitnessOperation.ReadOnlyArrayView { view with Participants = changed }) }
            let revised = { revision with Emission = { revision.Emission with Memory = changedMemory } }
            let hits = Fidelity.PSG.Integrity.check revised |> List.filter (fun v -> v.Node = Some view.Site && v.Reason = reason)
            Assert.True(hits.Length = 1, sprintf "Mutation '%s' expected 1 refusal, got %d" name hits.Length)

    [<Fact>]
    member _.``PSG #40 MemoryRegionRuntime typed participants exclude synthetic BoundaryDomain and reject same-ID swaps``() =
        let runtimeAuthority =
            AsyncAndRegionFixture.authority
                .Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
                .Replace(
                    "let regionPages =",
                    "let heap = { Name = \"heap\"; Kind = \"heap\"; Capacity = 1048576; Alignment = 16; Granularity = 1; Growth = \"up\"; Access = \"rw\"; Base = None }\nlet regionPages =")
                .Replace("Spaces = [| rodata; stack; regionPages |]", "Spaces = [| rodata; stack; regionPages; heap |]")
            + """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference | ReadOnlyReference
type CallConv = | CDecl
type Transfer = | CallerOwns | CalleeOwns | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type RegionMemoryDescriptor = { Space: string; EscapeSpace: string; Acquire: string; Release: string; Address: int; Protection: int; Flags: int; FileDescriptor: int; Offset: int; FailureValue: int; ReleaseSuccess: int; FailureAction: string }

[<FidelityExtern("c", "mmap")>]
let regionAcquire (addr: option<CHandle<unit>>) (len: int) (prot: int) (flags: int) (fd: int) (offset: int) : CHandle<unit> =
    NativeDefault.zeroed ()

let regionAcquireDescriptor: Expr<FunctionDescriptor> =
    <@ { CName = "mmap"
         Parameters =
           [| { Name = "addr"; Type = Pointer 64; PassBy = Value }
              { Name = "len"; Type = Integer (Unsigned, 64); PassBy = Value }
              { Name = "prot"; Type = Integer (Signed, 32); PassBy = Value }
              { Name = "flags"; Type = Integer (Signed, 32); PassBy = Value }
              { Name = "fd"; Type = Integer (Signed, 32); PassBy = Value }
              { Name = "offset"; Type = Integer (Signed, 64); PassBy = Value } |]
         ReturnType = Pointer 64
         CallingConvention = CDecl
         OwnershipTransfer = CallerOwns } @>

[<FidelityExtern("c", "munmap")>]
let regionRelease (addr: CHandle<unit>) (len: int) : int =
    NativeDefault.zeroed ()

let regionReleaseDescriptor: Expr<FunctionDescriptor> =
    <@ { CName = "munmap"
         Parameters =
           [| { Name = "addr"; Type = Pointer 64; PassBy = Value }
              { Name = "len"; Type = Integer (Unsigned, 64); PassBy = Value } |]
         ReturnType = Integer (Signed, 32)
         CallingConvention = CDecl
         OwnershipTransfer = CalleeOwns } @>

let regionMemory: Expr<RegionMemoryDescriptor> =
    <@ { Space = "region"; EscapeSpace = "heap"
         Acquire = "WriteAuthority.regionAcquire"; Release = "WriteAuthority.regionRelease"
         Address = 0; Protection = 3; Flags = 34; FileDescriptor = -1; Offset = 0
         FailureValue = -1; ReleaseSuccess = 0; FailureAction = "Abort" } @>
"""
        let program = """
module RegionRuntimeParticipants

[<EntryPoint>]
let main _ =
    let r = Region.create 4
    let buf = Region.alloc<int> r 4
    buf.[0] <- 42
    let v = buf.[0]
    Region.release r
    if v = 42 then 0 else 1
"""
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "Parse failed: %A" errors
        let platform = { AsyncAndRegionFixture.platform with RuntimeModel = Some RuntimeModel.Libc }
        let checkResult =
            Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                [ parse runtimeAuthority "write-authority.clef"; parse program "region-runtime.clef" ]
                (Some platform)
        DimensionalCases.noErrors checkResult
        let graph = checkResult.Graph
        let revision = AsyncAndRegionFixture.publish graph
        AsyncAndRegionFixture.wellFormed revision

        // Chief Architect ruling PSG #40#11578: synthetic BoundaryDomain anchor stays inside Clef, never in runtime.Participants.
        let boundaryDomainAnchors =
            graph.Edges
            |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryDomain _ -> Some (AsyncAndRegionFixture.psgId edge.Target) | _ -> None)
            |> Set.ofList
        Assert.NotEmpty boundaryDomainAnchors

        let regionOps =
            revision.Emission.Memory.Operations.Values
            |> Seq.choose (function Fidelity.PSG.MemoryWitnessOperation.Region row -> Some row | _ -> None)
            |> Seq.toList
        Assert.NotEmpty regionOps
        let op = regionOps |> List.find (fun row -> row.Kind = Fidelity.PSG.MemoryRegionKind.Create)
        let runtime =
            match op.Runtime with
            | Some rt -> rt
            | None -> failwith "Expected settled MemoryRegionRuntime on Region.create."
        let descriptorPs = runtime.Participants |> List.filter (fun p -> p.Role = Fidelity.PSG.ParticipantRole.RegionRuntimeDescriptor)
        let acquirePs = runtime.Participants |> List.filter (fun p -> p.Role = Fidelity.PSG.ParticipantRole.RegionRuntimeAcquire)
        let releasePs = runtime.Participants |> List.filter (fun p -> p.Role = Fidelity.PSG.ParticipantRole.RegionRuntimeRelease)
        Assert.NotEmpty descriptorPs
        Assert.NotEmpty acquirePs
        Assert.NotEmpty releasePs
        Assert.Equal(descriptorPs.Length + acquirePs.Length + releasePs.Length, runtime.Participants.Length)
        Assert.All(descriptorPs, fun p -> Assert.Equal(runtime.Declaration, p.Group))
        Assert.All(acquirePs, fun p -> Assert.Equal(runtime.Acquire, p.Group))
        Assert.All(releasePs, fun p -> Assert.Equal(runtime.Release, p.Group))
        Assert.Equal<int list>([0 .. descriptorPs.Length - 1], descriptorPs |> List.map _.Ordinal)
        Assert.Equal<int list>([0 .. acquirePs.Length - 1], acquirePs |> List.map _.Ordinal)
        Assert.Equal<int list>([0 .. releasePs.Length - 1], releasePs |> List.map _.Ordinal)
        Assert.Contains(runtime.Declaration, descriptorPs |> List.map _.Node)
        // Verify synthetic BoundaryDomain anchor never leaks into published runtime.Participants.
        for anchor in boundaryDomainAnchors do
            Assert.DoesNotContain(runtime.Participants, fun p -> p.Node = anchor || p.Group = anchor)

        let nodeIds (entries: Fidelity.PSG.Participant list) = entries |> List.map _.Node |> List.sort
        let checkTampered (changedRuntime: Fidelity.PSG.MemoryRegionRuntime) =
            let changedOp = { op with Runtime = Some changedRuntime }
            let memory = revision.Emission.Memory
            let changedMemory = { memory with Operations = memory.Operations.Add(op.Site, Fidelity.PSG.MemoryWitnessOperation.Region changedOp) }
            let revised = { revision with Emission = { revision.Emission with Memory = changedMemory } }
            Fidelity.PSG.Integrity.check revised
            |> List.filter (fun v -> v.Part.StartsWith("Emission.Memory.Operations.Region") && v.Node = Some op.Site)

        // Same-ID-multiset mutations: role swap, ordinal swap, group swap, and coherent acquire/release swap.
        let participantReason = "Region runtime participants differ from the immutable descriptor and bounded acquire or release imports."
        let importReason = "Region runtime lost its exact generated import declarations."
        let desc0 = descriptorPs.Head
        let acq0 = acquirePs.Head
        let rel0 = releasePs.Head
        let mutations =
            [ "descriptor/acquire role swap", participantReason,
              { runtime with
                  Participants =
                      runtime.Participants |> List.map (fun p ->
                          if p = desc0 then { p with Role = acq0.Role }
                          elif p = acq0 then { p with Role = desc0.Role }
                          else p) }
              "acquire/release single-entry role swap", participantReason,
              { runtime with
                  Participants =
                      runtime.Participants |> List.map (fun p ->
                          if p = acq0 then { p with Role = rel0.Role }
                          elif p = rel0 then { p with Role = acq0.Role }
                          else p) }
              "acquire ordinal swap", participantReason,
              { runtime with
                  Participants =
                      runtime.Participants |> List.map (fun p ->
                          if p.Role = Fidelity.PSG.ParticipantRole.RegionRuntimeAcquire && p.Ordinal < 2 then
                              { p with Ordinal = 1 - p.Ordinal }
                          else p) }
              "descriptor group swap", participantReason,
              { runtime with
                  Participants =
                      runtime.Participants |> List.map (fun p ->
                          if p = desc0 then { p with Group = runtime.Acquire } else p) }
              "acquire/release coherent swap", importReason,
              { runtime with
                  Acquire = runtime.Release
                  Release = runtime.Acquire
                  Participants =
                      descriptorPs
                      @ (releasePs |> List.map (fun p -> { p with Role = Fidelity.PSG.ParticipantRole.RegionRuntimeAcquire }))
                      @ (acquirePs |> List.map (fun p -> { p with Role = Fidelity.PSG.ParticipantRole.RegionRuntimeRelease })) } ]
        for name, expectedReason, mutated in mutations do
            Assert.Equal<Fidelity.PSG.NodeId list>(nodeIds runtime.Participants, nodeIds mutated.Participants)
            let hits = checkTampered mutated |> List.filter (fun v -> v.Reason = expectedReason)
            Assert.True(not hits.IsEmpty, sprintf "Runtime mutation '%s' expected exact refusal '%s', got: %A" name expectedReason (checkTampered mutated |> List.map _.Reason))

        // Withdrawal of a single descriptor participant must be refused with exact reason.
        let withdrawn = { runtime with Participants = runtime.Participants |> List.filter ((<>) desc0) }
        Assert.Contains(checkTampered withdrawn, fun v -> v.Reason = participantReason)

    [<Fact>]
    member _.``PSG #40 MemoryRegionRuntime and MemoryRegionWitness preserve canonical participants and memory rows under non-monotone SSA remap``() =
        let runtimeAuthority =
            AsyncAndRegionFixture.authority
                .Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
                .Replace(
                    "let regionPages =",
                    "let heap = { Name = \"heap\"; Kind = \"heap\"; Capacity = 1048576; Alignment = 16; Granularity = 1; Growth = \"up\"; Access = \"rw\"; Base = None }\nlet regionPages =")
                .Replace("Spaces = [| rodata; stack; regionPages |]", "Spaces = [| rodata; stack; regionPages; heap |]")
            + """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference | ReadOnlyReference
type CallConv = | CDecl
type Transfer = | CallerOwns | CalleeOwns | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type RegionMemoryDescriptor = { Space: string; EscapeSpace: string; Acquire: string; Release: string; Address: int; Protection: int; Flags: int; FileDescriptor: int; Offset: int; FailureValue: int; ReleaseSuccess: int; FailureAction: string }

[<FidelityExtern("c", "mmap")>]
let regionAcquire (addr: option<CHandle<unit>>) (len: int) (prot: int) (flags: int) (fd: int) (offset: int) : CHandle<unit> =
    NativeDefault.zeroed ()

let regionAcquireDescriptor: Expr<FunctionDescriptor> =
    <@ { CName = "mmap"
         Parameters =
           [| { Name = "addr"; Type = Pointer 64; PassBy = Value }
              { Name = "len"; Type = Integer (Unsigned, 64); PassBy = Value }
              { Name = "prot"; Type = Integer (Signed, 32); PassBy = Value }
              { Name = "flags"; Type = Integer (Signed, 32); PassBy = Value }
              { Name = "fd"; Type = Integer (Signed, 32); PassBy = Value }
              { Name = "offset"; Type = Integer (Signed, 64); PassBy = Value } |]
         ReturnType = Pointer 64
         CallingConvention = CDecl
         OwnershipTransfer = CallerOwns } @>

[<FidelityExtern("c", "munmap")>]
let regionRelease (addr: CHandle<unit>) (len: int) : int =
    NativeDefault.zeroed ()

let regionReleaseDescriptor: Expr<FunctionDescriptor> =
    <@ { CName = "munmap"
         Parameters =
           [| { Name = "addr"; Type = Pointer 64; PassBy = Value }
              { Name = "len"; Type = Integer (Unsigned, 64); PassBy = Value } |]
         ReturnType = Integer (Signed, 32)
         CallingConvention = CDecl
         OwnershipTransfer = CalleeOwns } @>

let regionMemory: Expr<RegionMemoryDescriptor> =
    <@ { Space = "region"; EscapeSpace = "heap"
         Acquire = "WriteAuthority.regionAcquire"; Release = "WriteAuthority.regionRelease"
         Address = 0; Protection = 3; Flags = 34; FileDescriptor = -1; Offset = 0
         FailureValue = -1; ReleaseSuccess = 0; FailureAction = "Abort" } @>
"""
        let program = """
module RegionRuntimeSsaRemap

[<EntryPoint>]
let main _ =
    let r = Region.create 4
    let buf = Region.alloc<int> r 4
    buf.[0] <- 42
    let v = buf.[0]
    Region.release r
    if v = 42 then 0 else 1
"""
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "Parse failed: %A" errors
        let platform = { AsyncAndRegionFixture.platform with RuntimeModel = Some RuntimeModel.Libc }
        let checkResult =
            Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                [ parse runtimeAuthority "write-authority.clef"; parse program "region-runtime-remap.clef" ]
                (Some platform)
        DimensionalCases.noErrors checkResult
        let graph = checkResult.Graph
        let baselinePlan =
            graph.Codata.Value.SSAAssignment
            |> Option.defaultWith (fun () -> failwith "Expected baseline SSAAssignment plan.")
        let memoryDomain =
            graph.Edges
            |> List.pick (fun edge -> match edge.Role with EdgeRole.MemoryDomain domain -> Some domain | _ -> None)
        let createOp =
            memoryDomain.Operations
            |> List.pick (fun (_, operation) ->
                match operation with
                | MemoryWitnessOperation.Region row when row.Kind = MemoryRegionKind.Create -> Some row
                | _ -> None)
        let runtime =
            createOp.Runtime
            |> Option.defaultWith (fun () -> failwith "Expected MemoryRegionRuntime on Region.create.")
        let descNodes = runtime.Participants |> List.choose (fun p -> if p.Role = ParticipantRole.RegionRuntimeDescriptor then Some p.Node else None)
        let acqNodes = runtime.Participants |> List.choose (fun p -> if p.Role = ParticipantRole.RegionRuntimeAcquire then Some p.Node else None)
        let relNodes = runtime.Participants |> List.choose (fun p -> if p.Role = ParticipantRole.RegionRuntimeRelease then Some p.Node else None)
        let declNodes = createOp.Declarations |> Map.toList |> List.map fst
        let proofParticipants =
            memoryDomain.Proofs
            |> List.pick (fun proof -> if proof.Participants.Count >= 2 then Some (Set.toList proof.Participants) else None)
        Assert.True(descNodes.Length >= 2)
        Assert.True(acqNodes.Length >= 2)
        Assert.True(relNodes.Length >= 2)
        Assert.True(declNodes.Length >= 2)

        // Exclude the minimum NodeId from each sorted participant/declaration/proof set so those
        // lowest-ID nodes jump above NodeHighWater while higher-ID peers stay retained, creating
        // a provable non-monotone NodeId order inversion across every group.
        let minDesc = List.min descNodes
        let minAcq = List.min acqNodes
        let minRel = List.min relNodes
        let minDecl = List.min declNodes
        let minProofP = List.min proofParticipants
        let reassigned = Set.ofList [ minDesc; minAcq; minRel; minDecl; minProofP ]
        let allNodes = graph.Nodes.Keys |> Set.ofSeq
        let retained = Set.difference allNodes reassigned
        let alignment = allNodes |> Seq.map (fun id -> id, id) |> Map.ofSeq

        let reconciled, plan =
            match DimensionalCases.reconcileCheckedPhysical graph alignment retained graph with
            | Result.Ok result -> result
            | Result.Error failure -> failwithf "Non-monotone SSA reconciliation refused: %A" failure

        // Verify genuine order inversion occurred on all 5 groups.
        for minId, groupNodes in
            [ minDesc, descNodes; minAcq, acqNodes; minRel, relNodes; minDecl, declNodes; minProofP, proofParticipants ] do
            let remappedMin = plan.NodeRemap[minId]
            let retainedPeer = groupNodes |> List.find (fun id -> not (reassigned.Contains id))
            let remappedPeer = plan.NodeRemap[retainedPeer]
            Assert.True(NodeId.value remappedMin > baselinePlan.NodeHighWater)
            Assert.Equal(retainedPeer, remappedPeer)
            Assert.True(remappedMin > remappedPeer, sprintf "Expected order inversion %A > %A" remappedMin remappedPeer)

        // Remapped graph must pass WitnessEmission.prepare (MemoryPublication + BoundaryEmission),
        // RevisionPublication.publish, and Fidelity.PSG.Integrity.check with zero defects.
        let prepared =
            match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare reconciled with
            | Ok graph -> graph
            | Error failures -> failwithf "WitnessEmission.prepare refused (%d failures): %A" failures.Length failures
        let revision =
            match Publication.publish prepared with
            | Ok rev -> rev
            | Error failures -> failwithf "Publication refused (%d failures): %A" failures.Length failures
        AsyncAndRegionFixture.wellFormed revision

        let remappedSite = AsyncAndRegionFixture.psgId plan.NodeRemap[createOp.Site]
        let remappedOp =
            match revision.Emission.Memory.Operations.TryFind remappedSite with
            | Some (Fidelity.PSG.MemoryWitnessOperation.Region row) -> row
            | other -> failwithf "Expected remapped Region.create operation, got %A" other
        let remappedRuntime =
            remappedOp.Runtime
            |> Option.defaultWith (fun () -> failwith "Expected remapped MemoryRegionRuntime.")
        let assertSortedReindexed role originalMin originalGroup =
            let entries = remappedRuntime.Participants |> List.filter (fun p -> p.Role = role)
            let nodes = entries |> List.map _.Node
            let remappedMin = AsyncAndRegionFixture.psgId plan.NodeRemap[originalMin]
            let retainedPeer = originalGroup |> List.find (fun id -> not (reassigned.Contains id)) |> fun id -> AsyncAndRegionFixture.psgId plan.NodeRemap[id]
            Assert.Equal<Fidelity.PSG.NodeId list>(List.sort nodes, nodes)
            Assert.Equal<int list>([0 .. entries.Length - 1], entries |> List.map _.Ordinal)
            Assert.True(List.findIndex ((=) remappedMin) nodes > List.findIndex ((=) retainedPeer) nodes)
        assertSortedReindexed Fidelity.PSG.ParticipantRole.RegionRuntimeDescriptor minDesc descNodes
        assertSortedReindexed Fidelity.PSG.ParticipantRole.RegionRuntimeAcquire minAcq acqNodes
        assertSortedReindexed Fidelity.PSG.ParticipantRole.RegionRuntimeRelease minRel relNodes

        let remappedDecls =
            remappedOp.Participants
            |> List.choose (fun p -> if p.Role = Fidelity.PSG.ParticipantRole.RegionDeclaration then Some p.Node else None)
        let retainedDecl = declNodes |> List.find (fun id -> not (reassigned.Contains id)) |> fun id -> AsyncAndRegionFixture.psgId plan.NodeRemap[id]
        Assert.Equal<Fidelity.PSG.NodeId list>(remappedOp.Declarations |> Map.toList |> List.map fst, remappedDecls)
        Assert.True(List.findIndex ((=) (AsyncAndRegionFixture.psgId plan.NodeRemap[minDecl])) remappedDecls > List.findIndex ((=) retainedDecl) remappedDecls)

        // Exact-reason negative control (Opus m4): SSAAssignment must propagate StringOrigins.relations
        // failures instead of silently falling back to the stale remapped graph.
        let corruptedGraph =
            let edgesWithOriginSlot =
                graph.Edges |> List.map (fun edge ->
                    match edge.Role with
                    | EdgeRole.BoundaryDomain domain ->
                        { edge with Role = EdgeRole.BoundaryDomain { domain with StringOriginRelations = Some [] } }
                    | _ -> edge)
            let invalidRecordedEdge : Hyperedge =
                { Class = EdgeClass.Reference
                  Role = EdgeRole.StringByteRange(0I, 1I)
                  Ordinal = 0
                  Sources = [ createOp.Site ]
                  Target = createOp.Site }
            { graph with Edges = invalidRecordedEdge :: edgesWithOriginSlot }
        match DimensionalCases.reconcileCheckedPhysical graph Map.empty Set.empty corruptedGraph with
        | Result.Error (DimensionalCases.CheckedPhysicalReconciliationFailure.Reconciliation (Clef.Compiler.Nanopass.SSAAssignment.ReconciliationFailure.InvalidReturnedIdentities [ _, reason ])) ->
            Assert.Contains("SSAAssignment:", reason)
            Assert.Contains("unsupported recorded incidence payload", reason)
        | other -> failwithf "Expected SSAAssignment to refuse invalid StringOrigins relation payload, got %A" other

    [<Fact>]
    member _.``PSG #40 (22_RegionEscape): real publication admits arena-only Runtime=None and refuses coordinated all-row runtime withdrawal``() =
        let escapeProgram = """
module RegionEscapeSample

let writeValue value =
    if value >= 0 && value <= 25 then Console.write (Format.int value)
    else Console.write "invalid"

let processAndExtract (input: int array) =
    let region = Region.create 4
    let len = Array.length input
    let temp = Region.alloc<int> region len
    for i in 0..(len - 1) do
        let value = input.[i]
        if value >= 0 && value <= 100 then
            temp.[i] <- value * value
        else
            temp.[i] <- 0
    let result = Region.copyOut<int> temp len
    result

let copyBetweenRegions () =
    let destination = Region.create 1
    let source = Region.create 1
    let buffer = Region.alloc<int> source 4
    for i in 0..3 do
        buffer.[i] <- 99
    let copied = Region.copyTo<int> buffer destination 4
    Region.release source
    let result = copied.[0]
    Region.release destination
    result

[<EntryPoint>]
let main _ =
    Console.writeln "=== Region Escape Test ==="
    let input = [| 1; 2; 3; 4; 5 |]
    Console.write "Input:"
    for i in 0..4 do
        Console.write " "
        writeValue input.[i]
    Console.writeln ""
    let squared = processAndExtract input
    Console.write "Squared:"
    for i in 0..4 do
        Console.write " "
        writeValue squared.[i]
    Console.writeln ""
    if copyBetweenRegions () = 99 then 0 else 1
"""
        let baseAuthority spaceName =
            AsyncAndRegionFixture.authority
                .Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
                .Replace(
                    "let regionPages =",
                    "let heap = { Name = \"heap\"; Kind = \"heap\"; Capacity = 1048576; Alignment = 16; Granularity = 1; Growth = \"up\"; Access = \"rw\"; Base = None }\nlet regionPages =")
                .Replace("Name = \"region\"; Kind = \"region\"", sprintf "Name = \"%s\"; Kind = \"region\"" spaceName)
                .Replace("Spaces = [| rodata; stack; regionPages |]", "Spaces = [| rodata; stack; regionPages; heap |]")
        let runtimeDecls = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference | ReadOnlyReference
type CallConv = | CDecl
type Transfer = | CallerOwns | CalleeOwns | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type RegionMemoryDescriptor = { Space: string; EscapeSpace: string; Acquire: string; Release: string; Address: int; Protection: int; Flags: int; FileDescriptor: int; Offset: int; FailureValue: int; ReleaseSuccess: int; FailureAction: string }

[<FidelityExtern("c", "mmap")>]
let regionAcquire (addr: option<CHandle<unit>>) (len: int) (prot: int) (flags: int) (fd: int) (offset: int) : CHandle<unit> =
    NativeDefault.zeroed ()

let regionAcquireDescriptor: Expr<FunctionDescriptor> =
    <@ { CName = "mmap"
         Parameters =
           [| { Name = "addr"; Type = Pointer 64; PassBy = Value }
              { Name = "len"; Type = Integer (Unsigned, 64); PassBy = Value }
              { Name = "prot"; Type = Integer (Signed, 32); PassBy = Value }
              { Name = "flags"; Type = Integer (Signed, 32); PassBy = Value }
              { Name = "fd"; Type = Integer (Signed, 32); PassBy = Value }
              { Name = "offset"; Type = Integer (Signed, 64); PassBy = Value } |]
         ReturnType = Pointer 64
         CallingConvention = CDecl
         OwnershipTransfer = CallerOwns } @>

[<FidelityExtern("c", "munmap")>]
let regionRelease (addr: CHandle<unit>) (len: int) : int =
    NativeDefault.zeroed ()

let regionReleaseDescriptor: Expr<FunctionDescriptor> =
    <@ { CName = "munmap"
         Parameters =
           [| { Name = "addr"; Type = Pointer 64; PassBy = Value }
              { Name = "len"; Type = Integer (Unsigned, 64); PassBy = Value } |]
         ReturnType = Integer (Signed, 32)
         CallingConvention = CDecl
         OwnershipTransfer = CalleeOwns } @>

let regionMemory: Expr<RegionMemoryDescriptor> =
    <@ { Space = "region"; EscapeSpace = "heap"
         Acquire = "WriteAuthority.regionAcquire"; Release = "WriteAuthority.regionRelease"
         Address = 0; Protection = 3; Flags = 34; FileDescriptor = -1; Offset = 0
         FailureValue = -1; ReleaseSuccess = 0; FailureAction = "Abort" } @>
"""
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "Parse failed: %A" errors
        let policyPlatform =
            { AsyncAndRegionFixture.platform with
                RuntimeModel = Some RuntimeModel.Libc
                ProjectMemoryPolicy = Some ("RegionEscape.fidproj", System.String('0', 64), "Standard", true) }
        let compileAndPublish authorityText fileTag =
            let res =
                Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                    [ parse authorityText "write-authority.clef"; parse escapeProgram (fileTag + ".clef") ]
                    (Some policyPlatform)
            DimensionalCases.noErrors res
            AsyncAndRegionFixture.publish res.Graph
        let regionRows (rev: Fidelity.PSG.Revision) =
            rev.Emission.Memory.Operations.Values
            |> Seq.choose (function Fidelity.PSG.MemoryWitnessOperation.Region row -> Some row | _ -> None)
            |> Seq.toList

        // 1. Real Positive Control (Absent Runtime — arena-only placement without runtime descriptor):
        let arenaOnlyRev = compileAndPublish (baseAuthority "arena") "region-escape-arena-only"
        let arenaOnlyRows = regionRows arenaOnlyRev
        Assert.Equal(11, arenaOnlyRows.Length)
        Assert.All(arenaOnlyRows, fun row -> Assert.True(row.Runtime.IsNone))
        AsyncAndRegionFixture.wellFormed arenaOnlyRev

        // 2. Real Positive Control (Absent Runtime — arena placement alongside unrelated "region" descriptor & imports):
        let arenaWithUnrelatedRev = compileAndPublish (baseAuthority "arena" + runtimeDecls) "region-escape-arena-unrelated"
        let arenaWithUnrelatedRows = regionRows arenaWithUnrelatedRev
        Assert.Equal(11, arenaWithUnrelatedRows.Length)
        Assert.All(arenaWithUnrelatedRows, fun row -> Assert.True(row.Runtime.IsNone))
        AsyncAndRegionFixture.wellFormed arenaWithUnrelatedRev

        // 3. Real Present Publication (all 11 rows carry Runtime = Some _ for Space = "region"):
        let presentRev = compileAndPublish (baseAuthority "region" + runtimeDecls) "region-escape-present"
        let presentRows = regionRows presentRev
        Assert.Equal(11, presentRows.Length)
        Assert.All(presentRows, fun row ->
            match row.Runtime with
            | Some rt -> Assert.Equal("region", rt.Contract.Space)
            | None -> failwithf "Expected Runtime = Some on region op %A" row.Site)
        AsyncAndRegionFixture.wellFormed presentRev

        // 4. Real Negative Control (Coordinated All-Row Withdrawal on Real Published 22_RegionEscape):
        // Withdraw Runtime <- None and strip all local RegionMemoryDescriptor facts + RegionDeclaration participants
        // across ALL 11 region operations simultaneously, while leaving Boundary.Imports intact.
        let reachableFactIds (facts: Map<Fidelity.PSG.NodeId, Fidelity.PSG.BoundaryDeclarationFact>) (roots: Fidelity.PSG.NodeId list) =
            let rec walk seen pending =
                match pending with
                | [] -> seen
                | id :: rest when Set.contains id seen -> walk seen rest
                | id :: rest ->
                    let next =
                        match facts.TryFind id with
                        | Some fact -> fact.References @ rest
                        | None -> rest
                    walk (Set.add id seen) next
            walk Set.empty roots
        let stripRowRuntime (row: Fidelity.PSG.MemoryRegionWitness) =
            let owner = presentRev.Codata.RegionAllocations[row.Region]
            let keptIds = reachableFactIds row.Declarations [ owner.SpacePlacement; row.Space ]
            let strippedDecls = row.Declarations |> Map.filter (fun id _ -> keptIds.Contains id)
            let strippedParticipants =
                row.Participants |> List.filter (fun p ->
                    p.Role <> Fidelity.PSG.ParticipantRole.RegionDeclaration || strippedDecls.ContainsKey p.Node)
            { row with Runtime = None; Declarations = strippedDecls; Participants = strippedParticipants }
        let strippedOps =
            presentRev.Emission.Memory.Operations
            |> Map.map (fun _ op ->
                match op with
                | Fidelity.PSG.MemoryWitnessOperation.Region row ->
                    Fidelity.PSG.MemoryWitnessOperation.Region (stripRowRuntime row)
                | other -> other)
        let coordinatedWithdrawalRev =
            { presentRev with
                Emission =
                    { presentRev.Emission with
                        Memory = { presentRev.Emission.Memory with Operations = strippedOps } } }
        let withdrawnRows = regionRows coordinatedWithdrawalRev
        Assert.Equal(11, withdrawnRows.Length)
        Assert.All(withdrawnRows, fun row ->
            Assert.True(row.Runtime.IsNone)
            Assert.DoesNotContain(row.Declarations.Values, fun f -> f.Form = "record" && List.contains "EscapeSpace" f.Text))
        let withdrawalReason = "Region runtime was withdrawn while its allocation placement matches a declared region runtime."
        let violations = Fidelity.PSG.Integrity.check coordinatedWithdrawalRev
        let withdrawalHits = violations |> List.filter (fun v -> v.Reason = withdrawalReason)
        Assert.Equal(11, withdrawalHits.Length)
        for row in withdrawnRows do
            Assert.Contains(withdrawalHits, fun v -> v.Node = Some row.Site && v.Reason = withdrawalReason)

namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module WritableInventory = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorage
module WritableProjection = Clef.Compiler.PSGSaturation.SemanticGraph.StorageWitness

module private ProgramInventoryFixture =
    let closureSource = """
module ProgramInventory
let make (flag: bool) = fun (value: bool) -> if flag then value else not value
let first = make true
let second = make false
[<EntryPoint>]
let main _ = if first true && second false then 0 else 1
"""

    let graph family =
        match family with
        | "lazy" -> LazyResidenceFixture.programWith None
        | _ -> LazyResidenceFixture.programWith (Some closureSource)

    let allocations (graph: SemanticGraph) =
        graph.Codata.Value.ProgramStorage.Entries.Keys |> Seq.choose (function
            | ProgramStorageIdentity.Allocation id -> Some id | _ -> None) |> Set.ofSeq

    let withoutAuthority (graph: SemanticGraph) =
        { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramValue) }

    let requirePending (sites: Set<NodeId>) (inventory: ProgramStorageInventory) =
        Assert.NotEmpty sites
        for site in sites do
            let identity = ProgramStorageIdentity.Allocation site
            Assert.True(inventory.Unresolved.ContainsKey identity, sprintf "Static allocation %A disappeared" site)
            Assert.False(inventory.Entries.ContainsKey identity, "Missing authority retained an accepted allocation")
        Assert.Empty inventory.Reservations

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProgramStorageInventory")>]
type ProgramStorageInventoryCases() =
    [<Theory>]
    [<InlineData("closure")>]
    [<InlineData("lazy")>]
    member _.``Lost writable authority retains every static allocation as unresolved`` family =
        let original = ProgramInventoryFixture.graph family
        let sites = ProgramInventoryFixture.allocations original
        let changed = ProgramInventoryFixture.withoutAuthority original
        let current = WritableInventory.settle changed
        ProgramInventoryFixture.requirePending sites current
        Assert.True((WritableInventory.read changed).IsNone)
        let retained = { changed with Codata = lazy { changed.Codata.Value with ProgramStorage = current } }
        Assert.Equal(Some current, WritableInventory.read retained)
        Assert.Equal(Some original.Codata.Value.ProgramStorage, WritableInventory.read original)

    [<Theory>]
    [<InlineData("closure")>]
    [<InlineData("lazy")>]
    member _.``Missing startup cannot turn retained static allocations into an empty inventory`` family =
        let original = ProgramInventoryFixture.graph family
        let changed = { original with Edges = original.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
        ProgramInventoryFixture.requirePending (ProgramInventoryFixture.allocations original) (WritableInventory.settle changed)

    [<Theory>]
    [<InlineData("closure")>]
    [<InlineData("lazy")>]
    member _.``An empty copied inventory cannot validate after all authorities disappear`` family =
        let original = ProgramInventoryFixture.graph family
        let changed = ProgramInventoryFixture.withoutAuthority original
        let omitted = { changed with Codata = lazy { changed.Codata.Value with ProgramStorage = ProgramStorageInventory.empty } }
        Assert.True((WritableInventory.read omitted).IsNone, "Missing allocations validated as an empty inventory")

    [<Theory>]
    [<InlineData("closure")>]
    [<InlineData("lazy")>]
    member _.``Source storage failures locate current allocations absent from copied inventory`` family =
        let original = ProgramInventoryFixture.graph family
        let changed = ProgramInventoryFixture.withoutAuthority original
        let omitted = { changed with Codata = lazy { changed.Codata.Value with ProgramStorage = ProgramStorageInventory.empty } }
        match WritableProjection.project omitted with
        | Ok _ -> failwith "Missing writable allocation authority was published"
        | Error failures ->
            for site in ProgramInventoryFixture.allocations original do
                Assert.Contains(failures, fun failure ->
                    failure.Occurrence = Some site && failure.Participants.Contains site
                    && failure.Reason.Contains("Writable program inventory"))

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Nonstatic and retired occurrences do not acquire unresolved program storage`` retired =
        let original = ProgramInventoryFixture.graph "closure"
        let sites = ProgramInventoryFixture.allocations original
        let changed = ProgramInventoryFixture.withoutAuthority original
        let excluded =
            if retired then
                { changed with Nodes = changed.Nodes |> Map.map (fun id node -> if sites.Contains id then { node with IsReachable = false } else node) }
            else
                { changed with Codata = lazy { changed.Codata.Value with Escapes = changed.Codata.Value.Escapes |> Map.map (fun id kind -> if sites.Contains id then EscapeKind.StackScoped else kind) } }
        let inventory = WritableInventory.settle excluded
        for site in sites do
            Assert.False(inventory.Unresolved.ContainsKey (ProgramStorageIdentity.Allocation site))
            Assert.False(inventory.Entries.ContainsKey (ProgramStorageIdentity.Allocation site))

module private EnvironmentReservationFixture =
    module Settlement = Clef.Compiler.Nanopass.ClosureEnvironmentSettlement
    module Authority = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority
    let rows (graph: SemanticGraph) =
        graph.Edges |> List.choose (fun edge ->
            match edge.Role, graph.Nodes.TryFind edge.Target with
            | EdgeRole.EnvironmentReservation participants, Some { Kind = SemanticKind.Obligation info } -> Some(edge, participants, info)
            | _ -> None)
    let rerun (graph: SemanticGraph) =
        let input = { graph with Codata = lazy (failwith "Environment proposal birth forced codata") }
        let settled, result = Settlement.settle input
        let fresh = rows settled |> List.filter (fun (edge, _, _) -> not (graph.Nodes.ContainsKey edge.Target))
        settled, result, fresh
    let allocation participants =
        participants |> List.find (fun (p: Participant) -> p.Role = ParticipantRole.EnvironmentAllocation && p.Group = p.Node) |> _.Node
    let solve body =
        let obligation = { Id = "environment_reservation_check"; Kind = "environment-storage-reservation"; Logic = "QF_LIA"
                           Statement = "individual reservation counterexample"; Source = "test"; Refs = []; Body = body }
        let start = System.Diagnostics.ProcessStartInfo("cvc5")
        start.ArgumentList.Add "--lang=smt2"
        start.ArgumentList.Add "--tlimit-per=2000"
        start.RedirectStandardInput <- true
        start.RedirectStandardOutput <- true
        start.RedirectStandardError <- true
        start.UseShellExecute <- false
        use solver = new System.Diagnostics.Process(StartInfo = start)
        Assert.True(solver.Start())
        let output, errors = solver.StandardOutput.ReadToEndAsync(), solver.StandardError.ReadToEndAsync()
        solver.StandardInput.Write(Clef.Compiler.Nanopass.ObligationDischarge.smtLib [obligation])
        solver.StandardInput.Close()
        if not (solver.WaitForExit 5000) then
            solver.Kill(true)
            failwith "Environment reservation solver timed out"
        Assert.True(solver.ExitCode = 0, errors.GetAwaiter().GetResult())
        output.GetAwaiter().GetResult().Trim()
    let shrinkSpace (graph: SemanticGraph) =
        let binding = LazyResidenceFixture.binding "first" graph
        let authority = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.tryValueAuthority graph binding |> Option.get
        let capacity =
            match graph.Nodes[authority.Space.Node].Kind with
            | SemanticKind.RecordExpr(fields, _) -> fields |> List.find (fst >> (=) "Capacity") |> snd
            | _ -> failwith "Expected writable declaration"
        let node = graph.Nodes[capacity]
        let reduced =
            match node.Kind with
            | SemanticKind.Literal(NativeLiteral.Int(_, kind)) -> { node with Kind = SemanticKind.Literal(NativeLiteral.Int(1L, kind)) }
            | _ -> failwith "Expected capacity literal"
        { graph with Nodes = graph.Nodes.Add(capacity, reduced) }, capacity

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "EnvironmentReservations")>]
type EnvironmentReservationCases() =
    [<Fact>]
    member _.``Factory reservation birth keeps distinct allocations and call grouped occurrences`` () =
        let graph = ProgramInventoryFixture.graph "closure"
        let rows = EnvironmentReservationFixture.rows graph
        Assert.Equal(2, rows.Length)
        Assert.Equal(2, rows |> List.map (fun (_, participants, _) -> EnvironmentReservationFixture.allocation participants) |> Set.ofList |> Set.count)
        for edge, participants, info in rows do
            let site = EnvironmentReservationFixture.allocation participants
            Assert.Equal("unsat", EnvironmentReservationFixture.solve info.Body)
            Assert.Equal<NodeId list>(participants |> List.map _.Node, edge.Sources)
            let call = participants |> List.filter (fun p -> p.Role = ParticipantRole.EnvironmentCall) |> Assert.Single
            Assert.Equal(call.Node, call.Group)
            let source = graph.Edges |> List.filter (fun row -> row.Role = EdgeRole.EnvironmentResultCall && row.Target = call.Node) |> Assert.Single
            let origin =
                match graph.Nodes[site].Metadata.TryFind ElaborationMetadata.Id with
                | Some(MetadataValue.Int id) -> id
                | _ -> failwith "Factory allocation lost its recipe source occurrence"
            Assert.StartsWith(sprintf "environment_%d_binding_" origin, info.Id)
            Assert.False(info.Id.StartsWith(sprintf "environment_%d_binding_" (NodeId.value site)))
            let group = participants |> List.filter (fun p -> p.Group = call.Node)
            Assert.Equal<NodeId list>(call.Node :: source.Sources, group |> List.map _.Node)
            Assert.All(group, fun p -> Assert.Equal(source.Ordinal, p.Ordinal))
            // The same allocation has an own occurrence and a call-input occurrence.
            Assert.Equal(2, participants |> List.filter (fun p -> p.Node = site && p.Role = ParticipantRole.EnvironmentAllocation) |> List.length)
            Assert.Contains(graph.Edges, fun row -> row.Role = EdgeRole.EnvironmentResidence && row.Sources |> List.contains edge.Target)
            let mapped = Clef.Compiler.PSGSaturation.Publication.RevisionMappers.mapEdgeRole edge.Role
            match mapped with
            | Fidelity.PSG.EdgeRole.EnvironmentReservation actual ->
                Assert.Equal<Fidelity.PSG.Participant list>(participants |> List.map Clef.Compiler.PSGSaturation.Publication.RevisionMappers.mapParticipant, actual)
            | _ -> failwith "Publication dropped the role-bearing reservation"

    [<Theory>]
    [<InlineData("authority")>]
    [<InlineData("startup")>]
    [<InlineData("intent")>]
    member _.``Missing program authority retains obligations without granting static residence`` missing =
        let graph = ProgramInventoryFixture.graph "closure"
        let removed = match missing with "authority" -> EdgeRole.ProgramValue | "startup" -> EdgeRole.ProgramInitialization | _ -> EdgeRole.ProgramValueIntent
        let changed = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> removed) }
        let _, settlement, rows = EnvironmentReservationFixture.rerun changed
        Assert.Equal(2, rows.Length)
        for _, participants, info in rows do
            let site = EnvironmentReservationFixture.allocation participants
            Assert.NotEqual(Some EscapeKind.StaticLifetime, settlement.Residences.TryFind site)
            Assert.Contains(settlement.Diagnostics, fun d -> d.Code = "CCS8403" && List.contains site d.RelatedNodes)
            Assert.Equal("sat", EnvironmentReservationFixture.solve info.Body)
            match info.Body with
            | ObligationBody.EnvironmentStorageReservation(Some _, Some _, None, None, None) -> ()
            | body -> failwithf "Missing authority did not remain an explicit premise: %A" body

    [<Fact>]
    member _.``Insufficient capacity retains the exact failing reservation and declaration identity`` () =
        let changed, capacity = ProgramInventoryFixture.graph "closure" |> EnvironmentReservationFixture.shrinkSpace
        let _, settlement, rows = EnvironmentReservationFixture.rerun changed
        Assert.Equal(2, rows.Length)
        for _, participants, info in rows do
            Assert.Contains(participants, fun p -> p.Node = capacity && p.Role = ParticipantRole.EnvironmentDeclarationInput)
            Assert.NotEqual(Some EscapeKind.StaticLifetime, settlement.Residences.TryFind (EnvironmentReservationFixture.allocation participants))
            Assert.Equal("sat", EnvironmentReservationFixture.solve info.Body)
            match info.Body with
            | ObligationBody.EnvironmentStorageReservation(Some _, Some _, Some 1L, Some 16, Some 16) -> ()
            | body -> failwithf "Source capacity was substituted: %A" body

    [<Fact>]
    member _.``Unsettled layout does not erase a reservation proposal`` () =
        let graph = ProgramInventoryFixture.graph "closure"
        let changed = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.EnvironmentFormal) }
        let _, settlement, rows = EnvironmentReservationFixture.rerun changed
        Assert.Equal(2, rows.Length)
        Assert.Empty settlement.Layouts
        for _, _, info in rows do
            match info.Body with
            | ObligationBody.EnvironmentStorageReservation(None, None, Some _, Some _, Some _) -> ()
            | body -> failwithf "Missing layout was substituted: %A" body
            Assert.Equal("sat", EnvironmentReservationFixture.solve info.Body)

    [<Fact>]
    member _.``Repeated initializer proposals survive the all path singleton rejection`` () =
        let graph = ProgramInventoryFixture.graph "closure"
        let plan = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read graph |> Option.get
        let first = LazyResidenceFixture.binding "first" graph
        let initializer = plan.Initializers |> List.find (fun row -> row.Binding = first) |> _.Initializer
        let root = graph.Nodes[initializer]
        let body = { root with Id = NodeId.fresh(); Parent = Some initializer }
        let guard = graph.Nodes.Values |> Seq.find (fun node -> node.Kind = SemanticKind.Literal(NativeLiteral.Bool true))
        let loop = { root with Kind = SemanticKind.WhileLoop(guard.Id, body.Id); Children = [guard.Id; body.Id] }
        let changed = { graph with Nodes = graph.Nodes.Add(body.Id, body).Add(root.Id, loop) }
        let proposals = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority.environmentProposals changed
        let sites = proposals |> Map.toList |> List.filter (fun (_, rows) -> rows |> List.contains (first, initializer)) |> List.map fst
        Assert.Single sites |> ignore
        for site in sites do Assert.Empty(Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority.candidates changed site)
        let _, settlement, rows = EnvironmentReservationFixture.rerun changed
        for site in sites do
            Assert.Contains(rows, fun (_, participants, _) -> EnvironmentReservationFixture.allocation participants = site)
            Assert.NotEqual(Some EscapeKind.StaticLifetime, settlement.Residences.TryFind site)
            Assert.Contains(settlement.Diagnostics, fun d -> List.contains site d.RelatedNodes)

    [<Fact>]
    member _.``Reservation incidence edits retract accepted program instances`` () =
        let graph = ProgramInventoryFixture.graph "closure"
        let first = LazyResidenceFixture.binding "first" graph
        let read graph = Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.programInstance graph first
        let instance = read graph |> Option.get
        let row, _, _ = EnvironmentReservationFixture.rows graph |> List.find (fun (_, ps, _) -> EnvironmentReservationFixture.allocation ps = instance.Allocation.Value)
        let changed = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Target <> row.Target || edge.Role <> row.Role) }
        Assert.True((read changed).IsNone)
        Assert.True((read graph).IsSome)

    [<Fact>]
    member _.``Reservation arithmetic includes rounding invalid declarations missing premises and wide sums`` () =
        let body bytes align capacity space grain = ObligationBody.EnvironmentStorageReservation(Some bytes, Some align, Some capacity, Some space, Some grain)
        let cases = [body 17 8 32L 16 16, "unsat"; body 17 8 31L 16 16, "sat"
                     body 8 16 1024L 8 16, "sat"; body 8 3 1024L 16 16, "sat"
                     body 8 8 1024L 16 0, "sat"; body 8 8 1024L 16 3, "sat"
                     body 0 8 1024L 16 16, "sat"; body -1 8 1024L 16 16, "sat"
                     body System.Int32.MaxValue 1 System.Int64.MaxValue 16 16, "unsat"
                     ObligationBody.EnvironmentStorageReservation(None, Some 8, Some 1024L, Some 16, Some 16), "sat"]
        for claim, expected in cases do Assert.Equal(expected, EnvironmentReservationFixture.solve claim)

    [<Theory>]
    [<InlineData("role")>]
    [<InlineData("ordinal")>]
    [<InlineData("group")>]
    member _.``Same identity sets cannot substitute changed reservation occurrences`` field =
        let graph = ProgramInventoryFixture.graph "closure"
        let first = LazyResidenceFixture.binding "first" graph
        let read graph = Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.programInstance graph first
        let instance = read graph |> Option.get
        let row, participants, _ = EnvironmentReservationFixture.rows graph |> List.find (fun (_, ps, _) -> EnvironmentReservationFixture.allocation ps = instance.Allocation.Value)
        let changedParticipants = participants |> List.map (fun p ->
            if p.Role <> ParticipantRole.EnvironmentCall then p else
            match field with
            | "role" -> { p with Role = ParticipantRole.EnvironmentFactory }
            | "ordinal" -> { p with Ordinal = p.Ordinal + 1 }
            | _ -> { p with Group = first })
        let edges = graph.Edges |> List.map (fun edge ->
            if edge.Target = row.Target && edge.Role = row.Role then { edge with Role = EdgeRole.EnvironmentReservation changedParticipants } else edge)
        let changed = { graph with Edges = edges }
        Assert.True((read changed).IsNone)
        Assert.True((read graph).IsSome)

    [<Fact>]
    member _.``Proposal traversal stops at deferred bodies and does not expand shared paths`` () =
        let graph = ProgramInventoryFixture.graph "closure"
        let plan = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read graph |> Option.get
        let first = LazyResidenceFixture.binding "first" graph
        let initializer = plan.Initializers |> List.find (fun row -> row.Binding = first) |> _.Initializer
        let root = graph.Nodes[initializer]
        let leaf = { root with Id = NodeId.fresh() }
        let top, nodes = [1 .. 32] |> List.fold (fun (previous, nodes: Map<NodeId, SemanticNode>) _ ->
            let node = { root with Id = NodeId.fresh(); Kind = SemanticKind.Sequential [previous; previous]; Children = [previous; previous] }
            node.Id, nodes.Add(node.Id, node)) (leaf.Id, graph.Nodes.Add(leaf.Id, leaf))
        let diamond = { root with Kind = SemanticKind.Sequential [top; top]; Children = [top; top] }
        let changed = { graph with Nodes = nodes.Add(root.Id, diamond) }
        let proposals graph = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority.environmentProposals graph
        Assert.Equal<Map<NodeId, (NodeId * NodeId) list>>(proposals graph, proposals changed)
        let delayed = { root with Kind = SemanticKind.Lambda([], top, [], None, LambdaContext.RegularClosure); Children = [top] }
        let deferred = proposals { changed with Nodes = changed.Nodes.Add(root.Id, delayed) }
        Assert.DoesNotContain(deferred.Values |> Seq.collect id, fun (binding, _) -> binding = first)

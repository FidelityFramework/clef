namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module OrderUses = Clef.Compiler.Baker.Ingredients.ProgramValueUses
module OrderSettlement = Clef.Compiler.Nanopass.ProgramInitializationOrder
module OrderProgram = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization
module OrderDischarge = Clef.Compiler.Nanopass.ObligationDischarge

module private InitializationOrderFixture =
    type EdgeSnapshot = EdgeClass * EdgeRole * NodeId list * NodeId * int
    let incidence (edge: Hyperedge) : EdgeSnapshot = edge.Class, edge.Role, edge.Sources, edge.Target, edge.Ordinal
    let source = """
module ProgramInitializationOrder
let make (flag: bool) = fun (value: bool) -> if flag then value else not value
let first = make true
let second = make false
let alias = first
let later = make true
[<EntryPoint>]
let main _ = if alias true && second false && later true then 0 else 1
"""

    let graph () = LazyResidenceFixture.programWith (Some source)
    let binding name graph = LazyResidenceFixture.binding name graph
    let rows (graph: SemanticGraph) =
        graph.Edges |> List.choose (fun edge ->
            match edge.Role, graph.Nodes.TryFind edge.Target with
            | EdgeRole.ProgramInitializationOrder participants, Some { Kind = SemanticKind.Obligation info } ->
                let owner = participants |> List.filter (fun p -> p.Role = ParticipantRole.InitializationBinding && p.Group = p.Node) |> Assert.Single
                Some(owner.Node, edge, participants, info)
            | _ -> None)
    let row graph binding = rows graph |> List.filter (fun (owner, _, _, _) -> owner = binding) |> Assert.Single
    let history (graph: SemanticGraph) =
        graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.ProgramInitializationOrderHistory _ -> true | _ -> false)
        |> List.map incidence
    let identities graph = rows graph |> List.map (fun (binding, edge, _, info) -> binding, edge.Target, info.Id) |> Set.ofList
    let instance graph binding = Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.programInstance graph binding

    let readLater (graph: SemanticGraph) =
        let first, alias, later = binding "first" graph, binding "alias" graph, binding "later" graph
        let plan = OrderProgram.read graph |> Option.get
        let aliasRow = plan.Initializers |> List.find (fun row -> row.Binding = alias)
        let laterRow = plan.Initializers |> List.find (fun row -> row.Binding = later)
        Assert.True(aliasRow.Ordinal < laterRow.Ordinal)
        let reference = graph.Nodes[aliasRow.Initializer]
        match reference.Kind with
        | SemanticKind.VarRef(_, Some source) -> Assert.Equal(first, source)
        | kind -> failwithf "Expected the admitted alias initializer: %A" kind
        let changed =
            { graph with
                Nodes = graph.Nodes.Add(reference.Id, { reference with Kind = SemanticKind.VarRef("later", Some later) })
                Edges = graph.Edges |> List.map (fun edge ->
                    if edge.Role = EdgeRole.Definition && edge.Target = reference.Id then { edge with Sources = [later] }
                    else edge) }
        Assert.Equal(Some plan, OrderProgram.read changed)
        changed, aliasRow, laterRow

    let solve (obligation: ObligationInfo) =
        let query =
            match OrderDischarge.trySmtLib [obligation] with
            | Ok query -> query
            | Error unavailable -> failwithf "Expected a complete finite order query: %A" unavailable
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
        solver.StandardInput.Write query
        solver.StandardInput.Close()
        if not (solver.WaitForExit 5000) then
            solver.Kill true
            failwith "Initialization order solver timed out"
        Assert.True(solver.ExitCode = 0, errors.GetAwaiter().GetResult())
        output.GetAwaiter().GetResult().Trim()

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProgramInitializationOrder")>]
type ProgramInitializationOrderCases() =
    [<Fact>]
    member _.``Final Codata retains source artifact accounts and canonical alias residence`` () =
        let graph = InitializationOrderFixture.graph ()
        let facts = graph.Codata.Value
        Assert.Equal(3, facts.EnvironmentFactoryResults.Count)
        Assert.Equal(3, facts.EnvironmentResidences.Count)
        Assert.Equal(4, facts.ProgramInitializationOrders.Count)
        let first = InitializationOrderFixture.binding "first" graph
        let alias = InitializationOrderFixture.binding "alias" graph
        let firstInstance = InitializationOrderFixture.instance graph first |> Option.get
        let aliasInstance = InitializationOrderFixture.instance graph alias |> Option.get
        Assert.Equal(firstInstance.Allocation, aliasInstance.Allocation)
        let residence = facts.EnvironmentResidences[firstInstance.Allocation.Value]
        Assert.Equal(first, residence.Binding)
        Assert.Contains(first, aliasInstance.Participants)
        let reservation = facts.EnvironmentReservations[residence.ReservationClaim]
        Assert.Equal(first, reservation.Binding)
        Assert.Equal(residence.Allocation, reservation.Allocation)
        Assert.Empty(Clef.Compiler.Nanopass.EnvironmentFactoryResults.validateAccounts graph)
        Assert.Empty(Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.validateArtifactAccounts graph)
        Assert.Empty(OrderSettlement.validateAccounts graph)

    [<Theory>]
    [<InlineData("call")>]
    [<InlineData("factory")>]
    [<InlineData("formal")>]
    [<InlineData("allocation")>]
    [<InlineData("destination")>]
    member _.``Held factory result accounts refuse a substituted source identity`` defect =
        let graph = InitializationOrderFixture.graph ()
        let facts = graph.Codata.Value
        let call, account = facts.EnvironmentFactoryResults |> Map.toList |> List.head
        let foreign = InitializationOrderFixture.binding "alias" graph
        let replacement =
            match defect with
            | "call" -> { account with Call = foreign }
            | "factory" -> { account with Factory = foreign }
            | "formal" -> { account with Formal = foreign }
            | "allocation" -> { account with Allocation = foreign }
            | "destination" -> { account with Destination = foreign }
            | _ -> failwith "Unknown source account defect"
        let changed =
            { graph with Codata = lazy { facts with EnvironmentFactoryResults = facts.EnvironmentFactoryResults.Add(call, replacement) } }
        let failures = Clef.Compiler.Nanopass.EnvironmentFactoryResults.validateAccounts changed
        Assert.Contains(failures, fun (site, _) -> site = call)
        Assert.Empty(Clef.Compiler.Nanopass.EnvironmentFactoryResults.validateAccounts graph)

    [<Fact>]
    member _.``Held initialization accounts refuse removed and added alias use premises`` () =
        let graph = InitializationOrderFixture.graph ()
        let changed, _, later = InitializationOrderFixture.readLater graph
        Assert.Empty(OrderSettlement.validateAccounts graph)
        let first = InitializationOrderFixture.binding "first" graph
        let invalidated = OrderSettlement.validateAccounts changed |> List.map fst |> Set.ofList
        Assert.Equal<Set<NodeId>>(Set.ofList [first; later.Binding], invalidated)

    [<Fact>]
    member _.``Distinct allocations and shared aliases retain every required initialization order receipt`` () =
        let graph = InitializationOrderFixture.graph ()
        let plan = OrderProgram.read graph |> Option.get
        let names = ["first"; "second"; "alias"; "later"]
        let bindings = names |> List.map (fun name -> InitializationOrderFixture.binding name graph)
        Assert.Equal<Set<NodeId>>(Set.ofList bindings, Set.ofList (OrderUses.bindings graph))
        let rows = InitializationOrderFixture.rows graph
        Assert.Equal(4, rows.Length)
        Assert.Equal(4, InitializationOrderFixture.history graph |> List.length)
        let instances = bindings |> List.map (InitializationOrderFixture.instance graph >> Option.get)
        Assert.Equal(instances[0].Allocation, instances[2].Allocation)
        Assert.Equal(3, [instances[0].Allocation; instances[1].Allocation; instances[3].Allocation] |> Set.ofList |> Set.count)
        for binding, edge, participants, info in rows do
            Assert.True(OrderUses.current graph binding)
            Assert.Equal<NodeId list>(participants |> List.map _.Node, edge.Sources)
            let initialization = plan.Initializers |> List.find (fun row -> row.Binding = binding)
            match info.Body with
            | ObligationBody.ProgramInitializationOrder(ordinal, count, uses) ->
                Assert.Equal(initialization.Ordinal, ordinal)
                Assert.Equal(plan.Initializers.Length, count)
                Assert.NotEmpty uses
                Assert.All(uses, fun usePhase -> Assert.True(ordinal < usePhase && usePhase <= count))
                Assert.Contains(participants, fun p -> p.Role = ParticipantRole.InitializationUse)
                Assert.Contains(participants, fun p -> p.Role = ParticipantRole.InitializationPhase && List.contains p.Ordinal uses)
            | body -> failwithf "Admitted callable binding lost a complete order body: %A" body
            Assert.Equal("unsat", InitializationOrderFixture.solve info)

    [<Fact>]
    member _.``A forward alias read renews the same required obligation and produces a solver counterexample`` () =
        let original = InitializationOrderFixture.graph ()
        let changed, aliasRow, laterRow = InitializationOrderFixture.readLater original
        Assert.False(OrderUses.current changed laterRow.Binding)
        let settled, diagnostics = OrderSettlement.settle changed
        Assert.Empty diagnostics
        Assert.Equal<Set<NodeId * NodeId * string>>(InitializationOrderFixture.identities original, InitializationOrderFixture.identities settled)
        Assert.Equal<InitializationOrderFixture.EdgeSnapshot list>(InitializationOrderFixture.history original, InitializationOrderFixture.history settled)
        let _, _, participants, obligation = InitializationOrderFixture.row settled laterRow.Binding
        match obligation.Body with
        | ObligationBody.ProgramInitializationOrder(ordinal, count, uses) ->
            Assert.Equal(laterRow.Ordinal, ordinal)
            Assert.Equal((OrderProgram.read settled |> Option.get).Initializers.Length, count)
            Assert.Contains(aliasRow.Ordinal, uses)
            Assert.True(aliasRow.Ordinal < ordinal)
            Assert.Contains(participants, fun p ->
                p.Role = ParticipantRole.InitializationUse && p.Node = aliasRow.Initializer && p.Group = aliasRow.Initializer)
            Assert.Contains(participants, fun p ->
                p.Role = ParticipantRole.InitializationPhase && p.Node = aliasRow.Binding && p.Group = aliasRow.Initializer && p.Ordinal = aliasRow.Ordinal)
        | body -> failwithf "A known early use was hidden by unavailable premises: %A" body
        Assert.Equal("sat", InitializationOrderFixture.solve obligation)

    [<Fact>]
    member _.``Missing startup retains required pending rows and located unavailable premises`` () =
        let original = InitializationOrderFixture.graph ()
        let changed = { original with Edges = original.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
        let settled, diagnostics = OrderSettlement.settle changed
        Assert.True((OrderProgram.read settled).IsNone)
        Assert.Equal<Set<NodeId * NodeId * string>>(InitializationOrderFixture.identities original, InitializationOrderFixture.identities settled)
        Assert.Equal<InitializationOrderFixture.EdgeSnapshot list>(InitializationOrderFixture.history original, InitializationOrderFixture.history settled)
        let rows = InitializationOrderFixture.rows settled
        Assert.Equal(4, rows.Length)
        for binding, _, participants, obligation in rows do
            Assert.False(OrderUses.current settled binding)
            Assert.Contains(participants, fun p -> p.Role = ParticipantRole.InitializationBinding && p.Node = binding)
            match obligation.Body with
            | ObligationBody.Pending reasons ->
                Assert.Contains(reasons, fun reason -> reason.Contains("startup plan"))
                Assert.Contains(diagnostics, fun diagnostic ->
                    diagnostic.Code = "CCS8403" && diagnostic.Range = settled.Nodes[binding].Range && List.contains binding diagnostic.RelatedNodes)
            | body -> failwithf "Missing startup became a solver proposition: %A" body
        match OrderDischarge.trySmtLib (rows |> List.map (fun (_, _, _, info) -> info)) with
        | Error unavailable -> Assert.Equal(4, unavailable.Length)
        | Ok query -> failwithf "Missing startup produced a solver query: %s" query

    [<Theory>]
    [<InlineData("role")>]
    [<InlineData("ordinal")>]
    [<InlineData("group")>]
    member _.``Equal identity sets cannot replace exact initialization use occurrences`` field =
        let graph = InitializationOrderFixture.graph ()
        let alias = InitializationOrderFixture.binding "alias" graph
        let _, row, participants, _ = InitializationOrderFixture.row graph alias
        Assert.True(OrderUses.current graph alias)
        Assert.True((InitializationOrderFixture.instance graph alias).IsSome)
        let read = participants |> List.find (fun p -> p.Role = ParticipantRole.InitializationUse)
        let replacement =
            match field with
            | "role" -> { read with Role = ParticipantRole.InitializationScope }
            | "ordinal" -> { read with Ordinal = read.Ordinal + 1 }
            | _ -> { read with Group = alias }
        Assert.NotEqual(read, replacement)
        let changedParticipants = participants |> List.map (fun p -> if p = read then replacement else p)
        Assert.Equal<Set<NodeId>>(participants |> List.map _.Node |> Set.ofList, changedParticipants |> List.map _.Node |> Set.ofList)
        let edges = graph.Edges |> List.map (fun edge ->
            if InitializationOrderFixture.incidence edge = InitializationOrderFixture.incidence row then
                { edge with Role = EdgeRole.ProgramInitializationOrder changedParticipants }
            else edge)
        let changed = { graph with Edges = edges }
        Assert.False(OrderUses.current changed alias)
        Assert.True((InitializationOrderFixture.instance changed alias).IsNone)
        Assert.Equal<InitializationOrderFixture.EdgeSnapshot list>(InitializationOrderFixture.history graph, InitializationOrderFixture.history changed)

    [<Fact>]
    member _.``An independent unclassified callable reference remains a required pending use`` () =
        let original = InitializationOrderFixture.graph ()
        let first = InitializationOrderFixture.binding "first" original
        let plan = OrderProgram.read original |> Option.get
        let independent = { Class = EdgeClass.Reference; Role = EdgeRole.Symbol; Sources = [first]; Target = plan.OriginalBody; Ordinal = 0 }
        let changed = { original with Edges = independent :: original.Edges }
        let settled, diagnostics = OrderSettlement.settle changed
        let _, _, participants, obligation = InitializationOrderFixture.row settled first
        Assert.Equal<Set<NodeId * NodeId * string>>(InitializationOrderFixture.identities original, InitializationOrderFixture.identities settled)
        Assert.Contains(participants, fun p -> p.Role = ParticipantRole.InitializationUse && p.Node = independent.Target)
        Assert.False(OrderUses.current settled first)
        match obligation.Body with
        | ObligationBody.Pending reasons -> Assert.Contains(reasons, fun reason -> reason.Contains("Unclassified reference"))
        | body -> failwithf "An unknown live reference disappeared from the required premises: %A" body
        Assert.Contains(diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8403" && List.contains first diagnostic.RelatedNodes && List.contains independent.Target diagnostic.RelatedNodes)
        match OrderDischarge.trySmtLib [obligation] with
        | Error unavailable -> Assert.Equal(obligation.Id, (Assert.Single unavailable).Anchor)
        | Ok query -> failwithf "An unclassified reference produced a solver query: %s" query

    [<Theory>]
    [<InlineData("orphan-reference")>]
    [<InlineData("uncovered-entry")>]
    member _.``Live callable reads need complete execution scopes even with a valid startup plan`` scope =
        let original = InitializationOrderFixture.graph ()
        let plan = OrderProgram.read original |> Option.get
        let changed, binding, useSite, reason =
            match scope with
            | "orphan-reference" ->
                let first = InitializationOrderFixture.binding "first" original
                let alias = InitializationOrderFixture.binding "alias" original
                let initializer = plan.Initializers |> List.find (fun row -> row.Binding = alias) |> _.Initializer
                let orphan = { original.Nodes[initializer] with Id = NodeId.fresh(); Parent = None }
                match orphan.Kind with
                | SemanticKind.VarRef(_, Some source) -> Assert.Equal(first, source)
                | kind -> failwithf "Expected a callable reference to clone: %A" kind
                { original with Nodes = original.Nodes.Add(orphan.Id, orphan) }, first, orphan.Id, "outside every supported"
            | _ ->
                let alias = InitializationOrderFixture.binding "alias" original
                let useSite = original.Nodes.Values |> Seq.find (fun node ->
                    match node.Kind with SemanticKind.VarRef(_, Some source) -> source = alias && node.IsReachable | _ -> false)
                // This is a separate opaque use of the source entry callable.
                // Its ordinary call no longer proves complete invocation scope.
                let opaque = { Class = EdgeClass.Reference; Role = EdgeRole.Symbol; Sources = [plan.SourceBinding]
                               Target = plan.OriginalBody; Ordinal = 0 }
                { original with Edges = opaque :: original.Edges }, alias, useSite.Id, "invocation scope"
        Assert.Equal(Some plan, OrderProgram.read changed)
        let settled, diagnostics = OrderSettlement.settle changed
        let _, _, participants, obligation = InitializationOrderFixture.row settled binding
        Assert.False(OrderUses.current settled binding)
        Assert.Contains(participants, fun p -> p.Role = ParticipantRole.InitializationUse && p.Node = useSite)
        match obligation.Body with
        | ObligationBody.Pending reasons -> Assert.Contains(reasons, fun missing -> missing.Contains reason)
        | body -> failwithf "A live read acquired an order phase without complete scope: %A" body
        Assert.Contains(diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8403" && List.contains binding diagnostic.RelatedNodes && List.contains useSite diagnostic.RelatedNodes)
        match OrderDischarge.trySmtLib [obligation] with
        | Error unavailable -> Assert.Equal(obligation.Id, (Assert.Single unavailable).Anchor)
        | Ok query -> failwithf "A read without a complete scope produced a solver query: %s" query

    [<Fact>]
    member _.``Residual callable capture metadata cannot disappear from required order premises`` () =
        let original = InitializationOrderFixture.graph ()
        let first = InitializationOrderFixture.binding "first" original
        let plan = OrderProgram.read original |> Option.get
        let lambda = original.Nodes[plan.SourceLambda]
        let capture = { Name = "first"; Type = original.Nodes[first].Type; IsMutable = false; SourceNodeId = Some first }
        let changedLambda =
            match lambda.Kind with
            | SemanticKind.Lambda(parameters, body, captures, owner, context) ->
                Assert.Empty captures
                { lambda with Kind = SemanticKind.Lambda(parameters, body, [capture], owner, context) }
            | kind -> failwithf "Expected the admitted source entry lambda: %A" kind
        let changed = { original with Nodes = original.Nodes.Add(lambda.Id, changedLambda) }
        Assert.Equal(Some plan, OrderProgram.read changed)
        Assert.True(OrderUses.current original first)
        let reading = OrderUses.read changed first
        match reading.Body with
        | ObligationBody.Pending reasons -> Assert.NotEmpty reasons
        | body -> failwithf "Residual callable capture metadata was omitted from the order premise: %A" body
        Assert.False(OrderUses.current changed first)
        Assert.Contains(reading.Participants, fun p ->
            p.Role = ParticipantRole.InitializationUse && p.Node = lambda.Id && p.Group = lambda.Id && p.Ordinal = 0)
        Assert.Contains(reading.Participants, fun p -> p.Role = ParticipantRole.InitializationBinding && p.Node = first)

    [<Fact>]
    member _.``Direct structural callable projections cannot disappear from required order premises`` () =
        let original = InitializationOrderFixture.graph ()
        let first = InitializationOrderFixture.binding "first" original
        let plan = OrderProgram.read original |> Option.get
        let template = original.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.EnvironmentReference _ -> true | _ -> false)
        let projection = { template with Id = NodeId.fresh(); Kind = SemanticKind.EnvironmentReference first
                                         Children = [first]; Parent = Some plan.OriginalBody }
        let body = original.Nodes[plan.OriginalBody]
        let changed =
            { original with Nodes = original.Nodes.Add(projection.Id, projection).Add(body.Id, { body with Children = body.Children @ [projection.Id] }) }
        Assert.Equal(Some plan, OrderProgram.read changed)
        Assert.True(OrderUses.current original first)
        let reading = OrderUses.read changed first
        match reading.Body with
        | ObligationBody.Pending reasons -> Assert.NotEmpty reasons
        | body -> failwithf "Direct structural callable projection was omitted from the order premise: %A" body
        Assert.False(OrderUses.current changed first)
        Assert.Contains(reading.Participants, fun p ->
            p.Role = ParticipantRole.InitializationUse && p.Node = projection.Id && p.Group = projection.Id)

    [<Fact>]
    member _.``A callable capture without source identity keeps the complete use census pending`` () =
        let original = InitializationOrderFixture.graph ()
        let first = InitializationOrderFixture.binding "first" original
        let plan = OrderProgram.read original |> Option.get
        let lambda = original.Nodes[plan.SourceLambda]
        // The name deliberately identifies no program binding. It cannot repair
        // the missing declaration identity or justify omitting the capture.
        let capture = { Name = "unresolved_callable_capture"; Type = original.Nodes[first].Type
                        IsMutable = false; SourceNodeId = None }
        let changedLambda =
            match lambda.Kind with
            | SemanticKind.Lambda(parameters, body, captures, owner, context) ->
                Assert.Empty captures
                { lambda with Kind = SemanticKind.Lambda(parameters, body, [capture], owner, context) }
            | kind -> failwithf "Expected the admitted source entry lambda: %A" kind
        let changed = { original with Nodes = original.Nodes.Add(lambda.Id, changedLambda) }
        Assert.Equal(Some plan, OrderProgram.read changed)
        Assert.True(OrderUses.current original first)
        let reading = OrderUses.read changed first
        match reading.Body with
        | ObligationBody.Pending reasons -> Assert.NotEmpty reasons
        | body -> failwithf "A callable capture without source identity disappeared from the complete use census: %A" body
        Assert.False(OrderUses.current changed first)
        Assert.Contains(reading.Participants, fun p ->
            p.Role = ParticipantRole.InitializationUse && p.Node = lambda.Id && p.Group = lambda.Id && p.Ordinal = 0)

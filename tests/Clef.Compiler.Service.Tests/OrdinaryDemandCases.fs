namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module DemandProjection = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand
module DemandRecipe = Clef.Compiler.Nanopass.OrdinaryDemand
module DemandRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module DemandStrings = Clef.Compiler.PSGSaturation.SemanticGraph.StaticStringLayout
module WitnessInput = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

module private OrdinaryDemandFixture =
    let check source =
        match parseAndCheck ("module OrdinaryDemand\n" + source) "ordinary-demand.clef" with
        | Success result | CheckFailure result ->
            Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error))
            result.Graph
        | ParseFailure errors -> failwithf "%A" errors
    let source = """
[<Measure>] type m
let discard (value: int<m>) = 0
[<EntryPoint>]
let main _ =
    discard (1<m> + 2<m>) + discard (eager (3<m> + 4<m>))
"""
    let witnessSource () = LazyResidenceFixture.programWith (Some("module OrdinaryDemand\n" + source))
    let formal (graph: SemanticGraph) =
        (DemandProjection.read graph).Formals.Values |> Seq.filter (fun proof ->
            match graph.Nodes[proof.Formal].Kind with SemanticKind.PatternBinding "value" -> true | _ -> false)
        |> Assert.Single
    let calls graph (formal: DemandProjection.Formal) =
        (DemandProjection.read graph).Calls.Values |> Seq.filter (fun call -> call.Implementation = formal.Implementation) |> Seq.toList
    let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Sources, edge.Target, edge.Ordinal

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "OrdinaryDemand")>]
type OrdinaryDemandCases() =
    [<Fact>]
    member _.``Logical measured formals and actuals remain while ordinary transport is omitted`` () =
        let graph = OrdinaryDemandFixture.check OrdinaryDemandFixture.source
        let formal = OrdinaryDemandFixture.formal graph
        let calls = OrdinaryDemandFixture.calls graph formal
        Assert.Equal(2, calls.Length)
        Assert.Equal(1, calls |> List.filter (fun call -> call.Eager = Set.singleton 0) |> List.length)
        Assert.Equal(1, calls |> List.filter (fun call -> call.Eager.IsEmpty) |> List.length)
        for call in calls do
            Assert.Equal<Set<int>>(Set.singleton 0, call.Omitted)
            Assert.Equal(graph.Nodes[formal.Formal].Type, graph.Nodes[call.Actuals.Head].Type)
            Assert.True(graph.Nodes[call.Actuals.Head].IsReachable)
            Assert.Contains(call.Site, formal.Participants)
            Assert.Contains(call.Actuals.Head, formal.Participants)
        let cold = calls |> List.find (fun call -> call.Eager.IsEmpty)
        let hot = calls |> List.find (fun call -> not call.Eager.IsEmpty)
        let deferred = DemandProjection.deferredOnly graph
        Assert.Contains(cold.Actuals.Head, deferred)
        Assert.DoesNotContain(hot.Actuals.Head, deferred)
        match graph.Nodes[formal.Implementation].Kind with
        | SemanticKind.Lambda(parameters, _, _, _, _) -> Assert.Equal(formal.Formal, (List.head parameters |> fun (_, _, id) -> id))
        | _ -> failwith "Expected unchanged source lambda"

    [<Fact>]
    member _.``Immutable callee aliases retain one implementation projection`` () =
        let graph = OrdinaryDemandFixture.check """
let discard (value: int) = 0
let alias = discard
[<EntryPoint>]
let main _ = alias (1 + 2) + discard (3 + 4)
"""
        let formal = OrdinaryDemandFixture.formal graph
        Assert.Equal(2, (OrdinaryDemandFixture.calls graph formal).Length)

    [<Fact>]
    member _.``Shared actual demanded elsewhere is not a deferred-only node`` () =
        let graph = OrdinaryDemandFixture.check OrdinaryDemandFixture.source
        let formal = OrdinaryDemandFixture.formal graph
        let call = OrdinaryDemandFixture.calls graph formal |> List.find (fun call -> call.Eager.IsEmpty)
        // Use a separate demanded holder rather than claiming a skipped root's
        // shared descendants were emitted at their omitted occurrence.
        let holder = { graph.Nodes[call.Actuals.Head] with Id = NodeId.fresh(); Kind = SemanticKind.Sequential [call.Actuals.Head]; Children = [call.Actuals.Head] }
        let changed = { graph with Nodes = graph.Nodes.Add(holder.Id, holder) }
        let changed = DemandRecipe.normalize changed
        Assert.DoesNotContain(call.Actuals.Head, DemandProjection.deferredOnly changed)

    [<Fact>]
    member _.``Recorded additional actual references prevent deferred-only coverage`` () =
        let graph = OrdinaryDemandFixture.check OrdinaryDemandFixture.source
        let formal = OrdinaryDemandFixture.formal graph
        let call = OrdinaryDemandFixture.calls graph formal |> List.find (fun call -> call.Eager.IsEmpty)
        let holder = { graph.Nodes[call.Actuals.Head] with Id = NodeId.fresh(); Kind = SemanticKind.VarRef("recorded", None); Children = [] }
        let reference =
            { Class = EdgeClass.Reference; Role = EdgeRole.Definition
              Sources = [call.Actuals.Head]; Target = holder.Id; Ordinal = 0 }
        let changed = { graph with Nodes = graph.Nodes.Add(holder.Id, holder); Edges = reference :: graph.Edges }
        let changed = DemandRecipe.normalize changed
        Assert.True((DemandProjection.read changed).Calls.ContainsKey call.Site)
        Assert.DoesNotContain(call.Actuals.Head, DemandProjection.deferredOnly changed)
        Assert.True(graph.Nodes[call.Actuals.Head].IsReachable)

    [<Fact>]
    member _.``Returned environment factories retain logical unused actual and destination indices`` () =
        let source = """
module DemandFactory
[<Measure>] type m
let touch () = ()
let make (offset: int<m>) (unused: int) =
    if "formed" = "formed" then touch () else touch ()
    fun (value: int<m>) -> value + offset
let first = make 3<m> (1 + 2)
let second = make 5<m> (3 + 4)
[<EntryPoint>]
let main _ = if first 1<m> + second 1<m> = 10<m> then 0 else 1
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let proof =
            (DemandProjection.read graph).Formals.Values
            |> Seq.filter (fun proof -> graph.Nodes[proof.Formal].Kind = SemanticKind.PatternBinding "unused")
            |> Assert.Single
        let calls = OrdinaryDemandFixture.calls graph proof
        Assert.Equal(2, calls.Length)
        Assert.Equal(2, proof.Ordinal)
        let prefix = graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && node.Kind = SemanticKind.Literal(NativeLiteral.String "formed"))
        Assert.Contains(graph.Edges, fun edge ->
            edge.Class = EdgeClass.Reference && edge.Role = EdgeRole.Resides && edge.Target = prefix.Id)
        for role in [EdgeRole.Definition; EdgeRole.Resides] do
            let useOfFormal =
                { Class = EdgeClass.Reference; Role = role; Sources = [proof.Formal]
                  Target = prefix.Id; Ordinal = 0 }
            let changed = { graph with Edges = useOfFormal :: graph.Edges } |> DemandRecipe.normalize
            Assert.Empty(DemandProjection.parameters changed proof.Implementation)
        Assert.Contains(graph.Edges, fun edge ->
            edge.Role = EdgeRole.EnvironmentResultDestination && edge.Sources.Head = proof.Implementation)
        for call in calls do
            Assert.Equal<Set<int>>(Set.singleton 2, call.Omitted)
            Assert.Equal(3, call.Parameters.Length)
            Assert.DoesNotContain(call.Parameters.Head, DemandProjection.parameters graph proof.Implementation)
            Assert.Contains(call.Actuals[2], DemandProjection.deferredOnly graph)
            Assert.True(graph.Nodes[call.Actuals[2]].IsReachable)
            match graph.Nodes[call.Site].Kind with
            | SemanticKind.Application(_, actuals) -> Assert.Equal<NodeId list>(call.Actuals, actuals)
            | _ -> failwith "Expected original complete call"
        let creation =
            graph.Nodes.Values |> Seq.find (fun node ->
                match node.Kind with
                | SemanticKind.EnvironmentCreate(_, initializers) ->
                    node.IsReachable && not initializers.IsEmpty && proof.Participants.Contains node.Id
                | _ -> false)
        let initializer =
            match creation.Kind with
            | SemanticKind.EnvironmentCreate(_, initializers) -> snd initializers.Head
            | _ -> failwith "Expected actual environment formation"
        let replaceChildren children =
            let changed = { creation with Children = children }
            let unrelatedRows = graph.Edges |> List.filter (fun edge ->
                edge.Target <> creation.Id || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
            { graph with Nodes = graph.Nodes.Add(creation.Id, changed)
                         Edges = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence changed @ unrelatedRows }
            |> DemandRecipe.normalize
        for children in [[]; [initializer]] do
            let changed = replaceChildren children
            Assert.Contains(proof.Formal, DemandProjection.parameters changed proof.Implementation)
        for children in [[initializer; initializer]; [proof.Formal]] do
            let changed = replaceChildren children
            Assert.Empty(DemandProjection.parameters changed proof.Implementation)
        // An initializer remains an actual use even when it has no attached
        // child. Removing its resident derived row cannot erase Kind authority.
        let retained =
            graph.Nodes[proof.Implementation].Children
            |> List.filter (fun id -> id <> proof.Formal)
            |> List.find (fun id ->
                match graph.Nodes[id].Kind with SemanticKind.PatternBinding "offset" -> true | _ -> false)
        let noRecordedInitializer =
            let edges = graph.Edges |> List.filter (fun edge ->
                edge.Target <> creation.Id || edge.Role <> EdgeRole.EnvironmentInitializer)
            { graph with Edges = edges }
            |> DemandRecipe.normalize
        Assert.DoesNotContain(retained, DemandProjection.parameters noRecordedInitializer proof.Implementation)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Static literal commitment follows actual demand without removing typed source`` isEager =
        let argument = if isEager then "eager \"ACTUAL-DEMAND-ONLY\"" else "\"ACTUAL-DEMAND-ONLY\""
        let source =
            "module DemandPool\nlet discard (value: string) = 0\n[<EntryPoint>]\nlet main _ = discard (" + argument + ")\n"
        let graph = LazyResidenceFixture.programWith (Some source)
        let literal =
            graph.Nodes.Values
            |> Seq.filter (fun node -> node.IsReachable && node.Kind = SemanticKind.Literal(NativeLiteral.String "ACTUAL-DEMAND-ONLY"))
            |> Assert.Single
        let contributors =
            graph.StaticStringPool |> Option.map (fun pool -> pool.Entries |> List.collect _.NodeIds |> Set.ofList)
            |> Option.defaultValue Set.empty
        Assert.Equal<Set<NodeId>>((if isEager then Set.singleton literal.Id else Set.empty), contributors)
        Assert.Equal(isEager, graph.StaticStringPool.IsSome)
        Assert.Equal(not isEager, (DemandProjection.deferredOnly graph).Contains literal.Id)
        Assert.Equal(isEager, (DemandStrings.literalEvidence graph).ContainsKey literal.Id)
        Assert.Equal(Types.stringType, literal.Type)
        if not isEager then
            let missing = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.OrdinaryUnusedActual) }
            Assert.Empty(DemandStrings.literalEvidence missing)
            let restored, diagnostics = DemandStrings.settle missing
            Assert.Empty diagnostics
            Assert.Contains(restored.StaticStringPool.Value.Entries, fun entry -> List.contains literal.Id entry.NodeIds)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Unexecuted actuals retain numeric facts without a physical capacity commitment`` isEager =
        let argument = if isEager then "eager (100 * 100)" else "100 * 100"
        let graph = OrdinaryDemandFixture.check ("let discard (value: int) = 0\n[<EntryPoint>]\nlet main _ = discard (" + argument + ")\n")
        let offered: NumericRepresentation =
            { Name = "signed8"; Capability = "native"; Family = "int"; Bits = 8
              MinMagnitude = "-128"; MaxMagnitude = "127"; Boundary = "wrap" }
        let context = { LazyResidenceFixture.platform 64 with Representations = Map.ofList [offered.Name, offered] }
        let settled, diagnostics = DemandRanges.run (Some context) graph
        let formal = OrdinaryDemandFixture.formal settled
        let call = OrdinaryDemandFixture.calls settled formal |> Assert.Single
        let actual = settled.Nodes[call.Actuals.Head]
        Assert.Equal(Some(ValueRange.point 10000I), actual.ValueRange)
        Assert.True actual.IsReachable
        let capacity = diagnostics |> List.filter (fun diagnostic -> diagnostic.Code = "CCS8012")
        if isEager then Assert.NotEmpty capacity else Assert.Empty capacity

    [<Fact>]
    member _.``Unused actuals still require dimensionally valid source expressions`` () =
        let source = """module InvalidDeferredArgument
[<Measure>] type m
[<Measure>] type s
let discard (value: int<m>) = 0
[<EntryPoint>]
let main _ = discard (1<m> + 2<s>)
"""
        match parseAndCheck source "invalid-deferred-argument.clef" with
        | CheckFailure result ->
            Assert.NotEmpty(result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error))
        | result -> failwithf "Dimensionally invalid deferred argument was accepted: %A" result

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Unobservable arithmetic requires executable range evidence only when demanded`` isEager =
        let argument = if isEager then "eager (1 / 0)" else "1 / 0"
        let graph = OrdinaryDemandFixture.check ("let discard (value: int) = 0\n[<EntryPoint>]\nlet main _ = discard (" + argument + ")\n")
        let context = { LazyResidenceFixture.platform 64 with SubstrateKind = Some SubstrateKind.FPGA }
        let settled, diagnostics = DemandRanges.run (Some context) graph
        let formal = OrdinaryDemandFixture.formal settled
        let call = OrdinaryDemandFixture.calls settled formal |> Assert.Single
        Assert.True(settled.Nodes[call.Actuals.Head].IsReachable)
        let required = diagnostics |> List.filter (fun diagnostic -> diagnostic.Code = "CCS8011")
        if isEager then Assert.NotEmpty required else Assert.Empty required

    [<Theory>]
    [<InlineData("library")>]
    [<InlineData("callback")>]
    member _.``Open or family callback conventions acquire no direct omission permission`` defect =
        let source =
            if defect = "library" then "let discard (value: int) = 0\nlet useValue () = discard (1 + 2)\n"
            else "let discard (value: int) = 0\nlet invoke f value = f value\n[<EntryPoint>]\nlet main _ = invoke discard (1 + 2)\n"
        let graph = OrdinaryDemandFixture.check source
        let value = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.PatternBinding "value" -> true | _ -> false)
        Assert.False((DemandProjection.read graph).Formals.ContainsKey value.Id)

    [<Theory>]
    [<InlineData("formal-use")>]
    [<InlineData("callee")>]
    [<InlineData("escape")>]
    [<InlineData("hidden")>]
    [<InlineData("actual-type")>]
    [<InlineData("missing-row")>]
    [<InlineData("duplicate-row")>]
    member _.``Changed complete use and convention premises retract resident omission evidence`` defect =
        let graph = OrdinaryDemandFixture.check OrdinaryDemandFixture.source
        let proof = OrdinaryDemandFixture.formal graph
        let call = OrdinaryDemandFixture.calls graph proof |> List.head
        let changed =
            match defect with
            | "formal-use" ->
                let implementation = graph.Nodes[proof.Implementation]
                match implementation.Kind with
                | SemanticKind.Lambda(parameters, body, captures, scope, context) ->
                    let read = { graph.Nodes[proof.Formal] with Id = NodeId.fresh(); Kind = SemanticKind.VarRef("value", Some proof.Formal); Children = [] }
                    let result = { graph.Nodes[body] with Id = NodeId.fresh(); Kind = SemanticKind.Sequential [read.Id; body]; Children = [read.Id; body] }
                    let implementation = { implementation with Kind = SemanticKind.Lambda(parameters, result.Id, captures, scope, context)
                                                               Children = (parameters |> List.map (fun (_, _, id) -> id)) @ [result.Id] }
                    { graph with Nodes = graph.Nodes.Add(read.Id, read).Add(result.Id, result).Add(implementation.Id, implementation) }
                | _ -> failwith "Expected source lambda"
            | "callee" ->
                let callee = graph.Nodes[call.Callee]
                { graph with Nodes = graph.Nodes.Add(callee.Id, { callee with Kind = SemanticKind.VarRef("unknown", None); Children = [] }) }
            | "escape" -> { graph with DeclarationRoots = (proof.Implementation, DeclRoot.KernelModule) :: graph.DeclarationRoots }
            | "hidden" ->
                let row = { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentFormal; Sources = [proof.Implementation; proof.Implementation]
                            Target = proof.Formal; Ordinal = 0 }
                { graph with Edges = row :: graph.Edges }
            | "actual-type" ->
                let actual = graph.Nodes[call.Actuals.Head]
                { graph with Nodes = graph.Nodes.Add(actual.Id, { actual with Type = Types.boolType }) }
            | "missing-row" ->
                { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.OrdinaryUnusedFormal || edge.Target <> proof.Formal) }
            | _ ->
                let row = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.OrdinaryUnusedFormal && edge.Target = proof.Formal)
                { graph with Edges = row :: graph.Edges }
        Assert.Empty(DemandProjection.parameters changed proof.Implementation)
        Assert.Empty(DemandProjection.deferredActuals changed call.Site)
        if defect <> "missing-row" && defect <> "duplicate-row" then
            let fresh = DemandRecipe.normalize changed
            if defect = "callee" then
                // The changed opaque call loses its projection. The independent
                // surviving direct call may still prove the original formal unused.
                Assert.False((DemandProjection.read fresh).Calls.ContainsKey call.Site)
                Assert.Single(OrdinaryDemandFixture.calls fresh proof) |> ignore
            else Assert.Empty(DemandProjection.parameters fresh proof.Implementation)
        Assert.Equal<Set<NodeId>>(Set.singleton proof.Formal, DemandProjection.parameters graph proof.Implementation)

    [<Fact>]
    member _.``Unchanged projection is idempotent and does not change source reachability`` () =
        let graph = OrdinaryDemandFixture.check OrdinaryDemandFixture.source
        let next = DemandRecipe.normalize graph
        Assert.Equal<(EdgeClass * EdgeRole * NodeId list * NodeId * int) list>((graph.Edges |> List.map OrdinaryDemandFixture.key), (next.Edges |> List.map OrdinaryDemandFixture.key))
        Assert.Equal<Map<NodeId, bool>>(graph.Nodes |> Map.map (fun _ node -> node.IsReachable), next.Nodes |> Map.map (fun _ node -> node.IsReachable))

    [<Fact>]
    member _.``Emission receives the sealed projection and no same-shaped graph copy authority`` () =
        let graph = OrdinaryDemandFixture.witnessSource ()
        let expected = DemandProjection.project graph
        Assert.False expected.Parameters.IsEmpty
        Assert.False expected.Calls.IsEmpty
        Assert.False expected.DeferredOnly.IsEmpty
        Assert.Equal(Result.Ok expected, WitnessInput.tryOrdinary graph)
        Assert.Equal(Result.Ok (), WitnessInput.admit graph)
        Assert.Equal(Result.Ok expected, WitnessInput.tryOrdinary graph)
        let copy = { graph with Nodes = graph.Nodes }
        match WitnessInput.tryRead copy with
        | Result.Error _ -> ()
        | Result.Ok _ -> failwith "A different graph reference inherited an emission seal"
        Assert.Equal(Result.Ok (), WitnessInput.admit copy)
        Assert.Equal(Result.Ok expected, WitnessInput.tryOrdinary copy)

    [<Theory>]
    [<InlineData("missing row")>]
    [<InlineData("duplicate row")>]
    [<InlineData("wrong projection")>]
    member _.``Invalid source authority cannot seal even an empty fallback projection`` defect =
        let graph = OrdinaryDemandFixture.witnessSource ()
        let changed =
            match defect with
            | "missing row" ->
                { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.OrdinaryUnusedFormal) }
            | "duplicate row" ->
                let row = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.OrdinaryUnusedFormal)
                { graph with Edges = row :: graph.Edges }
            | _ -> { graph with Nodes = graph.Nodes }
        let facts = changed.Codata.Value
        let changed = { changed with Codata = lazy { facts with OrdinaryDemand = OrdinaryDemandProjection.empty } }
        match WitnessInput.admit changed, WitnessInput.tryRead changed with
        | Result.Error _, Result.Error _ -> ()
        | result -> failwithf "Invalid source/projection pair acquired emission authority: %A" result
        Assert.Equal(Result.Ok graph.Codata.Value.OrdinaryDemand, WitnessInput.tryOrdinary graph)

    [<Fact>]
    member _.``Target free source checking does not claim physical witness readiness`` () =
        let graph = OrdinaryDemandFixture.check OrdinaryDemandFixture.source
        Assert.True graph.Platform.IsNone
        Assert.False (DemandProjection.project graph).Calls.IsEmpty
        match WitnessInput.tryRead graph with
        | Result.Error _ -> ()
        | Result.Ok _ -> failwith "A target-free source check acquired physical emission authority."

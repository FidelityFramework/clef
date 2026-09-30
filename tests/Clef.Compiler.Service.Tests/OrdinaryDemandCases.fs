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
            let omittedSites =
                graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.OrdinaryUnusedActual)
                |> List.map _.Target |> Set.ofList
            let missing = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.OrdinaryUnusedActual) }
            Assert.Empty(DemandStrings.literalEvidence missing)
            let refused, diagnostics = DemandStrings.settle missing
            Assert.False refused.StaticStringPool.IsSome
            Assert.Equal<Set<NodeId>>(omittedSites, diagnostics |> List.map (fun diagnostic -> List.head diagnostic.RelatedNodes) |> Set.ofList)
            Assert.All(diagnostics, fun diagnostic ->
                Assert.Equal("CCS8403", diagnostic.Code)
                Assert.Equal(NativeDiagnosticSeverity.Error, diagnostic.Severity)
                Assert.Contains("PSG settlement (OrdinaryDemand)", diagnostic.Message)
                Assert.Equal(graph.Nodes[List.head diagnostic.RelatedNodes].Range, diagnostic.Range))
            let restored, restoredDiagnostics = DemandStrings.settle (DemandRecipe.normalize missing)
            Assert.Empty restoredDiagnostics
            Assert.False restored.StaticStringPool.IsSome
            Assert.Empty(DemandStrings.literalEvidence restored)
            Assert.Contains(literal.Id, DemandProjection.deferredOnly restored)
            Assert.Equal(literal.Kind, restored.Nodes[literal.Id].Kind)

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
        let source = "module OrdinaryDemand\nlet discard (value: int) = 0\n[<EntryPoint>]\nlet main _ = discard (" + argument + ")\n"
        let result =
            match parseAndCheck source "ordinary-demand.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "%A" errors
        let graph = result.Graph
        let sourceErrors = result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
        let assertUnobservable (diagnostic: Diagnostic) =
            Assert.Equal("CCS8011", diagnostic.Code)
            Assert.Contains("the result of '/'", diagnostic.Message)
            let site = Assert.Single diagnostic.RelatedNodes
            Assert.True graph.Nodes[site].IsReachable
            Assert.Equal(graph.Nodes[site].Range, diagnostic.Range)
        if isEager then assertUnobservable (Assert.Single sourceErrors) else Assert.Empty sourceErrors
        let context = { LazyResidenceFixture.platform 64 with SubstrateKind = Some SubstrateKind.FPGA }
        let settled, diagnostics = DemandRanges.run (Some context) graph
        let formal = OrdinaryDemandFixture.formal settled
        let call = OrdinaryDemandFixture.calls settled formal |> Assert.Single
        Assert.True(settled.Nodes[call.Actuals.Head].IsReachable)
        let required = diagnostics |> List.filter (fun diagnostic -> diagnostic.Code = "CCS8011")
        if isEager then assertUnobservable (Assert.Single required) else Assert.Empty required

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
        let failures =
            match DemandProjection.tryRead changed with
            | Result.Error failures -> failures
            | Result.Ok _ -> failwith "Changed ordinary-demand proof premises were admitted."
        let expectedSites =
            if defect = "missing-row" || defect = "duplicate-row" then Set.singleton proof.Formal
            else
                proof.Formal :: (OrdinaryDemandFixture.calls graph proof |> List.map _.Site)
                |> Set.ofList
        Assert.Equal<Set<NodeId>>(expectedSites, failures |> List.choose _.Occurrence |> Set.ofList)
        Assert.All(failures, fun failure ->
            Assert.Contains(failure.Occurrence.Value, failure.Participants)
            Assert.Contains(proof.Formal, failure.Participants)
            Assert.Contains("PSG settlement (OrdinaryDemand)", failure.Reason)
            Assert.Contains("OrdinaryUnusedFormal/OrdinaryUnusedActual rows do not match", failure.Reason))
        let sites = expectedSites |> Set.toList |> List.map (NodeId.value >> string) |> String.concat ", "
        let expectedRefusal =
            sprintf "PSG settlement (OrdinaryDemand) did not settle the ordinary-demand relations for the current graph: the published OrdinaryUnusedFormal/OrdinaryUnusedActual rows do not match the current complete use proof at nodes [%s]." sites
        let parameterRefusal = Assert.Throws<System.InvalidOperationException>(fun () -> DemandProjection.parameters changed proof.Implementation |> ignore)
        let actualRefusal = Assert.Throws<System.InvalidOperationException>(fun () -> DemandProjection.deferredActuals changed call.Site |> ignore)
        Assert.Equal(expectedRefusal, parameterRefusal.Message)
        Assert.Equal(expectedRefusal, actualRefusal.Message)
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
    member _.``Emission reads graph-owned projection across unchanged graph copies`` () =
        let graph = OrdinaryDemandFixture.witnessSource ()
        let expected = DemandProjection.project graph
        Assert.False expected.Parameters.IsEmpty
        Assert.False expected.Calls.IsEmpty
        Assert.False expected.DeferredOnly.IsEmpty
        Assert.Equal(Result.Ok expected, WitnessInput.tryOrdinary graph)
        Assert.Equal(Result.Ok (), WitnessInput.admit graph)
        Assert.Equal(Result.Ok expected, WitnessInput.tryOrdinary graph)
        let copy = { graph with Nodes = graph.Nodes }
        Assert.Equal(WitnessInput.tryRead graph, WitnessInput.tryRead copy)
        Assert.Equal(Result.Ok (), WitnessInput.admit copy)
        Assert.Equal(Result.Ok expected, WitnessInput.tryOrdinary copy)

    [<Theory>]
    [<InlineData("missing row")>]
    [<InlineData("duplicate row")>]
    [<InlineData("wrong projection")>]
    member _.``Source validation rejects invalid proof rows and mismatched held projections`` defect =
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
        match WitnessInput.admit changed with
        | Result.Error _ -> ()
        | result -> failwithf "Invalid source/projection pair passed source validation: %A" result
        let draft = WitnessInput.invalidate changed
        match WitnessInput.tryRead draft with
        | Result.Error _ -> ()
        | result -> failwithf "An edited source draft retained publication: %A" result
        Assert.Equal(Result.Ok graph.Codata.Value.OrdinaryDemand, WitnessInput.tryOrdinary graph)

    [<Fact>]
    member _.``Target free source checking does not claim physical witness readiness`` () =
        let graph = OrdinaryDemandFixture.check OrdinaryDemandFixture.source
        Assert.True graph.Platform.IsNone
        Assert.False (DemandProjection.project graph).Calls.IsEmpty
        match WitnessInput.tryRead graph with
        | Result.Error _ -> ()
        | Result.Ok _ -> failwith "A target-free source check acquired physical emission authority."

    [<Theory>]
    [<InlineData("node")>]
    [<InlineData("edges")>]
    [<InlineData("root")>]
    [<InlineData("platform")>]
    [<InlineData("map")>]
    [<InlineData("filter")>]
    member _.``Source edit APIs invalidate publication without revoking the old snapshot`` edit =
        let graph = OrdinaryDemandFixture.witnessSource ()
        let original = WitnessInput.tryRead graph
        Assert.True(Result.isOk original)
        let node = graph.Nodes.Values |> Seq.head
        let changed =
            match edit with
            | "node" -> Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.addNode node graph
            | "edges" -> Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.addEdges [] graph
            | "root" -> Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.addDeclarationRoot node.Id DeclRoot.EntryPoint graph
            | "platform" -> Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withPlatform graph.Platform.Value graph
            | "map" -> Clef.Compiler.PSGSaturation.SemanticGraph.Traversal.map id graph
            | _ -> Clef.Compiler.PSGSaturation.SemanticGraph.Traversal.filter (fun _ -> true) graph
        Assert.True(Result.isError(WitnessInput.tryRead changed))
        Assert.Equal(original, WitnessInput.tryRead graph)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``An ordinary snapshot first reads at its dominating demand and later uses retain that binding`` conditionDemand =
        let body =
            if conditionDemand then """
    let mutable observed = 0
    if snapshot = 2 then observed <- 1 else observed <- -1
    current <- 3
    if snapshot = 2 then observed else -1
"""
            else """
    let first = eager snapshot
    current <- 3
    let second = eager snapshot
    if first = 2 && second = 2 then 0 else 1
"""
        let graph = OrdinaryDemandFixture.check ("""
[<EntryPoint>]
let main _ =
    let mutable current = 1
    let snapshot = current
    current <- 2
""" + body)
        let binding name = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single
        let current, snapshot = binding "current", binding "snapshot"
        Assert.Equal(formatType current.Type, formatType snapshot.Type)
        let read = graph.Nodes[Assert.Single snapshot.Children]
        match read.Kind with
        | SemanticKind.VarRef(_, Some source) -> Assert.Equal(current.Id, source)
        | kind -> failwithf "The deferred snapshot lost its original mutable-cell read: %A" kind
        let uses = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.VarRef(_, Some source) -> source = snapshot.Id | _ -> false) |> Seq.toList
        Assert.Equal(2, uses.Length)
        let startup = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read graph |> Option.get
        let rec statements id =
            let node = graph.Nodes[id]
            match node.Kind with
            | SemanticKind.Sequential values ->
                Assert.Equal<NodeId list>(values, node.Children)
                values |> List.collect statements
            | _ -> [id]
        let sequence = statements startup.OriginalBody
        Assert.Single(sequence |> List.filter ((=) snapshot.Id)) |> ignore
        let write value =
            graph.Nodes.Values |> Seq.filter (fun node ->
                if not node.IsReachable then false else
                match node.Kind with
                | SemanticKind.Set(target, assigned) ->
                    match graph.Nodes[target].Kind, graph.Nodes[assigned].Kind with
                    | SemanticKind.VarRef(_, Some source), SemanticKind.Literal(NativeLiteral.Int(actual, _)) -> source = current.Id && actual = value
                    | _ -> false
                | _ -> false)
            |> Assert.Single
        let firstDemand, secondDemand =
            if conditionDemand then
                match sequence |> List.filter (fun id -> match graph.Nodes[id].Kind with SemanticKind.IfThenElse _ -> true | _ -> false) with
                | [first; second] -> first, second
                | values -> failwithf "Expected two demanded source conditions: %A" values
            else (binding "first").Id, (binding "second").Id
        let position id = sequence |> List.findIndex ((=) id)
        Assert.True(position (write 2L).Id < position snapshot.Id,
                    "The ordinary snapshot still reads its mutable cell before the write preceding its first demand.")
        Assert.True(position snapshot.Id < position firstDemand)
        Assert.True(position firstDemand < position (write 3L).Id)
        Assert.True(position (write 3L).Id < position secondDemand)

    [<Fact>]
    member _.``A snapshot alias family moves together and numeric analysis sees the delayed value`` () =
        let graph = OrdinaryDemandFixture.check """
[<EntryPoint>]
let main _ =
    let mutable current = 1
    let snapshot = current
    let alias = snapshot
    current <- 257
    let first = eager alias
    current <- 3
    let second = eager snapshot
    if first = 257 && second = 257 then 0 else 1
"""
        let named name = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single
        let snapshot, alias = named "snapshot", named "alias"
        let schedule = Clef.Compiler.Baker.Ingredients.BindingDemand.analyze graph |> Assert.Single
        Assert.Equal<NodeId list>([snapshot.Id; alias.Id], schedule.Family)
        Assert.True(schedule.Pending.IsNone, sprintf "%A" schedule.Pending)
        Assert.Equal<NodeId list>(schedule.Desired, schedule.Slots |> List.map _.Statement)
        Assert.Empty(Clef.Compiler.Baker.Ingredients.BindingDemand.failures graph)
        for node in [snapshot; alias; named "first"; named "second"] do
            match node.ValueRange with
            | Some(ValueRange.Bounded(lower, upper)) -> Assert.True(lower <= 257I && upper >= 257I, sprintf "The delayed value 257 was excluded from %A: %A" node.Id node.ValueRange)
            | value -> failwithf "Expected a finite post-scheduling range for %A, got %A" node.Id value
        let history = graph.Edges |> List.filter (fun edge ->
            edge.Target = snapshot.Id && match edge.Role with EdgeRole.OrdinaryBindingDemandHistory _ -> true | _ -> false) |> Assert.Single
        let original = match history.Role with EdgeRole.OrdinaryBindingDemandHistory evidence -> evidence | _ -> failwith "Expected input history"
        let originalOrder = original.Participants |> List.filter (fun p -> p.Role = ParticipantRole.DemandStatement) |> List.sortBy _.Ordinal |> List.map _.Node
        Assert.NotEqual<NodeId list>(originalOrder, schedule.Desired)
        Assert.Equal(snapshot.Type, alias.Type)
        let settled, diagnostics = Clef.Compiler.Nanopass.BindingDemand.settle graph
        Assert.Empty diagnostics
        Assert.Equal<(EdgeClass * EdgeRole * NodeId list * NodeId * int) list>(graph.Edges |> List.map OrdinaryDemandFixture.key, settled.Edges |> List.map OrdinaryDemandFixture.key)

    [<Theory>]
    [<InlineData("role")>]
    [<InlineData("ordinal")>]
    [<InlineData("group")>]
    [<InlineData("type")>]
    member _.``Current snapshot demand evidence rejects changed roles order grouping and native types`` defect =
        let graph = OrdinaryDemandFixture.check """
[<EntryPoint>]
let main _ =
    let mutable current = 1
    let snapshot = current
    current <- 257
    let first = eager snapshot
    current <- 3
    let second = eager snapshot
    if first = 257 && second = 257 then 0 else 1
"""
        let row = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.OrdinaryBindingDemand _ -> true | _ -> false) |> Assert.Single
        let evidence = match row.Role with EdgeRole.OrdinaryBindingDemand evidence -> evidence | _ -> failwith "Expected current evidence"
        let changedEvidence =
            if defect = "type" then { evidence with SourceTypes = evidence.SourceTypes.Add(row.Target, Clef.Compiler.NativeTypedTree.TypeIdentities.ofType Types.boolType) }
            else
                let index = evidence.Participants |> List.findIndex (fun p -> p.Role = ParticipantRole.DemandUse)
                let participants =
                    evidence.Participants |> List.mapi (fun i p ->
                        if i <> index then p else
                        match defect with
                        | "role" -> { p with Role = ParticipantRole.DemandInitializer }
                        | "ordinal" -> { p with Ordinal = p.Ordinal + 1 }
                        | _ -> { p with Group = row.Target })
                { evidence with Participants = participants }
        let changed = { graph with Edges = graph.Edges |> List.map (fun edge -> if OrdinaryDemandFixture.key edge = OrdinaryDemandFixture.key row then { edge with Role = EdgeRole.OrdinaryBindingDemand changedEvidence } else edge) }
        Assert.NotEmpty(Clef.Compiler.Baker.Ingredients.BindingDemand.failures changed)
        Assert.True(Result.isError(DemandProjection.projectValidated changed))
        Assert.Equal<Set<NodeId>>(Set.ofList(evidence.Participants |> List.map _.Node), Set.ofList(changedEvidence.Participants |> List.map _.Node))

    [<Theory>]
    [<InlineData("independent-reference")>]
    [<InlineData("shared-initializer")>]
    [<InlineData("capture")>]
    [<InlineData("unknown-capture")>]
    member _.``An additional snapshot use cannot disappear from the demand census`` defect =
        let graph = OrdinaryDemandFixture.check """
[<EntryPoint>]
let main _ =
    let mutable current = 1
    let snapshot = current
    current <- 257
    let first = eager snapshot
    if first = 257 then 0 else 1
"""
        let schedule = Clef.Compiler.Baker.Ingredients.BindingDemand.analyze graph |> Assert.Single
        let plan = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read graph |> Option.get
        let changed =
            if defect = "shared-initializer" then
                let read = graph.Nodes[schedule.Binding].Children |> Assert.Single
                let holder = { graph.Nodes[read] with Id = NodeId.fresh(); Kind = SemanticKind.EagerExpr read; Children = [read]; Parent = None }
                { graph with Nodes = graph.Nodes.Add(holder.Id, holder) }
            elif defect = "independent-reference" then
                let row = { Class = EdgeClass.Reference; Role = EdgeRole.Resides; Sources = [schedule.Binding]; Target = plan.OriginalBody; Ordinal = 0 }
                { graph with Edges = row :: graph.Edges }
            else
                let owner = graph.Nodes[plan.SourceLambda]
                let capture = { Name = "snapshot"; Type = graph.Nodes[schedule.Binding].Type; IsMutable = false; SourceNodeId = if defect = "capture" then Some schedule.Binding else None }
                let kind = match owner.Kind with SemanticKind.Lambda(parameters, body, captures, owner, context) -> SemanticKind.Lambda(parameters, body, capture :: captures, owner, context) | _ -> failwith "Expected source activation"
                { graph with Nodes = graph.Nodes.Add(owner.Id, { owner with Kind = kind }) }
        Assert.NotEmpty(Clef.Compiler.Baker.Ingredients.BindingDemand.failures changed)
        let settled, diagnostics = Clef.Compiler.Nanopass.BindingDemand.settle changed
        Assert.Contains(diagnostics, fun diagnostic -> diagnostic.Code = "CCS8403" && diagnostic.Range = graph.Nodes[schedule.Binding].Range)
        Assert.Contains(settled.Edges, fun edge -> edge.Target = schedule.Binding && match edge.Role with EdgeRole.OrdinaryBindingDemandPending _ -> true | _ -> false)

    [<Theory>]
    [<InlineData("branch")>]
    [<InlineData("loop")>]
    [<InlineData("discard")>]
    member _.``A branch loop or discarded expression is not an unconditional snapshot frontier`` shape =
        let useText =
            match shape with
            | "branch" -> "if current = 257 then\n        let forced = eager snapshot\n        forced\n    else 0"
            | "loop" -> "while current < 258 do\n        let forced = eager snapshot\n        current <- forced + 1\n    0"
            | _ -> "snapshot\n    0"
        let source = "module UnsupportedDemand\n[<EntryPoint>]\nlet main _ =\n    let mutable current = 1\n    let snapshot = current\n    current <- 257\n    " + useText + "\n"
        match parseAndCheck source "unsupported-demand.clef" with
        | Success result | CheckFailure result ->
            let pending = result.Graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.OrdinaryBindingDemandPending _ -> true | _ -> false)
            Assert.NotEmpty pending
            Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8403" && diagnostic.Message.Contains("OrdinaryBindingDemand"))
        | ParseFailure errors -> failwithf "The negative source fixture did not parse: %A" errors

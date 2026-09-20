namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Startup = Clef.Compiler.Nanopass.ProgramInitialization
module StartupFacts = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization

module private ProgramInitializationFixture =
    let source = """
let mutable trace = 0
let first = trace <- 1
let advance () = trace <- 2
let unused = advance ()
[<EntryPoint>]
let main _ = trace
"""
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result.Graph
    let plan graph = StartupFacts.read graph |> Option.defaultWith (fun () -> failwith "Missing validated startup plan")
    let name (graph: SemanticGraph) id = match graph.Nodes[id].Kind with SemanticKind.Binding(name, _, _, _) -> name | _ -> failwith "Expected a declaration"
    let platform =
        { PlatformId = "startup-structure-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
          Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None
          PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.empty
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProgramInitialization")>]
type ProgramInitializationCases() =
    [<Fact>]
    member _.``Unreachable declaration errors cannot erase executable startup ownership``() =
        let result = DimensionalCases.check "let unused = fun () -> true + 1\nlet value = 7\n[<EntryPoint>]\nlet main _ = value"
        let rawErrors = result.Diagnostics |> List.filter (fun diagnostic -> diagnostic.Severity = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error)
        Assert.NotEmpty rawErrors
        Assert.DoesNotContain(rawErrors, fun diagnostic ->
            Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.Diagnostic.effectiveSeverity diagnostic = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error)
        let plan = ProgramInitializationFixture.plan result.Graph
        Assert.Equal<string list>(["value"], plan.Initializers |> List.map (fun row -> ProgramInitializationFixture.name result.Graph row.Binding))
        Assert.True(result.Graph.Nodes[plan.EntryLambda].IsReachable)
        let invalid = DimensionalCases.check "let value = true + 1\n[<EntryPoint>]\nlet main _ = 0"
        Assert.Contains(invalid.Diagnostics, fun diagnostic ->
            Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.Diagnostic.effectiveSeverity diagnostic = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error)
        Assert.True((StartupFacts.read invalid.Graph).IsSome)

    [<Fact>]
    member _.``Unused eager effects occur in source order before the preserved source entry``() =
        let graph = ProgramInitializationFixture.check ProgramInitializationFixture.source
        let plan = ProgramInitializationFixture.plan graph
        Assert.Equal<string list>(["trace"; "first"; "unused"], plan.Initializers |> List.map (fun row -> ProgramInitializationFixture.name graph row.Binding))
        Assert.Equal("main", plan.Symbol)
        Assert.Equal("main", ProgramInitializationFixture.name graph plan.SourceBinding)
        Assert.Equal("__clef_program_entry", ProgramInitializationFixture.name graph plan.EntryBinding)
        Assert.NotEqual(plan.EntryLambda, plan.SourceLambda)
        Assert.Equal<(NodeId * DeclRoot) list>([plan.EntryBinding, DeclRoot.EntryPoint], graph.DeclarationRoots)
        Assert.True(plan.Initializers |> List.forall (fun row -> graph.Nodes[row.Binding].IsReachable))
        Assert.Single(graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding("main", _, _, _) -> true | _ -> false)) |> ignore

    [<Fact>]
    member _.``Module membership retains lexical identity without execution ownership``() =
        let graph = ProgramInitializationFixture.check ProgramInitializationFixture.source
        let plan = ProgramInitializationFixture.plan graph
        for row in plan.Initializers do
            Assert.Equal(Some row.Module, graph.Nodes[row.Binding].Parent)
            Assert.Empty(graph.Nodes[row.Module].Children)
            let membership = kindEdges row.Module graph.Nodes[row.Module].Kind
                             |> List.filter (fun edge -> edge.Sources = [row.Binding]) |> Assert.Single
            Assert.Equal(EdgeClass.Reference, membership.Class)
            Assert.Equal(EdgeRole.Member, membership.Role)
            Assert.Contains(kindEdges plan.Spine graph.Nodes[plan.Spine].Kind, fun edge ->
                edge.Class = EdgeClass.Structural && edge.Sources = [row.Binding])
        for edge in graph.Edges |> List.filter (fun edge ->
            match edge.Role with EdgeRole.ProgramInitialization | EdgeRole.ProgramInitializer | EdgeRole.ProgramEntryCall | EdgeRole.ProgramValueIntent | EdgeRole.ProgramUnitActivation -> true | _ -> false) do
            Assert.All(edge.Target :: edge.Sources, fun id -> Assert.True(graph.Nodes.ContainsKey id))
        let units = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ProgramUnitActivation)
        Assert.NotEmpty units
        for unit in units do
            Assert.Contains(plan.EntryLambda, unit.Sources)
            Assert.Contains(plan.SourceBinding, unit.Sources)
            match graph.Nodes[unit.Target].Kind with
            | SemanticKind.ModuleDef _ -> ()
            | kind -> failwithf "Unit activation lost its module identity: %A" kind

    [<Fact>]
    member _.``Calling the source entry again cannot execute the startup spine``() =
        let graph = ProgramInitializationFixture.check ProgramInitializationFixture.source
        let plan = ProgramInitializationFixture.plan graph
        match graph.Nodes[plan.SourceLambda].Kind with
        | SemanticKind.Lambda(parameters, body, _, _, _) ->
            Assert.Equal(plan.OriginalBody, body)
            Assert.NotEqual(plan.Spine, body)
            match graph.Nodes[plan.EntryCall].Kind with
            | SemanticKind.Application(callee, arguments) ->
                Assert.Equal(parameters.Length, arguments.Length)
                match graph.Nodes[callee].Kind with
                | SemanticKind.VarRef(_, Some definition) -> Assert.Equal(plan.SourceBinding, definition)
                | kind -> failwithf "Source call identity was replaced: %A" kind
            | kind -> failwithf "Expected an ordinary source call: %A" kind
        | kind -> failwithf "Source entry Lambda was replaced: %A" kind
        let again, diagnostics = Startup.normalize [] graph
        Assert.Empty diagnostics
        Assert.Same(graph, again)

    [<Fact>]
    member _.``Missing runtime space authority retains exact slot intent and diagnostic``() =
        let graph = ProgramInitializationFixture.check ProgramInitializationFixture.source
        let plan = ProgramInitializationFixture.plan graph
        let value = Assert.Single plan.ValueBindings
        Assert.True(StartupFacts.isSlotBinding graph value)
        Assert.True((StartupFacts.tryValueAuthority graph value).IsNone)
        let before = graph.Nodes
        let settled, diagnostics = Startup.settleValueAuthority true { graph with Platform = Some ProgramInitializationFixture.platform }
        let diagnostic = Assert.Single diagnostics
        Assert.Equal("CCS8403", diagnostic.Code)
        Assert.Equal<NodeId list>([value], diagnostic.RelatedNodes)
        Assert.Contains("explicit writable program space", diagnostic.Message)
        Assert.True(StartupFacts.isSlotBinding settled value)
        Assert.Same(before, settled.Nodes)

    [<Fact>]
    member _.``Missing call incidence and reordered initializer execution retract the plan``() =
        let graph = ProgramInitializationFixture.check ProgramInitializationFixture.source
        let plan = ProgramInitializationFixture.plan graph
        let missing = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramEntryCall) }
        Assert.True((StartupFacts.read missing).IsNone)
        let _, residuals = Startup.settleValueAuthority true { missing with Platform = Some ProgramInitializationFixture.platform }
        let residual = Assert.Single residuals
        Assert.Equal("CCS8403", residual.Code)
        Assert.Equal<NodeId list>([plan.Spine], residual.RelatedNodes)
        Assert.Contains("storage intent no longer agree", residual.Message)
        let spine = graph.Nodes[plan.Spine]
        let actions = match spine.Kind with SemanticKind.Sequential actions -> actions | _ -> failwith "Expected startup sequence"
        let changed = { spine with Kind = SemanticKind.Sequential(List.rev actions); Children = List.rev actions }
        Assert.True((StartupFacts.read { graph with Nodes = graph.Nodes.Add(spine.Id, changed) }).IsNone)
        Assert.True((StartupFacts.read graph).IsSome)

    [<Fact>]
    member _.``Explicit preparation preserves the ordered initializer relation``() =
        let graph = ProgramInitializationFixture.check ProgramInitializationFixture.source
        let plan = ProgramInitializationFixture.plan graph
        let spine = graph.Nodes[plan.Spine]
        let actions = match spine.Kind with SemanticKind.Sequential actions -> actions | _ -> failwith "Expected startup sequence"
        let preparation = { spine with Id = NodeId.fresh(); Kind = SemanticKind.Literal NativeLiteral.Unit
                                       Type = Types.unitType; Children = []; Parent = Some spine.Id }
        let replacement = { spine with Kind = SemanticKind.Sequential(preparation.Id :: actions); Children = preparation.Id :: actions }
        let prepared = { graph with Nodes = graph.Nodes.Add(preparation.Id, preparation).Add(spine.Id, replacement) }
        Assert.Equal(plan.EntryBinding, (ProgramInitializationFixture.plan prepared).EntryBinding)
        Assert.Equal(plan.ValueBindings, (ProgramInitializationFixture.plan prepared).ValueBindings)

    [<Fact>]
    member _.``Freestanding startup has one true entry and a zero-formal unit signature``() =
        let graph = ProgramInitializationFixture.check "let run (_: string array) = 0"
        let source = graph.Nodes.Values |> Seq.find (fun node -> match node.Kind with SemanticKind.Binding("run", _, _, _) -> true | _ -> false)
        let source = { source with Kind = SemanticKind.Binding("run", false, false, Some DeclRoot.EntryPoint) }
        let roots = graph.Nodes.Values |> Seq.choose (fun node -> match node.Kind with SemanticKind.ModuleDef("Dimensions", _) -> Some node.Id | _ -> None) |> Seq.toList
        let platform = { ProgramInitializationFixture.platform with FreestandingStartup = Some FreestandingStartup.defaultLinux_x86_64 }
        let prepared, diagnostics = Startup.normalize roots { graph with Nodes = graph.Nodes.Add(source.Id, source);
                                                                        DeclarationRoots = [source.Id, DeclRoot.EntryPoint]; Platform = Some platform }
        Assert.Empty diagnostics
        let plan = ProgramInitializationFixture.plan prepared
        Assert.Equal("_start", plan.Symbol)
        Assert.Equal(source.Id, plan.SourceBinding)
        match prepared.Nodes[plan.EntryLambda].Kind with
        | SemanticKind.Lambda([], _, [], _, _) -> Assert.True(prepared.Nodes[plan.EntryLambda].Type = Types.unitType)
        | kind -> failwithf "Unexpected freestanding formal shape: %A" kind
        Assert.Single prepared.DeclarationRoots |> ignore

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Pruning preserves non-executable evidence and pending target declaration identities`` targetDeclaration =
        let graph = ProgramInitializationFixture.check ProgramInitializationFixture.source
        let plan = ProgramInitializationFixture.plan graph
        let orphan = { graph.Nodes[plan.Spine] with Id = NodeId.fresh(); Kind = SemanticKind.Literal NativeLiteral.Unit;
                                                 Type = Types.unitType; Children = []; Parent = None }
        let incidence = { Sources = [orphan.Id; plan.SourceBinding]; Target = plan.Spine
                          Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0 }
        let graph = { graph with Nodes = graph.Nodes.Add(orphan.Id, orphan)
                                 Edges = if targetDeclaration then [] else incidence :: graph.Edges
                                 Platform = if targetDeclaration then Some ProgramInitializationFixture.platform else None }
        let pruned = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.pruneUnreachable graph
        Assert.Equal(graph.Nodes.Count, pruned.Nodes.Count)
        Assert.False(pruned.Nodes[orphan.Id].IsReachable)
        Assert.True(pruned.Nodes[plan.EntryLambda].IsReachable)
        for edge in pruned.Edges do
            Assert.All(edge.Target :: edge.Sources, fun id -> Assert.True(pruned.Nodes.ContainsKey id))

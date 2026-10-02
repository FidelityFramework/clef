namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module LiveScope = Clef.Compiler.Baker.Recipes.WitnessScopeRecipes

module WitnessLiveScopeCases =
    let private admitted graph =
        match LiveScope.project graph with
        | Result.Ok plan -> plan
        | Result.Error failures -> failwithf "Unexpected source-scope refusal: %A" failures

    let private refused (reason: string) graph =
        match LiveScope.project graph with
        | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains reason)
        | Result.Ok _ -> failwith "Malformed source incidence was admitted"

    let private library extra =
        "module ScopedLibrary\nlet leaf (x: int) = x + 1\nlet chosen (x: int) = leaf x\nlet dormant (x: int) = x - 1\n"
        + ([1..extra] |> List.map (fun index -> $"let extra{index} (x: int) = x + {index}\n") |> String.concat "")

    let private project extra opened useLibrary =
        let files = [
            "write-authority.clef", IntrinsicWriteFixture.authority
            "ScopedLibrary.clef", library extra
            "ScopeClient.clef", "module ScopeClient\n" + (if opened then "open ScopedLibrary" else "// open ScopedLibrary")
                                 + "\n[<EntryPoint>]\nlet main _ = " + (if useLibrary then "chosen 2" else "0") + "\n" ]
        let inputs = files |> List.map (fun (file, text) ->
            match parseStringWithDefaults text file with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Live-scope fixture did not parse: %A" errors)
        let result = checkParsedInputsWithPlatformAndSources inputs (Some IntrinsicWriteFixture.platform) (Set.singleton "ScopeClient.clef")
        Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic -> diagnostic.Severity = NativeDiagnosticSeverity.Error))
        result.Graph

    let private bodiesIn file (plan: WitnessLiveScopePlan) =
        plan.Occurrences.Values |> Seq.filter (fun row -> row.Body.Range.File = file) |> Seq.toList

    let private marked nodes root =
        let builder = NodeBuilder()
        let node = builder.Create(SemanticKind.Sequential nodes, Types.intType, dummyRange, children = nodes)
        let graph = builder.Build [(node.Id, DeclRoot.EntryPoint)]
        { graph with Nodes = root graph.Nodes node.Id }, node.Id

    let tests = [
        "An unused open cannot add a dependency body to the source scope", fun () ->
            let absent = project 0 false false |> admitted
            let openedGraph = project 0 true false
            let opened = admitted openedGraph
            Assert.Empty(bodiesIn "ScopedLibrary.clef" absent)
            Assert.Empty(bodiesIn "ScopedLibrary.clef" opened)
            Assert.Equal(absent.Occurrences.Count, opened.Occurrences.Count)
            for row in opened.Occurrences.Values do
                Assert.True(row.Body.IsReachable)
                Assert.Same(openedGraph.Nodes[row.Body.Id], row.Body)

        "Unused library growth does not enlarge source live bodies", fun () ->
            let original = project 0 true true |> admitted
            let grownGraph = project 64 true true
            let grown = admitted grownGraph
            Assert.Equal(original.Occurrences.Count, grown.Occurrences.Count)
            Assert.Equal((bodiesIn "ScopedLibrary.clef" original).Length, (bodiesIn "ScopedLibrary.clef" grown).Length)
            Assert.DoesNotContain(grown.Occurrences.Values, fun row -> row.Body.Range.File = "ScopedLibrary.clef" && row.Body.Range.Start.Line > 4)
            Assert.True(grownGraph.Nodes.Count > grown.Occurrences.Count)

        "Explicit source entries contain demanded definitions rather than a module census", fun () ->
            let graph = project 64 true true
            let plan = admitted graph
            let entryNames = plan.Entries |> List.choose (fun entry ->
                match plan.Occurrences.TryFind entry.Focus with
                | Some { Body = { Kind = SemanticKind.Binding(name, _, _, _) } } -> Some name
                | _ -> None) |> Set.ofList
            Assert.Contains("chosen", entryNames)
            Assert.Contains("leaf", entryNames)
            Assert.DoesNotContain("dormant", entryNames)
            Assert.DoesNotContain(plan.Entries, fun entry ->
                match plan.Occurrences.TryFind entry.Focus with Some { Body = { Kind = SemanticKind.ModuleDef _ } } -> true | _ -> false)
            for entry in plan.Entries do
                Assert.Contains(entry.Context, plan.Contexts[entry.Focus])

        "Resolved uses retain source binding class without a declaration body read", fun () ->
            let graph = project 0 true true
            let plan = admitted graph
            Assert.NotEmpty plan.BindingUses
            for KeyValue(site, useContract) in plan.BindingUses do
                let declaration = graph.Nodes[useContract.Binding]
                match declaration.Kind with
                | SemanticKind.PatternBinding name ->
                    Assert.Equal(name, useContract.Name)
                    Assert.Equal(WitnessBindingClass.Formal, useContract.Class)
                    Assert.False(useContract.IsProgramSlotIntent)
                | SemanticKind.Binding(name, mutableCell, _, _) ->
                    Assert.Equal(name, useContract.Name)
                    Assert.Equal((if mutableCell then WitnessBindingClass.MutableCell else WitnessBindingClass.ImmutableValue), useContract.Class)
                | other -> failwithf "Use named an unsupported declaration %A" other
                match plan.Occurrences[site].Body.Kind with
                | SemanticKind.VarRef(_, Some binding) -> Assert.Equal(binding, useContract.Binding)
                | other -> failwithf "Binding-use contract was stored on %A" other

        "Program slot intent survives a missing physical authority instead of becoming inline", fun () ->
            let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.writableAuthority IntrinsicWriteFixture.bindingBody
            DimensionalCases.noErrors result
            let graph = result.Graph
            let emission = graph.Codata.Value.WitnessEmission |> Option.defaultWith (fun () -> failwith "No admitted source emission")
            let binding = graph.Nodes.Values |> Seq.find (fun node -> match node.Kind with SemanticKind.Binding("msg", _, _, _) -> true | _ -> false)
            Assert.Contains(binding.Id, emission.Storage.Startup.Value.ValueBindings)
            Assert.Contains(binding.Id, emission.Storage.SlotAuthorities)
            let missingAuthority = { emission with Storage = { emission.Storage with SlotAuthorities = emission.Storage.SlotAuthorities.Remove binding.Id } }
            let plan = LiveScope.projectWithEmission missingAuthority graph |> Result.defaultWith (sprintf "%A" >> failwith)
            let reads = plan.BindingUses.Values |> Seq.filter (fun useContract -> useContract.Binding = binding.Id) |> Seq.toList
            Assert.NotEmpty reads
            for useContract in reads do
                Assert.True(useContract.IsProgramSlotIntent)
                Assert.False(useContract.HasProgramSlotAuthority)

        "A marked proof citizen remains a claim identity instead of an executable body", fun () ->
            let builder = NodeBuilder()
            let claim : ObligationInfo =
                { Id = "body-free-control"; Kind = "control"; Logic = "QF_LIA"
                  Statement = "True control"; Source = "control.clef:1:1"; Refs = []
                  Body = ObligationBody.IntegerLiteralRange(0I, 0I, 0I) }
            let proof = builder.Create(SemanticKind.Obligation claim, Types.unitType, dummyRange)
            let executable = builder.Create(SemanticKind.Sequential [proof.Id], Types.unitType, dummyRange, children = [proof.Id])
            let plan = builder.Build [(executable.Id, DeclRoot.EntryPoint)] |> admitted
            Assert.False(plan.Occurrences.ContainsKey proof.Id)
            Assert.Equal<WitnessChildDisposition list>([{ Ordinal = 0; Traversal = WitnessChildTraversal.SourceOmitted(plan.Support, proof.Id) }], plan.Occurrences[executable.Id].Children)

        "An actual library lookup keeps its compact original source declaration port", fun () ->
            let graph = project 0 true true
            let plan = admitted graph
            let declaration name =
                graph.Nodes.Values |> Seq.find (fun node ->
                    node.Range.File = "ScopedLibrary.clef" &&
                    match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
            let chosen, leaf, dormant = declaration "chosen", declaration "leaf", declaration "dormant"
            let container =
                graph.Modules[["ScopedLibrary"]] |> List.map (fun id -> graph.Nodes[id])
                |> List.find (fun node -> match node.Kind with SemanticKind.ModuleDef _ -> true | _ -> false)
            let members = match container.Kind with SemanticKind.ModuleDef(_, members) -> members | _ -> failwith "Expected source module"
            Assert.Equal<NodeId list>([leaf.Id; chosen.Id; dormant.Id], members)
            Assert.Empty(container.Children)
            Assert.False(container.IsReachable)
            Assert.False(plan.Occurrences.ContainsKey container.Id)
            Assert.False(plan.Occurrences.ContainsKey dormant.Id)
            Assert.Contains(container.Id, plan.ContextIdentities)
            Assert.DoesNotContain(dormant.Id, plan.ContextIdentities)
            Assert.Equal<WitnessOccurrenceBreadcrumb list list>([[]], plan.Contexts[container.Id])
            for used in [leaf; chosen] do
                Assert.Same(used, plan.Occurrences[used.Id].Body)
                let crumb = plan.Occurrences[used.Id].Contexts |> Assert.Single |> Assert.Single
                let ordinal = members |> List.findIndex ((=) used.Id)
                Assert.Equal(container.Id, crumb.Parent)
                Assert.Equal(WitnessOccurrencePort.ModuleDeclaration, crumb.Port)
                Assert.Equal(ordinal, crumb.Ordinal)
                Assert.Equal(members.Length, crumb.Extent)
                Assert.False(System.String.IsNullOrWhiteSpace crumb.Stamp)
                let account = plan.ContextHeaders[container.Id].Ports[WitnessOccurrencePort.ModuleDeclaration]
                Assert.Equal(crumb.Stamp, account.Stamp)
                Assert.Equal(used.Id, account.Positions[ordinal])
                Assert.DoesNotContain(dormant.Id, account.Positions.Values)

        "Every original child slot distinguishes a live body from an omitted identity", fun () ->
            let builder = NodeBuilder()
            let dormant = builder.Create(SemanticKind.Literal(NativeLiteral.Int(37L, NTUKind.NTUint(NTUWidth.Fixed 64))), Types.intType, dummyRange)
            let live = builder.Create(SemanticKind.Literal(NativeLiteral.Int(1L, NTUKind.NTUint(NTUWidth.Fixed 64))), Types.intType, dummyRange)
            let owner = builder.Create(SemanticKind.Sequential [dormant.Id; live.Id], Types.intType, dummyRange, children = [dormant.Id; live.Id])
            let graph = builder.Build [(owner.Id, DeclRoot.EntryPoint)]
            let graph = { graph with Nodes = graph.Nodes.Add(dormant.Id, { dormant with IsReachable = false }) }
            let plan = admitted graph
            let row = plan.Occurrences[owner.Id]
            Assert.Same(owner, row.Body)
            Assert.Equal<NodeId list>([dormant.Id; live.Id], row.Body.Children)
            Assert.False(plan.Occurrences.ContainsKey dormant.Id)
            Assert.Equal<WitnessChildDisposition list>([
                { Ordinal = 0; Traversal = WitnessChildTraversal.SourceOmitted(plan.Support, dormant.Id) }
                { Ordinal = 1; Traversal = WitnessChildTraversal.SourceLive live.Id } ], row.Children)
            Assert.Equal(WitnessScopeSupportPolicy.WholePreparedOwner, plan.Support.Policy)
            let context = plan.Occurrences[live.Id].Contexts |> Assert.Single |> Assert.Single
            Assert.Equal(2, context.Extent)
            Assert.Equal(1, context.Ordinal)

        "A shared live DAG body retains both actual occurrence paths", fun () ->
            let builder = NodeBuilder()
            let value = builder.Create(SemanticKind.Literal(NativeLiteral.Int(1L, NTUKind.NTUint(NTUWidth.Fixed 64))), Types.intType, dummyRange)
            let left = builder.Create(SemanticKind.Sequential [value.Id], Types.intType, dummyRange, children = [value.Id])
            let right = builder.Create(SemanticKind.Sequential [value.Id], Types.intType, dummyRange, children = [value.Id])
            let root = builder.Create(SemanticKind.Sequential [left.Id; right.Id], Types.intType, dummyRange, children = [left.Id; right.Id])
            let plan = builder.Build [(root.Id, DeclRoot.EntryPoint)] |> admitted
            let paths = plan.Occurrences[value.Id].Contexts
            Assert.Equal(2, paths.Length)
            Assert.Equal<Set<NodeId>>(Set.ofList [left.Id; right.Id], paths |> List.map (List.head >> _.Parent) |> Set.ofList)
            for path in paths do
                Assert.Equal(2, path.Length)
                Assert.Equal(root.Id, path[1].Parent)
                Assert.Equal(WitnessOccurrencePort.StructuralChild, path[0].Port)

        "Context path and frame budgets admit the exact boundary and refuse excess", fun () ->
            let builder = NodeBuilder()
            let value = builder.Create(SemanticKind.Binding("shared", false, false, None), Types.intType, dummyRange)
            let left = builder.Create(SemanticKind.Sequential [value.Id], Types.intType, dummyRange, children = [value.Id])
            let right = builder.Create(SemanticKind.Sequential [value.Id], Types.intType, dummyRange, children = [value.Id])
            let root = builder.Create(SemanticKind.Sequential [left.Id; right.Id], Types.intType, dummyRange, children = [left.Id; right.Id])
            let graph = builder.Build [(root.Id, DeclRoot.EntryPoint)]
            let exact : LiveScope.ScopeContextBudget = { MaxPaths = 5L; MaxFrames = 6L }
            let plan = LiveScope.projectWithBudget exact graph |> Result.defaultWith (sprintf "%A" >> failwith)
            Assert.Equal(2, plan.Occurrences[value.Id].Contexts.Length)
            for budget in [{ exact with MaxPaths = 4L }; { exact with MaxFrames = 5L }] do
                match LiveScope.projectWithBudget budget graph with
                | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains "source-host occurrence-context")
                | Result.Ok _ -> failwith "An exceeded source-host budget yielded a live plan"

        "A compact layered DAG refuses path explosion before context materialization", fun () ->
            let builder = NodeBuilder()
            let leaf = builder.Create(SemanticKind.Binding("shared", false, false, None), Types.intType, dummyRange)
            let mutable previous = leaf.Id
            for _ in 1..24 do
                previous <- builder.Create(SemanticKind.Sequential [previous; previous], Types.intType, dummyRange,
                                           children = [previous; previous]).Id
            let graph = builder.Build [(previous, DeclRoot.EntryPoint)]
            Assert.Equal(25, graph.Nodes.Count)
            let small : LiveScope.ScopeContextBudget = { MaxPaths = 64L; MaxFrames = 256L }
            match LiveScope.projectWithBudget small graph with
            | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains "budget")
            | Result.Ok _ -> failwith "Twenty-four shared layers materialized exponentially many paths"

        "Context-count arithmetic refuses overflow as a source resource diagnostic", fun () ->
            let builder = NodeBuilder()
            let leaf = builder.Create(SemanticKind.Binding("shared", false, false, None), Types.intType, dummyRange)
            let mutable previous = leaf.Id
            for _ in 1..64 do
                previous <- builder.Create(SemanticKind.Sequential [previous; previous], Types.intType, dummyRange,
                                           children = [previous; previous]).Id
            let graph = builder.Build [(previous, DeclRoot.EntryPoint)]
            let maximum : LiveScope.ScopeContextBudget =
                { MaxPaths = System.Int64.MaxValue; MaxFrames = System.Int64.MaxValue }
            match LiveScope.projectWithBudget maximum graph with
            | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains "budget")
            | Result.Ok _ -> failwith "An overflowing context count yielded a live plan"

        "An inactive rewritten parent is not a live occurrence path", fun () ->
            let builder = NodeBuilder()
            let value = builder.Create(SemanticKind.Literal(NativeLiteral.Int(1L, NTUKind.NTUint(NTUWidth.Fixed 64))), Types.intType, dummyRange)
            let retired = builder.Create(SemanticKind.Sequential [value.Id], Types.intType, dummyRange, children = [value.Id])
            let current = builder.Create(SemanticKind.Sequential [value.Id], Types.intType, dummyRange, children = [value.Id])
            let graph = builder.Build [(current.Id, DeclRoot.EntryPoint)]
            let graph = { graph with Nodes = graph.Nodes.Add(retired.Id, { retired with IsReachable = false }) }
            let plan = admitted graph
            let path = Assert.Single(plan.Occurrences[value.Id].Contexts)
            Assert.Equal(current.Id, (Assert.Single path).Parent)
            Assert.False(plan.Occurrences.ContainsKey retired.Id)

        "Declaration membership is preserved without inventing an execution child port", fun () ->
            let builder = NodeBuilder()
            let used = builder.Create(SemanticKind.Binding("used", false, false, None), Types.intType, dummyRange)
            let unused = builder.Create(SemanticKind.Binding("unused", false, false, None), Types.intType, dummyRange)
            let container = builder.Create(SemanticKind.ModuleDef("Library", [used.Id; unused.Id]), Types.unitType, dummyRange, children = [])
            let graph = builder.Build [(used.Id, DeclRoot.EntryPoint)]
            let graph = { graph with
                            Nodes = graph.Nodes.Add(container.Id, { container with Children = []; IsReachable = false })
                                               .Add(unused.Id, { unused with IsReachable = false })
                            Modules = Map.ofList [(["Library"], [container.Id])] }
            let plan = admitted graph
            let context = plan.Occurrences[used.Id].Contexts |> Assert.Single |> Assert.Single
            Assert.Equal(WitnessOccurrencePort.ModuleDeclaration, context.Port)
            Assert.Equal(container.Id, context.Parent)
            Assert.Equal(2, context.Extent)
            Assert.Equal<Map<int, NodeId>>(Map.ofList [0, used.Id], plan.ContextHeaders[container.Id].Ports[WitnessOccurrencePort.ModuleDeclaration].Positions)
            Assert.False(plan.Occurrences.ContainsKey container.Id)
            Assert.Contains(container.Id, plan.ContextIdentities)

        "An absent source child refuses scope preparation", fun () ->
            let graph, _ = marked [NodeId -987654] (fun nodes _ -> nodes)
            refused "absent node" graph

        "A thousand inactive declarations receive no body or occurrence inventory", fun () ->
            let builder = NodeBuilder()
            let chosen = builder.Create(SemanticKind.Binding("chosen", false, false, None), Types.intType, dummyRange)
            let inactive = [1..1000] |> List.map (fun index ->
                builder.Create(SemanticKind.Binding($"unused{index}", false, false, None), Types.intType, dummyRange))
            let members = chosen.Id :: List.map _.Id inactive
            let container = builder.Create(SemanticKind.ModuleDef("Large", members), Types.unitType, dummyRange, children = [])
            let graph = builder.Build [(chosen.Id, DeclRoot.EntryPoint)]
            let inactiveIds = container.Id :: List.map _.Id inactive |> Set.ofList
            let graph =
                { graph with
                    Nodes = graph.Nodes |> Map.map (fun id node -> { node with IsReachable = not (inactiveIds.Contains id) })
                    Modules = Map.ofList [(["Large"], [container.Id])] }
            let plan = admitted graph
            Assert.Equal(1, plan.Occurrences.Count)
            let context = plan.Occurrences[chosen.Id].Contexts |> Assert.Single |> Assert.Single
            Assert.Equal(1001, context.Extent)
            Assert.Equal(1, plan.ContextIdentities.Count)
            Assert.Equal<WitnessOccurrenceBreadcrumb list list>([[]], plan.Contexts[container.Id])
            Assert.Equal<Map<int, NodeId>>(Map.ofList [0, chosen.Id], plan.ContextHeaders[container.Id].Ports[WitnessOccurrencePort.ModuleDeclaration].Positions)

        "A structural cycle refuses scope preparation", fun () ->
            let graph, _ = marked [] (fun nodes root ->
                let value = nodes[root]
                nodes.Add(root, { value with Kind = SemanticKind.Sequential [root]; Children = [root] }))
            refused "structural cycle" graph
    ]

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "WitnessLiveScope")>]
type WitnessLiveScopeTests() =
    static member Cases = WitnessLiveScopeCases.tests |> Seq.map (fun (name, _) -> [| box name |])

    [<Theory; MemberData(nameof WitnessLiveScopeTests.Cases)>]
    member _.``Source live scope and occurrence authority``(name: string) =
        WitnessLiveScopeCases.tests |> List.find (fun (testName, _) -> testName = name) |> snd |> fun test -> test ()

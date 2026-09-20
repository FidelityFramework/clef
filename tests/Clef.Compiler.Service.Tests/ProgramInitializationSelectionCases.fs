namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
module StartupSelection = Clef.Compiler.Baker.Recipes.ProgramInitializationSelection
module StartupFacts = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization

module private StartupSelectionFixture =
    let graph source =
        let checkedSource = DimensionalCases.check source
        DimensionalCases.noErrors checkedSource
        checkedSource.Graph
    let binding (graph: SemanticGraph) name =
        let members = graph.Nodes.Values |> Seq.collect (fun node ->
            match node.Kind with SemanticKind.ModuleDef(_, members) -> members | _ -> []) |> Set.ofSeq
        graph.Nodes.Values |> Seq.filter (fun node ->
            members.Contains node.Id && (match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)) |> Assert.Single
    let members (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Kind with SemanticKind.ModuleDef("Dimensions", members) -> Some members | _ -> None)
    let select graph = StartupSelection.select graph (members graph)
    let names graph ids = ids |> List.map (fun id ->
        match graph.Nodes[id].Kind with SemanticKind.Binding(name, _, _, _) -> name | _ -> "expression")
    let descriptor = """
type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type ProgramLifetimeSpaces = { Immutable: string; Mutable: string option }
type PlatformDescription = { Id: string; Spaces: MemorySpace array; ProgramLifetime: ProgramLifetimeSpaces option }
let capacity = 128
let image = { Name = "image"; Kind = "rodata"; Capacity = capacity; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "r"; Base = None }
let description = { Id = "selection-test"; Spaces = [| image |]; ProgramLifetime = Some { Immutable = "image"; Mutable = None } }
"""
    let project files =
        let files = files |> List.map (fun (name, source) -> System.IO.Path.GetFullPath name, source)
        let inputs = files |> List.map (fun (file, source) ->
            match parseStringWithDefaults source file with
            | ParseSuccess parsed -> parsed
            | ParseError errors -> failwithf "Project selection fixture did not parse: %A" errors)
        let app = files |> List.last |> fst
        let result = checkParsedInputsWithPlatformAndSources inputs None (Set.singleton app)
        DimensionalCases.noErrors result
        result.Graph, app

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProgramInitializationSelection")>]
type ProgramInitializationSelectionCases() =
    [<Fact>]
    member _.``Type-only dependency does not activate its unrelated opaque initializer``() =
        let graph, _ = StartupSelectionFixture.project [
            "startup-types.clef", "namespace DeclarationOnly\nmodule Types =\n    type Row = { Value: int }\nmodule Runtime =\n    let mutable action = fun () -> 1\n    let unused = action ()\n"
            "startup-app.clef", "module Application\nopen DeclarationOnly.Types\nlet observed: Row = { Value = 3 }\n[<EntryPoint>]\nlet main _ = observed.Value\n" ]
        let plan = StartupFacts.read graph |> Option.defaultWith (fun () -> failwith "Owned application startup was not settled")
        Assert.Equal<string list>(["observed"], plan.Initializers |> List.map (fun row ->
            match graph.Nodes[row.Binding].Kind with SemanticKind.Binding(name, _, _, _) -> name | _ -> ""))
        let activated = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ProgramUnitActivation)
        Assert.NotEmpty activated
        Assert.DoesNotContain(activated, fun edge -> graph.Nodes[edge.Target].Range.File.EndsWith("startup-types.clef"))
        Assert.DoesNotContain(graph.Edges, fun edge -> match edge.Role with EdgeRole.ProgramInitializationPending _ -> true | _ -> false)

    [<Fact>]
    member _.``Value demand activates all modules in a dependency file and then its eager dependencies``() =
        let graph, _ = StartupSelectionFixture.project [
            "startup-tail.clef", "module Tail\nlet mutable tick = 0\nlet unusedTick = tick <- 1\nlet value () = tick\n"
            "startup-dependency.clef", "namespace Dependency\nmodule First =\n    let mutable trace = 0\n    let get () = trace\nmodule Second =\n    let unused = First.trace <- Tail.value ()\n"
            "startup-app.clef", "module Application\n[<EntryPoint>]\nlet main _ = Dependency.First.get ()\n" ]
        let plan = StartupFacts.read graph |> Option.defaultWith (fun () -> failwith "Dependency startup was not settled")
        Assert.Equal<string list>(["tick"; "unusedTick"; "trace"; "unused"], plan.Initializers |> List.map (fun row ->
            match graph.Nodes[row.Binding].Kind with SemanticKind.Binding(name, _, _, _) -> name | _ -> ""))
        let get = StartupSelectionFixture.binding graph "get"
        let dependencyUnits = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.ProgramUnitActivation && graph.Nodes[edge.Target].Range.File.EndsWith("startup-dependency.clef"))
        Assert.Equal(2, dependencyUnits.Length)
        for edge in dependencyUnits do Assert.Contains(get.Id, edge.Sources)
        Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.ProgramUnitActivation && graph.Nodes[edge.Target].Range.File.EndsWith("startup-tail.clef"))

    [<Fact>]
    member _.``Unreferenced eager effects retain their preceding storage and declaration order``() =
        let graph = StartupSelectionFixture.graph """
let mutable state = 0
let advance () = state <- 1
let unused = advance ()
let ignoredPure = 23
[<EntryPoint>]
let main _ = 0
"""
        let nodes, edges = graph.Nodes, graph.Edges
        let selected = StartupSelectionFixture.select graph
        Assert.Equal<string list>(["state"; "unused"], StartupSelectionFixture.names graph selected.Initializers)
        Assert.Contains((StartupSelectionFixture.binding graph "advance").Id, selected.CodeDeclarations)
        Assert.Empty selected.Unresolved
        Assert.Same(nodes, graph.Nodes)
        Assert.Same(edges, graph.Edges)

    [<Fact>]
    member _.``Deferred function sequence and lazy bodies do not seed startup effects``() =
        let graph = StartupSelectionFixture.graph """
let mutable state = 0
let dormant () = state <- 1
let delayed = seq { state <- 2; yield 3 }
let lazyValue = lazy (state <- 4; 5)
[<EntryPoint>]
let main _ = 0
"""
        let selected = StartupSelectionFixture.select graph
        Assert.Empty selected.Initializers
        Assert.Empty selected.Unresolved

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Plain platform declaration demand excludes its records but shares runtime constants`` runtimeUse =
        let main = if runtimeUse then "if capacity = 128 then 0 else 1" else "0"
        let graph = StartupSelectionFixture.graph (StartupSelectionFixture.descriptor + "\n[<EntryPoint>]\nlet main _ = " + main)
        let selected = StartupSelectionFixture.select graph
        for name in ["capacity"; "image"; "description"] do
            Assert.Contains((StartupSelectionFixture.binding graph name).Id, selected.DeclarationValues)
        Assert.Equal<string list>((if runtimeUse then ["capacity"] else []), StartupSelectionFixture.names graph selected.Initializers)
        Assert.Empty selected.Unresolved

    [<Fact>]
    member _.``Quotation dependencies remain phase data unless independently demanded``() =
        let graph = StartupSelectionFixture.graph """
let shared = 17
let declaration = <@ shared @>
[<EntryPoint>]
let main _ = if shared = 17 then 0 else 1
"""
        let selected = StartupSelectionFixture.select graph
        Assert.Equal<string list>(["shared"], StartupSelectionFixture.names graph selected.Initializers)
        Assert.Contains((StartupSelectionFixture.binding graph "shared").Id, selected.DeclarationValues)
        Assert.Empty selected.Unresolved

    [<Fact>]
    member _.``Unknown callable effects are retained with a precise dependency residual``() =
        let graph = StartupSelectionFixture.graph """
let mutable action = fun () -> 1
let unused = action ()
[<EntryPoint>]
let main _ = 0
"""
        let selected = StartupSelectionFixture.select graph
        let unused = StartupSelectionFixture.binding graph "unused"
        Assert.Contains(unused.Id, selected.Initializers)
        Assert.Contains(selected.Unresolved, fun (owner, reason) -> owner = unused.Id && reason.Contains "indirect initializer call")
        Assert.Empty selected.Contradictions

    [<Fact>]
    member _.``Eager loops are retained even without a demanded result``() =
        let graph = StartupSelectionFixture.graph "let unused = while false do ()\n[<EntryPoint>]\nlet main _ = 0"
        let selected = StartupSelectionFixture.select graph
        Assert.Equal<string list>(["unused"], StartupSelectionFixture.names graph selected.Initializers)
        Assert.Empty selected.Unresolved

    [<Fact>]
    member _.``Direct calls expose eager module dependencies without invoking deferred results``() =
        let graph = StartupSelectionFixture.graph """
let seed = 4
let make () = seq { yield seed }
let values = make ()
[<EntryPoint>]
let main _ = ignore values; 0
"""
        let selected = StartupSelectionFixture.select graph
        Assert.Contains((StartupSelectionFixture.binding graph "values").Id, selected.Initializers)
        Assert.Contains((StartupSelectionFixture.binding graph "seed").Id, selected.Initializers)
        Assert.Empty selected.Unresolved

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Missing and forward startup dependencies remain residual`` missing =
        let graph = StartupSelectionFixture.graph "let earlier = 1\nlet later = earlier\n[<EntryPoint>]\nlet main _ = later"
        let earlier = StartupSelectionFixture.binding graph "earlier"
        let later = StartupSelectionFixture.binding graph "later"
        let main = StartupSelectionFixture.binding graph "main"
        let roots = if missing then [later.Id; main.Id] else [later.Id; earlier.Id; main.Id]
        let selected = StartupSelection.select graph roots
        Assert.Equal<NodeId list>((if missing then [later.Id] else [later.Id; earlier.Id]), selected.Initializers)
        let expected = if missing then "no selected startup occurrence" else "before its source-ordered initializer"
        Assert.Contains(selected.Unresolved, fun (owner, reason) -> owner = later.Id && reason.Contains expected)
        Assert.Equal<(NodeId * string) list>(selected.Unresolved, selected.Contradictions)

    [<Fact>]
    member _.``An eager dependency cycle is reported rather than reordered``() =
        let graph = StartupSelectionFixture.graph "let first = 1\nlet second = first\n[<EntryPoint>]\nlet main _ = second"
        let first = StartupSelectionFixture.binding graph "first"
        let second = StartupSelectionFixture.binding graph "second"
        let value = graph.Nodes[List.exactlyOne first.Children]
        let replacement = { value with Kind = SemanticKind.VarRef("second", Some second.Id); Children = [] }
        let graph = { graph with Nodes = graph.Nodes.Add(value.Id, replacement) }
        let selected = StartupSelectionFixture.select graph
        Assert.Contains(selected.Unresolved, fun (owner, reason) -> owner = first.Id && reason.Contains "Cyclic eager initialization")
        Assert.Contains(selected.Unresolved, fun (owner, reason) -> owner = second.Id && reason.Contains "Cyclic eager initialization")
        Assert.Equal<(NodeId * string) list>(selected.Unresolved, selected.Contradictions)

    [<Fact>]
    member _.``Nonbinding eager occurrences preserve their exact source identity``() =
        let graph = StartupSelectionFixture.graph "let mutable state = 0\nlet unused = state <- 1\n[<EntryPoint>]\nlet main _ = 0"
        let state = StartupSelectionFixture.binding graph "state"
        let unused = StartupSelectionFixture.binding graph "unused"
        let main = StartupSelectionFixture.binding graph "main"
        let occurrence = graph.Nodes[List.exactlyOne unused.Children]
        let selected = StartupSelection.select graph [state.Id; occurrence.Id; main.Id]
        Assert.Equal<NodeId list>([state.Id; occurrence.Id], selected.Initializers)
        Assert.Empty selected.Unresolved

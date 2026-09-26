namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module LazyRangeAnalysis = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module LazyRangeValues = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues
module LazyRangeElaboration = Clef.Compiler.Nanopass.LazyElaboration

module private LazyRanges =
    let check source =
        match parseAndCheck ("module LazyRanges\n" + source) "lazy-ranges.clef" with
        | Success result | CheckFailure result ->
            DimensionalCases.noErrors result
            let graph = LazyRangeElaboration.normalize result.Graph
            Assert.Empty((LazyRangeValues.settle graph).Residuals)
            graph
        | ParseFailure errors -> failwithf "Lazy range source failed parsing: %A" errors

    let analyze graph = LazyRangeAnalysis.run graph.Platform graph |> fst
    let protocols graph = (LazyRangeValues.settle graph).Forces.Values |> Seq.toList
    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single
    let range lower upper id (graph: SemanticGraph) =
        Assert.Equal(Some(ValueRange.Bounded(lower, upper)), graph.Nodes[id].ValueRange)
    let modify id transform (graph: SemanticGraph) =
        { graph with Nodes = graph.Nodes.Add(id, transform graph.Nodes[id]) }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LazyRanges")>]
type LazyRangeCases() =
    [<Theory>]
    [<InlineData("7")>]
    [<InlineData("7<m>")>]
    member _.``Cache declaration and guarded reads inherit the exact typed thunk result`` expression =
        let graph = LazyRanges.check $"""
[<Measure>] type m
[<EntryPoint>]
let main _ =
    let delayed = lazy {expression}
    ignore (Lazy.force delayed)
    ignore (Lazy.force delayed)
    0
"""
        let graph = LazyRanges.analyze graph
        let forces = LazyRanges.protocols graph
        Assert.Equal(2, forces.Length)
        for force in forces do
            let instance = LazyRangeValues.instance graph force.Formation |> Option.get
            for id in [instance.ThunkBody; instance.Cached; force.CachedRead; force.Invocation; force.Site] do
                LazyRanges.range 7I 7I id graph
                Assert.Equal(graph.Nodes[instance.ThunkBody].Type, graph.Nodes[id].Type)
            Assert.Empty graph.Nodes[instance.Cached].Children

    [<Fact>]
    member _.``Immutable lazy capture reads its validated formation initializer`` () =
        let graph = LazyRanges.check """
[<EntryPoint>]
let main _ =
    let basis = 7
    let delayed = lazy (basis + 2)
    Lazy.force delayed
"""
        let graph = LazyRanges.analyze graph
        let basis = LazyRanges.binding "basis" graph
        let reads = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.LazyRead(_, slot) -> slot = basis.Id | _ -> false) |> Seq.toList
        Assert.NotEmpty reads
        for read in reads do LazyRanges.range 7I 7I read.Id graph
        let force = LazyRanges.protocols graph |> Assert.Single
        LazyRanges.range 9I 9I force.CachedRead graph
        LazyRanges.range 9I 9I force.Site graph

    [<Fact>]
    member _.``A later guard on a mutable capture cannot refine an earlier cached value`` () =
        let graph = LazyRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state = 3
    let delayed = lazy state
    let first = Lazy.force delayed
    state <- 700
    if state > 500 then
        let second = Lazy.force delayed
        first + second
    else 0
"""
        let graph = LazyRanges.analyze graph
        for force in LazyRanges.protocols graph do
            LazyRanges.range 3I 700I force.CachedRead graph
        LazyRanges.range 3I 700I (LazyRanges.binding "second" graph).Id graph

    [<Fact>]
    member _.``Formation keeps guards and forcing invalidates the original captured cell`` () =
        let graph = LazyRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state = 1
    if state < 10 then
        let delayed = lazy (state <- 300; state)
        let before = state
        ignore (Lazy.force delayed)
        let after = state
        before + after
    else 0
"""
        let graph = LazyRanges.analyze graph
        LazyRanges.range 1I 300I (LazyRanges.binding "state" graph).Id graph
        LazyRanges.range 1I 9I (LazyRanges.binding "before" graph).Id graph
        LazyRanges.range 1I 300I (LazyRanges.binding "after" graph).Id graph

    [<Fact>]
    member _.``Distinct factory environments share only a sound result enclosure`` () =
        let graph = LazyRanges.check """
let make value = lazy value
[<EntryPoint>]
let main _ =
    let first = make 3
    let second = make 7
    Lazy.force first + Lazy.force second
"""
        let graph = LazyRanges.analyze graph
        let forces = LazyRanges.protocols graph
        Assert.Equal(2, forces.Length)
        Assert.Single(forces |> List.map _.Formation |> List.distinct) |> ignore
        Assert.Equal(2, forces |> List.map _.EnvironmentBinding |> List.distinct |> List.length)
        for force in forces do LazyRanges.range 3I 7I force.CachedRead graph

    [<Theory>]
    [<InlineData("guard")>]
    [<InlineData("store")>]
    [<InlineData("extra-read")>]
    [<InlineData("capture-mode")>]
    member _.``Changed memoization or capture evidence cannot supply a cache range`` defect =
        let original = LazyRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state = 3
    let delayed = lazy state
    Lazy.force delayed
"""
        let force = LazyRanges.protocols original |> Assert.Single
        let instance = LazyRangeValues.instance original force.Formation |> Option.get
        let changed =
            match defect with
            | "guard" ->
                original |> LazyRanges.modify force.Conditional (fun node ->
                    { node with Kind = SemanticKind.IfThenElse(force.Condition, force.UncachedBranch, Some force.CachedRead)
                                Children = [force.Condition; force.UncachedBranch; force.CachedRead] })
            | "store" ->
                original |> LazyRanges.modify force.ResultStore (fun node ->
                    match node.Kind with
                    | SemanticKind.LazyWrite(environment, slot, _) ->
                        { node with Kind = SemanticKind.LazyWrite(environment, slot, instance.InitialComputed)
                                    Children = [environment; instance.InitialComputed] }
                    | _ -> failwith "Fixture lost its cache store")
            | "extra-read" ->
                let id = NodeId.fresh()
                let extra = { original.Nodes[force.CachedRead] with Id = id; Parent = None }
                { original with Nodes = original.Nodes.Add(id, extra) }
            | _ ->
                let edges = original.Edges |> List.map (fun edge ->
                    if edge.Role = EdgeRole.LazyCapture true then { edge with Role = EdgeRole.LazyCapture false }
                    else edge)
                { original with Edges = edges }
        Assert.NotEmpty((LazyRangeValues.settle changed).Residuals)
        let graph = LazyRanges.analyze changed
        Assert.Equal(Some ValueRange.Unbounded, graph.Nodes[instance.Cached].ValueRange)
        Assert.Equal(Some ValueRange.Unbounded, graph.Nodes[force.CachedRead].ValueRange)

    [<Fact>]
    member _.``An unknown thunk result stays unbounded without an invented integer width`` () =
        let original = LazyRanges.check """
[<EntryPoint>]
let main _ =
    let delayed = lazy 7
    Lazy.force delayed
"""
        let force = LazyRanges.protocols original |> Assert.Single
        let instance = LazyRangeValues.instance original force.Formation |> Option.get
        let changed = original |> LazyRanges.modify instance.ThunkBody (fun node ->
            { node with Kind = SemanticKind.PatternBinding "opaqueResult"; Children = []; ValueRange = None })
        Assert.Empty((LazyRangeValues.settle changed).Residuals)
        let graph = LazyRanges.analyze changed
        for id in [instance.ThunkBody; instance.Cached; force.CachedRead] do
            Assert.Equal(Some ValueRange.Unbounded, graph.Nodes[id].ValueRange)
            Assert.Equal(None, LazyRangeAnalysis.selectedWidth graph id)

namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private EnvironmentRangeFixture =
    let check body =
        let source = "module EnvironmentRanges\n[<EntryPoint>]\nlet main _ =\n" + body
        match parseAndCheck source "closure-environment-ranges.clef" with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "Expected admitted closure source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed closure source: %A" errors

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ClosureEnvironmentRange")>]
type ClosureEnvironmentRangeCases() =
    [<Fact>]
    member _.``Immutable mapped callback capture reads the exact formation value range`` () =
        let graph = EnvironmentRangeFixture.check """    let offset = 7
    let mapper = fun value -> value + offset
    let mapped = Seq.map mapper (seq { yield 2; yield 3 })
    let mutable answer = 0
    for value in mapped do answer <- value
    answer
"""
        let source = EnvironmentRangeFixture.binding "offset" graph
        let reads = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.EnvironmentRead(_, slot) -> slot = source.Id | _ -> false) |> Seq.toList
        Assert.NotEmpty reads
        for read in reads do Assert.Equal(Some(ValueRange.point 7I), read.ValueRange)
        Assert.Contains(graph.Edges, fun edge ->
            edge.Role = EdgeRole.EnvironmentCapture false &&
            match edge.Sources with [_; slot; value] -> slot = source.Id && value = source.Id | _ -> false)

    [<Fact>]
    member _.``A mapped callback environment write invalidates the same source cell guard`` () =
        let graph = EnvironmentRangeFixture.check """    let mutable state = 1
    let mapper = fun value -> state <- 300; value
    let mapped = Seq.map mapper (seq { yield 2 })
    let mutable answer = 0
    if state < 10 then
        for value in mapped do
            let afterPull = state
            answer <- afterPull
    answer
"""
        let source = EnvironmentRangeFixture.binding "state" graph
        Assert.Contains(graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.EnvironmentWrite(_, slot, _) -> slot = source.Id | _ -> false)
        for value in [source; EnvironmentRangeFixture.binding "afterPull" graph] do
            match value.ValueRange with
            | Some range -> Assert.True(ValueRange.contains range (ValueRange.point 300I), sprintf "Environment write was lost at %A: %A" value.Id range)
            | None -> failwithf "Environment source read lost its range at %A" value.Id

namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type CountedLoopCases() =
    [<Theory>]
    [<InlineData("to")>]
    [<InlineData("downto")>]
    member _.``Counted bounds retain start then finish evaluation and definition identity``(direction: string) =
        let source =
            "module CountedBounds\nlet first () = 1\nlet last () = 2\n[<EntryPoint>]\nlet main _ =\n    for i = first () "
            + direction + " last () do ignore i\n    0\n"
        let result =
            match parseAndCheck source "counted-bounds.clef" with
            | Success result -> result
            | CheckFailure result -> failwithf "Counted loop rejected: %A" result.Diagnostics
            | ParseFailure errors -> failwithf "Counted loop did not parse: %A" errors
        DimensionalCases.noErrors result
        let graph = result.Graph
        let sequence, startId, finishId, loopId =
            graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Sequential [first; second; loop] when node.IsReachable ->
                    match graph.Nodes[first].Kind, graph.Nodes[second].Kind, graph.Nodes[loop].Kind with
                    | SemanticKind.Binding _, SemanticKind.Binding _, SemanticKind.WhileLoop _ ->
                        Some (node, first, second, loop)
                    | _ -> None
                | _ -> None) |> Assert.Single
        let assertInitializer expected id =
            let binding = graph.Nodes[id]
            let value = graph.Nodes[binding.Children |> Assert.Single]
            match value.Kind with
            | SemanticKind.Application(callee, [_]) ->
                match graph.Nodes[callee].Kind with
                | SemanticKind.VarRef(name, Some definition) ->
                    Assert.True(name = expected || name.EndsWith("." + expected), name)
                    Assert.True(graph.Nodes.ContainsKey definition)
                | kind -> failwithf "Bound lost its resolved function identity: %A" kind
            | kind -> failwithf "Bound must be evaluated once at its initializer: %A" kind
            Assert.Equal(Some sequence.Id, binding.Parent)
        assertInitializer "first" startId
        assertInitializer "last" finishId
        Assert.Equal(Some sequence.Id, graph.Nodes[loopId].Parent)
        Assert.Equal<_ list>([startId; finishId; loopId], sequence.Children)

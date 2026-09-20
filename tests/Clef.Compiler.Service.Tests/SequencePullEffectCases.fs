namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module PullEffects = Clef.Compiler.Nanopass.SequenceEffects
module PullRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private PullEffectFixture =
    let check body =
        let source = "module PullEffects\n" + body + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n"
        match parseAndCheck source "sequence-pull-effects.clef" with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "Expected admitted effect source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed effect source: %A" errors

    let remaining (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(name, true, _, _) -> name.StartsWith "__seq_remaining_" | _ -> false) |> Assert.Single

    let bounded (graph: SemanticGraph) = Assert.Equal(Some(ValueRange.Bounded(0I, 3I)), (remaining graph).ValueRange)
    let openRange (graph: SemanticGraph) =
        match (remaining graph).ValueRange with
        | Some range -> Assert.False(ValueRange.isObservable range, sprintf "Unknown invocation acquired a finite private-counter range: %A" range)
        | None -> failwith "Remaining count lost its integer range"

    let simple = "let observed = Seq.take 3 (seq { yield 1; yield 2; yield 3; yield 4 })"
    let append = "let observed = Seq.take 3 (Seq.append (seq { yield 1; yield 2 }) (seq { yield 3; yield 4 }))"

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequencePullEffects")>]
type SequencePullEffectCases() =
    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Known pull bodies retain the private take counter bound through nested iterator initialization`` nested =
        let graph = PullEffectFixture.check (if nested then PullEffectFixture.append else PullEffectFixture.simple)
        PullEffectFixture.bounded graph
        Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.SequencePullBody)
        Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.SequenceInitialize)
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Role = EdgeRole.SequenceEffectUnknown)
        for edge in graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequencePullBody) do
            match edge.Sources with
            | [iterator; owner; generator; body] ->
                match graph.Nodes[edge.Target].Kind with SemanticKind.Application(_, [actual]) -> Assert.Equal(iterator, actual) | _ -> failwith "Effect target is not the exact pull"
                match graph.Nodes[owner].Kind with SemanticKind.SeqExpr(actual, _) -> Assert.Equal(generator, actual) | _ -> failwith "Missing sequence owner"
                match graph.Nodes[generator].Kind with SemanticKind.Lambda(_, actual, _, _, LambdaContext.SeqGenerator) -> Assert.Equal(body, actual) | _ -> failwith "Missing deferred body"
            | sources -> failwithf "Effect participants are incomplete: %A" sources

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Possible generator writes to captured cells invalidate the earlier guard`` alternatives =
        let input = if alternatives then "if choose then seq { yield true } else seq { shared <- 300; yield true }" else "seq { shared <- 300; yield true }"
        let source =
            "let mutable shared = 1\nlet mutable choose = true\nlet input = " + input + "\n" +
            "let observed =\n    let mutable answer = 0\n    if shared < 10 then\n" +
            "        for value in input do\n            let afterPull = shared\n            answer <- afterPull\n    answer\n"
        let graph = PullEffectFixture.check source
        let observed =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.Binding("afterPull", _, _, _) -> true | _ -> false) |> Assert.Single
        match observed.ValueRange with
        | Some range -> Assert.True(ValueRange.contains range (ValueRange.point 300I), sprintf "The pull was wrongly treated as pure: %A" range)
        | None -> failwith "Captured read lost its range"
        let bodies = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequencePullBody)
        Assert.Equal((if alternatives then 2 else 1), bodies.Length)
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Role = EdgeRole.SequenceEffectUnknown)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Opaque and mixed sequence origins retain unknown invocation effects`` mixed =
        let input = if mixed then "if choose then seq { yield 1 } else input" else "input"
        let graph = PullEffectFixture.check (
            "let inspect (choose: bool) (input: seq<int>) =\n    let selected = " + input + "\n    Seq.take 3 selected\nlet observed = inspect")
        Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.SequenceEffectUnknown)
        if mixed then Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.SequencePullBody)
        PullEffectFixture.openRange graph

    [<Theory>]
    [<InlineData("body")>]
    [<InlineData("initialization")>]
    [<InlineData("current")>]
    member _.``Missing graph effect dependencies cannot retain a stale finite range`` missing =
        let graph = PullEffectFixture.check (if missing = "initialization" then PullEffectFixture.append else PullEffectFixture.simple)
        PullEffectFixture.bounded graph
        let role = match missing with "body" -> EdgeRole.SequencePullBody | "initialization" -> EdgeRole.SequenceInitialize | _ -> EdgeRole.IteratorCurrentAdmitted
        let without = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> role) }
        let reranged = PullRanges.run None without |> fst
        PullEffectFixture.openRange reranged
        if missing <> "current" then
            let repaired = PullEffects.normalize without |> fun graph -> PullRanges.run None graph |> fst
            PullEffectFixture.bounded repaired

namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module LoopRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private LoopRangeFixture =
    let check body =
        let source = "module LoopRanges\n[<Measure>] type m\n" + body + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n"
        match parseAndCheck source "loop-ranges.clef" with
        | Success result | CheckFailure result ->
            DimensionalCases.noErrors result
            result.Graph
        | ParseFailure errors -> failwithf "Expected parsed recurrence: %A" errors

    let cell name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, true, _, _) -> actual = name | _ -> false) |> Assert.Single

    let pending name reason graph =
        let binding = cell name graph
        Assert.Contains(graph.Edges, fun edge -> edge.Target = binding.Id && edge.Role = EdgeRole.LoopRangePending reason)
        Assert.DoesNotContain(graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Obligation { Body = ObligationBody.AdditiveLoopInvariant _ } ->
                graph.Edges |> List.exists (fun edge -> edge.Target = node.Id && List.contains binding.Id edge.Sources)
            | _ -> false)

    let source initial guard step delta =
        sprintf "let observed = seq {\n    let mutable total = 0\n    let mutable i = %s\n    while %s do\n        total <- total + %s\n        yield total\n        i <- %s\n}" initial guard delta step

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LoopRange")>]
type LoopRangeCases() =
    [<Theory>]
    [<InlineData("1", "i <= 6", "i + 1", "i", 6, 36)>]
    [<InlineData("0", "i < 6", "i + 2", "1", 3, 3)>]
    [<InlineData("6", "i >= 1", "i - 2", "1", 3, 3)>]
    [<InlineData("1", "i < 0", "i + 1", "1", 0, 0)>]
    member _.``Finite trips bound every additive store including zero trips and descending strides``(initial, guard, step, delta, trips: int, upper: int) =
        let graph = LoopRangeFixture.check (LoopRangeFixture.source initial guard step delta)
        let cell = LoopRangeFixture.cell "total" graph
        Assert.Equal(Some(ValueRange.Bounded(0I, bigint upper)), cell.ValueRange)
        let relation = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LoopAccumulation && edge.Target = cell.Id) |> Assert.Single
        match relation.Sources with
        | [loop; induction; seed; store; update; delta] ->
            match graph.Nodes[update].ValueRange with
            | Some range -> Assert.True(ValueRange.contains (ValueRange.Bounded(0I, bigint upper)) range, sprintf "A store exceeds its proven cell enclosure: %A" range)
            | None -> failwith "The exact additive store lost its range"
            match graph.Nodes[store].Kind with
            | SemanticKind.Set(target, actual) ->
                Assert.Equal(update, actual)
                match graph.Nodes[target].Kind with SemanticKind.VarRef(_, Some origin) -> Assert.Equal(cell.Id, origin) | _ -> failwith "The update changed cell identity"
            | _ -> failwith "No actual store in accumulation incidence"
            Assert.Contains(graph.Edges, fun edge -> edge.Target = loop && match edge.Role with EdgeRole.LoopInduction _ -> List.contains induction edge.Sources | _ -> false)
            let obligations = graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.Obligation { Body = ObligationBody.AdditiveLoopInvariant _ } -> true | _ -> false) |> Seq.toList
            let obligation = Assert.Single obligations
            Assert.Contains(graph.Edges, fun edge -> edge.Target = obligation.Id && [loop; induction; seed; store; update; delta; cell.Id] |> List.forall (fun id -> List.contains id edge.Sources))
            match obligation.Kind with
            | SemanticKind.Obligation { Body = ObligationBody.AdditiveLoopInvariant model } -> Assert.Equal(bigint trips, model.MaximumIterations)
            | _ -> failwith "No additive invariant"
        | participants -> failwithf "Incomplete joint recurrence: %A" participants

    [<Fact>]
    member _.``Caller bounds and independent measured state participate in the same fixed point``() =
        let graph = LoopRangeFixture.check "let produce count = seq {\n    let mutable total = 0<m>\n    let mutable i = 1\n    while i <= count do\n        total <- total + i * 1<m>\n        yield total\n        i <- i + 1\n}\nlet observed = produce 6"
        let total = LoopRangeFixture.cell "total" graph
        Assert.Equal(Some(ValueRange.Bounded(0I, 36I)), total.ValueRange)
        Assert.Contains("<m>", formatType total.Type)
        Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.LoopAccumulation && edge.Target = total.Id)

    [<Theory>]
    [<InlineData("guard")>]
    [<InlineData("outside")>]
    [<InlineData("conditional")>]
    [<InlineData("capture")>]
    [<InlineData("reentry")>]
    [<InlineData("zero-step")>]
    member _.``Missing control and cell premises retain explicit residuals`` scenario =
        let source, reason =
            match scenario with
            | "guard" -> "let observed = seq {\n    let mutable stop = 6\n    let mutable total = 0\n    let mutable i = 1\n    while i <= stop do\n        total <- total + i\n        stop <- stop + 1\n        yield total\n        i <- i + 1\n}", LoopRangeResidual.Guard
            | "outside" -> "let observed = seq {\n    let mutable total = 0\n    let mutable i = 1\n    total <- 100\n    while i <= 6 do\n        total <- total + i\n        yield total\n        i <- i + 1\n}", LoopRangeResidual.OtherWrites
            | "conditional" -> "let observed = seq {\n    let mutable total = 0\n    let mutable i = 1\n    while i <= 6 do\n        total <- total + i\n        yield total\n        if i < 4 then i <- i + 1\n}", LoopRangeResidual.ConditionalUpdate
            | "capture" -> "let observed = seq {\n    let mutable total = 0\n    let mutable i = 1\n    let read () = total\n    while i <= 6 do\n        total <- total + i\n        yield read ()\n        i <- i + 1\n}", LoopRangeResidual.CapturedCell
            | "reentry" -> "let observed = seq {\n    let mutable total = 0\n    let mutable i = 1\n    while i <= 6 do\n        while i <= 6 do\n            total <- total + i\n            yield total\n            i <- i + 1\n}", LoopRangeResidual.Reentry
            | _ -> LoopRangeFixture.source "1" "i <= 6" "i + 0" "1", LoopRangeResidual.Step
        LoopRangeFixture.check source |> LoopRangeFixture.pending "total" reason

    [<Theory>]
    [<InlineData("total * 2")>]
    [<InlineData("other")>]
    member _.``Multiplicative and coupled recurrences do not borrow an additive proof`` update =
        let source = "let observed = seq {\n    let mutable total = 1\n    let mutable other = 2\n    let mutable i = 0\n    while i < 6 do\n        total <- " + update + "\n        other <- other + total\n        yield total\n        i <- i + 1\n}"
        LoopRangeFixture.check source |> LoopRangeFixture.pending "total" LoopRangeResidual.NonAdditive

    [<Fact>]
    member _.``Unknown trip bounds remain residual without selecting a carrier``() =
        let graph = LoopRangeFixture.check "let produce (count: int) = seq {\n    let mutable total = 0\n    let mutable i = 1\n    while i <= count do\n        total <- total + i\n        yield total\n        i <- i + 1\n}\nlet observed = produce"
        LoopRangeFixture.pending "total" LoopRangeResidual.MissingBound graph
        match (LoopRangeFixture.cell "total" graph).ValueRange with
        | Some range -> Assert.False(ValueRange.isObservable range)
        | None -> failwith "Missing numeric residual range"

    [<Fact>]
    member _.``Range recomputation replaces its own evidence and preserves independent resident obligations``() =
        let graph = LoopRangeFixture.check (LoopRangeFixture.source "1" "i <= 6" "i + 1" "i")
        let total = LoopRangeFixture.cell "total" graph
        let retained = { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Sources = [total.Id]; Target = total.Id; Ordinal = 71 }
        let changed = { graph with Edges = retained :: graph.Edges }
        let repeated, _ = LoopRanges.run None changed
        Assert.Equal(total.ValueRange, repeated.Nodes[total.Id].ValueRange)
        Assert.Contains(repeated.Edges, fun edge -> edge.Ordinal = 71 && edge.Target = total.Id)
        let count (graph: SemanticGraph) = graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Obligation { Body = ObligationBody.AdditiveLoopInvariant _ } -> true | _ -> false) |> Seq.length
        Assert.Equal(count graph, count repeated)

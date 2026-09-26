namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module LoopRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module FiniteRecurrences = Clef.Compiler.Baker.Recipes.LoopRangeRecipes

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

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FiniteRecurrence")>]
type FiniteRecurrenceCases() =
    let powers count =
        sprintf "let observed = seq {\n    let mutable power = 1\n    let mutable i = 0\n    while i < %d do\n        yield power\n        power <- power * 2\n        i <- i + 1\n}" count

    let fibonacci count snapshot stores =
        sprintf "let observed = seq {\n    let mutable a = 0\n    let mutable b = 1\n    let mutable i = 0\n    while i < %d do\n        yield a\n        let temp = %s\n        %s\n        i <- i + 1\n}" count snapshot stores

    let originalFibonacci count = fibonacci count "eager (a + b)" "a <- b\n        b <- temp"

    let linearProof graph =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation { Body = ObligationBody.FiniteLinearRecurrence model } -> Some(node, model)
            | _ -> None) |> Assert.Single

    let scalarCertificate count factor =
        let owner, loop, guard, cell, initial, limit, step, update, store, power, seed =
            NodeId 0, NodeId 1, NodeId 2, NodeId 3, NodeId 4, NodeId 5, NodeId 6, NodeId 7, NodeId 8, NodeId 9, NodeId 10
        let recurrence: FiniteRecurrences.LinearRecurrence = {
            Induction = { Owner = owner; Loop = loop; Guard = guard; Cell = cell; Initial = initial
                          Limit = limit; Step = step; Update = update; Store = store; Ascending = true; Inclusive = false }
            Cells = [power]; Initials = [seed]; Coefficients = [[FiniteRecurrences.Coefficient.Constant factor]]
            Targets = [power, 0]; Participants = [] }
        let ranges = Map.ofList [initial, ValueRange.point 0I; limit, ValueRange.point count; step, ValueRange.point 1I; seed, ValueRange.point 1I]
        recurrence, (fun id -> ranges.TryFind id |> Option.defaultValue ValueRange.Empty)

    [<Theory>]
    [<InlineData(0)>]
    [<InlineData(8)>]
    [<InlineData(70)>]
    member _.``Multiplicative cell includes final exhaustion store beyond the last yielded value``(count: int) =
        let graph = LoopRangeFixture.check (powers count)
        let power = LoopRangeFixture.cell "power" graph
        let upper = 1I <<< count
        Assert.Equal(Some(ValueRange.Bounded(1I, upper)), power.ValueRange)
        let proof, model = linearProof graph
        Assert.Equal(bigint count, model.MaximumIterations)
        Assert.Equal<bigint list>([upper], model.Upper)
        Assert.Equal(Some(count + 1), ValueRange.width (ValueRange.Bounded(0I, upper)))
        let stores = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with
            | SemanticKind.Set(target, _) ->
                match graph.Nodes[target].Kind with SemanticKind.VarRef(_, Some id) -> id = power.Id | _ -> false
            | _ -> false) |> Seq.toList
        let store = Assert.Single stores
        match store.Kind with
        | SemanticKind.Set(_, update) ->
            Assert.Contains(graph.Edges, fun edge -> edge.Target = proof.Id && List.contains store.Id edge.Sources && List.contains update edge.Sources)
            if count > 0 then Assert.Equal(Some(ValueRange.Bounded(2I, upper)), graph.Nodes[update].ValueRange)
        | _ -> failwith "Expected exact source store"

    [<Theory>]
    [<InlineData(0, "0", "1")>]
    [<InlineData(10, "55", "89")>]
    [<InlineData(100, "354224848179261915075", "573147844013817084101")>]
    member _.``Ordered coupled cells retain snapshot identity and all final update ranges``(count: int, expectedA: string, expectedB: string) =
        let graph = LoopRangeFixture.check (originalFibonacci count)
        let a, b = LoopRangeFixture.cell "a" graph, LoopRangeFixture.cell "b" graph
        let aUpper, bUpper = bigint.Parse expectedA, bigint.Parse expectedB
        Assert.Equal(Some(ValueRange.Bounded(0I, aUpper)), a.ValueRange)
        Assert.Equal(Some(ValueRange.Bounded(1I, bUpper)), b.ValueRange)
        let proof, model = linearProof graph
        Assert.Equal<bigint list>([aUpper; bUpper], model.Upper)
        let temp = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("temp", false, _, _) -> true | _ -> false) |> Assert.Single
        let marker = graph.Nodes[temp.Children.Head]
        match marker.Kind with
        | SemanticKind.EagerExpr sum ->
            Assert.Contains(graph.Edges, fun edge -> edge.Class = EdgeClass.Demand && edge.Role = EdgeRole.EagerDemand EagerFrontier.Binding && edge.Target = temp.Id && edge.Sources = [marker.Id; sum])
            Assert.Contains(graph.Edges, fun edge -> edge.Target = proof.Id && ([temp.Id; marker.Id; sum; a.Id; b.Id] |> List.forall (fun id -> List.contains id edge.Sources)))
            if count > 0 then
                match graph.Nodes[sum].ValueRange with
                | Some(ValueRange.Bounded(_, upper)) -> Assert.Equal(bUpper, upper)
                | range -> failwithf "The actual sum lacks its finite enclosure: %A" range
        | _ -> failwith "The recurrence must preserve the actual eager marker"

    [<Theory>]
    [<InlineData("deferred")>]
    [<InlineData("reordered")>]
    [<InlineData("changed sum")>]
    member _.``An unproved snapshot or different ordered update cannot inherit the coupled certificate``(change: string) =
        let source =
            match change with
            | "deferred" -> fibonacci 10 "a + b" "a <- b\n        b <- temp"
            | "reordered" -> fibonacci 10 "eager (a + b)" "b <- temp\n        a <- b"
            | _ -> fibonacci 10 "eager (a + a)" "a <- b\n        b <- temp"
        let graph = LoopRangeFixture.check source
        Assert.DoesNotContain(graph.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Obligation { Body = ObligationBody.FiniteLinearRecurrence _ } -> true | _ -> false)

    [<Theory>]
    [<InlineData("demand")>]
    [<InlineData("ordering")>]
    [<InlineData("marker child")>]
    [<InlineData("extra write")>]
    [<InlineData("state dimension")>]
    [<InlineData("sum dimension")>]
    member _.``Range rerun retracts changed demand and ordering premises instead of using old conclusions``(change: string) =
        let graph = LoopRangeFixture.check (originalFibonacci 10)
        linearProof graph |> ignore
        let a = LoopRangeFixture.cell "a" graph
        let temp = graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("temp", false, _, _) -> true | _ -> false)
        let marker = graph.Nodes[temp.Children.Head]
        let changed =
            match change with
            | "demand" ->
                { graph with Edges = graph.Edges |> List.filter (fun edge -> not (edge.Target = temp.Id && edge.Class = EdgeClass.Demand)) }
            | "ordering" ->
                let edge = graph.Edges |> List.find (fun edge ->
                    edge.Class = EdgeClass.Evaluation && List.contains temp.Id edge.Sources &&
                    match edge.Role with EdgeRole.EvaluationFlow _ -> true | _ -> false)
                let edges =
                    graph.Edges |> List.filter (fun item ->
                        not (item.Class = edge.Class && item.Role = edge.Role && item.Target = edge.Target && item.Sources = edge.Sources && item.Ordinal = edge.Ordinal))
                { graph with Edges = edges }
            | "marker child" -> { graph with Nodes = graph.Nodes.Add(marker.Id, { marker with Children = [] }) }
            | "state dimension" ->
                { graph with Nodes = graph.Nodes.Add(a.Id, { a with Type = DimensionalCases.measuredInt DimensionalCases.second }) }
            | "sum dimension" ->
                match marker.Kind with
                | SemanticKind.EagerExpr sum ->
                    { graph with Nodes = graph.Nodes.Add(sum, { graph.Nodes[sum] with Type = DimensionalCases.measuredInt DimensionalCases.second }) }
                | _ -> failwith "Expected source eager marker"
            | _ ->
                let store = graph.Nodes.Values |> Seq.find (fun node ->
                    match node.Kind with
                    | SemanticKind.Set(target, _) ->
                        match graph.Nodes[target].Kind with SemanticKind.VarRef(_, Some id) -> id = a.Id | _ -> false
                    | _ -> false)
                let id = NodeId((graph.Nodes.Keys |> Seq.map (fun (NodeId id) -> id) |> Seq.max) + 1)
                { graph with Nodes = graph.Nodes.Add(id, { store with Id = id }) }
        let rerun, _ = LoopRanges.run None changed
        Assert.DoesNotContain(rerun.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Obligation { Body = ObligationBody.FiniteLinearRecurrence _ } -> true | _ -> false)
        Assert.DoesNotContain(rerun.Edges, fun edge -> edge.Role = EdgeRole.LoopLinearRecurrence)
        linearProof graph |> ignore

    [<Fact>]
    member _.``Certificate resource boundary is deterministic and never a numeric width limit``() =
        let recurrence, ranges = scalarCertificate 70I 2I
        let settled =
            match FiniteRecurrences.saturateLinear ranges recurrence with
            | Ok value -> value
            | Error reason -> failwithf "A 71-bit lawful enclosure exhausted proof work: %A" reason
        Assert.Equal<bigint list>([1I <<< 70], settled.Invariant.Upper)
        match FiniteRecurrences.saturateLinearWithBudget settled.WorkBits ranges recurrence with
        | Ok repeated -> Assert.Equal(settled.WorkBits, repeated.WorkBits)
        | Error reason -> failwithf "The exact work boundary must fit: %A" reason
        Assert.Equal(Error LoopRangeResidual.ProofResources,
                     FiniteRecurrences.saturateLinearWithBudget (settled.WorkBits - 1I) ranges recurrence)
        let huge, hugeRanges = scalarCertificate (1I <<< 80) 2I
        Assert.Equal(Error LoopRangeResidual.ProofResources, FiniteRecurrences.saturateLinear hugeRanges huge)
        let stable, stableRanges = scalarCertificate (1I <<< 80) 1I
        match FiniteRecurrences.saturateLinear stableRanges stable with
        | Ok result -> Assert.Equal<bigint list>([1I], result.Invariant.Upper)
        | Error reason -> failwithf "Large trip count alone is not a source or width limit: %A" reason

    [<Fact>]
    member _.``Measured recurrence state retains its quantity while the multiplier remains dimensionless``() =
        let source = (powers 8).Replace("let mutable power = 1", "let mutable power = 1<m>")
        let graph = LoopRangeFixture.check source
        let power = LoopRangeFixture.cell "power" graph
        Assert.Contains("<m>", formatType power.Type)
        Assert.Equal(Some(ValueRange.Bounded(1I, 256I)), power.ValueRange)
        linearProof graph |> ignore

    [<Fact>]
    member _.``Independent measured recurrence instances retain their distinct source dimensions``() =
        let graph = LoopRangeFixture.check """[<Measure>] type s
let grow initial = seq {
    let mutable power = initial
    let mutable i = 0
    while i < 8 do
        yield power
        power <- power * 2
        i <- i + 1
}
let distances = grow 1<m>
let durations = grow 1<s>
let observed = distances, durations
"""
        let cells = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("power", true, _, _) -> true | _ -> false) |> Seq.toList
        Assert.NotEmpty cells
        let instance name =
            let value = graph.Nodes.Values |> Seq.find (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.Binding(actual, false, _, _) -> actual = name | _ -> false)
            let element =
                match applySubst value.Type with NativeType.TSeq element -> element | ty -> failwithf "Expected source sequence: %A" ty
            match graph.Nodes[value.Children.Head].Kind with
            | SemanticKind.Application(callee, [argument]) ->
                Assert.Equal(element, applySubst graph.Nodes[argument].Type)
                Assert.Equal(NativeType.TFun(element, NativeType.TSeq element), applySubst graph.Nodes[callee].Type)
                value.Children.Head, callee, argument, element
            | kind -> failwithf "Expected an actual measured invocation: %A" kind
        let distanceCall, distanceCallee, distanceArgument, distance = instance "distances"
        let durationCall, durationCallee, durationArgument, duration = instance "durations"
        Assert.NotEqual(distanceCall, durationCall)
        Assert.NotEqual(distanceCallee, durationCallee)
        Assert.NotEqual(distanceArgument, durationArgument)
        Assert.NotEqual(distance, duration)
        for cell in cells do
            Assert.Equal(applySubst cell.Type, applySubst graph.Nodes[cell.Children.Head].Type)
            Assert.True(not (freeMeasureVars cell.Type).IsEmpty || applySubst cell.Type = distance || applySubst cell.Type = duration)
            Assert.Equal(Some(ValueRange.Bounded(1I, 256I)), cell.ValueRange)

    [<Fact>]
    member _.``Changed multiplier dimension retracts a numerically unchanged certificate``() =
        let graph = LoopRangeFixture.check (powers 8)
        linearProof graph |> ignore
        let factor = graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Literal(NativeLiteral.Int(2L, _)) -> true | _ -> false)
        let changed = { graph with Nodes = graph.Nodes.Add(factor.Id, { factor with Type = DimensionalCases.measuredInt DimensionalCases.second }) }
        let rerun, _ = LoopRanges.run None changed
        Assert.DoesNotContain(rerun.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Obligation { Body = ObligationBody.FiniteLinearRecurrence _ } -> true | _ -> false)

    [<Theory>]
    [<InlineData("store target dimension")>]
    [<InlineData("application children")>]
    [<InlineData("reference incidence")>]
    [<InlineData("callee type")>]
    member _.``Current typed source incidence is required even when all numeric bounds are unchanged``(change: string) =
        let graph = LoopRangeFixture.check (powers 8)
        linearProof graph |> ignore
        let power = LoopRangeFixture.cell "power" graph
        let store = graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Set(target, _) ->
                match graph.Nodes[target].Kind with
                | SemanticKind.VarRef(_, Some id) -> id = power.Id
                | _ -> false
            | _ -> false)
        let target, update =
            match store.Kind with
            | SemanticKind.Set(target, update) -> target, update
            | _ -> failwith "Expected the actual recurrence store"
        let callee, arguments =
            match graph.Nodes[update].Kind with
            | SemanticKind.Application(callee, arguments) -> callee, arguments
            | _ -> failwith "Expected the actual multiplication"
        let changed =
            match change with
            | "store target dimension" ->
                let reference = graph.Nodes[target]
                { graph with Nodes = graph.Nodes.Add(target, { reference with Type = DimensionalCases.measuredInt DimensionalCases.second }) }
            | "application children" ->
                let operation = graph.Nodes[update]
                { graph with Nodes = graph.Nodes.Add(update, { operation with Children = callee :: List.rev arguments }) }
            | "reference incidence" ->
                let contradicting = { Class = EdgeClass.Reference; Role = EdgeRole.Definition; Ordinal = 0; Sources = [callee]; Target = target }
                { graph with Edges = contradicting :: graph.Edges }
            | _ ->
                let operation = graph.Nodes[callee]
                { graph with Nodes = graph.Nodes.Add(callee, { operation with Type = NativeType.TFun(Types.boolType, Types.boolType) }) }
        let rerun, _ = LoopRanges.run None changed
        Assert.DoesNotContain(rerun.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Obligation { Body = ObligationBody.FiniteLinearRecurrence _ } -> true | _ -> false)
        Assert.DoesNotContain(rerun.Edges, fun edge -> edge.Role = EdgeRole.LoopLinearRecurrence)
        linearProof graph |> ignore

    [<Theory>]
    [<InlineData("alias type")>]
    [<InlineData("annotation type")>]
    [<InlineData("annotation children")>]
    member _.``Immutable coefficient aliases retain complete type and definition authority``(change: string) =
        let source = "let coefficient = (2 : int)\n" + (powers 8).Replace("power * 2", "power * coefficient")
        let graph = LoopRangeFixture.check source
        linearProof graph |> ignore
        let coefficient = graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Binding("coefficient", false, _, _) -> true | _ -> false)
        let annotation = graph.Nodes[coefficient.Children.Head]
        let inner, declared =
            match annotation.Kind with
            | SemanticKind.TypeAnnotation(inner, declared) -> inner, declared
            | kind -> failwithf "Expected actual source coefficient annotation, got %A" kind
        let changed =
            match change with
            | "alias type" ->
                { graph with Nodes = graph.Nodes.Add(coefficient.Id, { coefficient with Type = DimensionalCases.measuredInt DimensionalCases.second }) }
            | "annotation type" ->
                { graph with Nodes = graph.Nodes.Add(annotation.Id, { annotation with Kind = SemanticKind.TypeAnnotation(inner, DimensionalCases.measuredInt DimensionalCases.second) }) }
            | _ ->
                { graph with Nodes = graph.Nodes.Add(annotation.Id, { annotation with Children = [] }) }
        Assert.Equal(applySubst graph.Nodes[inner].Type, applySubst declared)
        let rerun, _ = LoopRanges.run None changed
        Assert.DoesNotContain(rerun.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Obligation { Body = ObligationBody.FiniteLinearRecurrence _ } -> true | _ -> false)
        Assert.DoesNotContain(rerun.Edges, fun edge -> edge.Role = EdgeRole.LoopLinearRecurrence)
        linearProof graph |> ignore

    [<Fact>]
    member _.``Coupled measured recurrence retains its quantity through the eager snapshot``() =
        let source = (originalFibonacci 10).Replace("let mutable a = 0", "let mutable a = 0<m>").Replace("let mutable b = 1", "let mutable b = 1<m>")
        let graph = LoopRangeFixture.check source
        for name, upper in ["a", 55I; "b", 89I] do
            let cell = LoopRangeFixture.cell name graph
            Assert.Contains("<m>", formatType cell.Type)
            match cell.ValueRange with
            | Some(ValueRange.Bounded(_, actual)) -> Assert.Equal(upper, actual)
            | range -> failwithf "Missing measured recurrence enclosure: %A" range
        linearProof graph |> ignore

    [<Theory>]
    [<InlineData("coupled")>]
    [<InlineData("multiplier")>]
    member _.``Numerically bounded recurrence cannot erase incompatible dimensions``(scenario: string) =
        let body =
            if scenario = "coupled" then
                (originalFibonacci 10).Replace("let mutable a = 0", "let mutable a = 0<m>").Replace("let mutable b = 1", "let mutable b = 1<s>")
            else (powers 8).Replace("let mutable power = 1", "let mutable power = 1<m>").Replace("power * 2", "power * 2<s>")
        let source = "module MeasuredRecurrence\n[<Measure>] type m\n[<Measure>] type s\n" + body + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n"
        match parseAndCheck source "measured-recurrence-negative.clef" with
        | CheckFailure result ->
            Assert.Contains(result.Diagnostics, fun diagnostic ->
                diagnostic.Code = "CCS8040" && diagnostic.Severity = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error && diagnostic.Range.File = "measured-recurrence-negative.clef" && diagnostic.Range.Start.Line > 0)
        | result -> failwithf "Incompatible recurrence dimensions were admitted: %A" result

    [<Fact>]
    member _.``Exhausted proof work remains pending and blocks platform representation commitment``() =
        let graph = LoopRangeFixture.check (powers 1000000000)
        let power = LoopRangeFixture.cell "power" graph
        Assert.Contains(graph.Edges, fun edge -> edge.Target = power.Id && edge.Role = EdgeRole.LoopRangePending LoopRangeResidual.ProofResources)
        let platform: PlatformContext = {
            PlatformId = "recurrence-resource-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
            Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = None
            PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.empty
            Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
            AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }
        let rerun, diagnostics = LoopRanges.run (Some platform) { graph with Platform = Some platform }
        Assert.Contains(diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8011" && diagnostic.Severity = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error &&
            diagnostic.Range = power.Range && diagnostic.Message.Contains("certificate-work budget"))
        Assert.DoesNotContain(rerun.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Obligation { Body = ObligationBody.FiniteLinearRecurrence _ } -> true | _ -> false)

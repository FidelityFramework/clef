namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private EnvironmentRangeFixture =
    let inspect body =
        let source = "module EnvironmentRanges\n[<EntryPoint>]\nlet main _ =\n" + body
        parseAndCheck source "closure-environment-ranges.clef"

    let check body =
        match inspect body with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "Expected admitted closure source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed closure source: %A" errors

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

    let parameter name (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.PatternBinding actual -> actual = name | _ -> false)
        |> Assert.Single

    let scalarChainSource repeatedReads twice =
      let length = if repeatedReads then 13 else 50
      let steps =
        [ for index in 1 .. length do
            let previous = sprintf "step%d" (index - 1)
            let second = if repeatedReads && index > 1 then previous else "1"
            yield sprintf "        let step%d = %s + %s" index previous second ]
      let invocation =
        if twice then
          [ "    let twice callback start = callback (callback start)"
            "    let observed = twice deep 0" ]
        else [ "    let observed = deep 0" ]
      String.concat "\n"
        ([ "    let deep input ="; "        let step0 = input" ] @ steps @
         [ sprintf "        step%d" length ] @ invocation @ [ "    observed" ])

    let retainedResult name expected (graph: SemanticGraph) =
      let observed = binding name graph
      let call = Assert.Single observed.Children
      let facts = graph.RangeContextFacts |> Option.defaultWith (fun () -> failwith "The range producer did not retain invocation facts.")
      let invocation = facts.Invocations |> Seq.filter (fun row -> row.Call = call) |> Assert.Single
      Assert.Equal(ValueRange.point expected, facts.Values[invocation.Context, invocation.Body])
      Assert.Contains(facts.Reads[invocation.Context, invocation.Body], fun (context, _) -> context <> RangeContext.Shared)
      Assert.NotEmpty invocation.Arguments
      Assert.NotEmpty facts.Premises

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ClosureEnvironmentRange")>]
type ClosureEnvironmentRangeCases() =
    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("wrong-call")>]
    [<InlineData("wrong-actual")>]
    member _.``Application specialization requires its exact shared formal supplier`` defect =
      let graph = EnvironmentRangeFixture.check """    let double input = input * 2
    let first = double 3
    let second = double 100
    first + second
"""
      let call name = (EnvironmentRangeFixture.binding name graph).Children |> Assert.Single
      let first, second = call "first", call "second"
      let flow = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
      let target = flow.Calls[first].Targets |> Assert.Single
      let _, _, formal = target.Parameters |> Assert.Single
      let actual = target.Arguments |> Assert.Single
      let otherActual = (flow.Calls[second].Targets |> Assert.Single).Arguments |> Assert.Single
      let suppliers = flow.ParameterInputs[formal]
      Assert.Contains((first, actual), suppliers)
      Assert.Contains((second, otherActual), suppliers)
      let reachable = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
      let project arguments =
        Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.completeApplications
          reachable Set.empty arguments flow.Calls
      let admitted = project flow.ParameterInputs
      Assert.True(admitted.ContainsKey first)
      Assert.True(admitted.ContainsKey second)
      let changed =
        suppliers |> List.choose (fun supplier ->
          if supplier <> (first, actual) then Some supplier
          else
            match defect with
            | "missing" -> None
            | "wrong-call" -> Some(second, actual)
            | "wrong-actual" -> Some(first, otherActual)
            | _ -> failwithf "Unknown supplier defect: %s" defect)
      let refused = flow.ParameterInputs.Add(formal, changed) |> project
      Assert.False(refused.ContainsKey first, "A call absent from its shared formal enclosure cannot specialize.")
      Assert.True(refused.ContainsKey second, "An unchanged invocation must retain its complete correspondence.")

    [<Fact>]
    member _.``Higher order contexts retain distinct results while shared formals retain every invocation`` () =
        let graph = EnvironmentRangeFixture.check """    let twice callback start = callback (callback start)
    let double input = input * 2
    let first = twice double 3
    let second = twice double 100
    first + second
"""
        Assert.Equal(Some(ValueRange.point 12I), (EnvironmentRangeFixture.binding "first" graph).ValueRange)
        Assert.Equal(Some(ValueRange.point 400I), (EnvironmentRangeFixture.binding "second" graph).ValueRange)
        Assert.Equal(Some(ValueRange.Bounded(3I, 100I)), (EnvironmentRangeFixture.parameter "start" graph).ValueRange)
        Assert.Equal(Some(ValueRange.Bounded(3I, 200I)), (EnvironmentRangeFixture.parameter "input" graph).ValueRange)
        EnvironmentRangeFixture.retainedResult "first" 12I graph
        EnvironmentRangeFixture.retainedResult "second" 400I graph

    [<Fact>]
    member _.``Complete partial invocations retain the joined prefix and bind only remaining actuals`` () =
        let graph = EnvironmentRangeFixture.check """    let add prefix input = prefix + input
    let add5 = add 5
    let add7 = add 7
    let first = add5 3
    let second = add7 100
    first + second
"""
        Assert.Equal(Some(ValueRange.Bounded(5I, 7I)), (EnvironmentRangeFixture.parameter "prefix" graph).ValueRange)
        Assert.Equal(Some(ValueRange.Bounded(8I, 10I)), (EnvironmentRangeFixture.binding "first" graph).ValueRange)
        Assert.Equal(Some(ValueRange.Bounded(105I, 107I)), (EnvironmentRangeFixture.binding "second" graph).ValueRange)

    [<Fact>]
    member _.``Later factory invocation preserves the earlier stored immutable capture`` () =
        let graph = EnvironmentRangeFixture.check """    let make offset = fun input -> offset + input
    let old = eager (make 7)
    let later = eager (make 100)
    let oldAnswer = old 3
    let laterAnswer = later 3
    oldAnswer + laterAnswer
"""
        // The current capture owner may join the two formations. Either
        // enclosure must retain the value stored by its own source invocation.
        for name, expected in ["oldAnswer", 10I; "laterAnswer", 103I] do
            match (EnvironmentRangeFixture.binding name graph).ValueRange with
            | Some(ValueRange.Bounded _ as range) ->
                Assert.True(ValueRange.contains range (ValueRange.point expected), sprintf "%s lost its original capture: %A" name range)
            | range -> failwithf "A finite stored capture lost its enclosure: %s %A" name range

    [<Fact>]
    member _.``Recursive fixed point cannot invent a finite result from its cycle`` () =
        let source = """    let rec grow (input: int) : int = if input = 0 then 0 else input + grow (input + 1)
    let observed = grow 1
    observed
"""
        match EnvironmentRangeFixture.inspect source with
        | CheckFailure result ->
            let graph = result.Graph
            let observed = EnvironmentRangeFixture.binding "observed" graph
            let call = Assert.Single observed.Children
            let flow = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
            let reachable = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
            let inactiveCalls =
                Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryInactivity graph
                |> Result.toOption |> Option.map _.Calls |> Option.defaultValue Set.empty
            let admitted =
                Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.completeApplications
                    reachable inactiveCalls flow.ParameterInputs flow.Calls
            Assert.True(admitted.ContainsKey call, sprintf "The outer recursion control must specialize: %A" (flow.Calls.TryFind call))
            let target = admitted[call] |> Assert.Single
            let rec descendants seen id =
                if Set.contains id seen then seen
                else
                    let seen = Set.add id seen
                    match reachable.TryFind id with
                    | Some node -> List.fold descendants seen node.Children
                    | None -> seen
            let body = descendants Set.empty target.Body
            Assert.Contains(admitted |> Map.toList, fun (id, targets) ->
                id <> call && body.Contains id && (targets |> List.exists (fun recursive -> recursive.Lambda = target.Lambda)))
            let facts = graph.RangeContextFacts |> Option.defaultWith (fun () -> failwith "The recursive fixed point lost its retained context facts.")
            let merged =
                facts.Invocations
                |> List.filter (fun row -> row.Target = target.Lambda)
                |> List.groupBy _.Context
                |> List.filter (fun (_, rows) -> (rows |> List.map _.Caller |> List.distinct).Length > 1)
                |> List.collect snd
            Assert.NotEmpty merged
            Assert.Contains(merged, fun row ->
                match facts.Values.TryFind(row.Context, row.Body) with
                | Some range -> range <> ValueRange.Empty && not (ValueRange.isObservable range)
                | None -> false)
            Assert.Contains(result.Diagnostics, fun diagnostic ->
                diagnostic.Code = "CCS8011" && diagnostic.Message.Contains("merged invocation contexts") &&
                (merged |> List.exists (fun row ->
                    List.contains row.Call diagnostic.RelatedNodes && List.contains row.Target diagnostic.RelatedNodes)))
            Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8011")
            Assert.DoesNotContain(result.Diagnostics, fun diagnostic ->
                diagnostic.Code = "CCS8011" && diagnostic.Message.Contains("application-specific transfer exhausted"))
            match observed.ValueRange with
            | Some range ->
                Assert.NotEqual(ValueRange.Empty, range)
                Assert.False(ValueRange.isObservable range, sprintf "A recursive cycle fabricated an observable result %A" range)
            | None -> failwith "The recursion control did not reach range analysis."
        | Success result -> failwithf "An unbounded recursive cycle was admitted: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected a parsed recursion control: %A" errors

    [<Theory>]
    [<InlineData(false, 50)>]
    [<InlineData(true, 4096)>]
    member _.``Long scalar chains and repeated reads retain their finite direct result`` repeatedReads (expected: int) =
        let graph = EnvironmentRangeFixture.scalarChainSource repeatedReads false |> EnvironmentRangeFixture.check
        Assert.Equal(Some(ValueRange.point (bigint expected)), (EnvironmentRangeFixture.binding "observed" graph).ValueRange)
        EnvironmentRangeFixture.retainedResult "observed" (bigint expected) graph

    [<Theory>]
    [<InlineData(false, 100)>]
    [<InlineData(true, 16781312)>]
    member _.``Long scalar chains and repeated reads retain distinct higher order context results`` repeatedReads (expected: int) =
        let graph = EnvironmentRangeFixture.scalarChainSource repeatedReads true |> EnvironmentRangeFixture.check
        Assert.Equal(Some(ValueRange.point (bigint expected)), (EnvironmentRangeFixture.binding "observed" graph).ValueRange)
        EnvironmentRangeFixture.retainedResult "observed" (bigint expected) graph

    [<Fact>]
    member _.``Finite contextual results preserve independent undeclared field reasons`` () =
        let body = EnvironmentRangeFixture.scalarChainSource false true
        let body =
            body.Replace("    let observed = twice deep 0",
                         "    let calculated = twice deep 0\n    let observed = calculated + outside.Sample\n    let unrelated = outside.Other")
                .Replace("\n    observed", "\n    observed + unrelated")
        let source =
            "module EnvironmentRanges\ntype Input = { Sample: int; Other: int }\n[<EntryPoint>]\nlet main (outside: Input) =\n" + body
        match parseAndCheck source "closure-environment-ranges.clef" with
        | CheckFailure result ->
            let observed = EnvironmentRangeFixture.binding "observed" result.Graph
            Assert.Equal(Some(ValueRange.point 100I), (EnvironmentRangeFixture.binding "calculated" result.Graph).ValueRange)
            EnvironmentRangeFixture.retainedResult "calculated" 100I result.Graph
            let field name =
                result.Graph.Nodes.Values
                |> Seq.filter (fun node ->
                    node.IsReachable && match node.Kind with SemanticKind.FieldGet(_, actual) -> actual = name | _ -> false)
                |> Assert.Single
            let sample, other = field "Sample", field "Other"
            let reason name = sprintf "no descriptor declares the representation of field '%s' of 'Input'" name
            let mixed =
                result.Diagnostics
                |> Seq.filter (fun diagnostic -> diagnostic.Code = "CCS8011" && diagnostic.Message.Contains(reason "Sample"))
                |> Assert.Single
            Assert.DoesNotContain("application-specific transfer exhausted", mixed.Message)
            Assert.All(mixed.RelatedNodes, fun id -> Assert.True(result.Graph.Nodes.ContainsKey id))
            let independent =
                result.Diagnostics
                |> Seq.filter (fun diagnostic -> diagnostic.Code = "CCS8011" && diagnostic.Range = other.Range)
                |> Assert.Single
            Assert.Contains(reason "Other", independent.Message)
            Assert.DoesNotContain("application-specific transfer exhausted", independent.Message)
            Assert.Contains(other.Id, independent.RelatedNodes)
            for node in [observed; sample; other] do
                match node.ValueRange with
                | Some(ValueRange.Bounded _ as range) -> failwithf "An unobservable cause fabricated a finite result at %A: %A" node.Id range
                | Some _ -> ()
                | None -> failwithf "The mixed-provenance control did not reach range analysis at %A." node.Id
                Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedWidth result.Graph node.Id).IsNone)
        | Success result -> failwithf "The undeclared-field case was admitted: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected a parsed mixed-provenance control: %A" errors

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
        // This tests the cell observation after a pull, not a deferred binding's demand.
        let graph = EnvironmentRangeFixture.check """    let mutable state = 1
    let mapper = fun value -> state <- 300; value
    let mapped = Seq.map mapper (seq { yield 2 })
    let mutable answer = 0
    if state < 10 then
        for value in mapped do
            let afterPull = eager state
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

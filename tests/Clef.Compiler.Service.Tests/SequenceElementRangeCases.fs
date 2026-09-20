namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module ElementRecipes = Clef.Compiler.Baker.Recipes.SequenceElementRecipes
module ElementOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins
module ElementCurrent = Clef.Compiler.Nanopass.SequenceCurrentAdmission
module ElementRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private ElementRangeFixture =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result.Graph

    let isElement = function
        | EdgeRole.SequenceElementAdmission | EdgeRole.SequenceElementOwner
        | EdgeRole.SequenceElementPayload | EdgeRole.SequenceElementUnknown -> true
        | _ -> false

    let evidence (graph: SemanticGraph) =
        let graph = { graph with Edges = graph.Edges |> List.filter (fun edge -> not (isElement edge.Role) && edge.Role <> EdgeRole.IteratorCurrentAdmitted) }
        let _, certificates = ElementCurrent.certify graph
        let graph = { graph with Edges = graph.Edges @ certificates }
        let facts = ElementRecipes.elaborate graph
        { graph with Edges = graph.Edges @ facts }, certificates

    let ranged graph = ElementRanges.run None graph |> fst
    let ordinary () = check "[<EntryPoint>]\nlet main _ =\n    for value in seq { yield 7; yield 300 } do ignore value\n    0\n"
    let range expected (graph: SemanticGraph) id = Assert.Equal(Some expected, graph.Nodes[id].ValueRange)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceElementRange")>]
type SequenceElementRangeCases() =
    [<Fact>]
    member _.``Nested delegation joins exact source payload ranges in the same fixed point``() =
        let graph = ElementRangeFixture.check """
[<EntryPoint>]
let main _ =
    let inner = seq { yield 7<m>; yield 300<m> }
    let middle = seq { yield! inner }
    let outer = seq { yield! middle }
    for value in outer do ignore value
    0
"""
        let enriched, certificates = ElementRangeFixture.evidence graph
        Assert.Equal(3, certificates.Length)
        let ranged = ElementRangeFixture.ranged enriched
        for certificate in certificates do
            ElementRangeFixture.range (ValueRange.Bounded(7I, 300I)) ranged certificate.Target
            Assert.Contains(enriched.Edges, fun edge ->
                edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementAdmission
                && edge.Sources = certificate.Sources)
        Assert.Same(graph.Nodes, enriched.Nodes)

    [<Fact>]
    member _.``Pre-Curry declaration and application chains retain the unique factory origin``() =
        let graph = ElementRangeFixture.check """
let make (first: int) (last: int) = seq { yield first; yield last }
[<EntryPoint>]
let main _ =
    for value in make 7 300 do ignore value
    0
"""
        let binding = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("make", _, _, _) -> true | _ -> false) |> Assert.Single
        let lambda = graph.Nodes[Assert.Single binding.Children]
        // Reconstitute the declaration chain to exercise the earlier pass
        // seam, without relying on the public pipeline's later Curry coeffect.
        let parameters, body, captures, enclosing, context =
            match lambda.Kind with SemanticKind.Lambda(p, b, c, e, x) -> p, b, c, e, x | _ -> failwith "No factory lambda"
        Assert.Equal(2, parameters.Length)
        let _, lastType, lastId = parameters[1]
        let innerId = NodeId.fresh()
        let inner =
            { lambda with
                Id = innerId
                Kind = SemanticKind.Lambda([parameters[1]], body, [], enclosing, context)
                Type = NativeType.TFun(lastType, graph.Nodes[body].Type)
                Children = [lastId; body]
                Parent = None }
        let _, _, firstId = parameters.Head
        let outer = { lambda with Kind = SemanticKind.Lambda([parameters.Head], innerId, captures, enclosing, context); Children = [firstId; innerId] }
        let curry = { graph.Codata.Value.Curry with SaturatedCalls = Map.empty; PartialApplications = Map.empty; AbsorbedLambdas = Set.empty }
        let raw =
            { graph with
                Nodes = graph.Nodes |> Map.add lambda.Id outer |> Map.add innerId inner
                Codata = lazy { graph.Codata.Value with Curry = curry } }
        let unique, _ = ElementOrigins.settle raw curry
        let enriched, certificates = ElementRangeFixture.evidence raw
        let certificate = Assert.Single certificates
        let iterator = match raw.Nodes[certificate.Target].Kind with SemanticKind.Application(_, [value]) -> value | _ -> failwith "No current"
        Assert.Equal(body, unique[iterator])
        ElementRangeFixture.range (ValueRange.Bounded(7I, 300I)) (ElementRangeFixture.ranged enriched) certificate.Target

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Unknown input alternatives prevent narrowing even alongside a bounded owner`` mixed =
        let selected = if mixed then "if flag then seq { yield 7 } else input" else "input"
        let graph = ElementRangeFixture.check (
            "let consume (flag: bool) (input: seq<int>) =\n    let selected = " + selected +
            "\n    for value in selected do ignore value\n[<EntryPoint>]\nlet main _ = ignore consume; 0\n")
        let enriched, certificates = ElementRangeFixture.evidence graph
        let certificate = Assert.Single certificates
        Assert.Contains(enriched.Edges, fun edge -> edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementUnknown)
        if mixed then Assert.Contains(enriched.Edges, fun edge -> edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementOwner)
        ElementRangeFixture.range ValueRange.Unbounded (ElementRangeFixture.ranged enriched) certificate.Target

    [<Theory>]
    [<InlineData("admission")>]
    [<InlineData("dependency")>]
    [<InlineData("payload")>]
    member _.``Missing proof participants cannot leave a narrower stale range`` missing =
        let enriched, certificates = ElementRangeFixture.evidence (ElementRangeFixture.ordinary ())
        let certificate = Assert.Single certificates
        let removed = enriched.Edges |> List.find (fun edge ->
            edge.Target = certificate.Target && edge.Role =
                (match missing with "admission" -> EdgeRole.IteratorCurrentAdmitted | "dependency" -> EdgeRole.SequenceElementAdmission | _ -> EdgeRole.SequenceElementPayload))
        let without = { enriched with Edges = enriched.Edges |> List.filter (fun edge -> not (edge.Target = removed.Target && edge.Role = removed.Role && edge.Sources = removed.Sources && edge.Class = removed.Class && edge.Ordinal = removed.Ordinal)) }
        ElementRangeFixture.range ValueRange.Unbounded (ElementRangeFixture.ranged without) certificate.Target
        if missing = "admission" then Assert.Empty (ElementRecipes.elaborate without)

    [<Fact>]
    member _.``Known empty sequence has no possible current payload instead of an invented value``() =
        let graph = ElementRangeFixture.check "[<EntryPoint>]\nlet main _ =\n    let values: seq<int> = seq { () }\n    for value in values do ignore value\n    0\n"
        let enriched, certificates = ElementRangeFixture.evidence graph
        let certificate = Assert.Single certificates
        Assert.Contains(enriched.Edges, fun edge -> edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementOwner)
        Assert.DoesNotContain(enriched.Edges, fun edge -> edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementPayload)
        ElementRangeFixture.range ValueRange.Empty (ElementRangeFixture.ranged enriched) certificate.Target

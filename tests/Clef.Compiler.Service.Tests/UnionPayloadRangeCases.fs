namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private UnionPayloadRangeFixture =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result.Graph

    let payload name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.DUEliminate(_, _, actual, _) -> actual = name
                                | _ -> false) |> Assert.Single

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.Binding(actual, _, _, _) -> actual = name
                                | _ -> false) |> Assert.Single

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "UnionPayloadRange")>]
type UnionPayloadRangeCases() =
    [<Fact>]
    member _.``Fresh range facts read the current payload instead of cached projection ranges``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int
[<EntryPoint>]
let main _ = match IntVal 42 with IntVal x -> x
"""
        let payload = UnionPayloadRangeFixture.payload "IntVal" graph
        let literal = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Literal(NativeLiteral.Int(42L, _)) -> true | _ -> false) |> Assert.Single
        let kind = match literal.Kind with SemanticKind.Literal(NativeLiteral.Int(_, kind)) -> kind | _ -> failwith "literal"
        let changed = { literal with Kind = SemanticKind.Literal(NativeLiteral.Int(300L, kind)) }
        let current = { graph with Nodes = graph.Nodes.Add(literal.Id, changed) }
        let facts = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.sourceFacts current
        Assert.Equal(ValueRange.Bounded(300I, 300I), facts[payload.Id])
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), graph.Nodes[payload.Id].ValueRange)

    [<Fact>]
    member _.``An integer union payload retains its value rather than its tag``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int | FloatVal of float
let extract n = match n with IntVal x -> x | FloatVal _ -> 0
[<EntryPoint>]
let main _ = extract (IntVal 42)
"""
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Fact>]
    member _.``All actual callers contribute but another union case does not``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int | Other of int
let extract n = match n with IntVal x -> x | Other _ -> 0
[<EntryPoint>]
let main _ = extract (IntVal 7) + extract (IntVal 300) + extract (Other 9000)
"""
        Assert.Equal(Some(ValueRange.Bounded(7I, 300I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Fact>]
    member _.``A mutable union includes every assignment``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int | Other
[<EntryPoint>]
let main _ =
    let mutable selected = IntVal 7
    selected <- IntVal 300
    match selected with IntVal x -> x | Other -> 0
"""
        Assert.Equal(Some(ValueRange.Bounded(7I, 300I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Fact>]
    member _.``An opaque union alternative prevents narrowing beside a known constructor``() =
        let result = DimensionalCases.check """
type Number = IntVal of int | Other
let extract (flag: bool) (input: Number) =
    let selected = if flag then IntVal 7 else input
    match selected with IntVal x -> x | Other -> 0
[<EntryPoint>]
let main _ = ignore extract; 0
"""
        Assert.Equal(Some ValueRange.Unbounded, (UnionPayloadRangeFixture.payload "IntVal" result.Graph).ValueRange)
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8011")

    [<Fact>]
    member _.``Tuple fields inside a union retain distinct ranges``() =
        let graph = UnionPayloadRangeFixture.check """
type Pair = Pair of int * int
let extract n = match n with Pair (first, second) -> first + second
[<EntryPoint>]
let main _ = extract (Pair (7, 300))
"""
        Assert.Equal(Some(ValueRange.Bounded(7I, 7I)), (UnionPayloadRangeFixture.binding "first" graph).ValueRange)
        Assert.Equal(Some(ValueRange.Bounded(300I, 300I)), (UnionPayloadRangeFixture.binding "second" graph).ValueRange)

    [<Fact>]
    member _.``Nested union payload projection preserves dimensional type``() =
        let graph = UnionPayloadRangeFixture.check """
type Distance = Metres of int<m>
type Wrapped = Wrapped of Distance
let extract n = match n with Wrapped (Metres x) -> x
[<EntryPoint>]
let main _ = ignore (extract (Wrapped (Metres 42<m>))); 0
"""
        let payload = UnionPayloadRangeFixture.payload "Metres" graph
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), payload.ValueRange)
        Assert.Contains("<m>", formatType payload.Type)

    [<Fact>]
    member _.``Known function results and branch alternatives retain payload bounds``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int | Other
let make flag = if flag then IntVal 7 else IntVal 300
let extract n = match n with IntVal x -> x | Other -> 0
[<EntryPoint>]
let main _ = extract (make true)
"""
        Assert.Equal(Some(ValueRange.Bounded(7I, 300I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Fact>]
    member _.``Union projection composes after a tuple selection``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int
let extract pair = let (_, value) = pair in match value with IntVal x -> x
[<EntryPoint>]
let main _ = extract (9000, IntVal 42)
"""
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Opaque producer and recursive aggregate alternatives remain conservative`` recursive =
        let producer =
            if recursive then "let rec make flag = if flag then IntVal 7 else make flag\nlet extract flag = match make flag with IntVal x -> x\n"
            else "let extract (flag: bool) (make: unit -> Number) =\n    let selected = if flag then IntVal 7 else make ()\n    match selected with IntVal x -> x\n"
        let result = DimensionalCases.check ("type Number = IntVal of int\n" + producer + "[<EntryPoint>]\nlet main _ = ignore extract; 0\n")
        Assert.Equal(Some ValueRange.Unbounded, (UnionPayloadRangeFixture.payload "IntVal" result.Graph).ValueRange)
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8011")

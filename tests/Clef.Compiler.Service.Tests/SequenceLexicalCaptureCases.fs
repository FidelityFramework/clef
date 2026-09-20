namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module LexicalSequenceControl = Clef.Compiler.Baker.Recipes.SequenceControlRecipes

module private SequenceLexicalCaptures =
    let check source =
        let result = DimensionalCases.check (source + "\n[<EntryPoint>]\nlet main _ = ignore outer; 0\n")
        DimensionalCases.noErrors result
        result.Graph

    let seed (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding("seed", _, _, _) | SemanticKind.PatternBinding "seed" -> true | _ -> false)
        |> Assert.Single

    let owners (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList

    let controls graph =
        owners graph |> List.iter (fun owner ->
            match LexicalSequenceControl.forOwner graph owner with
            | Ok control ->
                for step in control.Steps.Values do
                    Assert.True(Set.isSubset step.Uses control.AssignedAtEntry[step.Label])
            | Error residual -> failwithf "A lexical capture was not initialized for its own continuation: %A" residual)

    let captured mutableValue graph =
        let source = seed graph
        Assert.NotEqual(EmissionStrategy.MainPrologue, source.EmissionStrategy)
        let owner, capture =
            owners graph |> List.collect (fun owner ->
                match owner.Kind with
                | SemanticKind.SeqExpr(_, captures) -> captures |> List.map (fun capture -> owner, capture)
                | _ -> [])
            |> List.filter (fun (_, capture) -> capture.SourceNodeId = Some source.Id)
            |> Assert.Single
        Assert.Equal(mutableValue, capture.IsMutable)
        DimensionalCases.same source.Type capture.Type
        let generator = match owner.Kind with SemanticKind.SeqExpr(generator, _) -> generator | _ -> failwith "No owner"
        match graph.Nodes[generator].Kind with
        | SemanticKind.Lambda(_, _, captures, _, LambdaContext.SeqGenerator) ->
            Assert.Contains(captures, fun retained -> retained.SourceNodeId = Some source.Id && retained.IsMutable = mutableValue)
        | kind -> failwithf "Capture lost generator residence: %A" kind
        controls graph

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceLexicalCapture")>]
type SequenceLexicalCaptureCases() =
    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Bindings inside a module-level sequence remain local to its execution and captured by inner sequences``(mutableValue: bool) =
        let mutableKeyword = if mutableValue then "mutable " else ""
        let update = if mutableValue then "seed <- 19; " else ""
        let graph = SequenceLexicalCaptures.check (
            "let outer = seq {\n    let " + mutableKeyword + "seed = 17\n    let child = seq { yield seed; " + update + "yield seed }\n    yield! child\n}")
        Assert.Equal(2, (SequenceLexicalCaptures.owners graph).Length)
        SequenceLexicalCaptures.captured mutableValue graph

    [<Theory>]
    [<InlineData("lazy (let seed = 17 in seq { yield seed })")>]
    [<InlineData("(fun () -> let seed = 17 in seq { yield seed })")>]
    [<InlineData("(let seed = 17 in seq { yield seed })")>]
    [<InlineData("(match 17 with | seed -> seq { yield seed })")>]
    member _.``Lexical binding scope does not depend on an enclosing named function``(expression: string) =
        SequenceLexicalCaptures.check ("let outer = " + expression)
        |> SequenceLexicalCaptures.captured false

    [<Fact>]
    member _.``Actual module declarations retain their established noncapture classification``() =
        let graph = SequenceLexicalCaptures.check "let seed = 17\nlet outer = seq { yield seed }"
        let source = SequenceLexicalCaptures.seed graph
        Assert.Equal(EmissionStrategy.MainPrologue, source.EmissionStrategy)
        let owner = SequenceLexicalCaptures.owners graph |> Assert.Single
        match owner.Kind with SemanticKind.SeqExpr(_, captures) -> Assert.Empty captures | _ -> failwith "No owner"
        SequenceLexicalCaptures.controls graph

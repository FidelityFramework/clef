namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private RangeLoops =
    let prelude = "module RangeLoops\n[<Measure>] type m\nlet first () = 1\nlet last () = 3\n"
    let parse source =
        match parseAndCheck source "range-loops.clef" with
        | Success result | CheckFailure result -> result
        | ParseFailure errors -> failwithf "Range loop did not parse: %A" errors
    let source range = prelude + "[<EntryPoint>]\nlet main _ =\n    for index in " + range + " do ignore index\n    0\n"

type RangeLoopCases() =
    [<Theory>]
    [<InlineData("first () .. last ()")>]
    [<InlineData("(first () .. last ())")>]
    [<InlineData("(first ()) .. (last ())")>]
    member _.``Closed integer range syntax reuses the counted loop and resolved induction binding``(range: string) =
        let result = RangeLoops.parse (RangeLoops.source range)
        DimensionalCases.noErrors result
        let nodes = result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) |> Seq.toList
        Assert.Single(nodes |> List.filter (fun node -> match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false)) |> ignore
        Assert.DoesNotContain(nodes, fun node -> match node.Kind with SemanticKind.ForEach _ | SemanticKind.Error _ -> true | _ -> false)
        let uses = nodes |> List.choose (fun node ->
            match node.Kind with SemanticKind.VarRef("index", definition) -> Some definition | _ -> None)
        Assert.NotEmpty uses
        for definition in uses do
            let binding = result.Graph.Nodes[definition |> Option.defaultWith (fun () -> failwith "Unresolved induction use")]
            match binding.Kind with
            | SemanticKind.Binding("index", _, _, _) -> ()
            | kind -> failwithf "Induction reference lost its counted binding: %A" kind

    [<Theory>]
    [<InlineData("0.0 .. 1", "CCS8003")>]
    [<InlineData("true .. 1", "CCS8003")>]
    [<InlineData("1<m> .. 3", "CCS8040")>]
    member _.``Counted range endpoints require dimensionless integers``(range: string, code: string) =
        let source = RangeLoops.source range
        let result = RangeLoops.parse source
        Assert.True(CheckResult.hasErrors result)
        let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
            diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
        let loop = "for index in " + range + " do ignore index"
        Assert.Equal<SourceRange>(
            { File = "range-loops.clef"; Start = { Line = 7; Column = 4 }; End = { Line = 7; Column = 4 + loop.Length } },
            diagnostic.Range)

    [<Theory>]
    [<InlineData("", "first () .. 2 .. last ()")>]
    [<InlineData("let op_Range first last = first\n", "first () .. last ()")>]
    member _.``Unelaborated stepped and lexically bound ranges cannot masquerade as iterable sequences``(binding: string, range: string) =
        let source = (RangeLoops.source range).Replace("[<EntryPoint>]", binding + "[<EntryPoint>]")
        let result = RangeLoops.parse source
        Assert.True(CheckResult.hasErrors result)
        let diagnostics = CheckResult.errors result
        let rangeMessage = "CCS source checking did not settle an elaboration for this range expression 'a..b': a range outside a counted for loop has no native graph form."
        let iterationMessage = "This iteration source has no admitted native sequence elaboration"
        Assert.Equal<string list>(List.sort [rangeMessage; iterationMessage], diagnostics |> List.map _.Message |> List.sort)
        let line = if binding = "" then 7 else 8
        let column = "    for index in ".Length
        let expectedRange =
            { File = "range-loops.clef"; Start = { Line = line; Column = column }; End = { Line = line; Column = column + range.Length } }
        for diagnostic in diagnostics do
            Assert.Equal("CCS8401", diagnostic.Code)
            Assert.Equal<SourceRange>(expectedRange, diagnostic.Range)
            if diagnostic.Message = rangeMessage then Assert.Empty diagnostic.RelatedNodes
            else
                let refusedSource = result.Graph.Nodes[Assert.Single diagnostic.RelatedNodes]
                Assert.True(refusedSource.IsReachable)
                Assert.Equal<SourceRange>(expectedRange, refusedSource.Range)
                match refusedSource.Kind with
                | SemanticKind.Error message -> Assert.Equal(rangeMessage, message)
                | kind -> failwithf "Iteration refusal must retain its exact unelaborated range source, got %A" kind
        let nodes = result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) |> Seq.toList
        Assert.DoesNotContain(nodes, fun node -> match node.Kind with SemanticKind.WhileLoop _ | SemanticKind.ForEach _ -> true | _ -> false)

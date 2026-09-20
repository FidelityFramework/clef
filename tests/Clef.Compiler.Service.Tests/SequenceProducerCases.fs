namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private SequenceProducers =
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"
    let check source =
        match parseAndCheck (prelude + source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n") "sequence-producers.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result
        | CheckFailure result -> failwithf "Expected admitted producer source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed producer source: %A" errors

    let reject code (marked: string) =
        let first, last = marked.IndexOf('«'), marked.IndexOf('»')
        Assert.True(first >= 0 && last > first)
        let before, selected = marked.Substring(0, first), marked.Substring(first + 1, last - first - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "sequence-producer-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + selected) }
        let source = prelude + marked.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Invalid producer reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s from checking: %A" code errors

[<Trait("Category", "NTU"); Trait("Subcategory", "SequenceProducers")>]
type SequenceProducerCases() =
    [<Theory>]
    [<InlineData("map", "Seq.map (fun (_: int<m>) -> 2<s>) (seq { yield 1<m> })", true)>]
    [<InlineData("filter", "Seq.filter (fun (value: int<m>) -> value > 0<m>) (seq { yield 1<m> })", false)>]
    [<InlineData("collect", "Seq.collect (fun (_: int<m>) -> seq { yield 2<s> }) (seq { yield 1<m> })", true)>]
    [<InlineData("append", "Seq.append (seq { yield 1<m> }) (seq { yield 2<m> })", false)>]
    member _.``Admitted public producers retain their source type and deferred generator graph``(operation: string, expression: string, changedElement: bool) =
        let result = SequenceProducers.check ("let observed = " + expression)
        let element = DimensionalCases.measuredInt (if changedElement then DimensionalCases.second else DimensionalCases.metre)
        DimensionalCases.same (Types.mkSeqType element) (DimensionalCases.bindingType "observed" result)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Intrinsic info -> info.Module = IntrinsicModule.Seq && info.Operation = operation | _ -> false)
        let binding = result.Graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding ("observed", _, _, _) -> true | _ -> false)
        let value = result.Graph.Nodes[Assert.Single binding.Children]
        match value.Kind with
        | SemanticKind.Sequential [first; second; owner] ->
            for snapshot in [first; second] do
                match result.Graph.Nodes[snapshot].Kind with
                | SemanticKind.Binding (_, false, false, _) -> ()
                | kind -> failwithf "Public producer lost its immutable operand snapshot: %A" kind
            match result.Graph.Nodes[owner].Kind with
            | SemanticKind.SeqExpr (generator, captures) ->
                Assert.Equal<Set<NodeId>>(Set.ofList [first; second], captures |> List.choose _.SourceNodeId |> Set.ofList)
                match result.Graph.Nodes[generator].Kind with
                | SemanticKind.Lambda ([_], _, _, _, LambdaContext.SeqGenerator) -> ()
                | kind -> failwithf "Public producer did not create a generator: %A" kind
            | kind -> failwithf "Public producer lost its sequence value: %A" kind
        | kind -> failwithf "Public producer has no eager formation boundary: %A" kind

    [<Theory>]
    [<InlineData("let wrong = «Seq.map (fun (_: int<m>) -> 1<s>) (seq { yield 2<s> })»", "CCS8040")>]
    [<InlineData("let wrong = «Seq.filter (fun (_: int<m>) -> 1<m>)» (seq { yield 2<m> })", "CCS8003")>]
    [<InlineData("let wrong = «Seq.collect (fun (_: int<m>) -> 1<s>)» (seq { yield 2<m> })", "CCS8003")>]
    [<InlineData("let wrong = «Seq.append (seq { yield 1<m> }) (seq { yield 2<s> })»", "CCS8040")>]
    member _.``Producer admission retains callback kind and independent dimensional constraints``(source: string, code: string) =
        SequenceProducers.reject code source

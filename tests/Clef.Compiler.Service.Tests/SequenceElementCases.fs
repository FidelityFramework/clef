namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

// C-06 §4.4: sequence element admission belongs to its actual source owner.
// These are source/type/graph gates, not sequence frame or execution evidence.
module private SequenceElements =
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"
    let checkWithMain mainBody source =
        let finish = "\n[<EntryPoint>]\nlet main _ = " + mainBody + "\n"
        match parseAndCheck (prelude + source + finish) "sequence-elements.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result
        | CheckFailure result -> failwithf "Expected admitted sequence elements: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed sequence source: %A" errors

    let check source = checkWithMain "ignore observed; 0" source

    let reject code (marked: string) =
        let first, last = marked.IndexOf('«'), marked.IndexOf('»')
        Assert.True(first >= 0 && last > first)
        let before, selected = marked.Substring(0, first), marked.Substring(first + 1, last - first - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "sequence-elements-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + selected) }
        let source = prelude + marked.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Contradictory sequence reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s from checking: %A" code errors

    let expectedElement = function
        | "int" -> Types.intType
        | "distance" -> DimensionalCases.measuredInt DimensionalCases.metre
        | "inverse" -> DimensionalCases.measured (DimensionalCases.power DimensionalCases.metre -1I)
        | "nested" -> Types.mkSeqType (DimensionalCases.measuredInt DimensionalCases.metre)
        | other -> failwithf "Unknown expected element contract: %s" other

    let owners (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList

    // Walk this generator's body only. A nested sequence has its own element
    // constraint; an ordinary deferred body cannot inherit this yield owner.
    let assertOwnedElements (result: CheckResult) (owner: SemanticNode) =
        let nodes = result.Graph.Nodes
        let element =
            match applySubst owner.Type with
            | NativeType.TSeq element -> element
            | ty -> failwithf "Sequence owner lost its sequence type: %A" ty
        Assert.False(hasUnboundVars element, sprintf "Sequence owner has no resolved element type: %A" element)
        Assert.Empty(freeMeasureVars element)
        let body =
            match owner.Kind with
            | SemanticKind.SeqExpr (generator, _) ->
                Assert.Equal<NodeId list>([generator], owner.Children)
                Assert.True(NodeId.value generator >= 0, "Completed sequence still has a placeholder child")
                Assert.NotEqual(owner.Id, generator)
                Assert.Equal(Some owner.Id, nodes[generator].Parent)
                match nodes[generator].Kind with
                | SemanticKind.Lambda (_, body, _, _, LambdaContext.SeqGenerator) -> body
                | kind -> failwithf "Sequence lost its own generator: %A" kind
            | kind -> failwithf "Expected sequence owner: %A" kind
        let rec walk seen id =
            if Set.contains id seen then seen
            else
                let seen = Set.add id seen
                let node = nodes[id]
                match node.Kind with
                | SemanticKind.Yield payload ->
                    DimensionalCases.same Types.unitType node.Type
                    DimensionalCases.same element nodes[payload].Type
                    seen
                | SemanticKind.YieldBang _ -> failwith "A final sequence graph retained an unelaborated delegation"
                | SemanticKind.SeqExpr _ | SemanticKind.Lambda _ | SemanticKind.LazyExpr _ -> seen
                | _ -> node.Children |> List.fold walk seen
        walk Set.empty body |> ignore

[<Trait("Category", "NTU"); Trait("Subcategory", "SequenceElements")>]
type SequenceElementCases() =
    [<Theory>]
    [<InlineData("let wrong = seq { yield 1; «yield true» }", "CCS8003")>]
    [<InlineData("let wrong = seq { yield 1<m>; «yield 2<s>» }", "CCS8040")>]
    [<InlineData("let wrong = seq { yield 1.0<1/m>; «yield 2.0<m>» }", "CCS8040")>]
    [<InlineData("let wrong = seq { yield! seq { yield 1 }; «yield true» }", "CCS8003")>]
    [<InlineData("let wrong = seq { «yield! 1» }", "CCS8003")>]
    [<InlineData("let wrong = seq { «yield! Some 1» }", "CCS8003")>]
    [<InlineData("let wrong = seq { yield! seq { yield 1 }; «yield! seq { yield true }» }", "CCS8003")>]
    [<InlineData("let wrong = seq { yield! seq { yield 1<m> }; «yield! seq { yield 2<s> }» }", "CCS8040")>]
    [<InlineData("let wrong = seq { yield! seq { yield 1; «yield true» } }", "CCS8003")>]
    [<InlineData("let choose enabled = seq { if enabled then yield 1<m> else «yield 2<s>» }\nlet wrong = choose true", "CCS8040")>]
    [<InlineData("let wrong = seq {\n    let mutable enabled = true\n    while enabled do\n        yield 1<m>\n        enabled <- false\n    «yield 2<s>»\n}", "CCS8040")>]
    [<InlineData("let wrong = seq { yield 1<m>; for index in 1 .. 2 do «yield 2<s>» }", "CCS8040")>]
    [<InlineData("let incoming: seq<int<s>> = seq { yield 1<s> }\nlet wrong = seq { yield 1<m>; «yield! incoming» }", "CCS8040")>]
    [<InlineData("let wrong = seq { yield (seq { yield 1 }); «yield 2» }", "CCS8003")>]
    [<InlineData("let ints = seq { yield 1 }\nlet wrong: seq<bool> = «seq { yield! ints }»", "CCS8003")>]
    member _.``Every yield and delegation participates in its owner element constraint``(source: string, code: string) =
        SequenceElements.reject code source

    [<Theory>]
    [<InlineData("let observed = seq { yield 1; yield 2 }", "int")>]
    [<InlineData("let observed = seq { yield! seq { yield 1 } }", "int")>]
    [<InlineData("let observed = seq { yield! seq { yield 1<m> }; yield 2<m> }", "distance")>]
    [<InlineData("let observed: seq<int<m>> = seq { () }", "distance")>]
    [<InlineData("let observed = seq { yield 1.0<1/m>; yield! seq { yield 2.0<1/m> } }", "inverse")>]
    [<InlineData("let choose enabled = seq { if enabled then yield 1<m> else yield! seq { yield 2<m> } }\nlet observed = choose true", "distance")>]
    [<InlineData("let observed = seq {\n    let mutable enabled = true\n    while enabled do\n        yield! seq { yield 1<m> }\n        enabled <- false\n    yield 2<m>\n}", "distance")>]
    [<InlineData("let observed = seq { for index in 1 .. 2 do yield index }", "int")>]
    [<InlineData("let observed = seq { for index in 1 .. 2 do yield! seq { yield index } }", "int")>]
    [<InlineData("let observed = seq { yield (seq { yield 1<m> }); yield (seq { yield 2<m> }) }", "nested")>]
    member _.``Accepted sequence owners retain one precise element type across control flow``(source: string, expected: string) =
        let result = SequenceElements.check source
        DimensionalCases.same (Types.mkSeqType (SequenceElements.expectedElement expected)) (DimensionalCases.bindingType "observed" result)
        let owners = SequenceElements.owners result
        Assert.NotEmpty owners
        owners |> List.iter (SequenceElements.assertOwnedElements result)

    [<Theory>]
    [<InlineData("let inner = seq { yield true }")>]
    [<InlineData("let inner () = seq { yield true }")>]
    [<InlineData("let inner = fun () -> seq { yield true }")>]
    [<InlineData("let inner = lazy (seq { yield true })")>]
    member _.``Nested sequences establish independent element owners instead of donating a first yield``(inner: string) =
        let result = SequenceElements.check ("let observed = seq {\n    " + inner + "\n    yield 1<m>\n}")
        DimensionalCases.same (Types.mkSeqType (SequenceElements.expectedElement "distance")) (DimensionalCases.bindingType "observed" result)
        let owners = SequenceElements.owners result
        Assert.Equal(2, owners.Length)
        let actualTypes = owners |> List.map (fun node -> applySubst node.Type)
        Assert.Contains(Types.mkSeqType Types.boolType, actualTypes)
        Assert.Contains(Types.mkSeqType (SequenceElements.expectedElement "distance"), actualTypes)
        owners |> List.iter (SequenceElements.assertOwnedElements result)

    [<Fact>]
    member _.``Typed empty owners admit independent element types without a first yield``() =
        let result = SequenceElements.checkWithMain "ignore distance; ignore flags; 0" """
let distance: seq<int<m>> = seq { () }
let flags: seq<bool> = seq { () }
"""
        DimensionalCases.same (Types.mkSeqType (SequenceElements.expectedElement "distance")) (DimensionalCases.bindingType "distance" result)
        DimensionalCases.same (Types.mkSeqType Types.boolType) (DimensionalCases.bindingType "flags" result)
        let owners = SequenceElements.owners result
        Assert.Equal(2, owners.Length)
        Assert.NotEqual(owners[0].Id, owners[1].Id)
        owners |> List.iter (SequenceElements.assertOwnedElements result)

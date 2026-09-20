namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private ComputationAdmission =
    let prelude = "module ComputationAdmission\n"
    let reject (marked: string) =
        let first, last = marked.IndexOf('«'), marked.IndexOf('»')
        Assert.True(first >= 0 && last > first)
        let before, selected = marked.Substring(0, first), marked.Substring(first + 1, last - first - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "computation-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + selected) }
        let source = prelude + marked.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let errors = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = "CCS8401" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
            Assert.True(errors.Length = 1, sprintf "Expected one located CE admission error: %A" result.Diagnostics)
            let diagnostic = Assert.Single errors
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
            Assert.Contains(result.Graph.Nodes.Values, fun node ->
                node.Range = expected &&
                match node.Kind, node.Type with SemanticKind.Error _, NativeType.TError _ -> true | _ -> false)
        | Success result -> failwithf "Unsupported CE syntax reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected a checker admission diagnostic: %A" errors

    let check source =
        match parseAndCheck (prelude + source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n") "computation-positive.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result
        | CheckFailure result -> failwithf "Admitted source failed checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Admitted source failed parsing: %A" errors

    let observedType (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Kind with SemanticKind.Binding ("observed", _, _, _) -> Some node.Type | _ -> None)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ComputationAdmission")>]
type ComputationAdmissionCases() =
    [<Theory>]
    [<InlineData("return true")>]
    [<InlineData("return! true")>]
    [<InlineData("let! value = true\n    return value")>]
    [<InlineData("use! value = true\n    return value")>]
    [<InlineData("let! first = true\n    and! second = false\n    return first && second")>]
    [<InlineData("do! true\n    return ()")>]
    [<InlineData("match! true with\n    | true -> return 1\n    | false -> return 2")>]
    [<InlineData("while! false do ()\n    return ()")>]
    member _.``A plain function cannot erase a computation body``(body: string) =
        ComputationAdmission.reject ("let builder value = value\nlet observed = builder «{\n    " + body + "\n}»")

    [<Theory>]
    [<InlineData("type Surface = { choose: bool -> bool }\nlet surface = { choose = fun value -> value }\nlet observed = surface.choose «{ return true }»")>]
    [<InlineData("let factory () = fun value -> value\nlet observed = (factory ()) «{ return true }»")>]
    member _.``Resolved function fields and produced callees do not become builders``(source: string) =
        ComputationAdmission.reject source

    [<Theory>]
    [<InlineData("let! value = true\n    yield value")>]
    [<InlineData("use! value = true\n    yield value")>]
    [<InlineData("let! first = true\n    and! second = false\n    yield first && second")>]
    [<InlineData("do! true")>]
    [<InlineData("match! true with\n    | true -> yield 1\n    | false -> yield 2")>]
    [<InlineData("while! false do yield 1")>]
    member _.``Native seq does not supply missing bind or bang-control semantics``(body: string) =
        ComputationAdmission.reject ("let observed = seq {\n    «" + body + "»\n}")

    [<Theory>]
    [<InlineData("let observed =\n    «use value = true\n    value»")>]
    [<InlineData("let observed = seq {\n    «use value = true\n    yield value»\n}")>]
    member _.``Resource-use syntax requires lifecycle elaboration instead of ordinary let``(source: string) =
        ComputationAdmission.reject source

    [<Theory>]
    [<InlineData("yield 1")>]
    [<InlineData("yield! seq { yield 1 }")>]
    [<InlineData("return true")>]
    [<InlineData("return! true")>]
    member _.``Forms without an admitted semantic owner cannot become their payload``(expression: string) =
        ComputationAdmission.reject ("let observed = («" + expression + "»)")

    [<Theory>]
    [<InlineData("return true")>]
    [<InlineData("return! true")>]
    member _.``Native seq does not erase return forms``(expression: string) =
        ComputationAdmission.reject ("let observed = seq { «" + expression + "» }")

    [<Theory>]
    [<InlineData("let work = fun () -> «yield 1»")>]
    [<InlineData("let work () = «yield 1»")>]
    [<InlineData("let work = lazy («yield 1»)")>]
    member _.``Ordinary deferred bodies do not inherit an enclosing seq yield owner``(binding: string) =
        ComputationAdmission.reject ("let observed = seq {\n    " + binding + "\n    yield 2\n}")

    [<Fact>]
    member _.``A lexical seq binding retains precedence over native syntax fallback``() =
        ComputationAdmission.reject "let seq value = not value\nlet observed = seq «{ yield true }»"

    [<Theory>]
    [<InlineData("let observed = seq { yield 1; yield 2 }")>]
    [<InlineData("let observed = seq {\n    let mutable value = 1\n    while value <= 2 do\n        yield value\n        value <- value + 1\n}")>]
    [<InlineData("let observed = seq { for value in 1 .. 2 do yield value }")>]
    [<InlineData("let observed = seq { yield! seq { yield 1 } }")>]
    member _.``Native sequence construction retains its admitted yield path``(source: string) =
        let result = ComputationAdmission.check source
        DimensionalCases.same (Types.mkSeqType Types.intType) (ComputationAdmission.observedType result)
        Assert.Contains(result.Graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false)
        Assert.Contains(result.Graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Yield _ -> true | _ -> false)

    [<Theory>]
    [<InlineData("let work = fun () -> seq { yield 1 }\n    yield! work ()")>]
    [<InlineData("let work () = seq { yield 1 }\n    yield! work ()")>]
    [<InlineData("let work = lazy (seq { yield 1 })\n    yield! Lazy.force work")>]
    member _.``An actual inner seq establishes its own yield context``(body: string) =
        let result = ComputationAdmission.check ("let observed = seq {\n    " + body + "\n}")
        DimensionalCases.same (Types.mkSeqType Types.intType) (ComputationAdmission.observedType result)
        let sequences = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList
        Assert.Equal(2, sequences.Length)

    [<Fact>]
    member _.``Ordinary functions bindings and control flow retain their existing meaning``() =
        let result = ComputationAdmission.check """
let seq value = not value
let builder value = value
let observed =
    let mutable enabled = builder true
    let flip = fun () -> seq enabled
    while enabled do enabled <- flip ()
    match enabled with true -> false | false -> true
"""
        DimensionalCases.same Types.boolType (ComputationAdmission.observedType result)

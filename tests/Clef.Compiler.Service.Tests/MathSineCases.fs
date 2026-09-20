namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private MathSine =
    let prelude = "module Sine\n[<Measure>] type m\n"

    let check body =
        match parseAndCheck (prelude + body) "math-sine.clef" with
        | Success result ->
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            for node in result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) do
                for child in node.Children do Assert.True(result.Graph.Nodes.ContainsKey child)
            result
        | CheckFailure result -> failwithf "Expected successful source checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Parse failed: %A" errors

    let value name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Kind with
            | SemanticKind.Binding (actual, _, _, _) when actual = name -> Some result.Graph.Nodes[node.Children.Head]
            | _ -> None)

    let reject code (markedBody: string) =
        let start, finish = markedBody.IndexOf('«'), markedBody.IndexOf('»')
        Assert.True(start >= 0 && finish > start)
        let before = markedBody.Substring(0, start)
        let span = markedBody.Substring(start + 1, finish - start - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "math-sine-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + span) }
        let source = prelude + markedBody.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Invalid sine reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s from checking: %A" code errors

[<Trait("Category", "NTU"); Trait("Subcategory", "MathSine")>]
type MathSineCases() =
    [<Theory>]
    [<InlineData("0.0")>]
    [<InlineData("-0.25")>]
    [<InlineData("(1.0<m> / 2.0<m>)")>]
    member _.``Sine retains a dimensionless real application for passive witnessing``(argument: string) =
        let result = MathSine.check $"let observed = Math.sin {argument}\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n"
        let site = MathSine.value "observed" result
        DimensionalCases.same Types.floatType site.Type
        Assert.True(site.ValueRange.IsNone, "An integer range cannot stand in for a sine enclosure")
        match site.Kind with
        | SemanticKind.Application (callee, [operand]) ->
            DimensionalCases.same Types.floatType result.Graph.Nodes[operand].Type
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.Intrinsic info ->
                Assert.Equal(IntrinsicModule.Math, info.Module)
                Assert.Equal("sin", info.Operation)
                Assert.Equal("Math.sin", info.FullName)
                DimensionalCases.same (NativeType.TFun(Types.floatType, Types.floatType)) result.Graph.Nodes[callee].Type
            | kind -> failwithf "Sine lost its resolved semantic operation: %A" kind
            Assert.Equal<NodeId list>([callee; operand], site.Children)
        | kind -> failwithf "Expected one real operand: %A" kind

    [<Fact>]
    member _.``Exact source literal evidence does not become an invented sine result range``() =
        let result = MathSine.check "let observed = Math.sin 0.125\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n"
        let site = MathSine.value "observed" result
        match site.Kind with
        | SemanticKind.Application (_, [operand]) ->
            match result.Graph.Nodes[operand].Metadata.TryFind "Numeric.RealLiteral" with
            | Some (MetadataValue.RealLiteral ("0.125", exact)) ->
                Assert.Equal(1I, exact.Numerator)
                Assert.Equal(8I, exact.Denominator)
                let obligation = result.Graph.Nodes.Values |> Seq.find (fun node ->
                    match node.Kind with
                    | SemanticKind.Obligation { Body = ObligationBody.RealLiteralRange (value, _, _) } -> value = exact
                    | _ -> false)
                Assert.Contains(result.Graph.Edges, fun edge -> edge.Target = obligation.Id && List.contains operand edge.Sources)
                Assert.True(site.ValueRange.IsNone)
            | metadata -> failwithf "Sine input lost exact source evidence: %A" metadata
        | kind -> failwithf "Expected a sine application: %A" kind

    [<Fact>]
    member _.``Bare aliases fields and higher order use have the same source signature``() =
        // This is source/PSG admission, not an assertion of native closure or
        // target-math support. Unary sine has no nonempty proper partial call.
        let result = MathSine.check """
type Functions = { sine: float -> float }
let invoke operation value = operation value
let sine = Math.sin
let fields = { sine = Math.sin }
let throughAlias = sine 0.0
let throughField = fields.sine 0.25
let throughArgument = invoke Math.sin -0.25
let mapped = Option.map Math.sin (Some 0.0)
[<EntryPoint>]
let main _ = ignore throughAlias; ignore throughField; ignore throughArgument; ignore mapped; 0
"""
        DimensionalCases.same (NativeType.TFun(Types.floatType, Types.floatType)) (DimensionalCases.bindingType "sine" result)
        for name in ["throughAlias"; "throughField"; "throughArgument"] do
            DimensionalCases.same Types.floatType (DimensionalCases.bindingType name result)
        DimensionalCases.same (NativeType.TApp(Types.optionTyCon, [Types.floatType])) (DimensionalCases.bindingType "mapped" result)

    [<Theory>]
    [<InlineData("module Math =\n    let sin (x: int<m>) = x\nlet observed = Math.sin 2<m>")>]
    [<InlineData("type Functions = { sin: int<m> -> int<m> }\nlet Math = { sin = fun x -> x }\nlet observed = Math.sin 2<m>")>]
    [<InlineData("module Math =\n    let sqrt (x: int<m>) = x\nlet observed = Math.sqrt 2<m>")>]
    member _.``Lexical definitions retain precedence over the dimensionless intrinsic``(source: string) =
        let result = MathSine.check (source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0")
        DimensionalCases.same (DimensionalCases.measuredInt { Bases = Map.ofList [({ Name = "m"; Module = ["Sine"] }, 1)]; Vars = Map.empty })
            (DimensionalCases.bindingType "observed" result)

    [<Theory>]
    [<InlineData("let wrong = «Math.sin 1.0<m>»", "CCS8040")>]
    [<InlineData("let wrong = «Math.sin -0.25<m^-1>»", "CCS8040")>]
    [<InlineData("let sine = Math.sin\nlet wrong = «sine 1.0<m>»", "CCS8040")>]
    [<InlineData("let wrong = «Math.sin 1»", "CCS8003")>]
    [<InlineData("let wrong = «Math.sin true»", "CCS8003")>]
    [<InlineData("let wrong = «Math.sin ()»", "CCS8003")>]
    [<InlineData("let wrong = «Math.sin (Some 1.0)»", "CCS8003")>]
    [<InlineData("let wrong = «Math.sin (1.0, 2.0)»", "CCS8003")>]
    [<InlineData("let wrong = «Math.sin 0.0 1.0»", "CCS8003")>]
    member _.``Wrong dimensions kinds and arity fail before successful checking``(source: string, code: string) =
        MathSine.reject code source

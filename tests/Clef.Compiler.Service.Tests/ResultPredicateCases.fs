namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private ResultPredicates =
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"
    let check source =
        match parseAndCheck (prelude + source) "result-predicates.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            for node in result.Graph.Nodes.Values do
                match node.Kind with SemanticKind.Error _ -> failwithf "Error node reached successful checking: %A" node.Id | _ -> ()
                if node.IsReachable then
                    for child in node.Children do Assert.True(result.Graph.Nodes.ContainsKey child)
                    match node.Kind with
                    | SemanticKind.Intrinsic info -> Assert.NotEqual(IntrinsicModule.Result, info.Module)
                    | SemanticKind.VarRef (_, Some definition) -> Assert.True(result.Graph.Nodes.ContainsKey definition)
                    | SemanticKind.Lambda (_, _, captures, _, _) ->
                        Assert.Empty(freeTypeVars node.Type)
                        for capture in captures do
                            Assert.True(capture.SourceNodeId |> Option.exists result.Graph.Nodes.ContainsKey)
                    | SemanticKind.DUGetTag _ | SemanticKind.DUConstruct _ | SemanticKind.PatternBinding _ ->
                        Assert.Empty(freeTypeVars node.Type)
                    | _ -> ()
            result
        | CheckFailure result -> failwithf "Expected admitted Result predicate: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed Result predicate: %A" errors

    let binding name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name) | _ -> false)
    let value name result = result.Graph.Nodes[(binding name result).Children.Head]

    let assertTagOnly operation (result: CheckResult) input comparison =
        let nodes = result.Graph.Nodes
        DimensionalCases.same Types.boolType nodes[comparison].Type
        match nodes[comparison].Kind with
        | SemanticKind.Application (callee, [tag; expected]) ->
            match nodes[callee].Kind with
            | SemanticKind.Intrinsic info ->
                Assert.Equal(IntrinsicModule.Operators, info.Module)
                Assert.Equal("op_Equality", info.Operation)
            | kind -> failwithf "Predicate invoked more than a tag comparison: %A" kind
            match nodes[tag].Kind with
            | SemanticKind.DUGetTag (original, carrier) ->
                Assert.Equal(input, original)
                DimensionalCases.same nodes[input].Type carrier
            | kind -> failwithf "Predicate did not inspect the original Result tag: %A" kind
            match nodes[expected].Kind with
            | SemanticKind.Literal (NativeLiteral.Int (tag, _)) -> Assert.Equal((if operation = "isOk" then 0L else 1L), tag)
            | kind -> failwithf "Predicate lost its canonical case tag: %A" kind
        | kind -> failwithf "Predicate extracted or invoked a payload instead of comparing its tag: %A" kind

    let assertInputCall (result: CheckResult) input =
        match result.Graph.Nodes[input].Kind with
        | SemanticKind.Application (callee, [_]) ->
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.VarRef ("input", Some definition) -> Assert.Equal((binding "input" result).Id, definition)
            | kind -> failwithf "Predicate lost the source input factory: %A" kind
        | kind -> failwithf "Expected one input factory application: %A" kind

    let reject code (marked: string) =
        let first, last = marked.IndexOf('«'), marked.IndexOf('»')
        Assert.True(first >= 0 && last > first)
        let before, selected = marked.Substring(0, first), marked.Substring(first + 1, last - first - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "result-predicate-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + selected) }
        let source = prelude + marked.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Invalid predicate reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s from checking: %A" code errors

[<Trait("Category", "NTU"); Trait("Subcategory", "ResultPredicates")>]
type ResultPredicateCases() =
    [<Theory>]
    [<InlineData("isOk", true)>]
    [<InlineData("isOk", false)>]
    [<InlineData("isError", true)>]
    [<InlineData("isError", false)>]
    member _.``Predicates evaluate their one Result operand before inspecting only the selected tag``(operation: string, ok: bool) =
        let result = ResultPredicates.check $"""
let input () : Result<int<m>, int<s>> = {if ok then "Ok 3<m>" else "Error 4<s>"}
let observed = Result.{operation} (input ())
[<EntryPoint>]
let main _ = ignore observed; 0
"""
        DimensionalCases.same Types.boolType (DimensionalCases.bindingType "observed" result)
        match (ResultPredicates.value "observed" result).Kind with
        | SemanticKind.Sequential [input; comparison] ->
            ResultPredicates.assertInputCall result input
            ResultPredicates.assertTagOnly operation result input comparison
        | kind -> failwithf "Predicate lost its eager one-operand boundary: %A" kind

    [<Theory>]
    [<InlineData("isOk")>]
    [<InlineData("isError")>]
    member _.``Both pipe directions retain the same single input evaluation``(operation: string) =
        let result = ResultPredicates.check $"""
let input () : Result<unit, int<m>> = Ok ()
let forward = input () |> Result.{operation}
let backward = Result.{operation} <| input ()
[<EntryPoint>]
let main _ = ignore forward; ignore backward; 0
"""
        match (ResultPredicates.value "backward" result).Kind with
        | SemanticKind.Sequential [input; comparison] ->
            ResultPredicates.assertInputCall result input
            ResultPredicates.assertTagOnly operation result input comparison
        | kind -> failwithf "Backward pipe changed unary operand evaluation: %A" kind
        match (ResultPredicates.value "forward" result).Kind with
        | SemanticKind.Sequential [input; call] ->
            ResultPredicates.assertInputCall result input
            match result.Graph.Nodes[call].Kind with
            | SemanticKind.Sequential [reused; comparison] ->
                Assert.Equal(input, reused)
                ResultPredicates.assertTagOnly operation result input comparison
            | kind -> failwithf "Forward pipe did not reuse its eager input: %A" kind
        | kind -> failwithf "Forward pipe lost its source input: %A" kind

    [<Theory>]
    [<InlineData("isOk")>]
    [<InlineData("isError")>]
    member _.``Bare aliases and explicit type arguments instantiate both payload types independently``(operation: string) =
        let result = ResultPredicates.check $"""
let inspect = Result.{operation}
let first = inspect (Ok 3<m>: Result<int<m>, unit>)
let second = inspect (Error 0.25<1/s>: Result<bool, float<1/s>>)
let explicit = Result.{operation}<int<s>, unit> (Ok 4<s>)
let bound: Result<unit, int<m>> -> bool = Result.{operation}<unit, int<m>>
let third = bound (Error 5<m>)
[<EntryPoint>]
let main _ = ignore first; ignore second; ignore explicit; ignore third; 0
"""
        for name in ["first"; "second"; "explicit"; "third"] do
            DimensionalCases.same Types.boolType (DimensionalCases.bindingType name result)
        let bound =
            let rec withoutAnnotation node =
                match node.Kind with
                | SemanticKind.TypeAnnotation (value, _) -> withoutAnnotation result.Graph.Nodes[value]
                | _ -> node
            withoutAnnotation (ResultPredicates.value "bound" result)
        match bound.Kind with
        | SemanticKind.Lambda ([_], body, [], _, _) ->
            match result.Graph.Nodes[body].Kind with
            | SemanticKind.Sequential [input; comparison] -> ResultPredicates.assertTagOnly operation result input comparison
            | kind -> failwithf "Bare predicate lost its local input boundary: %A" kind
        | kind -> failwithf "Typed predicate value is not an ordinary unary closure: %A" kind
        let site = ResultPredicates.value "third" result
        match site.Kind with
        | SemanticKind.Application (callee, arguments) ->
            let obligation = result.Graph.Nodes.Values |> Seq.find (fun node ->
                node.Range = site.Range &&
                match node.Kind with SemanticKind.Obligation { Body = ObligationBody.ApplicationDimensions _ } -> true | _ -> false)
            let edge = result.Graph.Edges |> List.find (fun edge -> edge.Target = obligation.Id)
            Assert.Equal<Set<NodeId>>(Set.ofList ((ResultPredicates.binding "bound" result).Id :: site.Id :: callee :: arguments), Set.ofList edge.Sources)
        | kind -> failwithf "Stored predicate lost its ordinary application and participants: %A" kind

    [<Theory>]
    [<InlineData("isOk", "Ok payload")>]
    [<InlineData("isError", "Error payload")>]
    member _.``Callable payloads retain their capture identity without extraction or invocation``(operation: string, input: string) =
        let result = ResultPredicates.check $"""
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let payload = fun () -> calls <- calls + 1; 3<m>
    let observed = Result.{operation} ({input}: Result<unit -> int<m>, unit -> int<m>>)
    ignore observed
    calls
"""
        match (ResultPredicates.value "observed" result).Kind with
        | SemanticKind.Sequential [input; comparison] -> ResultPredicates.assertTagOnly operation result input comparison
        | kind -> failwithf "Callable payload changed predicate semantics: %A" kind
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.DUEliminate _ | SemanticKind.FieldGet _ -> true | _ -> false)
        match (ResultPredicates.value "payload" result).Kind with
        | SemanticKind.Lambda ([_], _, [capture], _, _) ->
            Assert.True capture.IsMutable
            Assert.Equal(Some (ResultPredicates.binding "calls" result).Id, capture.SourceNodeId)
        | kind -> failwithf "Payload lost its unit formal or captured cell identity: %A" kind

    [<Theory>]
    [<InlineData("module Result =\n    let isOk (value: int<m>) = value\n    let isError (value: int<s>) = value")>]
    [<InlineData("type Surface = { isOk: int<m> -> int<m>; isError: int<s> -> int<s> }\nlet Result = { isOk = (fun value -> value); isError = (fun value -> value) }")>]
    member _.``Lexical predicate names retain source module and record resolution``(definitions: string) =
        let result = ResultPredicates.check (definitions + "\nlet distance = Result.isOk 3<m>\nlet duration = Result.isError 4<s>\n[<EntryPoint>]\nlet main _ = ignore distance; ignore duration; 0\n")
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) (DimensionalCases.bindingType "distance" result)
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.second) (DimensionalCases.bindingType "duration" result)

    [<Theory>]
    [<InlineData("let wrong = «Result.isOk 3»", "CCS8003")>]
    [<InlineData("let wrong = «Result.isError true»", "CCS8003")>]
    [<InlineData("let wrong = «Result.isOk (Some 1)»", "CCS8003")>]
    [<InlineData("let wrong = «Result.isError (Error (): Result<int<m>, unit>) true»", "CCS8003")>]
    [<InlineData("let wrong = «Result.isOk<int<m>, bool> (Ok 3<s>)»", "CCS8040")>]
    [<InlineData("let wrong = «Result.isError<unit, int<m>> (Error 3<s>)»", "CCS8040")>]
    [<InlineData("let inspect: Result<int<m>, bool> -> bool = Result.isOk\nlet wrong = «inspect (Ok 3<s>)»", "CCS8040")>]
    [<InlineData("let inspect = Result.isError\nlet wrong = «inspect (Error (): Result<int<m>, unit>) ()»", "CCS8003")>]
    member _.``Predicates reject wrong carriers dimensional conflicts and extra bool application``(source: string, code: string) =
        ResultPredicates.reject code source

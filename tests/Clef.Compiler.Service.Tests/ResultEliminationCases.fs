namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private ResultElimination =
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"
    let check source =
        let result =
            match parseAndCheck (prelude + source) "result-elimination.clef" with
            | Success result -> result
            | CheckFailure result -> failwithf "Result elimination failed checking: %A" result.Diagnostics
            | ParseFailure errors -> failwithf "Result elimination failed parsing: %A" errors
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
                | SemanticKind.DUEliminate _ | SemanticKind.DUConstruct _ | SemanticKind.PatternBinding _ ->
                    Assert.Empty(freeTypeVars node.Type)
                | _ -> ()
        result

    let binding name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name) | _ -> false)
    let value name result = result.Graph.Nodes[(binding name result).Children.Head]
    let metre = DimensionalCases.measuredInt DimensionalCases.metre
    let first operation =
        match operation with
        | "defaultValue" -> "3<m>"
        | "defaultWith" -> "fun (_: int<s>) -> 3<m>"
        | _ -> "fun (_: int<m>) -> ()"

    let assertCall name (result: CheckResult) id =
        match result.Graph.Nodes[id].Kind with
        | SemanticKind.Application (callee, _) ->
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (actual, _) -> Assert.True(actual = name || actual.EndsWith("." + name), actual)
            | kind -> failwithf "Expected source function %s: %A" name kind
        | kind -> failwithf "Expected invocation of %s: %A" name kind

    let assertChoice operation (result: CheckResult) first input choice =
        let graph = result.Graph
        let extracted caseName caseIndex id =
            match graph.Nodes[id].Kind with
            | SemanticKind.DUEliminate (original, index, name, ty) ->
                Assert.Equal(input, original)
                Assert.Equal(caseIndex, index)
                Assert.Equal(caseName, name)
                DimensionalCases.same ty graph.Nodes[id].Type
                match graph.Nodes[input].Type with
                | NativeType.TApp (_, types) -> DimensionalCases.same types[index] ty
                | ty -> failwithf "Result input lost payload types: %A" ty
            | kind -> failwithf "Expected %s payload extraction: %A" caseName kind
        let invoked caseName caseIndex id =
            match graph.Nodes[id].Kind with
            | SemanticKind.Application (callback, [argument]) ->
                Assert.Equal(first, callback)
                extracted caseName caseIndex argument
            | kind -> failwithf "Expected the selected callback to consume %s: %A" caseName kind
        match graph.Nodes[choice].Kind with
        | SemanticKind.IfThenElse (guard, ok, Some error) ->
            match graph.Nodes[guard].Kind with
            | SemanticKind.Application (_, [tag; expected]) ->
                match graph.Nodes[tag].Kind, graph.Nodes[expected].Kind with
                | SemanticKind.DUGetTag (original, ty), SemanticKind.Literal (NativeLiteral.Int (0L, _)) ->
                    Assert.Equal(input, original)
                    DimensionalCases.same graph.Nodes[input].Type ty
                | kinds -> failwithf "Result guard lost its canonical Ok case: %A" kinds
            | kind -> failwithf "Expected Result case test: %A" kind
            match operation with
            | "defaultValue" -> extracted "Ok" 0 ok; Assert.Equal(first, error)
            | "defaultWith" -> extracted "Ok" 0 ok; invoked "Error" 1 error
            | _ ->
                invoked "Ok" 0 ok
                match graph.Nodes[error].Kind with
                | SemanticKind.Literal NativeLiteral.Unit -> ()
                | kind -> failwithf "Error iteration path lost its logical unit: %A" kind
                DimensionalCases.same Types.unitType graph.Nodes[choice].Type
        | kind -> failwithf "Result elimination lost its case boundary: %A" kind

    let reject code (marked: string) =
        let start, finish = marked.IndexOf('«'), marked.IndexOf('»')
        Assert.True(start >= 0 && finish > start)
        let before, span = marked.Substring(0, start), marked.Substring(start + 1, finish - start - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "result-elimination-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + span) }
        let source = prelude + marked.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let matches = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
            Assert.True(matches.Length = 1, sprintf "Expected one %s: %A" code result.Diagnostics)
            Assert.Equal<SourceRange>(expected, (Assert.Single matches).Range)
        | Success result -> failwithf "Invalid eliminator reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s: %A" code errors

[<Trait("Category", "NTU"); Trait("Subcategory", "ResultElimination")>]
type ResultEliminationCases() =
    [<Theory>]
    [<InlineData("defaultValue", true)>]
    [<InlineData("defaultValue", false)>]
    [<InlineData("defaultWith", true)>]
    [<InlineData("defaultWith", false)>]
    [<InlineData("iter", true)>]
    [<InlineData("iter", false)>]
    member _.``Operands are eager while each eliminator uses only its selected payload and callback``(operation: string, ok: bool) =
        let result = ResultElimination.check $"""
let factory () = {ResultElimination.first operation}
let input () : Result<int<m>, int<s>> = {if ok then "Ok 2<m>" else "Error 4<s>"}
let observed = Result.{operation} (factory ()) (input ())
[<EntryPoint>]
let main _ = ignore observed; 0
"""
        DimensionalCases.same (if operation = "iter" then Types.unitType else ResultElimination.metre) (DimensionalCases.bindingType "observed" result)
        match (ResultElimination.value "observed" result).Kind with
        | SemanticKind.Sequential [first; input; choice] ->
            ResultElimination.assertCall "factory" result first
            ResultElimination.assertCall "input" result input
            ResultElimination.assertChoice operation result first input choice
        | kind -> failwithf "Result eliminator lost eager operands: %A" kind

    [<Theory>]
    [<InlineData("defaultValue")>]
    [<InlineData("defaultWith")>]
    [<InlineData("iter")>]
    member _.``Partial formation snapshots the supplied value and resolves residual references locally``(operation: string) =
        let replacement = if operation = "defaultValue" then "9<m>" else ResultElimination.first operation
        let supplied =
            if operation = "defaultValue" then "3<m>"
            elif operation = "defaultWith" then "fun (_: int<s>) -> calls <- calls + 1; 3<m>"
            else "fun (_: int<m>) -> calls <- calls + 1"
        let result = ResultElimination.check $"""
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let mutable supplied = {supplied}
    let stored = Result.{operation} supplied
    supplied <- {replacement}
    let observed = stored (Error 2<s>: Result<int<m>, int<s>>)
    ignore observed
    calls
"""
        let graph = result.Graph
        match (ResultElimination.value "stored" result).Kind with
        | SemanticKind.Sequential [snapshot; closure] ->
            match graph.Nodes[snapshot].Kind, graph.Nodes[graph.Nodes[snapshot].Children.Head].Kind with
            | SemanticKind.Binding (_, false, false, _), SemanticKind.VarRef (_, Some definition) ->
                Assert.Equal((ResultElimination.binding "supplied" result).Id, definition)
            | kinds -> failwithf "Partial lost its immutable snapshot: %A" kinds
            match graph.Nodes[closure].Kind with
            | SemanticKind.Lambda ([(_, _, formal)], body, [capture], _, _) ->
                Assert.False capture.IsMutable
                Assert.Equal(Some snapshot, capture.SourceNodeId)
                match graph.Nodes[body].Kind with
                | SemanticKind.Sequential [first; input; choice] ->
                    match graph.Nodes[first].Kind, graph.Nodes[input].Kind with
                    | SemanticKind.VarRef (_, Some source), SemanticKind.VarRef (_, Some parameter) ->
                        Assert.Equal(snapshot, source)
                        Assert.Equal(formal, parameter)
                    | kinds -> failwithf "Residual references lost their resolved participants: %A" kinds
                    ResultElimination.assertChoice operation result first input choice
                | kind -> failwithf "Residual operands do not precede branch selection: %A" kind
            | kind -> failwithf "Partial lost its one-result-parameter closure: %A" kind
        | kind -> failwithf "Partial lost formation sequencing: %A" kind
        if operation <> "defaultValue" then
            let calls = ResultElimination.binding "calls" result
            Assert.Contains(graph.Nodes.Values, fun node ->
                match node.Kind with
                | SemanticKind.Lambda (_, _, captures, _, _) -> captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some calls.Id)
                | _ -> false)

    [<Theory>]
    [<InlineData("defaultValue")>]
    [<InlineData("defaultWith")>]
    [<InlineData("iter")>]
    member _.``Bare aliases and explicit schemes keep success and error types independent``(operation: string) =
        let second =
            match operation with
            | "defaultValue" -> "-0.25<m^-1>"
            | "defaultWith" -> "fun (_: bool) -> -0.25<m^-1>"
            | _ -> "fun (_: float<m^-1>) -> ()"
        let resultType = if operation = "iter" then "unit" else "int<m>"
        let firstType =
            match operation with "defaultValue" -> "int<m>" | "defaultWith" -> "int<s> -> int<m>" | _ -> "int<m> -> unit"
        let result = ResultElimination.check $"""
type Surface = {{ choose: ({firstType}) -> Result<int<m>, int<s>> -> {resultType} }}
let choose = Result.{operation}
let first = choose ({ResultElimination.first operation}) (Ok 2<m>: Result<int<m>, int<s>>)
let inverse = choose ({second}) (Error true: Result<float<m^-1>, bool>)
let surface = {{ choose = Result.{operation}<int<m>, int<s>> }}
let stored = surface.choose ({ResultElimination.first operation})
let observed = stored (Error 2<s>)
[<EntryPoint>]
let main _ = ignore first; ignore inverse; ignore observed; 0
"""
        DimensionalCases.same (if operation = "iter" then Types.unitType else ResultElimination.metre) (DimensionalCases.bindingType "first" result)
        let inverse = DimensionalCases.measured (DimensionalCases.power DimensionalCases.metre -1I)
        DimensionalCases.same (if operation = "iter" then Types.unitType else inverse) (DimensionalCases.bindingType "inverse" result)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Binding ("choose", _, _, _) -> true | _ -> false)

    [<Theory>]
    [<InlineData("defaultValue")>]
    [<InlineData("defaultWith")>]
    [<InlineData("iter")>]
    member _.``Pipes preserve their source operand order through elimination``(operation: string) =
        let result = ResultElimination.check $"""
let factory () = {ResultElimination.first operation}
let input () : Result<int<m>, int<s>> = Error 2<s>
let forward = input () |> Result.{operation} (factory ())
let backward = Result.{operation} (factory ()) <| input ()
[<EntryPoint>]
let main _ = ignore forward; ignore backward; 0
"""
        match (ResultElimination.value "forward" result).Kind with
        | SemanticKind.Sequential [first; call] ->
            ResultElimination.assertCall "input" result first
            match result.Graph.Nodes[call].Kind with
            | SemanticKind.Sequential [callback; input; choice] ->
                Assert.Equal(first, input)
                ResultElimination.assertCall "factory" result callback
                ResultElimination.assertChoice operation result callback input choice
            | kind -> failwithf "Forward pipe lost operand reuse: %A" kind
        | kind -> failwithf "Forward pipe lost its leading input: %A" kind
        match (ResultElimination.value "backward" result).Kind with
        | SemanticKind.Sequential [first; input; choice] ->
            ResultElimination.assertCall "factory" result first
            ResultElimination.assertCall "input" result input
            ResultElimination.assertChoice operation result first input choice
        | kind -> failwithf "Backward pipe lost eager operand order: %A" kind

    [<Theory>]
    [<InlineData("defaultValue", true)>]
    [<InlineData("defaultValue", false)>]
    [<InlineData("defaultWith", true)>]
    [<InlineData("defaultWith", false)>]
    member _.``Function valued defaults keep their declared boundary after every supplied operand``(operation: string, ok: bool) =
        let payload = "fun (distance: int<m>) (elapsed: int<s>) -> distance / elapsed"
        let fallback = if operation = "defaultValue" then payload else $"fun (_: bool) -> trace <- trace * 10 + 3; {payload}"
        let result = ResultElimination.check $"""
let mutable trace = 0
let factory () = trace <- trace * 10 + 1; {fallback}
let input () : Result<int<m> -> int<s> -> int<m/s>, bool> =
    trace <- trace * 10 + 2
    {if ok then $"Ok ({payload})" else "Error true"}
let distance () = trace <- trace * 10 + 4; 6<m>
let elapsed () = trace <- trace * 10 + 6; 2<s>
let observed = Result.{operation} (factory ()) (input ()) (distance ()) (elapsed ())
[<EntryPoint>]
let main _ = if observed = 3<m/s> then 0 else 1
"""
        match (ResultElimination.value "observed" result).Kind with
        | SemanticKind.Sequential [first; input; distance; elapsed; applied] ->
            for name, id in ["factory", first; "input", input; "distance", distance; "elapsed", elapsed] do
                ResultElimination.assertCall name result id
            match result.Graph.Nodes[applied].Kind with
            | SemanticKind.Application (choice, [actualDistance; actualElapsed]) ->
                Assert.Equal(distance, actualDistance)
                Assert.Equal(elapsed, actualElapsed)
                ResultElimination.assertChoice operation result first input choice
            | kind -> failwithf "Later operands did not apply to the selected function: %A" kind
        | kind -> failwithf "Function result absorbed or delayed a supplied operand: %A" kind

    [<Theory>]
    [<InlineData("defaultValue")>]
    [<InlineData("defaultWith")>]
    member _.``Stored function defaults retain subsequent callable stages and capture identity``(operation: string) =
        let first = if operation = "defaultValue" then "payload" else "fun (_: int<s>) -> payload"
        let result = ResultElimination.check $"""
[<EntryPoint>]
let main _ =
    let mutable offset = 1<m>
    let payload = fun (distance: int<m>) -> fun () -> distance + offset
    let choose = Result.{operation}
    let stored = choose ({first})
    let selected = stored (Error 2<s>: Result<int<m> -> unit -> int<m>, int<s>>)
    let stage = selected 3<m>
    offset <- 2<m>
    let observed = stage ()
    if observed = 5<m> then 0 else 1
"""
        let payloadType = NativeType.TFun(ResultElimination.metre, NativeType.TFun(Types.unitType, ResultElimination.metre))
        DimensionalCases.same payloadType (DimensionalCases.bindingType "selected" result)
        DimensionalCases.same (NativeType.TFun(Types.unitType, ResultElimination.metre)) (DimensionalCases.bindingType "stage" result)
        let offset = ResultElimination.binding "offset" result
        Assert.Contains(result.Graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Lambda (_, _, captures, _, _) -> captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some offset.Id)
            | _ -> false)

    [<Fact>]
    member _.``Iteration consumes function and unit payloads without implicit extra invocation``() =
        let result = ResultElimination.check """
let payload = fun (value: int<m>) -> value
let functionValue = Result.iter (fun (_: int<m> -> int<m>) -> ()) (Ok payload: Result<int<m> -> int<m>, int<s>>)
let unitValue = Result.iter (fun () -> ()) (Ok (): Result<unit, bool>)
let unitDefault = Result.defaultWith (fun (_: bool) -> ()) (Error true: Result<unit, bool>)
[<EntryPoint>]
let main _ = functionValue; unitValue; unitDefault; 0
"""
        for name in ["functionValue"; "unitValue"; "unitDefault"] do
            DimensionalCases.same Types.unitType (DimensionalCases.bindingType name result)
        match (ResultElimination.value "functionValue" result).Kind with
        | SemanticKind.Sequential [action; input; choice] -> ResultElimination.assertChoice "iter" result action input choice
        | kind -> failwithf "Function payload acquired another invocation: %A" kind

    [<Theory>]
    [<InlineData("defaultValue")>]
    [<InlineData("defaultWith")>]
    [<InlineData("iter")>]
    member _.``Stored eliminators preserve resident ordinary application participants``(operation: string) =
        let result = ResultElimination.check $"""
let stored = Result.{operation} ({ResultElimination.first operation})
let observed = stored (Ok 2<m>: Result<int<m>, int<s>>)
[<EntryPoint>]
let main _ = ignore observed; 0
"""
        let graph = result.Graph
        let site = ResultElimination.value "observed" result
        match site.Kind with
        | SemanticKind.Application (callee, arguments) ->
            let obligation = graph.Nodes.Values |> Seq.find (fun node ->
                node.Range = site.Range && match node.Kind with
                                           | SemanticKind.Obligation { Body = ObligationBody.ApplicationDimensions _ } -> true
                                           | _ -> false)
            let edge = graph.Edges |> List.find (fun edge -> edge.Target = obligation.Id)
            match graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (_, Some definition) ->
                Assert.Equal<Set<NodeId>>(Set.ofList (definition :: site.Id :: callee :: arguments), Set.ofList edge.Sources)
                for participant in edge.Sources do Assert.True(graph.Nodes.ContainsKey participant)
            | kind -> failwithf "Stored eliminator lost its declaration: %A" kind
        | kind -> failwithf "Expected an ordinary retained application: %A" kind

    [<Theory>]
    [<InlineData("CCS8040", "let wrong = «Result.defaultValue 1<m> (Ok 2<s>: Result<int<s>, bool>)»")>]
    [<InlineData("CCS8040", "let stored = Result.defaultValue -0.25<m^-1>\nlet wrong = «stored (Ok 0.5<s^-1>: Result<float<s^-1>, bool>)»")>]
    [<InlineData("CCS8040", "let wrong = «Result.defaultWith (fun (_: int<s>) -> 1<m>) (Error 2<m>: Result<int<m>, int<m>>)»")>]
    [<InlineData("CCS8040", "let wrong = «Result.defaultWith (fun (_: bool) -> 1<m>) (Ok 2<s>: Result<int<s>, bool>)»")>]
    [<InlineData("CCS8040", "let wrong = «Result.iter (fun (_: int<m>) -> ()) (Ok 2<s>: Result<int<s>, bool>)»")>]
    [<InlineData("CCS8040", "let wrong = «Result.defaultValue<int<m>, int<s>> 1<s>» (Error 2<s>)")>]
    [<InlineData("CCS8040", "let wrong = «Result.defaultWith<int<m>, int<s>> (fun (_: int<m>) -> 1<m>)» (Error 2<s>)")>]
    [<InlineData("CCS8003", "let wrong = «Result.iter (fun (_: bool) -> 3)» (Ok true: Result<bool, bool>)")>]
    [<InlineData("CCS8003", "let wrong = «Result.defaultWith 3» (Error true: Result<int, bool>)")>]
    [<InlineData("CCS8003", "let wrong = «Result.iter true» (Ok true: Result<bool, bool>)")>]
    [<InlineData("CCS8003", "let wrong = «Result.defaultValue 3 (Some 2)»")>]
    [<InlineData("CCS8003", "let wrong = «Result.defaultWith (fun (_: bool) -> 3) true»")>]
    [<InlineData("CCS8003", "let wrong = «Result.iter (fun (_: bool) -> ()) true»")>]
    [<InlineData("CCS8003", "let wrong = «Result.defaultValue 3 (Ok 2: Result<int, bool>) 1»")>]
    [<InlineData("CCS8004", "let wrong = «Result.defaultValue<int<m>>»")>]
    [<InlineData("CCS8004", "let wrong = «Result.defaultWith<int<m>>»")>]
    [<InlineData("CCS8004", "let wrong = «Result.iter<int<m>>»")>]
    member _.``Invalid elimination contracts fail with exact diagnostics before witnessing``(code: string, source: string) =
        ResultElimination.reject code source

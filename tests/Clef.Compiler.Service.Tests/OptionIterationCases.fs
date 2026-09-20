namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private OptionIteration =
    let option payload = NativeType.TApp(Types.optionTyCon, [payload])
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"

    let check source =
        let result =
            match parseAndCheck (prelude + source) "option-iteration.clef" with
            | Success result -> result
            | CheckFailure result -> failwithf "Expected successful checking: %A" result.Diagnostics
            | ParseFailure errors -> failwithf "Parse failed: %A" errors
        DimensionalCases.noErrors result
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Error _ -> true | _ -> false)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Intrinsic info ->
                info.Module = IntrinsicModule.Option && info.Operation = "iter"
            | _ -> false)
        for node in result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) do
            for child in node.Children do Assert.True(result.Graph.Nodes.ContainsKey child)
            match node.Kind with
            | SemanticKind.VarRef (_, Some definition) -> Assert.True(result.Graph.Nodes.ContainsKey definition)
            | SemanticKind.Lambda (_, _, captures, _, _) ->
                for capture in captures do
                    capture.SourceNodeId |> Option.iter (fun source -> Assert.True(result.Graph.Nodes.ContainsKey source))
            | _ -> ()
        result

    let binding name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name)
            | _ -> false)

    let value name result = result.Graph.Nodes[(binding name result).Children.Head]

    let reject code (markedBody: string) =
        let start = markedBody.IndexOf('«')
        let finish = markedBody.IndexOf('»')
        Assert.True(start >= 0 && finish > start)
        let before = markedBody.Substring(0, start)
        let span = markedBody.Substring(start + 1, finish - start - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "option-iteration-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + span) }
        let source = prelude + markedBody.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Invalid iteration reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s from checking: %A" code errors

    let assertCall name (result: CheckResult) id =
        match result.Graph.Nodes[id].Kind with
        | SemanticKind.Application (callee, _) ->
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (actual, _) -> Assert.True(actual = name || actual.EndsWith("." + name), actual)
            | kind -> failwithf "Expected reference to %s: %A" name kind
        | kind -> failwithf "Expected call to %s: %A" name kind

    let assertIteration (result: CheckResult) action input choice =
        let graph = result.Graph
        DimensionalCases.same Types.unitType graph.Nodes[choice].Type
        match graph.Nodes[choice].Kind with
        | SemanticKind.IfThenElse (guard, present, Some absent) ->
            Assert.Equal(SemanticKind.Literal NativeLiteral.Unit, graph.Nodes[absent].Kind)
            DimensionalCases.same Types.unitType graph.Nodes[absent].Type
            match graph.Nodes[present].Kind with
            | SemanticKind.Application (callee, [payload]) ->
                Assert.Equal(action, callee)
                DimensionalCases.same Types.unitType graph.Nodes[present].Type
                match graph.Nodes[payload].Kind with
                | SemanticKind.DUEliminate (original, 1, "Some", payloadType) ->
                    Assert.Equal(input, original)
                    DimensionalCases.same payloadType graph.Nodes[payload].Type
                    DimensionalCases.same (NativeType.TFun(payloadType, Types.unitType)) graph.Nodes[action].Type
                | kind -> failwithf "Action did not receive the guarded original payload: %A" kind
            | kind -> failwithf "Some did not contain the action invocation: %A" kind
            match graph.Nodes[guard].Kind with
            | SemanticKind.Application (_, [tag; expected]) ->
                match graph.Nodes[tag].Kind with
                | SemanticKind.DUGetTag (original, carrier) ->
                    Assert.Equal(input, original)
                    DimensionalCases.same carrier graph.Nodes[input].Type
                | kind -> failwithf "Guard did not inspect the action's option: %A" kind
                match graph.Nodes[expected].Kind with
                | SemanticKind.Literal (NativeLiteral.Int (1L, _)) -> ()
                | kind -> failwithf "Guard did not select Some: %A" kind
            | kind -> failwithf "Expected a tag comparison: %A" kind
        | kind -> failwithf "Expected a conditional action: %A" kind

[<Trait("Category", "NTU"); Trait("Subcategory", "OptionIteration")>]
type OptionIterationCases() =
    [<Theory>]
    [<InlineData("Some 4<m>", "Option.iter (factory ()) (input ())", false)>]
    [<InlineData("None", "Option.iter (factory ()) (input ())", false)>]
    [<InlineData("Some 4<m>", "Option.iter (factory ()) <| input ()", false)>]
    [<InlineData("None", "input () |> Option.iter (factory ())", true)>]
    member _.``The action factory and option are eager with invocation confined to Some``(optionBody: string, expression: string, forward: bool) =
        let result = OptionIteration.check $"""
let mutable total: int<m> = 0<m>
let factory () = fun (value: int<m>) -> total <- value
let input () : int<m> option = {optionBody}
let observed = {expression}
[<EntryPoint>]
let main _ = observed; if total >= 0<m> then 0 else 1
"""
        let value = OptionIteration.value "observed" result
        let selection =
            if forward then
                match value.Kind with
                | SemanticKind.Sequential [input; call] ->
                    OptionIteration.assertCall "input" result input
                    match result.Graph.Nodes[call].Kind with
                    | SemanticKind.Sequential [_; reused; _] -> Assert.Equal(input, reused)
                    | kind -> failwithf "Piped iteration lost its shared input: %A" kind
                    result.Graph.Nodes[call]
                | kind -> failwithf "Forward pipe lost its prerequisite: %A" kind
            else value
        match selection.Kind with
        | SemanticKind.Sequential [action; input; choice] ->
            OptionIteration.assertCall "factory" result action
            OptionIteration.assertCall "input" result input
            OptionIteration.assertIteration result action input choice
        | kind -> failwithf "Iteration lost its eager operand prefix: %A" kind

    [<Fact>]
    member _.``Bare aliases stored fields and partials preserve fresh measured and unit payloads``() =
        let result = OptionIteration.check """
type Actions = { visit: (int<m> -> unit) -> int<m> option -> unit }
let run action value = action value
[<EntryPoint>]
let main _ =
    let visit = Option.iter
    let distance = visit (fun (_: int<m>) -> ()) (Some 2<m>)
    let elapsed = visit (fun (_: int<s>) -> ()) (Some 3<s>)
    let inverse = visit (fun (_: float<m^-1>) -> ()) (Some -0.25<m^-1>)
    let empty = visit (fun () -> ()) (Some ())
    let fields = { visit = Option.iter<int<m>> }
    let partial = fields.visit (fun (_: int<m>) -> ())
    let observed = run partial None
    distance; elapsed; inverse; empty; observed; 0
"""
        for name in ["distance"; "elapsed"; "inverse"; "empty"; "observed"] do
            DimensionalCases.same Types.unitType (DimensionalCases.bindingType name result)
        DimensionalCases.same (NativeType.TFun(OptionIteration.option (DimensionalCases.measuredInt DimensionalCases.metre), Types.unitType))
            (DimensionalCases.bindingType "partial" result)
        let aliases = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Binding (name, _, _, _) -> name.StartsWith("visit__mono") | _ -> false) |> Seq.toList
        Assert.Equal(4, aliases.Length)

    [<Fact>]
    member _.``Partial formation snapshots the action while retaining its shared mutable capture``() =
        let result = OptionIteration.check """
[<EntryPoint>]
let main _ =
    let mutable total: int<m> = 0<m>
    let mutable action: int<m> -> unit = fun value -> total <- value
    let stored = Option.iter action
    action <- fun value -> total <- value + 10<m>
    stored (Some 3<m>)
    if total = 3<m> then 0 else 1
"""
        let graph = result.Graph
        let action = OptionIteration.binding "action" result
        let total = OptionIteration.binding "total" result
        match (OptionIteration.value "stored" result).Kind with
        | SemanticKind.Sequential [snapshot; closure] ->
            match graph.Nodes[snapshot].Kind, graph.Nodes[graph.Nodes[snapshot].Children.Head].Kind with
            | SemanticKind.Binding (_, false, false, _), SemanticKind.VarRef (_, Some source) -> Assert.Equal(action.Id, source)
            | kinds -> failwithf "Action was not snapshotted at partial formation: %A" kinds
            match graph.Nodes[closure].Kind with
            | SemanticKind.Lambda (parameters, body, captures, _, _) ->
                Assert.Single parameters |> ignore
                let capture = Assert.Single captures
                Assert.Equal(Some snapshot, capture.SourceNodeId)
                Assert.False capture.IsMutable
                match graph.Nodes[body].Kind with
                | SemanticKind.IfThenElse (_, present, _) ->
                    match graph.Nodes[present].Kind with
                    | SemanticKind.Application (callee, [payload]) ->
                        match graph.Nodes[callee].Kind, graph.Nodes[payload].Kind with
                        | SemanticKind.VarRef (_, Some source), SemanticKind.DUEliminate (input, _, _, _) ->
                            Assert.Equal(snapshot, source)
                            OptionIteration.assertIteration result callee input body
                        | kinds -> failwithf "Residual invocation lost capture/payload identity: %A" kinds
                    | kind -> failwithf "Residual Some branch lost its invocation: %A" kind
                | kind -> failwithf "Partial lost conditional action: %A" kind
            | kind -> failwithf "Partial lost its closure: %A" kind
        | kind -> failwithf "Partial lost eager action formation: %A" kind
        Assert.Contains(graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Lambda (_, _, captures, _, _) -> captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some total.Id)
            | _ -> false)

    [<Theory>]
    [<InlineData("(int<m> -> int<m>)", "Some (fun (value: int<m>) -> value)")>]
    [<InlineData("int<m> option", "Some (Some 4<m>)")>]
    [<InlineData("unit", "Some ()")>]
    member _.``Nested function and unit payloads are passed as single action arguments``(payloadType: string, input: string) =
        let result = OptionIteration.check $"""
let action (_: {payloadType}) = ()
let observed = Option.iter action ({input})
[<EntryPoint>]
let main _ = observed; 0
"""
        match (OptionIteration.value "observed" result).Kind with
        | SemanticKind.Sequential [action; input; choice] -> OptionIteration.assertIteration result action input choice
        | kind -> failwithf "Payload was not retained until the action: %A" kind

    [<Fact>]
    member _.``Stored measured iteration retains its resident application obligation``() =
        let result = OptionIteration.check """
let stored = Option.iter (fun (_: int<m>) -> ())
let observed = stored (Some 4<m>)
[<EntryPoint>]
let main _ = observed; 0
"""
        let graph = result.Graph
        let site = OptionIteration.value "observed" result
        match site.Kind with
        | SemanticKind.Application (callee, arguments) ->
            let obligation = graph.Nodes.Values |> Seq.find (fun node ->
                node.Range = site.Range &&
                match node.Kind with SemanticKind.Obligation { Body = ObligationBody.ApplicationDimensions _ } -> true | _ -> false)
            let edge = graph.Edges |> List.find (fun edge -> edge.Target = obligation.Id)
            match graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (_, Some definition) ->
                Assert.Equal<Set<NodeId>>(Set.ofList (definition :: site.Id :: callee :: arguments), Set.ofList edge.Sources)
                for participant in edge.Sources do Assert.True(graph.Nodes.ContainsKey participant)
            | kind -> failwithf "Stored action lost its definition: %A" kind
        | kind -> failwithf "Expected stored iteration application: %A" kind

    [<Theory>]
    [<InlineData("module Option =\n    let iter (x: int<m>) = x + 1<m>\nlet value = Option.iter 2<m>")>]
    [<InlineData("type Surface = { iter: int<m> -> int<m> }\nlet Option = { iter = fun x -> x + 1<m> }\nlet value = Option.iter 2<m>")>]
    member _.``Lexical iteration definitions take precedence over library lookup``(source: string) =
        let result = OptionIteration.check (source + "\n[<EntryPoint>]\nlet main _ = ignore value; 0")
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) (DimensionalCases.bindingType "value" result)

    [<Theory>]
    [<InlineData("let wrong = «Option.iter (fun (_: int<m>) -> 1)» (Some 2<m>)", "CCS8003")>]
    [<InlineData("let wrong = «Option.iter (fun (_: int<m>) -> ()) (Some 2<s>)»", "CCS8040")>]
    [<InlineData("let visit = Option.iter (fun (_: int<m>) -> ())\nlet wrong = «visit (Some 2<s>)»", "CCS8040")>]
    [<InlineData("let visit = Option.iter\nlet wrong = «visit (fun (_: int<m>) -> ()) (Some 2<s>)»", "CCS8040")>]
    [<InlineData("let wrong = «Option.iter 1» None", "CCS8003")>]
    [<InlineData("let wrong = «Option.iter (Some 1)»", "CCS8003")>]
    [<InlineData("let wrong = «Option.iter (fun (_: int<m>) -> ()) 2<m>»", "CCS8003")>]
    [<InlineData("let wrong = «Option.iter (fun (_: int<m>) -> ()) None ()»", "CCS8003")>]
    [<InlineData("let wrong = «Option.iter<int<m>> (fun (_: int<s>) -> ())» None", "CCS8040")>]
    [<InlineData("let wrong = «Option.iter<int<m>, int<s>>»", "CCS8004")>]
    [<InlineData("let wrong = «Option.iter (fun (_: int<m> -> int<m>) -> ()) (Some (fun (x: int<s>) -> x))»", "CCS8040")>]
    [<InlineData("let wrong = «Option.iter (fun (_: int<m> option) -> ()) (Some (Some 1<s>))»", "CCS8040")>]
    member _.``Invalid callbacks payloads and aliases fail at their exact diagnostic spans``(source: string, code: string) =
        OptionIteration.reject code source

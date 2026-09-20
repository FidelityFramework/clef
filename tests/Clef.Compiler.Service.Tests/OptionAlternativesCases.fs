namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private OptionAlternatives =
    let option payload = NativeType.TApp(Types.optionTyCon, [payload])
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"

    let check source =
        let result =
            match parseAndCheck (prelude + source) "option-alternatives.clef" with
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
                info.Module = IntrinsicModule.Option && (info.Operation = "orElse" || info.Operation = "orElseWith")
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
        let file = "option-alternatives-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + span) }
        let source = prelude + markedBody.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Invalid alternative reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s from checking: %A" code errors

    let assertCall name (result: CheckResult) id =
        match result.Graph.Nodes[id].Kind with
        | SemanticKind.Application (callee, _) ->
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (actual, _) -> Assert.True(actual = name || actual.EndsWith("." + name), actual)
            | kind -> failwithf "Expected reference to %s: %A" name kind
        | kind -> failwithf "Expected call to %s: %A" name kind

    let assertSelection lazyFallback (result: CheckResult) fallback input choice =
        let graph = result.Graph
        match graph.Nodes[choice].Kind with
        | SemanticKind.IfThenElse (guard, present, Some absent) ->
            // Selecting Some retains the original option, without elimination or reconstruction.
            Assert.Equal(input, present)
            DimensionalCases.same graph.Nodes[input].Type graph.Nodes[choice].Type
            if lazyFallback then
                match graph.Nodes[absent].Kind with
                | SemanticKind.Application (callee, [argument]) ->
                    Assert.Equal(fallback, callee)
                    Assert.Equal(SemanticKind.Literal NativeLiteral.Unit, graph.Nodes[argument].Kind)
                    DimensionalCases.same graph.Nodes[input].Type graph.Nodes[absent].Type
                | kind -> failwithf "None did not invoke precisely the fallback with unit: %A" kind
            else Assert.Equal(fallback, absent)
            match graph.Nodes[guard].Kind with
            | SemanticKind.Application (_, [tag; expected]) ->
                match graph.Nodes[tag].Kind with
                | SemanticKind.DUGetTag (actual, carrier) ->
                    Assert.Equal(input, actual)
                    DimensionalCases.same graph.Nodes[input].Type carrier
                | kind -> failwithf "Guard lost the retained option identity: %A" kind
                match graph.Nodes[expected].Kind with
                | SemanticKind.Literal (NativeLiteral.Int (1L, _)) -> ()
                | kind -> failwithf "Guard did not select Some: %A" kind
            | kind -> failwithf "Expected a tag comparison: %A" kind
        | kind -> failwithf "Expected option selection: %A" kind

[<Trait("Category", "NTU"); Trait("Subcategory", "OptionAlternatives")>]
type OptionAlternativesCases() =
    [<Theory>]
    [<InlineData("orElse", "")>]
    [<InlineData("orElseWith", "fun () -> ")>]
    member _.``Fresh schemes preserve independently admitted payloads and dimensions``(operation: string, thunk: string) =
        let result = OptionAlternatives.check $"""
let distance = Option.{operation} ({thunk}Some 1<m>) (Some 2<m>)
let elapsed = Option.{operation} ({thunk}Some 3<s>) None
let enabled = Option.{operation} ({thunk}Some false) (Some true)
let explicit = Option.{operation}<int<m/s>> ({thunk}Some 2<m/s>) None
let inverse = Option.{operation} ({thunk}Some 1<m^-1>) (Some (2 / 1<m>))
let fractional = Option.{operation} ({thunk}Some -0.25<m^-1>) (Some (1.0 / 2.0<m>))
let root = Option.{operation} ({thunk}Some (Math.sqrt 4.0<m^2>)) (Some 2.0<m>)
let unitValue = Option.{operation} ({thunk}Some ()) None
[<EntryPoint>]
let main _ = ignore distance; ignore elapsed; ignore enabled; ignore explicit; ignore inverse; ignore fractional; ignore root; ignore unitValue; 0
"""
        let metre = DimensionalCases.metre
        for name, payload in
            [ "distance", DimensionalCases.measuredInt metre
              "elapsed", DimensionalCases.measuredInt DimensionalCases.second
              "enabled", Types.boolType
              "explicit", DimensionalCases.measuredInt (DimensionalCases.product(metre, DimensionalCases.power DimensionalCases.second -1I))
              "inverse", DimensionalCases.measuredInt (DimensionalCases.power metre -1I)
              "fractional", DimensionalCases.measured (DimensionalCases.power metre -1I)
              "root", DimensionalCases.measured metre
              "unitValue", Types.unitType ] do
            DimensionalCases.same (OptionAlternatives.option payload) (DimensionalCases.bindingType name result)

    [<Theory>]
    [<InlineData("orElse", "", false, "Some 4<m>")>]
    [<InlineData("orElse", "", false, "None")>]
    [<InlineData("orElseWith", "fun () -> ", true, "Some 4<m>")>]
    [<InlineData("orElseWith", "fun () -> ", true, "None")>]
    member _.``Both operands are eager and the branch retains exactly the selected option``(operation: string, thunk: string, lazyFallback: bool, optionBody: string) =
        let result = OptionAlternatives.check $"""
let factory () = {thunk}Some 7<m>
let input () : int<m> option = {optionBody}
let observed = Option.{operation} (factory ()) (input ())
[<EntryPoint>]
let main _ = if Option.isSome observed then 0 else 1
"""
        match (OptionAlternatives.value "observed" result).Kind with
        | SemanticKind.Sequential [fallback; input; choice] ->
            OptionAlternatives.assertCall "factory" result fallback
            OptionAlternatives.assertCall "input" result input
            OptionAlternatives.assertSelection lazyFallback result fallback input choice
            Assert.Equal(Some (MetadataValue.String ("Option." + operation)), result.Graph.Nodes[choice].Metadata.TryFind ElaborationMetadata.For)
        | kind -> failwithf "Alternative lost eager source operand order: %A" kind

    [<Theory>]
    [<InlineData("orElse", "", false, true)>]
    [<InlineData("orElseWith", "fun () -> ", true, true)>]
    [<InlineData("orElse", "", false, false)>]
    [<InlineData("orElseWith", "fun () -> ", true, false)>]
    member _.``Forward and backward pipes retain their source evaluation order``(operation: string, thunk: string, lazyFallback: bool, forward: bool) =
        let expression =
            if forward then $"input () |> Option.{operation} (factory ())"
            else $"Option.{operation} (factory ()) <| input ()"
        let result = OptionAlternatives.check $"""
let factory () = {thunk}Some 7<m>
let input () = Some 4<m>
let observed = {expression}
[<EntryPoint>]
let main _ = if Option.isSome observed then 0 else 1
"""
        let value = OptionAlternatives.value "observed" result
        let selection =
            if forward then
                match value.Kind with
                | SemanticKind.Sequential [input; call] ->
                    OptionAlternatives.assertCall "input" result input
                    match result.Graph.Nodes[call].Kind with
                    | SemanticKind.Sequential [_; reused; _] -> Assert.Equal(input, reused)
                    | kind -> failwithf "Piped alternative lost its shared input: %A" kind
                    result.Graph.Nodes[call]
                | kind -> failwithf "Forward pipe lost its prerequisite: %A" kind
            else value
        match selection.Kind with
        | SemanticKind.Sequential [fallback; input; choice] ->
            OptionAlternatives.assertCall "factory" result fallback
            OptionAlternatives.assertCall "input" result input
            OptionAlternatives.assertSelection lazyFallback result fallback input choice
        | kind -> failwithf "Alternative lost its argument prefix: %A" kind

    [<Theory>]
    [<InlineData("orElse", "int<m> option", "Some 3<m>", "Some 9<m>", false)>]
    [<InlineData("orElseWith", "unit -> int<m> option", "fun () -> Some 3<m>", "fun () -> Some 9<m>", true)>]
    member _.``Partial application snapshots the supplied value at formation``(operation: string, fallbackType: string, first: string, replacement: string, lazyFallback: bool) =
        let result = OptionAlternatives.check $"""
let mutable fallback: {fallbackType} = {first}
[<EntryPoint>]
let main _ =
    let stored = Option.{operation} fallback
    fallback <- {replacement}
    if Option.get (stored None) = 3<m> then 0 else 1
"""
        let graph = result.Graph
        let carrier = OptionAlternatives.option (DimensionalCases.measuredInt DimensionalCases.metre)
        DimensionalCases.same (NativeType.TFun(carrier, carrier)) (DimensionalCases.bindingType "stored" result)
        match (OptionAlternatives.value "stored" result).Kind with
        | SemanticKind.Sequential [snapshot; closure] ->
            match graph.Nodes[snapshot].Kind with
            | SemanticKind.Binding (_, false, false, _) -> ()
            | kind -> failwithf "Expected immutable formation snapshot: %A" kind
            let original = OptionAlternatives.binding "fallback" result
            match graph.Nodes[graph.Nodes[snapshot].Children.Head].Kind with
            | SemanticKind.VarRef (_, Some definition) -> Assert.Equal(original.Id, definition)
            | kind -> failwithf "Snapshot lost its mutable source: %A" kind
            match graph.Nodes[closure].Kind with
            | SemanticKind.Lambda (parameters, body, captures, _, _) ->
                let _, domain, _ = Assert.Single parameters
                DimensionalCases.same carrier domain
                let capture = Assert.Single captures
                Assert.Equal(Some snapshot, capture.SourceNodeId)
                Assert.False capture.IsMutable
                match graph.Nodes[body].Kind with
                | SemanticKind.IfThenElse (_, input, Some absent) ->
                    let fallback =
                        if lazyFallback then
                            match graph.Nodes[absent].Kind with
                            | SemanticKind.Application (callee, [_]) -> callee
                            | kind -> failwithf "Missing conditional thunk invocation: %A" kind
                        else absent
                    match graph.Nodes[fallback].Kind with
                    | SemanticKind.VarRef (_, Some definition) -> Assert.Equal(snapshot, definition)
                    | kind -> failwithf "Selection lost snapshot identity: %A" kind
                    OptionAlternatives.assertSelection lazyFallback result fallback input body
                | kind -> failwithf "Partial did not retain its guarded selection: %A" kind
            | kind -> failwithf "Partial did not become a closure: %A" kind
        | kind -> failwithf "Partial did not snapshot at formation: %A" kind

    [<Theory>]
    [<InlineData("orElse", "", "int<m> option")>]
    [<InlineData("orElseWith", "fun () -> ", "unit -> int<m> option")>]
    member _.``Bare aliases and stored function fields specialize independently``(operation: string, thunk: string, leadingType: string) =
        let result = OptionAlternatives.check $"""
let invoke f x = f x
type Alternatives = {{ choose: ({leadingType}) -> int<m> option -> int<m> option }}
[<EntryPoint>]
let main _ =
    let choose = Option.{operation}
    let distance = choose ({thunk}Some 3<m>) None
    let elapsed = choose ({thunk}Some 2<s>) (Some 4<s>)
    let enabled = choose ({thunk}Some false) (Some true)
    let surface = {{ choose = Option.{operation}<int<m>> }}
    let stored = surface.choose ({thunk}Some 8<m>)
    if Option.get distance = 3<m> && Option.get elapsed = 4<s> && Option.get enabled && Option.get (invoke stored None) = 8<m> then 0 else 1
"""
        let aliases = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (name, _, _, _) -> name.StartsWith("choose__mono")
            | _ -> false) |> Seq.toList
        Assert.Equal(3, aliases.Length)

    [<Theory>]
    [<InlineData("orElse", "")>]
    [<InlineData("orElseWith", "fun () -> ")>]
    member _.``Nested absence and function payloads remain inside their option layer``(operation: string, thunk: string) =
        let result = OptionAlternatives.check $"""
let stored = Option.{operation} ({thunk}Some (None: int<m> option))
let present = stored (Some (Some 4<m>))
let empty = stored (Some None)
let absent = stored None
let functionChoice = Option.{operation} ({thunk}Some (fun (x: int<m>) -> fun () -> x)) None
let functionStage = Option.get functionChoice 6<m>
let observed = functionStage ()
[<EntryPoint>]
let main _ = if Option.isSome present && Option.isSome empty && Option.isSome absent && observed = 6<m> then 0 else 1
"""
        let payload = DimensionalCases.measuredInt DimensionalCases.metre
        let nested = OptionAlternatives.option (OptionAlternatives.option payload)
        for name in ["present"; "empty"; "absent"] do DimensionalCases.same nested (DimensionalCases.bindingType name result)
        DimensionalCases.same (OptionAlternatives.option (NativeType.TFun(payload, NativeType.TFun(Types.unitType, payload))))
            (DimensionalCases.bindingType "functionChoice" result)
        DimensionalCases.same (NativeType.TFun(Types.unitType, payload)) (DimensionalCases.bindingType "functionStage" result)
        DimensionalCases.same payload (DimensionalCases.bindingType "observed" result)

    [<Fact>]
    member _.``Thunk snapshots preserve shared mutable capture identity``() =
        let result = OptionAlternatives.check """
[<EntryPoint>]
let main _ =
    let mutable seed: int<m> = 3<m>
    let stored = Option.orElseWith (fun () -> Some seed)
    seed <- 9<m>
    if Option.get (stored None) = 9<m> then 0 else 1
"""
        let seed = OptionAlternatives.binding "seed" result
        Assert.Contains(result.Graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Lambda (_, _, captures, _, _) ->
                captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some seed.Id)
            | _ -> false)

    [<Theory>]
    [<InlineData("orElse", "")>]
    [<InlineData("orElseWith", "fun () -> ")>]
    member _.``Stored alternatives retain resident measured application participants``(operation: string, thunk: string) =
        let result = OptionAlternatives.check $"""
let stored = Option.{operation} ({thunk}Some 3<m>)
let observed = stored (Some 4<m>)
[<EntryPoint>]
let main _ = if Option.isSome observed then 0 else 1
"""
        let graph = result.Graph
        let site = OptionAlternatives.value "observed" result
        match site.Kind with
        | SemanticKind.Application (callee, arguments) ->
            let obligation = graph.Nodes.Values |> Seq.find (fun node ->
                node.Range = site.Range &&
                match node.Kind with
                | SemanticKind.Obligation { Body = ObligationBody.ApplicationDimensions _ } -> true
                | _ -> false)
            let edge = graph.Edges |> List.find (fun edge -> edge.Target = obligation.Id)
            match graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (_, Some definition) ->
                Assert.Equal<Set<NodeId>>(Set.ofList (definition :: site.Id :: callee :: arguments), Set.ofList edge.Sources)
                for participant in edge.Sources do Assert.True(graph.Nodes.ContainsKey participant)
            | kind -> failwithf "Application lost its definition: %A" kind
        | kind -> failwithf "Expected a stored application: %A" kind

    [<Theory>]
    [<InlineData("module Option =\n    let orElse (x: int<m>) = x + 1<m>\nlet value = Option.orElse 2<m>")>]
    [<InlineData("type Surface = { orElseWith: int<m> -> int<m> }\nlet Option = { orElseWith = fun x -> x + 1<m> }\nlet value = Option.orElseWith 2<m>")>]
    member _.``Lexical modules and function fields keep precedence``(source: string) =
        let result = OptionAlternatives.check (source + "\n[<EntryPoint>]\nlet main _ = ignore value; 0")
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) (DimensionalCases.bindingType "value" result)

    [<Theory>]
    [<InlineData("let wrong = «Option.orElse (Some 1<m>) (Some 2<s>)»", "CCS8040")>]
    [<InlineData("let wrong = «Option.orElseWith (fun () -> Some 1<m>) (Some 2<s>)»", "CCS8040")>]
    [<InlineData("let choose = Option.orElse (Some 1<m>)\nlet wrong = «choose (Some 2<s>)»", "CCS8040")>]
    [<InlineData("let choose = Option.orElseWith (fun () -> Some 1<m>)\nlet wrong = «choose (Some 2<s>)»", "CCS8040")>]
    [<InlineData("let wrong = «Option.orElse (Some 1<m^-1>) (Some 2<s^-1>)»", "CCS8040")>]
    [<InlineData("let wrong = «Option.orElseWith (fun () -> Some (6<m> / 2<s>)) (Some (6<s> / 2<m>))»", "CCS8040")>]
    [<InlineData("let wrong = «Option.orElse (Some (None: int<m> option)) (Some (Some 2<s>))»", "CCS8040")>]
    [<InlineData("let wrong = «Option.orElseWith (fun () -> Some (fun (x: int<m>) -> x)) (Some (fun (x: int<s>) -> x))»", "CCS8040")>]
    [<InlineData("let wrong = «Option.orElse<int<m>> (Some 1<s>)» None", "CCS8040")>]
    [<InlineData("let wrong = «Option.orElseWith<int<m>> (fun () -> Some 1<s>)» None", "CCS8040")>]
    [<InlineData("let wrong = «Option.orElse 1<m>» None", "CCS8003")>]
    [<InlineData("let wrong = «Option.orElseWith (fun (_: int<m>) -> Some 1<m>)» None", "CCS8003")>]
    [<InlineData("let wrong = «Option.orElseWith (fun () -> 1<m>)» None", "CCS8003")>]
    [<InlineData("let wrong = «Option.orElse (Some 1<m>) 2<m>»", "CCS8003")>]
    [<InlineData("let wrong = «Option.orElseWith (fun () -> Some 1<m>) (Some 2.0<m>)»", "CCS8003")>]
    [<InlineData("let wrong = «Option.orElse (Some (fun (x: int<m>) -> x)) None 2<m>»", "CCS8003")>]
    [<InlineData("let wrong = «Option.orElseWith (fun () -> Some (fun (x: int<m>) -> x)) None 2<m>»", "CCS8003")>]
    [<InlineData("let wrong = «Option.orElse<int<m>, int<s>>»", "CCS8004")>]
    [<InlineData("let wrong = «Option.orElseWith<int<m>, int<s>>»", "CCS8004")>]
    [<InlineData("let wrong = Option.orElse<float<«m^(1/2)»>>", "CCS8048")>]
    [<InlineData("let wrong = Option.orElseWith<float<«m^(1/2)»>>", "CCS8048")>]
    [<InlineData("let wrong = Option.orElseWith (fun () -> Some («Math.sqrt 2.0<m>»)) None", "CCS8041")>]
    member _.``Invalid alternatives fail with exact diagnostic identity severity and location``(source: string, code: string) =
        OptionAlternatives.reject code source

namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private OptionDefaultWith =
    let option payload = NativeType.TApp(Types.optionTyCon, [payload])
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"

    let check source =
        let result =
            match parseAndCheck (prelude + source) "option-default-with.clef" with
            | Success result -> result
            | CheckFailure result -> failwithf "Expected successful checking: %A" result.Diagnostics
            | ParseFailure errors -> failwithf "Parse failed: %A" errors
        DimensionalCases.noErrors result
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Error _ -> true | _ -> false)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Intrinsic info -> info.Module = IntrinsicModule.Option && info.Operation = "defaultWith"
            | _ -> false)
        for node in result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) do
            for child in node.Children do
                Assert.True(result.Graph.Nodes.ContainsKey child, $"Dangling child {child} of {node.Id}")
        result

    /// Rejection is checked at the public pipeline boundary on reachable code,
    /// including the diagnostic identity and exact source range.
    let reject code (markedBody: string) =
        let start = markedBody.IndexOf('«')
        let finish = markedBody.IndexOf('»')
        Assert.True(start >= 0 && finish > start, "Expected one marked diagnostic span")
        let before = markedBody.Substring(0, start)
        let span = markedBody.Substring(start + 1, finish - start - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "option-default-with-negative.clef"
        let expected =
            { File = file
              Start = position (prelude + before)
              End = position (prelude + before + span) }
        let body = markedBody.Replace("«", "").Replace("»", "")
        let source = prelude + body + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostics = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
            let diagnostic = Assert.Single diagnostics
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Invalid defaultWith reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s from checking: %A" code errors

    let binding name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name)
            | _ -> false)

    let value name result = result.Graph.Nodes[(binding name result).Children.Head]

    let assertCall name (result: CheckResult) id =
        match result.Graph.Nodes[id].Kind with
        | SemanticKind.Application (callee, _) ->
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (actual, _) -> Assert.True(actual = name || actual.EndsWith("." + name), actual)
            | kind -> failwithf "Expected reference to %s, got %A" name kind
        | kind -> failwithf "Expected call to %s, got %A" name kind

    let assertSelection (result: CheckResult) fallback optionId choice =
        let graph = result.Graph
        match graph.Nodes[choice].Kind with
        | SemanticKind.IfThenElse (guard, present, Some absent) ->
            match graph.Nodes[present].Kind with
            | SemanticKind.DUEliminate (input, 1, "Some", payloadType) ->
                Assert.Equal(optionId, input)
                DimensionalCases.same payloadType graph.Nodes[choice].Type
            | kind -> failwithf "Some branch lost its guarded extraction: %A" kind
            match graph.Nodes[absent].Kind with
            | SemanticKind.Application (callee, [argument]) ->
                Assert.Equal(fallback, callee)
                Assert.Equal(SemanticKind.Literal NativeLiteral.Unit, graph.Nodes[argument].Kind)
                DimensionalCases.same graph.Nodes[choice].Type graph.Nodes[absent].Type
            | kind -> failwithf "None branch lost its sole unit invocation: %A" kind
            match graph.Nodes[guard].Kind with
            | SemanticKind.Application (_, [tag; expected]) ->
                match graph.Nodes[tag].Kind with
                | SemanticKind.DUGetTag (input, _) -> Assert.Equal(optionId, input)
                | kind -> failwithf "Guard did not inspect the same option: %A" kind
                match graph.Nodes[expected].Kind with
                | SemanticKind.Literal (NativeLiteral.Int (1L, _)) -> ()
                | kind -> failwithf "Guard did not select Some: %A" kind
            | kind -> failwithf "Option guard is not a case comparison: %A" kind
        | kind -> failwithf "Expected a guarded defaultWith selection, got %A" kind

[<Trait("Category", "NTU"); Trait("Subcategory", "OptionDefaultWith")>]
type OptionDefaultWithCases() =
    [<Fact>]
    member _.``Defaults preserve payload dimensions and independently instantiate the thunk scheme``() =
        let result = OptionDefaultWith.check """
let present = Option.defaultWith (fun () -> 1<m>) (Some 12<m>)
let absent = Option.defaultWith (fun () -> 3<s>) None
let enabled = Option.defaultWith (fun () -> false) (Some true)
let explicit = Option.defaultWith<int<m/s>> (fun () -> 2<m/s>) None
let inverse = Option.defaultWith (fun () -> 1<m^-1>) (Some (2 / 1<m>))
let fractional = Option.defaultWith (fun () -> -0.25<m^-1>) (Some (1.0 / 2.0<m>))
let root = Option.defaultWith (fun () -> Math.sqrt 4.0<m^2>) (Some 2.0<m>)
[<EntryPoint>]
let main _ = ignore present; ignore absent; ignore enabled; ignore explicit; ignore inverse; ignore fractional; ignore root; 0
"""
        let metre = DimensionalCases.metre
        DimensionalCases.same (DimensionalCases.measuredInt metre) (DimensionalCases.bindingType "present" result)
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.second) (DimensionalCases.bindingType "absent" result)
        DimensionalCases.same Types.boolType (DimensionalCases.bindingType "enabled" result)
        DimensionalCases.same (DimensionalCases.measuredInt (DimensionalCases.product(metre, DimensionalCases.power DimensionalCases.second -1I)))
            (DimensionalCases.bindingType "explicit" result)
        DimensionalCases.same (DimensionalCases.measuredInt (DimensionalCases.power metre -1I)) (DimensionalCases.bindingType "inverse" result)
        DimensionalCases.same (DimensionalCases.measured (DimensionalCases.power metre -1I)) (DimensionalCases.bindingType "fractional" result)
        DimensionalCases.same (DimensionalCases.measured metre) (DimensionalCases.bindingType "root" result)

    [<Theory>]
    [<InlineData("let wrong = «Option.defaultWith (fun () -> 1<m>) (Some 2<s>)»", "CCS8040")>]
    [<InlineData("let choose = Option.defaultWith (fun () -> 1<m>)\nlet wrong = «choose (Some 2<s>)»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultWith (fun () -> 1<m^-1>) (Some 2<s^-1>)»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultWith (fun () -> 6<m> / 2<s>) (Some (6<s> / 2<m>))»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultWith (fun () -> (None: int<m> option)) (Some (Some 2<s>))»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultWith (fun () -> fun (x: int<m>) -> x) (Some (fun (x: int<s>) -> x))»", "CCS8040")>]
    [<InlineData("let choose = Option.defaultWith (fun () -> fun (x: int<m>) -> x)\nlet wrong = «choose None 2<s>»", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultWith<int<m>> (fun () -> 1<s>)» None", "CCS8040")>]
    [<InlineData("let wrong = «Option.defaultWith (fun (_: int<m>) -> 1<m>)» None", "CCS8003")>]
    [<InlineData("let wrong = «Option.defaultWith 1<m>» None", "CCS8003")>]
    [<InlineData("let wrong = «Option.defaultWith (fun () -> 1<m>) 2<m>»", "CCS8003")>]
    [<InlineData("let wrong = «Option.defaultWith (fun () -> 1<m>) (Some 2.0<m>)»", "CCS8003")>]
    [<InlineData("let wrong = «Option.defaultWith (fun () -> 1<m>) None 2<m>»", "CCS8003")>]
    [<InlineData("let wrong = «Option.defaultWith<int<m>, int<s>>»", "CCS8004")>]
    [<InlineData("let wrong = Option.defaultWith<float<«m^(1/2)»>>", "CCS8048")>]
    [<InlineData("let wrong = Option.defaultWith (fun () -> «Math.sqrt 2.0<m>») None", "CCS8041")>]
    member _.``Invalid thunk and payload contracts are rejected before a successful graph``(source: string, code: string) =
        OptionDefaultWith.reject code source

    [<Theory>]
    [<InlineData("module Option =\n    let defaultWith (x: int<m>) = x + 1<m>\nlet value = Option.defaultWith 2<m>")>]
    [<InlineData("type Surface = { defaultWith: int<m> -> int<m> }\nlet Option = { defaultWith = fun x -> x + 1<m> }\nlet value = Option.defaultWith 2<m>")>]
    member _.``Lexical modules and function fields retain precedence``(source: string) =
        let result = OptionDefaultWith.check (source + "\n[<EntryPoint>]\nlet main _ = ignore value; 0")
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) (DimensionalCases.bindingType "value" result)

    [<Theory>]
    [<InlineData("Some 4<m>")>]
    [<InlineData("None")>]
    member _.``Factory and option are eager while the thunk call belongs only to None``(optionBody: string) =
        let result = OptionDefaultWith.check $"""
let factory () = fun () -> 7<m>
let input () : int<m> option = {optionBody}
let observed = Option.defaultWith (factory ()) (input ())
[<EntryPoint>]
let main _ = if observed > 0<m> then 0 else 1
"""
        match (OptionDefaultWith.value "observed" result).Kind with
        | SemanticKind.Sequential [fallback; input; choice] ->
            OptionDefaultWith.assertCall "factory" result fallback
            OptionDefaultWith.assertCall "input" result input
            OptionDefaultWith.assertSelection result fallback input choice
            Assert.Equal(Some (MetadataValue.String "Option.defaultWith"),
                result.Graph.Nodes[choice].Metadata.TryFind ElaborationMetadata.For)
        | kind -> failwithf "DefaultWith lost eager argument order: %A" kind

    [<Theory>]
    [<InlineData("Some ()")>]
    [<InlineData("None")>]
    member _.``Unit payloads retain their selection and conditional unit invocation``(optionBody: string) =
        let result = OptionDefaultWith.check $"""
let mutable calls: int = 0
let factory () = fun () -> calls <- calls + 1
let input () : unit option = {optionBody}
let observed = Option.defaultWith (factory ()) (input ())
[<EntryPoint>]
let main _ = observed; if calls >= 0 then 0 else 1
"""
        DimensionalCases.same Types.unitType (DimensionalCases.bindingType "observed" result)
        match (OptionDefaultWith.value "observed" result).Kind with
        | SemanticKind.Sequential [fallback; input; choice] ->
            OptionDefaultWith.assertCall "factory" result fallback
            OptionDefaultWith.assertCall "input" result input
            OptionDefaultWith.assertSelection result fallback input choice
            DimensionalCases.same Types.unitType result.Graph.Nodes[choice].Type
            DimensionalCases.same (OptionDefaultWith.option Types.unitType) result.Graph.Nodes[input].Type
        | kind -> failwithf "Unit payload selection was erased or reordered: %A" kind

    [<Theory>]
    [<InlineData("Some (1.0 / 2.0<m>)")>]
    [<InlineData("None")>]
    member _.``Measured real defaults retain exact fractional values without integer range facts``(optionBody: string) =
        let result = OptionDefaultWith.check $"""
let factory () = fun () -> -0.25<m^-1>
let input () : float<m^-1> option = {optionBody}
let observed = Option.defaultWith (factory ()) (input ())
[<EntryPoint>]
let main _ = if observed >= -0.25<m^-1> then 0 else 1
"""
        let payload = DimensionalCases.measured (DimensionalCases.power DimensionalCases.metre -1I)
        DimensionalCases.same payload (DimensionalCases.bindingType "observed" result)
        match (OptionDefaultWith.value "observed" result).Kind with
        | SemanticKind.Sequential [fallback; input; choice] ->
            OptionDefaultWith.assertSelection result fallback input choice
            DimensionalCases.same payload result.Graph.Nodes[choice].Type
            DimensionalCases.same (OptionDefaultWith.option payload) result.Graph.Nodes[input].Type
        | kind -> failwithf "Measured real selection lost its payload: %A" kind
        let literals = result.Graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Metadata.TryFind "Numeric.RealLiteral" with
            | Some (MetadataValue.RealLiteral ("-0.25", value)) -> Some (node, value)
            | _ -> None) |> Seq.toList
        Assert.NotEmpty literals
        for literal, value in literals do
            Assert.Equal(-1I, value.Numerator)
            Assert.Equal(4I, value.Denominator)
            Assert.True(literal.ValueRange.IsNone)
            DimensionalCases.same payload literal.Type

    [<Fact>]
    member _.``Forward pipe evaluates its option before constructing the fallback thunk``() =
        let result = OptionDefaultWith.check """
let factory () = fun () -> 7<m>
let input () = Some 4<m>
let observed = input () |> Option.defaultWith (factory ())
[<EntryPoint>]
let main _ = if observed > 0<m> then 0 else 1
"""
        match (OptionDefaultWith.value "observed" result).Kind with
        | SemanticKind.Sequential [input; call] ->
            OptionDefaultWith.assertCall "input" result input
            match result.Graph.Nodes[call].Kind with
            | SemanticKind.Sequential [fallback; reusedInput; choice] ->
                Assert.Equal(input, reusedInput)
                OptionDefaultWith.assertCall "factory" result fallback
                OptionDefaultWith.assertSelection result fallback input choice
            | kind -> failwithf "Piped default lost its thunk selection: %A" kind
        | kind -> failwithf "Forward pipe lost its input prerequisite: %A" kind

    [<Fact>]
    member _.``Partial formation snapshots the thunk value without invoking it``() =
        let result = OptionDefaultWith.check """
let mutable fallback: unit -> int<m> = fun () -> 3<m>
[<EntryPoint>]
let main _ =
    let stored = Option.defaultWith fallback
    fallback <- fun () -> 9<m>
    if stored None = 3<m> then 0 else 1
"""
        let graph = result.Graph
        let payload = DimensionalCases.measuredInt DimensionalCases.metre
        DimensionalCases.same (NativeType.TFun(OptionDefaultWith.option payload, payload))
            (DimensionalCases.bindingType "stored" result)
        match (OptionDefaultWith.value "stored" result).Kind with
        | SemanticKind.Sequential [snapshot; closure] ->
            match graph.Nodes[snapshot].Kind with
            | SemanticKind.Binding (_, false, false, _) -> ()
            | kind -> failwithf "Partial did not snapshot its thunk: %A" kind
            Assert.NotEqual((OptionDefaultWith.binding "fallback" result).Id, snapshot)
            DimensionalCases.same (NativeType.TFun(Types.unitType, payload)) graph.Nodes[snapshot].Type
            match graph.Nodes[closure].Kind with
            | SemanticKind.Lambda (parameters, body, captures, _, _) ->
                let _, domain, _ = Assert.Single parameters
                DimensionalCases.same (OptionDefaultWith.option payload) domain
                let capture = Assert.Single captures
                Assert.Equal(Some snapshot, capture.SourceNodeId)
                Assert.False capture.IsMutable
                match graph.Nodes[body].Kind with
                | SemanticKind.IfThenElse (_, _, Some absent) ->
                    match graph.Nodes[absent].Kind with
                    | SemanticKind.Application (callee, [_]) ->
                        match graph.Nodes[callee].Kind with
                        | SemanticKind.VarRef (_, Some source) -> Assert.Equal(snapshot, source)
                        | kind -> failwithf "Invocation lost the captured thunk identity: %A" kind
                    | kind -> failwithf "Residual None branch is not an invocation: %A" kind
                | kind -> failwithf "Residual is not an option selection: %A" kind
            | kind -> failwithf "Partial did not become a closure: %A" kind
        | kind -> failwithf "Partial did not evaluate its thunk at formation: %A" kind

    [<Fact>]
    member _.``Thunk snapshots preserve referenced mutable captures``() =
        let result = OptionDefaultWith.check """
[<EntryPoint>]
let main _ =
    let mutable seed: int<m> = 3<m>
    let stored = Option.defaultWith (fun () -> seed)
    seed <- 9<m>
    if stored None = 9<m> && stored (Some 4<m>) = 4<m> then 0 else 1
"""
        let seed = OptionDefaultWith.binding "seed" result
        Assert.Contains(result.Graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Lambda (_, _, captures, _, _) ->
                captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some seed.Id)
            | _ -> false)

    [<Fact>]
    member _.``Bare aliases and stored fields retain independently specialized composition``() =
        let result = OptionDefaultWith.check """
let invoke f x = f x
type Defaults = { choose: (unit -> int<m>) -> int<m> option -> int<m> }
[<EntryPoint>]
let main _ =
    let choose = Option.defaultWith
    let distance = choose (fun () -> 3<m>) None
    let elapsed = choose (fun () -> 2<s>) (Some 4<s>)
    let enabled = choose (fun () -> false) (Some true)
    let surface = { choose = Option.defaultWith<int<m>> }
    let stored = surface.choose (fun () -> 8<m>)
    if distance = 3<m> && elapsed = 4<s> && enabled && invoke stored None = 8<m> then 0 else 1
"""
        let aliases = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (name, _, _, _) -> name.StartsWith("choose__mono")
            | _ -> false) |> Seq.toList
        Assert.Equal(3, aliases.Length)

    [<Fact>]
    member _.``Nested options preserve both absence levels``() =
        let result = OptionDefaultWith.check """
let stored = Option.defaultWith (fun () -> (None: int<m> option))
let present = stored (Some (Some 4<m>))
let empty = stored (Some None)
let absent = stored None
[<EntryPoint>]
let main _ = if Option.isSome present && Option.isNone empty && Option.isNone absent then 0 else 1
"""
        let payload = OptionDefaultWith.option (DimensionalCases.measuredInt DimensionalCases.metre)
        DimensionalCases.same (NativeType.TFun(OptionDefaultWith.option payload, payload))
            (DimensionalCases.bindingType "stored" result)
        for name in ["present"; "empty"; "absent"] do
            DimensionalCases.same payload (DimensionalCases.bindingType name result)

    [<Fact>]
    member _.``Function payloads preserve the two argument boundary in every callable form``() =
        let result = OptionDefaultWith.check """
let fallback () = fun (distance: int<m>) -> distance + 1<m>
let direct = Option.defaultWith fallback (Some (fun distance -> distance + 2<m>)) 3<m>
let explicit = Option.defaultWith<(int<m> -> int<m>)> fallback None 3<m>
let stored = Option.defaultWith fallback
let partial = stored None 4<m>
let bare = Option.defaultWith<(int<m> -> int<m>)>
let throughBare = bare fallback None 5<m>
let staged = Option.defaultWith (fun () -> fun (x: int<m>) -> fun () -> x) None 6<m> ()
[<EntryPoint>]
let main _ = if direct = 5<m> && explicit = 4<m> && partial = 5<m> && throughBare = 6<m> && staged = 6<m> then 0 else 1
"""
        let payload = DimensionalCases.measuredInt DimensionalCases.metre
        for name in ["direct"; "explicit"; "partial"; "throughBare"; "staged"] do
            DimensionalCases.same payload (DimensionalCases.bindingType name result)

    [<Fact>]
    member _.``A thunk returning successive functions preserves each stored invocation boundary``() =
        let result = OptionDefaultWith.check """
let mutable trace: int = 0
let fallback () =
    trace <- trace * 10 + 1
    fun (distance: int<m>) ->
        trace <- trace * 10 + 2
        fun (elapsed: int<s>) ->
            trace <- trace * 10 + 3
            distance / elapsed
let chosen = Option.defaultWith fallback None
let withDistance = chosen 6<m>
let observed = withDistance 2<s>
[<EntryPoint>]
let main _ = if observed = 3<m/s> && trace = 123 then 0 else 1
"""
        let metre = DimensionalCases.measuredInt DimensionalCases.metre
        let second = DimensionalCases.measuredInt DimensionalCases.second
        let speed = DimensionalCases.measuredInt
                        (DimensionalCases.product(DimensionalCases.metre, DimensionalCases.power DimensionalCases.second -1I))
        let residual = NativeType.TFun(second, speed)
        let payload = NativeType.TFun(metre, residual)
        DimensionalCases.same payload (DimensionalCases.bindingType "chosen" result)
        DimensionalCases.same residual (DimensionalCases.bindingType "withDistance" result)
        DimensionalCases.same speed (DimensionalCases.bindingType "observed" result)
        match (OptionDefaultWith.value "chosen" result).Kind with
        | SemanticKind.Sequential [fallback; input; choice] ->
            OptionDefaultWith.assertSelection result fallback input choice
            DimensionalCases.same payload result.Graph.Nodes[choice].Type
        | kind -> failwithf "Thunk selection consumed a returned function argument: %A" kind
        for callName, calleeName, argumentType in ["withDistance", "chosen", metre; "observed", "withDistance", second] do
            let call = OptionDefaultWith.value callName result
            match call.Kind with
            | SemanticKind.Application (callee, [argument]) ->
                DimensionalCases.same argumentType result.Graph.Nodes[argument].Type
                match result.Graph.Nodes[callee].Kind with
                | SemanticKind.VarRef (_, Some definition) ->
                    Assert.Equal((OptionDefaultWith.binding calleeName result).Id, definition)
                | kind -> failwithf "A stored stage lost its producing binding: %A" kind
            | kind -> failwithf "A stored function result lost its own invocation: %A" kind

    [<Theory>]
    [<InlineData("None")>]
    [<InlineData("Some (fun x -> x + 2<m>)")>]
    member _.``All supplied operands precede elimination and any fallback invocation``(optionBody: string) =
        let result = OptionDefaultWith.check $"""
let factory () = fun () -> fun (x: int<m>) -> x + 1<m>
let input () : (int<m> -> int<m>) option = {optionBody}
let argument () = 3<m>
let observed = Option.defaultWith (factory ()) (input ()) (argument ())
[<EntryPoint>]
let main _ = if observed > 0<m> then 0 else 1
"""
        match (OptionDefaultWith.value "observed" result).Kind with
        | SemanticKind.Sequential [fallback; input; suppliedArgument; call] ->
            OptionDefaultWith.assertCall "factory" result fallback
            OptionDefaultWith.assertCall "input" result input
            OptionDefaultWith.assertCall "argument" result suppliedArgument
            match result.Graph.Nodes[call].Kind with
            | SemanticKind.Application (choice, [argument]) ->
                Assert.Equal(suppliedArgument, argument)
                OptionDefaultWith.assertSelection result fallback input choice
                Assert.Equal<NodeId list>([choice; argument], result.Graph.Nodes[call].Children)
            | kind -> failwithf "Overapplication lost its selected function: %A" kind
        | kind -> failwithf "Application lost its eager supplied-operand prefix: %A" kind

    [<Fact>]
    member _.``Stored measured applications retain ordinary participant obligations``() =
        let result = OptionDefaultWith.check """
let stored = Option.defaultWith (fun () -> 3<m>)
let observed = stored (Some 4<m>)
[<EntryPoint>]
let main _ = if observed = 4<m> then 0 else 1
"""
        let graph = result.Graph
        let site = OptionDefaultWith.value "observed" result
        match site.Kind with
        | SemanticKind.Application (callee, arguments) ->
            let obligation = graph.Nodes.Values |> Seq.find (fun node ->
                node.Range = site.Range &&
                match node.Kind with
                | SemanticKind.Obligation { Body = ObligationBody.ApplicationDimensions _ } -> true
                | _ -> false)
            let edge = graph.Edges |> List.find (fun edge -> edge.Target = obligation.Id)
            for participant in site.Id :: callee :: arguments do
                Assert.Contains(participant, edge.Sources)
            match graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (_, Some definition) ->
                Assert.Equal<Set<NodeId>>(Set.ofList (definition :: site.Id :: callee :: arguments), Set.ofList edge.Sources)
                for participant in edge.Sources do Assert.True(graph.Nodes.ContainsKey participant)
            | kind -> failwithf "Stored application lost its definition: %A" kind
        | kind -> failwithf "Expected a stored function application, got %A" kind

namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private OptionFolds =
    let option payload = NativeType.TApp(Types.optionTyCon, [payload])
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"

    let check source =
        let result =
            match parseAndCheck (prelude + source) "option-folds.clef" with
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
                info.Module = IntrinsicModule.Option && (info.Operation = "fold" || info.Operation = "foldBack")
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
        let file = "option-folds-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + span) }
        let source = prelude + markedBody.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Invalid fold reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s from checking: %A" code errors

    let assertCall name (result: CheckResult) id =
        match result.Graph.Nodes[id].Kind with
        | SemanticKind.Application (callee, _) ->
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (actual, _) -> Assert.True(actual = name || actual.EndsWith("." + name), actual)
            | kind -> failwithf "Expected reference to %s: %A" name kind
        | kind -> failwithf "Expected call to %s: %A" name kind

    let assertFold operation (result: CheckResult) folder state input choice =
        let graph = result.Graph
        DimensionalCases.same graph.Nodes[state].Type graph.Nodes[choice].Type
        match graph.Nodes[choice].Kind with
        | SemanticKind.IfThenElse (guard, present, Some absent) ->
            Assert.Equal(state, absent)
            match graph.Nodes[present].Kind with
            | SemanticKind.Application (callee, arguments) ->
                Assert.Equal(folder, callee)
                Assert.Equal(2, arguments.Length)
                let stateArg, payload = if operation = "fold" then arguments[0], arguments[1] else arguments[1], arguments[0]
                Assert.Equal(state, stateArg)
                DimensionalCases.same graph.Nodes[state].Type graph.Nodes[present].Type
                match graph.Nodes[payload].Kind with
                | SemanticKind.DUEliminate (original, 1, "Some", payloadType) ->
                    Assert.Equal(input, original)
                    DimensionalCases.same payloadType graph.Nodes[payload].Type
                    DimensionalCases.same (option payloadType) graph.Nodes[input].Type
                | kind -> failwithf "Fold lost its guarded payload: %A" kind
            | kind -> failwithf "Some did not invoke the folder: %A" kind
            match graph.Nodes[guard].Kind with
            | SemanticKind.Application (_, [tag; expected]) ->
                match graph.Nodes[tag].Kind with
                | SemanticKind.DUGetTag (original, _) -> Assert.Equal(input, original)
                | kind -> failwithf "Guard lost input identity: %A" kind
                match graph.Nodes[expected].Kind with
                | SemanticKind.Literal (NativeLiteral.Int (1L, _)) -> ()
                | kind -> failwithf "Guard did not select Some: %A" kind
            | kind -> failwithf "Expected tag comparison: %A" kind
        | kind -> failwithf "Expected guarded fold: %A" kind

    let call operation folder state input =
        if operation = "fold" then $"Option.fold ({folder}) ({state}) ({input})"
        else $"Option.foldBack ({folder}) ({input}) ({state})"

    let folder operation state payload body =
        if operation = "fold" then $"fun {state} {payload} -> {body}"
        else $"fun {payload} {state} -> {body}"

[<Trait("Category", "NTU"); Trait("Subcategory", "OptionFolds")>]
type OptionFoldCases() =
    [<Theory>]
    [<InlineData("fold", "Some 2<s>")>]
    [<InlineData("fold", "None")>]
    [<InlineData("foldBack", "Some 2<s>")>]
    [<InlineData("foldBack", "None")>]
    member _.``Every operand is eager and the folder consumes independent state and payload types only for Some``(operation: string, input: string) =
        let folder = OptionFolds.folder operation "(state: int<m>)" "(_: int<s>)" "state + 1<m>"
        let expression = OptionFolds.call operation "factory ()" "initial ()" "input ()"
        let result = OptionFolds.check $"""
let factory () = {folder}
let initial () = 3<m>
let input () : int<s> option = {input}
let observed = {expression}
[<EntryPoint>]
let main _ = if observed >= 3<m> then 0 else 1
"""
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) (DimensionalCases.bindingType "observed" result)
        match (OptionFolds.value "observed" result).Kind with
        | SemanticKind.Sequential [folder; second; third; choice] ->
            let state, input = if operation = "fold" then second, third else third, second
            OptionFolds.assertCall "factory" result folder
            OptionFolds.assertCall "initial" result state
            OptionFolds.assertCall "input" result input
            OptionFolds.assertFold operation result folder state input choice
        | kind -> failwithf "Fold lost its three eager inputs: %A" kind

    [<Theory>]
    [<InlineData("fold", true)>]
    [<InlineData("foldBack", true)>]
    [<InlineData("fold", false)>]
    [<InlineData("foldBack", false)>]
    member _.``Pipes preserve their written evaluation order across the three argument boundary``(operation: string, forward: bool) =
        let folder = OptionFolds.folder operation "(state: int<m>)" "(_: int<s>)" "state"
        let expression =
            match operation, forward with
            | "fold", true -> "input () |> Option.fold (factory ()) (initial ())"
            | "foldBack", true -> "initial () |> Option.foldBack (factory ()) (input ())"
            | "fold", false -> "Option.fold (factory ()) (initial ()) <| input ()"
            | _ -> "Option.foldBack (factory ()) (input ()) <| initial ()"
        let result = OptionFolds.check $"""
let factory () = {folder}
let initial () = 3<m>
let input () = Some 2<s>
let observed = {expression}
[<EntryPoint>]
let main _ = if observed = 3<m> then 0 else 1
"""
        let value = OptionFolds.value "observed" result
        let selection =
            if forward then
                match value.Kind with
                | SemanticKind.Sequential [first; call] ->
                    OptionFolds.assertCall (if operation = "fold" then "input" else "initial") result first
                    match result.Graph.Nodes[call].Kind with
                    | SemanticKind.Sequential [_; _; reused; _] -> Assert.Equal(first, reused)
                    | kind -> failwithf "Pipe lost operand identity: %A" kind
                    result.Graph.Nodes[call]
                | kind -> failwithf "Forward pipe lost its prerequisite: %A" kind
            else value
        match selection.Kind with
        | SemanticKind.Sequential [folder; second; third; choice] ->
            let state, input = if operation = "fold" then second, third else third, second
            OptionFolds.assertFold operation result folder state input choice
        | kind -> failwithf "Piped fold lost its ordered prefix: %A" kind

    [<Theory>]
    [<InlineData("fold")>]
    [<InlineData("foldBack")>]
    member _.``Both partial frontiers snapshot supplied values and retain shared captured storage``(operation: string) =
        let folder = OptionFolds.folder operation "(state: int<m>)" "(value: int<s>)" "calls <- calls + 1; state"
        let secondType, first, replacement, last =
            if operation = "fold" then "int<m>", "3<m>", "9<m>", "Some 2<s>"
            else "int<s> option", "Some 2<s>", "None", "3<m>"
        let result = OptionFolds.check $"""
[<EntryPoint>]
let main _ =
    let mutable calls: int = 0
    let mutable callback = {folder}
    let mutable supplied: {secondType} = {first}
    let firstFrontier = Option.{operation} callback
    let secondFrontier = Option.{operation} callback supplied
    callback <- {OptionFolds.folder operation "(state: int<m>)" "(_: int<s>)" "state + 10<m>"}
    supplied <- {replacement}
    let observed = secondFrontier ({last})
    ignore firstFrontier
    if observed = 3<m> && calls = 1 then 0 else 1
"""
        let graph = result.Graph
        let callback = OptionFolds.binding "callback" result
        let supplied = OptionFolds.binding "supplied" result
        for name, definitions in ["firstFrontier", [callback.Id]; "secondFrontier", [callback.Id; supplied.Id]] do
            match (OptionFolds.value name result).Kind with
            | SemanticKind.Sequential items ->
                let closure, snapshots = List.last items, items |> List.take (items.Length - 1)
                Assert.Equal(definitions.Length, snapshots.Length)
                List.iter2 (fun snapshot definition ->
                    match graph.Nodes[snapshot].Kind, graph.Nodes[graph.Nodes[snapshot].Children.Head].Kind with
                    | SemanticKind.Binding (_, false, false, _), SemanticKind.VarRef (_, Some original) -> Assert.Equal(definition, original)
                    | kinds -> failwithf "Partial formation lost its immutable value snapshot: %A" kinds) snapshots definitions
                match graph.Nodes[closure].Kind with
                | SemanticKind.Lambda (parameters, _, captures, _, _) ->
                    Assert.Single parameters |> ignore
                    Assert.Equal<NodeId list>(snapshots, captures |> List.choose (fun c -> c.SourceNodeId))
                    for capture in captures do Assert.False capture.IsMutable
                | kind -> failwithf "A partial frontier lost its residual closure: %A" kind
            | kind -> failwithf "A partial frontier lost its formation sequence: %A" kind
        let calls = OptionFolds.binding "calls" result
        Assert.Contains(graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Lambda (_, _, captures, _, _) -> captures |> List.exists (fun c -> c.IsMutable && c.SourceNodeId = Some calls.Id)
            | _ -> false)

    [<Theory>]
    [<InlineData("fold")>]
    [<InlineData("foldBack")>]
    member _.``Bare aliases fields and staged applications instantiate state and payload independently``(operation: string) =
        let firstFolder = OptionFolds.folder operation "(state: int<m>)" "(_: int<s>)" "state"
        let secondFolder = OptionFolds.folder operation "(state: float<s^-1>)" "(_: bool)" "state"
        let first = if operation = "fold" then $"choose ({firstFolder}) 3<m> (Some 2<s>)" else $"choose ({firstFolder}) (Some 2<s>) 3<m>"
        let second = if operation = "fold" then $"choose ({secondFolder}) -0.25<s^-1> (Some true)" else $"choose ({secondFolder}) (Some true) -0.25<s^-1>"
        let tailType = if operation = "fold" then "int<m> -> int<s> option -> int<m>" else "int<s> option -> int<m> -> int<m>"
        let partial = if operation = "fold" then "withFolder 3<m>" else "withFolder (Some 2<s>)"
        let final = if operation = "fold" then "withSecond None" else "withSecond 3<m>"
        let result = OptionFolds.check $"""
type Surface = {{ choose: ({if operation = "fold" then "int<m> -> int<s> -> int<m>" else "int<s> -> int<m> -> int<m>"}) -> {tailType} }}
[<EntryPoint>]
let main _ =
    let choose = Option.{operation}
    let distance = {first}
    let inverseTime = {second}
    let surface = {{ choose = Option.{operation}<int<m>, int<s>> }}
    let withFolder = surface.choose ({firstFolder})
    let withSecond = {partial}
    let staged = {final}
    if distance = 3<m> && inverseTime = -0.25<s^-1> && staged = 3<m> then 0 else 1
"""
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) (DimensionalCases.bindingType "distance" result)
        DimensionalCases.same (DimensionalCases.measured (DimensionalCases.power DimensionalCases.second -1I)) (DimensionalCases.bindingType "inverseTime" result)
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) (DimensionalCases.bindingType "staged" result)

    [<Theory>]
    [<InlineData("fold", true)>]
    [<InlineData("foldBack", true)>]
    [<InlineData("fold", false)>]
    [<InlineData("foldBack", false)>]
    member _.``Completed residual operands precede both branches and retain local capture and formal identities``(operation: string, bare: bool) =
        let folder = OptionFolds.folder operation "(state: int<m>)" "(_: int<s>)" "state"
        let formation, present, absent =
            match operation, bare with
            | "fold", true -> "Option.fold", $"choose ({folder}) 3<m> (Some 2<s>)", $"choose ({folder}) 5<m> None"
            | "foldBack", true -> "Option.foldBack", $"choose ({folder}) (Some 2<s>) 3<m>", $"choose ({folder}) None 5<m>"
            | "fold", false -> $"Option.fold ({folder}) 3<m>", "choose (Some 2<s>)", "choose None"
            | _ -> $"Option.foldBack ({folder}) None", "choose 3<m>", "choose 5<m>"
        let result = OptionFolds.check $"""
[<EntryPoint>]
let main _ =
    let choose = {formation}
    let present = {present}
    let absent = {absent}
    if present >= 3<m> && absent >= 3<m> then 0 else 1
"""
        let graph = result.Graph
        let residuals =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Lambda ([(name, _, formal)], body, captures, _, _)
                    when node.IsReachable && captures.Length = 2 &&
                         name = (if operation = "fold" then "__option" else "__state") ->
                    Some (formal, body, captures)
                | _ -> None)
            |> Seq.toList
        Assert.NotEmpty residuals
        for formal, body, captures in residuals do
            match graph.Nodes[body].Kind with
            | SemanticKind.Sequential [folder; second; third; choice] ->
                let operands = [folder; second; third]
                let state, input = if operation = "fold" then second, third else third, second
                OptionFolds.assertFold operation result folder state input choice
                // These references belong to this residual scope. Their definitions
                // retain the two captured snapshots and its final logical formal.
                let definitions = captures |> List.map (fun capture -> capture.SourceNodeId |> Option.get)
                List.iter2 (fun operand definition ->
                    match graph.Nodes[operand].Kind with
                    | SemanticKind.VarRef (_, Some actual) -> Assert.Equal(definition, actual)
                    | kind -> failwithf "Residual operand lost its resolved local reference: %A" kind)
                    operands (definitions @ [formal])
                Assert.DoesNotContain(operands, fun id ->
                    match graph.Nodes[id].Kind with
                    | SemanticKind.Application _ | SemanticKind.DUEliminate _ -> true
                    | _ -> false)
            | kind -> failwithf "Residual operands do not dominate both fold branches: %A" kind

    [<Theory>]
    [<InlineData("fold", "Some 2<s>")>]
    [<InlineData("fold", "None")>]
    [<InlineData("foldBack", "Some 2<s>")>]
    [<InlineData("foldBack", "None")>]
    member _.``Function valued state remains behind the declared boundary after all supplied operands``(operation: string, input: string) =
        let folder = OptionFolds.folder operation "(state: int<m> -> int<m>)" "(_: int<s>)" "state"
        let expression = OptionFolds.call operation "factory ()" "initial ()" "input ()"
        let result = OptionFolds.check $"""
let factory () = {folder}
let initial () = fun (value: int<m>) -> value
let input () : int<s> option = {input}
let argument () = 3<m>
let observed = {expression} (argument ())
[<EntryPoint>]
let main _ = if observed = 3<m> then 0 else 1
"""
        match (OptionFolds.value "observed" result).Kind with
        | SemanticKind.Sequential [folder; second; third; argument; call] ->
            let state, input = if operation = "fold" then second, third else third, second
            OptionFolds.assertCall "factory" result folder
            OptionFolds.assertCall "initial" result state
            OptionFolds.assertCall "input" result input
            OptionFolds.assertCall "argument" result argument
            match result.Graph.Nodes[call].Kind with
            | SemanticKind.Application (choice, [actual]) ->
                Assert.Equal(argument, actual)
                OptionFolds.assertFold operation result folder state input choice
            | kind -> failwithf "Extra argument did not apply to the selected state: %A" kind
        | kind -> failwithf "Fold consumed an extra argument before its boundary: %A" kind

    [<Theory>]
    [<InlineData("fold")>]
    [<InlineData("foldBack")>]
    member _.``Nested option and unit states preserve their own shapes``(operation: string) =
        let optional = OptionFolds.call operation (OptionFolds.folder operation "(state: int<m> option)" "(_: int<s> option)" "state") "Some 3<m>" "Some None"
        let unit = OptionFolds.call operation (OptionFolds.folder operation "()" "(_: int<s> -> int<s>)" "()") "()" "Some (fun x -> x)"
        let result = OptionFolds.check $"""
let nested = {optional}
let unitState = {unit}
[<EntryPoint>]
let main _ = unitState; if Option.get nested = 3<m> then 0 else 1
"""
        DimensionalCases.same (OptionFolds.option (DimensionalCases.measuredInt DimensionalCases.metre)) (DimensionalCases.bindingType "nested" result)
        DimensionalCases.same Types.unitType (DimensionalCases.bindingType "unitState" result)

    [<Theory>]
    [<InlineData("fold")>]
    [<InlineData("foldBack")>]
    member _.``Bare and partial folds retain successive function valued state stages``(operation: string) =
        let folder = OptionFolds.folder operation "state" "(_: bool)" "state"
        let second = if operation = "fold" then "withFolder initial" else "withFolder None"
        let final = if operation = "fold" then "withSecond None" else "withSecond initial"
        let result = OptionFolds.check $"""
let initial (distance: int<m>) = fun (elapsed: int<s>) -> distance / elapsed
let choose = Option.{operation}
let withFolder = choose ({folder})
let withSecond = {second}
let chosen = {final}
let withDistance = chosen 6<m>
let observed = withDistance 2<s>
[<EntryPoint>]
let main _ = if observed = 3<m/s> then 0 else 1
"""
        let metre = DimensionalCases.measuredInt DimensionalCases.metre
        let second = DimensionalCases.measuredInt DimensionalCases.second
        let speed = DimensionalCases.measuredInt (DimensionalCases.product(DimensionalCases.metre, DimensionalCases.power DimensionalCases.second -1I))
        DimensionalCases.same (NativeType.TFun(metre, NativeType.TFun(second, speed))) (DimensionalCases.bindingType "chosen" result)
        DimensionalCases.same (NativeType.TFun(second, speed)) (DimensionalCases.bindingType "withDistance" result)
        DimensionalCases.same speed (DimensionalCases.bindingType "observed" result)
        for name, calleeName in ["withDistance", "chosen"; "observed", "withDistance"] do
            match (OptionFolds.value name result).Kind with
            | SemanticKind.Application (callee, [_]) ->
                match result.Graph.Nodes[callee].Kind with
                | SemanticKind.VarRef (_, Some definition) -> Assert.Equal((OptionFolds.binding calleeName result).Id, definition)
                | kind -> failwithf "Stored state stage lost producing binding: %A" kind
            | kind -> failwithf "A function-valued state stage lost its own call: %A" kind

    [<Theory>]
    [<InlineData("fold")>]
    [<InlineData("foldBack")>]
    member _.``Stored folds retain their actual application obligation participants``(operation: string) =
        let folder = OptionFolds.folder operation "(state: int<m>)" "(_: int<s>)" "state"
        let second, last = if operation = "fold" then "3<m>", "Some 2<s>" else "Some 2<s>", "3<m>"
        let result = OptionFolds.check $"""
let stored = Option.{operation} ({folder}) ({second})
let observed = stored ({last})
[<EntryPoint>]
let main _ = if observed = 3<m> then 0 else 1
"""
        let graph = result.Graph
        let site = OptionFolds.value "observed" result
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
            | kind -> failwithf "Stored fold lost its definition: %A" kind
        | kind -> failwithf "Expected ordinary measured application: %A" kind

    [<Theory>]
    [<InlineData("module Option =\n    let fold (x: int<m>) = x\nlet value = Option.fold 2<m>")>]
    [<InlineData("type Surface = { foldBack: int<m> -> int<m> }\nlet Option = { foldBack = fun x -> x }\nlet value = Option.foldBack 2<m>")>]
    member _.``Lexical fold bindings retain precedence over native library lookup``(source: string) =
        let result = OptionFolds.check (source + "\n[<EntryPoint>]\nlet main _ = ignore value; 0")
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) (DimensionalCases.bindingType "value" result)

    [<Theory>]
    [<InlineData("let wrong = «Option.fold (fun (state: int<m>) (_: int<s>) -> state) 1<m> (Some 2<m>)»", "CCS8040")>]
    [<InlineData("let wrong = «Option.foldBack (fun (_: int<s>) (state: int<m>) -> state) (Some 2<m>)» 1<m>", "CCS8040")>]
    [<InlineData("let wrong = «Option.fold (fun (state: int<m>) (_: int<s>) -> state) 1<s>» None", "CCS8040")>]
    [<InlineData("let wrong = «Option.foldBack (fun (_: int<s>) (state: int<m>) -> state) None 1<s>»", "CCS8040")>]
    [<InlineData("let wrong = «Option.fold (fun (state: int<m>) (_: int<s>) -> 1<s>)» 1<m> None", "CCS8040")>]
    [<InlineData("let wrong = «Option.foldBack (fun (_: int<s>) (state: int<m>) -> 1<s>)» None 1<m>", "CCS8040")>]
    [<InlineData("let wrong = «Option.fold (fun (state: int<m>) (_: int<s>) -> true)» 1<m> None", "CCS8003")>]
    [<InlineData("let wrong = «Option.foldBack (fun (_: int<s>) (state: int<m>) -> true)» None 1<m>", "CCS8003")>]
    [<InlineData("let wrong = «Option.fold (fun (state: int<m>) -> state)» 1<m> None", "CCS8003")>]
    [<InlineData("let wrong = «Option.foldBack 1» None 1", "CCS8003")>]
    [<InlineData("let wrong = «Option.fold (fun (state: int<m>) (_: int<s>) -> state) 1<m> 2<s>»", "CCS8003")>]
    [<InlineData("let wrong = «Option.foldBack (fun (_: int<s>) (state: int<m>) -> state) 2<s>» 1<m>", "CCS8003")>]
    [<InlineData("let wrong = «Option.fold (fun (state: int<m>) (_: int<s>) -> state) 1<m> None ()»", "CCS8003")>]
    [<InlineData("let wrong = «Option.foldBack (fun (_: int<s>) (state: int<m>) -> state) None 1<m> ()»", "CCS8003")>]
    [<InlineData("let wrong = «Option.fold<int<m>>»", "CCS8004")>]
    [<InlineData("let wrong = «Option.foldBack<int<m>>»", "CCS8004")>]
    member _.``State payload result and arity mismatches retain exact rejecting diagnostics``(source: string, code: string) =
        OptionFolds.reject code source

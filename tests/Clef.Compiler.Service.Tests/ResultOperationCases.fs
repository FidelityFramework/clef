namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private Results =
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"
    let check source =
        let result =
            match parseAndCheck (prelude + source) "result-operations.clef" with
            | Success result -> result
            | CheckFailure result -> failwithf "Expected successful Result checking: %A" result.Diagnostics
            | ParseFailure errors -> failwithf "Parse failed: %A" errors
        DimensionalCases.noErrors result
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Error _ -> true | _ -> false)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Intrinsic info -> info.Module = IntrinsicModule.Result
            | _ -> false)
        for node in result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) do
            for child in node.Children do Assert.True(result.Graph.Nodes.ContainsKey child)
            match node.Kind with
            | SemanticKind.VarRef (_, Some definition) -> Assert.True(result.Graph.Nodes.ContainsKey definition)
            | SemanticKind.Lambda (_, _, captures, _, _) ->
                for capture in captures do
                    capture.SourceNodeId |> Option.iter (fun id -> Assert.True(result.Graph.Nodes.ContainsKey id))
            | _ -> ()
            match node.Kind with
            | SemanticKind.DUGetTag _ | SemanticKind.DUEliminate _ | SemanticKind.DUConstruct _
            | SemanticKind.Lambda _ | SemanticKind.PatternBinding _ ->
                Assert.True(Clef.Compiler.NativeTypedTree.UnionFind.freeTypeVars node.Type |> Set.isEmpty,
                            sprintf "A generic template reached the settled callable/DU graph: %A %A" node.Id node.Type)
            | _ -> ()
        result

    let binding name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name)
            | _ -> false)

    let value name result = result.Graph.Nodes[(binding name result).Children.Head]
    let metre = DimensionalCases.measuredInt DimensionalCases.metre
    let second = DimensionalCases.measuredInt DimensionalCases.second

    let resultType ok error = function
        | NativeType.TApp (tycon, [actualOk; actualError]) ->
            Assert.Equal("Result", tycon.Name)
            DimensionalCases.same ok actualOk
            DimensionalCases.same error actualError
        | ty -> failwithf "Expected canonical Result type: %A" ty

    let inputType operation = if operation = "mapError" then "Result<bool, int<m>>" else "Result<int<m>, bool>"
    let callback operation =
        if operation = "bind" then "fun (_: int<m>) -> (Ok 2<s>: Result<int<s>, bool>)"
        else "fun (_: int<m>) -> 2<s>"
    let input operation ok =
        match operation, ok with
        | "mapError", true -> "Ok true"
        | "mapError", false -> "Error 3<m>"
        | _, true -> "Ok 3<m>"
        | _, false -> "Error true"

    let assertCall name (result: CheckResult) id =
        match result.Graph.Nodes[id].Kind with
        | SemanticKind.Application (callee, _) ->
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.VarRef (actual, _) -> Assert.True(actual = name || actual.EndsWith("." + name), actual)
            | kind -> failwithf "Expected reference to %s: %A" name kind
        | kind -> failwithf "Expected call to %s: %A" name kind

    let assertChoice operation (result: CheckResult) callback input choice =
        let graph = result.Graph
        let payload caseName caseIndex id =
            match graph.Nodes[id].Kind with
            | SemanticKind.DUEliminate (source, index, name, ty) ->
                Assert.Equal(input, source)
                Assert.Equal(caseIndex, index)
                Assert.Equal(caseName, name)
                DimensionalCases.same ty graph.Nodes[id].Type
                match graph.Nodes[input].Type with
                | NativeType.TApp (_, types) -> DimensionalCases.same types[index] ty
                | ty -> failwithf "Result input lost its payload types: %A" ty
            | kind -> failwithf "Expected extraction within %s: %A" caseName kind
        match graph.Nodes[choice].Kind with
        | SemanticKind.IfThenElse (guard, okBranch, Some errorBranch) ->
            match graph.Nodes[guard].Kind with
            | SemanticKind.Application (_, [tag; expected]) ->
                match graph.Nodes[tag].Kind, graph.Nodes[expected].Kind with
                | SemanticKind.DUGetTag (original, ty), SemanticKind.Literal (NativeLiteral.Int (0L, _)) ->
                    Assert.Equal(input, original)
                    DimensionalCases.same graph.Nodes[input].Type ty
                | kinds -> failwithf "Result guard lost canonical Ok identity: %A" kinds
            | kind -> failwithf "Expected Result case test: %A" kind
            let unchanged, changed = if operation = "mapError" then okBranch, errorBranch else errorBranch, okBranch
            let unchangedName, unchangedIndex = if operation = "mapError" then "Ok", 0 else "Error", 1
            match graph.Nodes[unchanged].Kind with
            | SemanticKind.DUConstruct (name, index, Some retained, None) ->
                Assert.Equal(unchangedName, name)
                Assert.Equal(unchangedIndex, index)
                payload name index retained
                DimensionalCases.same graph.Nodes[choice].Type graph.Nodes[unchanged].Type
            | kind -> failwithf "Untouched payload was not reconstructed without conversion: %A" kind
            let call =
                if operation = "bind" then changed
                else
                    match graph.Nodes[changed].Kind with
                    | SemanticKind.DUConstruct (name, index, Some mapped, None) ->
                        Assert.Equal((if operation = "mapError" then "Error" else "Ok"), name)
                        Assert.Equal((if operation = "mapError" then 1 else 0), index)
                        DimensionalCases.same graph.Nodes[choice].Type graph.Nodes[changed].Type
                        mapped
                    | kind -> failwithf "Mapped payload lost typed Result construction: %A" kind
            match graph.Nodes[call].Kind with
            | SemanticKind.Application (actualCallback, [argument]) ->
                Assert.Equal(callback, actualCallback)
                payload (if operation = "mapError" then "Error" else "Ok") (if operation = "mapError" then 1 else 0) argument
                if operation = "bind" then DimensionalCases.same graph.Nodes[choice].Type graph.Nodes[call].Type
            | kind -> failwithf "Callback lost its case-specific payload: %A" kind
        | kind -> failwithf "Expected Result branch selection: %A" kind

    let reject code (marked: string) =
        let start, finish = marked.IndexOf('«'), marked.IndexOf('»')
        Assert.True(start >= 0 && finish > start)
        let before, span = marked.Substring(0, start), marked.Substring(start + 1, finish - start - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "result-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + span) }
        let source = prelude + marked.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let matches = result.Diagnostics |> List.filter (fun item ->
                item.Code = code && Diagnostic.effectiveSeverity item = NativeDiagnosticSeverity.Error)
            Assert.True(matches.Length = 1, sprintf "Expected one %s: %A" code result.Diagnostics)
            let diagnostic = Assert.Single matches
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Invalid Result reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s: %A" code errors

[<Trait("Category", "NTU"); Trait("Subcategory", "ResultOperations")>]
type ResultOperationCases() =
    [<Theory>]
    [<InlineData("map", true)>]
    [<InlineData("map", false)>]
    [<InlineData("mapError", true)>]
    [<InlineData("mapError", false)>]
    [<InlineData("bind", true)>]
    [<InlineData("bind", false)>]
    member _.``Direct operations sequence inputs and preserve typed payloads in their own cases``(operation: string, ok: bool) =
        let result = Results.check $"""
let factory () = {Results.callback operation}
let input () : {Results.inputType operation} = {Results.input operation ok}
let observed = Result.{operation} (factory ()) (input ())
[<EntryPoint>]
let main _ = ignore observed; 0
"""
        let ty = DimensionalCases.bindingType "observed" result
        if operation = "mapError" then Results.resultType Types.boolType Results.second ty
        else Results.resultType Results.second Types.boolType ty
        match (Results.value "observed" result).Kind with
        | SemanticKind.Sequential [callback; input; choice] ->
            Results.assertCall "factory" result callback
            Results.assertCall "input" result input
            Results.assertChoice operation result callback input choice
        | kind -> failwithf "Result operands lost eager source order: %A" kind

    [<Theory>]
    [<InlineData("map")>]
    [<InlineData("mapError")>]
    [<InlineData("bind")>]
    member _.``Both pipe directions preserve their written input order``(operation: string) =
        let result = Results.check $"""
let factory () = {Results.callback operation}
let input () : {Results.inputType operation} = {Results.input operation true}
let forward = input () |> Result.{operation} (factory ())
let backward = Result.{operation} (factory ()) <| input ()
[<EntryPoint>]
let main _ = ignore forward; ignore backward; 0
"""
        match (Results.value "forward" result).Kind with
        | SemanticKind.Sequential [first; call] ->
            Results.assertCall "input" result first
            match result.Graph.Nodes[call].Kind with
            | SemanticKind.Sequential [callback; input; choice] ->
                Assert.Equal(first, input)
                Results.assertCall "factory" result callback
                Results.assertChoice operation result callback input choice
            | kind -> failwithf "Forward pipe lost its retained operand: %A" kind
        | kind -> failwithf "Forward pipe lost written order: %A" kind
        match (Results.value "backward" result).Kind with
        | SemanticKind.Sequential [callback; input; choice] ->
            Results.assertCall "factory" result callback
            Results.assertCall "input" result input
            Results.assertChoice operation result callback input choice
        | kind -> failwithf "Backward pipe lost written order: %A" kind

    [<Theory>]
    [<InlineData("map")>]
    [<InlineData("mapError")>]
    [<InlineData("bind")>]
    member _.``Partial formation snapshots the callback and retains its shared capture identity``(operation: string) =
        let body = if operation = "bind" then "(Ok 2<s>: Result<int<s>, bool>)" else "2<s>"
        let result = Results.check $"""
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let mutable callback = fun (_: int<m>) -> calls <- calls + 1; {body}
    let stored = Result.{operation} callback
    callback <- {Results.callback operation}
    let observed = stored ({Results.input operation true}: {Results.inputType operation})
    ignore observed
    0
"""
        let graph = result.Graph
        match (Results.value "stored" result).Kind with
        | SemanticKind.Sequential [snapshot; closure] ->
            match graph.Nodes[snapshot].Kind, graph.Nodes[graph.Nodes[snapshot].Children.Head].Kind with
            | SemanticKind.Binding (_, false, false, _), SemanticKind.VarRef (_, Some source) ->
                Assert.Equal((Results.binding "callback" result).Id, source)
            | kinds -> failwithf "Partial lost its callback snapshot: %A" kinds
            match graph.Nodes[closure].Kind with
            | SemanticKind.Lambda ([(_, _, formal)], body, [capture], _, _) ->
                Assert.Equal(Some snapshot, capture.SourceNodeId)
                Assert.False capture.IsMutable
                match graph.Nodes[body].Kind with
                | SemanticKind.Sequential [callback; input; choice] ->
                    match graph.Nodes[callback].Kind, graph.Nodes[input].Kind with
                    | SemanticKind.VarRef (_, Some source), SemanticKind.VarRef (_, Some parameter) ->
                        Assert.Equal(snapshot, source)
                        Assert.Equal(formal, parameter)
                    | kinds -> failwithf "Residual lost local source identities: %A" kinds
                    Results.assertChoice operation result callback input choice
                | kind -> failwithf "Residual operands do not precede branch selection: %A" kind
            | kind -> failwithf "Partial lost its one-input closure: %A" kind
        | kind -> failwithf "Partial lost its formation boundary: %A" kind
        let calls = Results.binding "calls" result
        Assert.Contains(graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Lambda (_, _, captures, _, _) -> captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some calls.Id)
            | _ -> false)

    [<Theory>]
    [<InlineData("map")>]
    [<InlineData("mapError")>]
    [<InlineData("bind")>]
    member _.``Bare aliases instantiate independent measures and explicit argument order through record fields``(operation: string) =
        let genericArgs = if operation = "mapError" then "bool, int<m>, int<s>" else "int<m>, int<s>, bool"
        let secondCallback = if operation = "bind" then "fun (_: float<s^-1>) -> (Ok (): Result<unit, int<m>>)" else "fun (_: float<s^-1>) -> ()"
        let inverseInput = if operation = "mapError" then "Error -0.25<s^-1>: Result<int<m>, float<s^-1>>" else "Ok -0.25<s^-1>: Result<float<s^-1>, int<m>>"
        let output = if operation = "mapError" then "Result<bool, int<s>>" else "Result<int<s>, bool>"
        let result = Results.check $"""
type Surface = {{ choose: ({if operation = "bind" then "int<m> -> Result<int<s>, bool>" else "int<m> -> int<s>"}) -> {Results.inputType operation} -> {output} }}
let choose = Result.{operation}
let first = choose ({Results.callback operation}) ({Results.input operation true}: {Results.inputType operation})
let inverse = choose ({secondCallback}) ({inverseInput})
let surface = {{ choose = Result.{operation}<{genericArgs}> }}
let stored = surface.choose ({Results.callback operation})
let observed = stored ({Results.input operation false}: {Results.inputType operation})
[<EntryPoint>]
let main _ = ignore first; ignore inverse; ignore observed; 0
"""
        for name in ["first"; "observed"] do
            let ty = DimensionalCases.bindingType name result
            if operation = "mapError" then Results.resultType Types.boolType Results.second ty
            else Results.resultType Results.second Types.boolType ty
        let inverse = DimensionalCases.bindingType "inverse" result
        if operation = "mapError" then Results.resultType Results.metre Types.unitType inverse
        else Results.resultType Types.unitType Results.metre inverse

    [<Theory>]
    [<InlineData("map")>]
    [<InlineData("mapError")>]
    [<InlineData("bind")>]
    member _.``Module and local aliases specialize their declaration membership before DU realization``(operation: string) =
        let otherCallback = if operation = "bind" then "fun (_: bool) -> (Ok (): Result<unit, int<m>>)" else "fun (_: bool) -> ()"
        let otherInput = if operation = "mapError" then "Error true: Result<int<m>, bool>" else "Ok true: Result<bool, int<m>>"
        let result = Results.check $"""
let moduleChoose = Result.{operation}
[<EntryPoint>]
let main _ =
    let localChoose = Result.{operation}
    let first = moduleChoose ({Results.callback operation}) ({Results.input operation true}: {Results.inputType operation})
    let second = moduleChoose ({otherCallback}) ({otherInput})
    let third = localChoose ({Results.callback operation}) ({Results.input operation false}: {Results.inputType operation})
    let fourth = localChoose ({otherCallback}) ({otherInput})
    ignore first; ignore second; ignore third; ignore fourth
    0
"""
        let graph = result.Graph
        for original in ["moduleChoose"; "localChoose"] do
            Assert.DoesNotContain(graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Binding (name, _, _, _) -> name = original | _ -> false)
            let clones = graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.Binding (name, _, _, _) -> name.StartsWith(original + "__mono") | _ -> false) |> Seq.toList
            Assert.Equal(2, clones.Length)
            let cloneIds = clones |> List.map (fun node -> node.Id) |> Set.ofList
            let uses = graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with SemanticKind.VarRef (name, Some definition) when name = original -> Some definition | _ -> None) |> Seq.toList
            Assert.Equal<Set<NodeId>>(cloneIds, Set.ofList uses)
            for clone in clones do
                Assert.Contains(graph.Nodes.Values, fun node ->
                    match node.Kind with
                    | SemanticKind.ModuleDef (_, members) | SemanticKind.Sequential members -> List.contains clone.Id members
                    | _ -> false)
        for node in graph.Nodes.Values do
            match node.Kind with
            | SemanticKind.ModuleDef (_, members) ->
                Assert.Empty node.Children
                let membership =
                    kindEdges node.Id node.Kind
                    |> List.filter (fun edge -> edge.Role = EdgeRole.Member)
                    |> List.sortBy _.Ordinal
                Assert.Equal<int list>([0 .. members.Length - 1], membership |> List.map _.Ordinal)
                let referenced = membership |> List.map (fun edge ->
                    Assert.Equal(EdgeClass.Reference, edge.Class)
                    Assert.Equal(node.Id, edge.Target)
                    Assert.Single edge.Sources)
                Assert.Equal<NodeId list>(members, referenced)
                for memberId in members do
                    Assert.True(graph.Nodes.ContainsKey memberId)
                    Assert.Equal(Some node.Id, graph.Nodes[memberId].Parent)
            | SemanticKind.Sequential members ->
                Assert.Equal<NodeId list>(members, node.Children)
                for memberId in members do Assert.True(graph.Nodes.ContainsKey memberId)
            | _ -> ()

    [<Fact>]
    member _.``Unused generic Result aliases do not become unresolved closure templates``() =
        let result = Results.check """
let unusedMap = Result.map
let unusedMapError = Result.mapError
let unusedBind = Result.bind
[<EntryPoint>]
let main _ = 0
"""
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Binding (name, _, _, _) -> ["unusedMap"; "unusedMapError"; "unusedBind"] |> List.contains name
            | _ -> false)

    [<Theory>]
    [<InlineData("map")>]
    [<InlineData("mapError")>]
    [<InlineData("bind")>]
    member _.``Untouched function payload retains the closure value and its mutable capture``(operation: string) =
        let input = if operation = "mapError" then "Ok payload: Result<unit -> int<m>, unit>" else "Error payload: Result<unit, unit -> int<m>>"
        let callback = if operation = "bind" then "fun () -> (Ok true: Result<bool, unit -> int<m>>)" else "fun () -> true"
        let result = Results.check $"""
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let payload = fun () -> calls <- calls + 1; 3<m>
    let observed = Result.{operation} ({callback}) ({input})
    ignore observed
    calls
"""
        match (Results.value "observed" result).Kind with
        | SemanticKind.Sequential [callback; input; choice] -> Results.assertChoice operation result callback input choice
        | kind -> failwithf "Function payload escaped ordinary Result handling: %A" kind
        let calls = Results.binding "calls" result
        match (Results.value "payload" result).Kind with
        | SemanticKind.Lambda ([_], _, [capture], _, _) ->
            Assert.True capture.IsMutable
            Assert.Equal(Some calls.Id, capture.SourceNodeId)
        | kind -> failwithf "Payload lost its explicit unit argument or storage identity: %A" kind

    [<Theory>]
    [<InlineData("map")>]
    [<InlineData("mapError")>]
    [<InlineData("bind")>]
    member _.``Stored Result calls retain resident application obligation participants``(operation: string) =
        let result = Results.check $"""
let stored = Result.{operation} ({Results.callback operation})
let observed = stored ({Results.input operation true}: {Results.inputType operation})
[<EntryPoint>]
let main _ = ignore observed; 0
"""
        let graph = result.Graph
        let site = Results.value "observed" result
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
            | kind -> failwithf "Stored Result call lost its producing definition: %A" kind
        | kind -> failwithf "Stored call lost its ordinary application site: %A" kind

    [<Theory>]
    [<InlineData("module Result =\n    let map (value: int<m>) = value\nlet observed = Result.map 3<m>")>]
    [<InlineData("type Surface = { map: int<m> -> int<m> }\nlet Result = { map = fun value -> value }\nlet observed = Result.map 3<m>")>]
    member _.``Lexical Result modules and fields take precedence over library schemes``(source: string) =
        let result = Results.check (source + "\n[<EntryPoint>]\nlet main _ = if observed = 3<m> then 0 else 1\n")
        DimensionalCases.same Results.metre (DimensionalCases.bindingType "observed" result)

    [<Theory>]
    [<InlineData("CCS8040", "let wrong = «Result.map (fun (_: int<m>) -> true) (Ok 2<s>: Result<int<s>, bool>)»")>]
    [<InlineData("CCS8040", "let wrong = «Result.mapError (fun (_: int<m>) -> true) (Error 2<s>: Result<bool, int<s>>)»")>]
    [<InlineData("CCS8040", "let wrong = «Result.bind (fun (_: int<m>) -> (Ok true: Result<bool, bool>)) (Ok 2<s>: Result<int<s>, bool>)»")>]
    [<InlineData("CCS8040", "let stored = Result.map (fun (_: float<m^-1>) -> true)\nlet wrong = «stored (Ok 0.25<s^-1>: Result<float<s^-1>, bool>)»")>]
    [<InlineData("CCS8040", "let stored = Result.mapError (fun (_: float<m^-1>) -> true)\nlet wrong = «stored (Error 0.25<s^-1>: Result<bool, float<s^-1>>)»")>]
    [<InlineData("CCS8040", "let wrong = «Result.bind (fun (_: bool) -> (Error 3<m>: Result<bool, int<m>>)) (Error 2<s>: Result<bool, int<s>>)»")>]
    [<InlineData("CCS8040", "let wrong = «Result.map<int<m>, int<s>, bool> (fun (_: int<m>) -> 1<m>)» (Ok 1<m>)")>]
    [<InlineData("CCS8040", "let wrong = «Result.mapError<bool, int<m>, int<s>> (fun (_: int<m>) -> 1<m>)» (Error 1<m>)")>]
    [<InlineData("CCS8040", "let wrong = «Result.bind<int<m>, int<s>, bool> (fun (_: int<m>) -> (Ok 1<m>: Result<int<m>, bool>))» (Ok 1<m>)")>]
    [<InlineData("CCS8003", "let wrong = «Result.map 3» (Ok true)")>]
    [<InlineData("CCS8003", "let wrong = «Result.mapError false» (Error true)")>]
    [<InlineData("CCS8003", "let wrong = «Result.bind (fun (_: bool) -> 3)» (Ok true)")>]
    [<InlineData("CCS8003", "let wrong = «Result.map (fun (_: bool) -> true) true»")>]
    [<InlineData("CCS8003", "let wrong = «Result.mapError (fun (_: bool) -> true) (Some true)»")>]
    [<InlineData("CCS8003", "let wrong = «Result.bind (fun (_: bool) -> (Ok true: Result<bool, bool>)) true»")>]
    [<InlineData("CCS8003", "let wrong = «Result.map (fun (_: bool) -> true) (Ok true: Result<bool, bool>) 3»")>]
    [<InlineData("CCS8004", "let wrong = «Result.map<int<m>, bool>»")>]
    [<InlineData("CCS8004", "let wrong = «Result.mapError<bool, int<m>>»")>]
    [<InlineData("CCS8004", "let wrong = «Result.bind<int<m>, bool>»")>]
    member _.``Invalid Result contracts fail with exact effective diagnostics``(code: string, source: string) =
        Results.reject code source
